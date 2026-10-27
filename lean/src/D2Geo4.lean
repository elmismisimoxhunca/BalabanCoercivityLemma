import D2Geo3

/-!
# D2Geo4 -- summing over the torus: `⟨A, Δ_lit A⟩ = −12 K ⟨X,X⟩` and `‖A‖² = 29 K ⟨X,X⟩` for the two-layer field (`K` = number of columns).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NonVac
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.DeltaPrime

variable {L : PeriodicLatticeExtent} {Om : Set (PeriodicLatticeSite L)} {P Q N : ℕ}

/-- number of columns (the transverse coordinates). -/
noncomputable def Kcol (L : PeriodicLatticeExtent) : ℝ :=
  (Fintype.card ((i : Fin 2) → Fin (L i.succ + 1)) : ℝ)

theorem Kcol_pos (L : PeriodicLatticeExtent) : 0 < Kcol L := by
  unfold Kcol
  have : 0 < Fintype.card ((i : Fin 2) → Fin (L i.succ + 1)) := Fintype.card_pos
  exact_mod_cast this

theorem sum_layer (F : ℕ → ℝ) :
    ∑ z : PeriodicLatticeSite L, F (z 0).val = Kcol L * ∑ a : Fin (L 0 + 1), F a.val := by
  classical
  rw [← Equiv.sum_comp (Fin.consEquiv (fun μ : Fin 3 => Fin (L μ + 1)))]
  rw [Fintype.sum_prod_type]
  unfold Kcol
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp [Fin.consEquiv]

theorem sum_ind (M c Q : ℕ) (hc : c ≤ Q) (hQ : Q < M) (v : ℝ) :
    ∑ a : Fin M, (if a.val + c = Q then v else 0) = v := by
  rw [Finset.sum_eq_single (⟨Q - c, by omega⟩ : Fin M)]
  · simp only
    rw [if_pos (by omega)]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    apply Fin.ext
    simp only
    omega
  · intro h; exact absurd (Finset.mem_univ _) h

theorem Gv_decomp (Q : ℕ) (n : ℝ) (l : ℕ) :
    Gv Q n l = (if l + 1 = Q then -25 * n else 0) + (if l + 2 = Q then 9 * n else 0) + (if l + 3 = Q then 4 * n else 0) := by
  unfold Gv
  by_cases h1 : l + 1 = Q
  · rw [if_pos h1, if_pos h1, if_neg (by omega), if_neg (by omega)]; ring
  · by_cases h2 : l + 2 = Q
    · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, if_neg (by omega)]; ring
    · by_cases h3 : l + 3 = Q
      · rw [if_neg h1, if_neg h2, if_pos h3, if_neg h1, if_neg h2, if_pos h3]; ring
      · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h1, if_neg h2, if_neg h3]; ring

theorem amp_sq (Q l : ℕ) : amp Q l ^ 2 = (if l + 1 = Q then 25 else 0) + (if l + 2 = Q then 4 else 0) := by
  by_cases h1 : l + 1 = Q
  · rw [amp_a h1, if_pos h1, if_neg (by omega)]; norm_num
  · by_cases h2 : l + 2 = Q
    · rw [amp_b h2, if_neg h1, if_pos h2]; norm_num
    · rw [amp_z h1 h2, if_neg h1, if_neg h2]; norm_num

theorem layer_sum_G (H : SlabH Om P Q N) (n : ℝ) :
    ∑ a : Fin (L 0 + 1), Gv Q n a.val = -12 * n := by
  have hN0 := H.hN 0
  have hPQ := H.hPQ
  have hQN := H.hQN
  simp only [Gv_decomp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [sum_ind (L 0 + 1) 1 Q (by omega) (by omega), sum_ind (L 0 + 1) 2 Q (by omega) (by omega),
    sum_ind (L 0 + 1) 3 Q (by omega) (by omega)]
  ring

theorem layer_sum_amp (H : SlabH Om P Q N) :
    ∑ a : Fin (L 0 + 1), amp Q a.val ^ 2 = 29 := by
  have hN0 := H.hN 0
  have hPQ := H.hPQ
  have hQN := H.hQN
  simp only [amp_sq]
  rw [Finset.sum_add_distrib]
  rw [sum_ind (L 0 + 1) 1 Q (by omega) (by omega), sum_ind (L 0 + 1) 2 Q (by omega) (by omega)]
  norm_num

/-- `⟨A, Δ_lit(U_π) A⟩ = −12 K ⟨X,X⟩`. -/
theorem form_value (H : SlabH Om P Q N) (X : SuTwo) :
    (inner ℝ (Afield Q X) (deltaKLocCLM (Uth Om Real.pi) (Set.univ : Set (PeriodicLatticePlaquette L)) (Afield Q X)) : ℝ)
      = -12 * Kcol L * hsInner X X := by
  rw [delta_form_sum]
  have h1 : ∀ p : PeriodicLatticePlaquette L,
      (hsInner (curlValueCovariant (Uth Om Real.pi) (WithLp.ofLp (Afield Q X)) p) (curlValueCovariant (Uth Om Real.pi) (WithLp.ofLp (Afield Q X)) p)
        + (1 / 2 : ℝ) * bilPlaq (Uth Om Real.pi) p (WithLp.ofLp (Afield Q X)) (WithLp.ofLp (Afield Q X)))
      = contrib (Uth Om Real.pi) (WithLp.ofLp (Afield Q X)) p := fun p => rfl
  rw [Finset.sum_congr rfl (fun p _ => h1 p)]
  rw [Fintype.sum_prod_type]
  have h2 : ∀ z : PeriodicLatticeSite L,
      ∑ d : PeriodicPlaquetteDirections, contrib (Uth Om Real.pi) (WithLp.ofLp (Afield Q X)) (z, d)
        = Gv Q (hsInner X X) (z 0).val := by
    intro z
    rw [Finset.sum_congr rfl (fun d _ => contrib_Afield H X z d)]
    rw [Finset.sum_ite_eq']
    simp
  rw [Finset.sum_congr rfl (fun z _ => h2 z)]
  rw [sum_layer (fun l => Gv Q (hsInner X X) l), layer_sum_G H]
  ring

/-- `‖A‖² = 29 K ⟨X,X⟩`. -/
theorem normsq_Afield (H : SlabH Om P Q N) (X : SuTwo) :
    ‖(Afield Q X : BondFnL2 L)‖ ^ 2 = 29 * Kcol L * hsInner X X := by
  rw [PiLp.norm_sq_eq_of_L2]
  rw [Fintype.sum_prod_type]
  have h2 : ∀ z : PeriodicLatticeSite L,
      ∑ m : Fin 3, ‖(Afield Q X) (z, m)‖ ^ 2 = amp Q (z 0).val ^ 2 * hsInner X X := by
    intro z
    rw [Fin.sum_univ_three]
    have e0 : (Afield Q X) (z, 0) = 0 := by rw [Afield_apply]; simp
    have e2 : (Afield Q X) (z, 2) = 0 := by rw [Afield_apply]; simp
    have e1 : (Afield Q X) (z, 1) = (amp Q (z 0).val) • X := by rw [Afield_apply]; simp
    rw [e0, e1, e2]
    have : ‖(amp Q (z 0).val) • X‖ ^ 2 = amp Q (z 0).val ^ 2 * hsInner X X := by
      rw [← real_inner_self_eq_norm_sq]
      show hsInner _ _ = _
      rw [hsInner_smul_smul]
    rw [this]
    simp
  rw [Finset.sum_congr rfl (fun z _ => h2 z)]
  rw [sum_layer (fun l => amp Q l ^ 2 * hsInner X X), ← Finset.sum_mul, layer_sum_amp H]
  ring

#print axioms form_value
#print axioms normsq_Afield

end AdalyFormal.D1Literal
