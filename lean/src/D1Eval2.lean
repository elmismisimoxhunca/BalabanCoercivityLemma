import D1Eval

/-!
# D1Eval2 -- the single-bond field and the support of the plaquette sum.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)

variable {L : PeriodicLatticeExtent}

open Classical in
/-- the single-bond field `X δ_{b0}`. -/
noncomputable def sing (b0 : Bond L) (X : SuTwo) : BondFnL2 L :=
  WithLp.toLp 2 (fun b => if b = b0 then X else 0)

open Classical in
theorem sing_apply (b0 : Bond L) (X : SuTwo) (b : Bond L) :
    (sing b0 X) b = if b = b0 then X else 0 := rfl

theorem sing_apply_ne (b0 : Bond L) (X : SuTwo) {b : Bond L} (h : b ≠ b0) : (sing b0 X) b = 0 := by
  rw [sing_apply, if_neg h]

theorem sing_apply_self (b0 : Bond L) (X : SuTwo) : (sing b0 X) b0 = X := by
  rw [sing_apply, if_pos rfl]

/-- a plaquette none of whose four boundary positions carries the field has zero curl and zero `bilPlaq`. -/
theorem curl_bil_zero (U : PeriodicLinkConfiguration SU2m L) (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (h1 : A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 0) (h2 : A (p.1, p.2.1.2) = 0)
    (h3 : A (p.1, p.2.1.1) = 0) (h4 : A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0) :
    curlValueCovariant U A p = 0 ∧ bilPlaq U p A A = 0 := by
  have hcurl : curlValueCovariant U A p = 0 := by
    unfold curlValueCovariant
    rw [h1, h2, h3, h4]; simp
  refine ⟨hcurl, ?_⟩
  have ha1 : a1LM U p A = 0 := by
    rw [a1LM_apply]; unfold AprimeZW; rw [h1]; simp
  have ha2 : a2LM p A = 0 := by
    rw [a2LM_apply]; unfold AprimeWX; rw [h2]; simp
  have ha3 : a3LM p A = 0 := by
    rw [a3LM_apply]; unfold AprimeXY; rw [h3]; simp
  have ha4 : a4LM U p A = 0 := by
    rw [a4LM_apply]; unfold AprimeYZ; rw [h4]; simp
  have hc : curlMatLM U p A = 0 := by
    rw [curlMatLM_apply, hcurl]; rfl
  rw [bilPlaq_atoms]
  simp [b1LM, b2LM, b3LM, b4LM, ha1, ha2, ha3, ha4, hc, smulILM_apply]

/-- the four plaquettes on the bond `(x,0)`: base `x`, directions `(0,ν)`. -/
def P1 (x : PeriodicLatticeSite L) (ν : {ν : Fin 3 // 0 < ν}) : PeriodicLatticePlaquette L :=
  (x, ⟨((0 : Fin 3), ν.1), ν.2⟩)

/-- base `x - e_ν`, directions `(0,ν)`. -/
def P2 (x : PeriodicLatticeSite L) (ν : {ν : Fin 3 // 0 < ν}) : PeriodicLatticePlaquette L :=
  (periodicLatticeShiftBack x ν.1, ⟨((0 : Fin 3), ν.1), ν.2⟩)

theorem shiftBack_shift' (z : PeriodicLatticeSite L) (ν : Fin 3) : periodicLatticeShiftBack (periodicLatticeShift z ν) ν = z :=
  periodicLatticeShiftBack_shift z ν

theorem plaq_cases (x : PeriodicLatticeSite L) (p : PeriodicLatticePlaquette L) :
    ((periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ≠ (x, (0 : Fin 3)) ∧ (p.1, p.2.1.2) ≠ (x, (0 : Fin 3)) ∧
      (p.1, p.2.1.1) ≠ (x, (0 : Fin 3)) ∧ (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ≠ (x, (0 : Fin 3))) ∨
    ∃ ν : {ν : Fin 3 // 0 < ν}, p = P1 x ν ∨ p = P2 x ν := by
  obtain ⟨z, ⟨⟨μ, ν⟩, h⟩⟩ := p
  have hν : 0 < ν := lt_of_le_of_lt (Fin.zero_le μ) h
  by_cases h3 : (z, μ) = (x, (0 : Fin 3))
  · right
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
    exact ⟨⟨ν, hν⟩, Or.inl rfl⟩
  by_cases h1 : (periodicLatticeShift z ν, μ) = (x, (0 : Fin 3))
  · right
    obtain ⟨h1a, rfl⟩ := Prod.mk.inj h1
    refine ⟨⟨ν, hν⟩, Or.inr ?_⟩
    have : z = periodicLatticeShiftBack x ν := by rw [← h1a, shiftBack_shift']
    subst this
    rfl
  left
  refine ⟨h1, ?_, h3, ?_⟩
  · intro h2
    have h0 : ν = 0 := (Prod.mk.inj h2).2
    rw [h0] at hν
    exact lt_irrefl _ hν
  · intro h4
    have h0 : ν = 0 := (Prod.mk.inj h4).2
    rw [h0] at hν
    exact lt_irrefl _ hν

theorem P1_ne_P2 (x : PeriodicLatticeSite L) (hs : ∀ ν : Fin 3, periodicLatticeShift x ν ≠ x)
    (ν ν' : {ν : Fin 3 // 0 < ν}) : P1 x ν ≠ P2 x ν' := by
  intro h
  have h1 : x = periodicLatticeShiftBack x ν'.1 := congrArg Prod.fst h
  have h2 := periodicLatticeShift_shiftBack x ν'.1
  rw [← h1] at h2
  exact hs ν'.1 h2

theorem P1_inj (x : PeriodicLatticeSite L) : Function.Injective (P1 x) := by
  intro ν ν' h
  have := congrArg (fun p : PeriodicLatticePlaquette L => p.2.1.2) h
  exact Subtype.ext this

theorem P2_inj (x : PeriodicLatticeSite L) : Function.Injective (P2 x) := by
  intro ν ν' h
  have := congrArg (fun p : PeriodicLatticePlaquette L => p.2.1.2) h
  exact Subtype.ext this

theorem sum_plaq (x : PeriodicLatticeSite L) (hs : ∀ ν : Fin 3, periodicLatticeShift x ν ≠ x)
    (f : PeriodicLatticePlaquette L → ℝ)
    (hf : ∀ p : PeriodicLatticePlaquette L,
      ((periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ≠ (x, (0 : Fin 3)) ∧ (p.1, p.2.1.2) ≠ (x, (0 : Fin 3)) ∧
      (p.1, p.2.1.1) ≠ (x, (0 : Fin 3)) ∧ (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ≠ (x, (0 : Fin 3))) → f p = 0) :
    ∑ p, f p = ∑ ν : {ν : Fin 3 // 0 < ν}, (f (P1 x ν) + f (P2 x ν)) := by
  classical
  set T : Finset (PeriodicLatticePlaquette L) := Finset.univ.image (P1 x) ∪ Finset.univ.image (P2 x) with hT
  have h1 : ∑ p, f p = ∑ p ∈ T, f p := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => ?_)
    rcases plaq_cases x p with h | ⟨ν, h | h⟩
    · exact hf p h
    · exfalso; apply hp; rw [hT]; simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl ⟨ν, h.symm⟩
    · exfalso; apply hp; rw [hT]; simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inr ⟨ν, h.symm⟩
  rw [h1, hT, Finset.sum_union, Finset.sum_image (fun a _ b _ h => P1_inj x h),
    Finset.sum_image (fun a _ b _ h => P2_inj x h), Finset.sum_add_distrib]
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp1 hp2
  obtain ⟨ν, rfl⟩ := hp1
  obtain ⟨ν', h⟩ := hp2
  exact P1_ne_P2 x hs ν ν' h.symm

theorem hsInner_neg_neg (X : SuTwo) : hsInner (-X) (-X) = hsInner X X := by
  unfold hsInner; simp

/-- the value of the literal form on the single bond `(x,0)` when the four plaquettes on it have central holonomy `-1`:
`⟨A, Δ A⟩ = -4 ⟨X,X⟩` (two directions `ν`, two sides). -/
theorem delta_value (U : PeriodicLinkConfiguration SU2m L) (x : PeriodicLatticeSite L) (X : SuTwo)
    (hs : ∀ ν : Fin 3, periodicLatticeShift x ν ≠ x)
    (hol1 : ∀ ν : {ν : Fin 3 // 0 < ν}, ((holonomyElem U (P1 x ν) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1)
    (hol2 : ∀ ν : {ν : Fin 3 // 0 < ν}, ((holonomyElem U (P2 x ν) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1)
    (hU2 : ∀ ν : {ν : Fin 3 // 0 < ν}, U (periodicLatticeShiftBack x ν.1, ν.1) = 1) :
    (inner ℝ (sing (x, (0 : Fin 3)) X) (deltaKLocCLM U (Set.univ : Set (PeriodicLatticePlaquette L)) (sing (x, (0 : Fin 3)) X)) : ℝ)
      = -4 * hsInner X X := by
  classical
  rw [delta_form_sum]
  set A := WithLp.ofLp (sing (x, (0 : Fin 3)) X) with hA
  have hAe : ∀ b : Bond L, b ≠ (x, (0 : Fin 3)) → A b = 0 := fun b hb => sing_apply_ne _ _ hb
  have hA0 : A (x, (0 : Fin 3)) = X := sing_apply_self _ _
  have hf : ∀ p : PeriodicLatticePlaquette L,
      ((periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ≠ (x, (0 : Fin 3)) ∧ (p.1, p.2.1.2) ≠ (x, (0 : Fin 3)) ∧
      (p.1, p.2.1.1) ≠ (x, (0 : Fin 3)) ∧ (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ≠ (x, (0 : Fin 3))) →
      (hsInner (curlValueCovariant U A p) (curlValueCovariant U A p) + (1 / 2 : ℝ) * bilPlaq U p A A) = 0 := by
    intro p ⟨h1, h2, h3, h4⟩
    obtain ⟨hc, hb⟩ := curl_bil_zero U p A (hAe _ h1) (hAe _ h2) (hAe _ h3) (hAe _ h4)
    rw [hc, hb]
    unfold hsInner; simp
  rw [sum_plaq x hs _ hf]
  have hν : ∀ ν : {ν : Fin 3 // 0 < ν}, ν.1 ≠ 0 := fun ν => ne_of_gt ν.2
  have hy : ∀ ν : {ν : Fin 3 // 0 < ν}, periodicLatticeShiftBack x ν.1 ≠ x := by
    intro ν h
    apply hs ν.1
    have := periodicLatticeShift_shiftBack x ν.1
    rw [h] at this
    exact this
  have key : ∀ ν : {ν : Fin 3 // 0 < ν},
      (hsInner (curlValueCovariant U A (P1 x ν)) (curlValueCovariant U A (P1 x ν)) + (1 / 2 : ℝ) * bilPlaq U (P1 x ν) A A)
      + (hsInner (curlValueCovariant U A (P2 x ν)) (curlValueCovariant U A (P2 x ν)) + (1 / 2 : ℝ) * bilPlaq U (P2 x ν) A A)
      = -2 * hsInner X X := by
    intro ν
    rw [plaq_central U _ A (hol1 ν), plaq_central U _ A (hol2 ν)]
    have c1 : curlValueCovariant U A (P1 x ν) = X := by
      unfold curlValueCovariant P1
      simp only
      rw [hAe (periodicLatticeShift x 0, ν.1) (fun h => hν ν (Prod.mk.inj h).2),
        hAe (periodicLatticeShift x ν.1, 0) (fun h => hs ν.1 (Prod.mk.inj h).1),
        hAe (x, ν.1) (fun h => hν ν (Prod.mk.inj h).2), hA0]
      simp
    have c2 : curlValueCovariant U A (P2 x ν) = -X := by
      unfold curlValueCovariant P2
      simp only
      rw [hAe (periodicLatticeShiftBack x ν.1, 0) (fun h => hy ν (Prod.mk.inj h).1),
        hAe (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0, ν.1) (fun h => hν ν (Prod.mk.inj h).2),
        hAe (periodicLatticeShiftBack x ν.1, ν.1) (fun h => hν ν (Prod.mk.inj h).2),
        periodicLatticeShift_shiftBack, hA0, hU2 ν, AdalyFormal.Balaban.CovariantOperators.RMap_one]
      simp
    rw [c1, c2, hsInner_neg_neg]
    ring
  rw [Finset.sum_congr rfl (fun ν _ => key ν)]
  have hcard : Fintype.card {ν : Fin 3 // 0 < ν} = 2 := by decide
  rw [Finset.sum_const, Finset.card_univ, hcard]
  simp
  ring

#print axioms delta_value
#print axioms plaq_cases
#print axioms sum_plaq

end AdalyFormal.D1Literal
