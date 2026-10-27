import R7Fork.DM7e

/-!
# DM7f -- `Q*` injective (`Q` onto `L^2(frakB)`) for EVERY admissible tower at flat `U`; consequently `IsUnit N` follows from `IsUnit G1inv`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower Admissible)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)

theorem Qs_injective_gen (P : IngrBParams) (hU : P.U = flatCfg) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) : Function.Injective P.data.Qs := by
  classical
  rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra hne
  have hex : ∃ β : BIdx P.G, (WithLp.ofLp f) β ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (PiLp.ext (fun β => by simpa using h β))
  set S0 : Finset (BIdx P.G) := Finset.univ.filter (fun β => (WithLp.ofLp f) β ≠ 0) with hS0def
  have hS0 : S0.Nonempty := by
    obtain ⟨β, hβ⟩ := hex
    exact ⟨β, by simp [S0, hβ]⟩
  obtain ⟨β0, hβ0, hmax⟩ := Finset.exists_max_image S0 (fun β : BIdx P.G => (β.1 : ℕ)) hS0
  obtain ⟨j0, b0, hb0⟩ := β0
  have hj0 : (j0 : ℕ) ≤ P.k := Nat.lt_succ_iff.mp j0.2
  set X : SuTwo := (WithLp.ofLp f) ⟨j0, ⟨b0, hb0⟩⟩ with hXdef
  have hX : X ≠ 0 := (Finset.mem_filter.mp hβ0).2
  set d := dB P j0 hj0 b0 hb0 with hd
  have hAmem : (WithLp.toLp 2 (spike d X) : BondFnL2 (scaleUp P.ell P.k P.Lu)) ∈ bondSupp P.G := by
    intro e he
    show spike d X e = 0
    unfold spike
    rw [if_neg]
    rintro rfl
    exact he (dB_mem_bondsOm0 P hS j0 hj0 b0 hb0)
  set A : ↥(bondSupp P.G) := ⟨WithLp.toLp 2 (spike d X), hAmem⟩ with hA
  have Qrow : ∀ (j : Fin (P.k + 1)) (b : Bond (scaleUp P.ell P.k P.Lu)) (hb : b ∈ bondsLam P.G j),
      (P.data.Q A) ⟨j, ⟨b, hb⟩⟩ = lineCoarseRestrictSuTwo (P.ell ^ (j : ℕ)) (spike d X)
        (bhat P j (Nat.lt_succ_iff.mp j.2) b hb) := by
    intro j b hb
    exact Qfull_row P hU (iE P.G A) j b hb
  have h0 : ⟪P.data.Q A, f⟫ = 0 := by rw [P.data.Q_adj, hf, inner_zero_right]
  rw [PiLp.inner_apply, Finset.sum_eq_single (⟨j0, ⟨b0, hb0⟩⟩ : BIdx P.G)] at h0
  · -- the main term
    obtain ⟨r, hr, hrr⟩ := lcr_spike_self (pow_pos P.hell (j0 : ℕ)) (bhat P j0 hj0 b0 hb0) X
    have hq : (P.data.Q A) ⟨j0, ⟨b0, hb0⟩⟩ = r • X := by
      rw [Qrow j0 b0 hb0]
      exact hrr
    rw [hq] at h0
    have : ⟪r • X, (WithLp.ofLp f) ⟨j0, ⟨b0, hb0⟩⟩⟫ = r * ‖X‖ ^ 2 := by
      rw [← hXdef, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [this] at h0
    have hX2 : 0 < ‖X‖ ^ 2 := by positivity
    have := mul_pos hr hX2
    linarith
  · -- all other terms vanish
    intro β _ hβne
    obtain ⟨j, b, hb⟩ := β
    by_cases hfz : (WithLp.ofLp f) ⟨j, ⟨b, hb⟩⟩ = 0
    · rw [hfz, inner_zero_right]
    · have hmem : (⟨j, ⟨b, hb⟩⟩ : BIdx P.G) ∈ S0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfz⟩
      have hle : (j : ℕ) ≤ (j0 : ℕ) := hmax _ hmem
      have hQ0 : (P.data.Q A) ⟨j, ⟨b, hb⟩⟩ = 0 := by
        rw [Qrow j b hb]
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact lcr_spike_zero _ _ _
            (no_read_lower P hS j0 j hj0 hlt b0 b hb0 hb)
        · have hjj : j = j0 := Fin.ext heq
          subst hjj
          have hbb : b ≠ b0 := by
            intro h
            subst h
            exact hβne rfl
          exact lcr_spike_zero _ _ _ (no_read_same P j hj0 b0 b hb0 hb hbb)
      rw [hQ0, inner_zero_left]
  · intro h
    exact absurd (Finset.mem_univ _) h

#print axioms Qs_injective_gen

/-- **`IsUnit N` from `IsUnit G1inv`** at every admissible tower, flat `U`, `a >= 0`. -/
theorem isUnit_Nmat_of_G1inv {M R : ℕ} (P : IngrBParams) (hU : P.U = flatCfg) (ha : 0 ≤ P.a)
    (hS : Admissible P.ell M R P.k P.S) (hG : IsUnit P.G1inv) : IsUnit (GenP.Nmat P) :=
  isUnit_Nmat_of_Qs_inj P hU ha hG (Qs_injective_gen P hU hS)

#print axioms isUnit_Nmat_of_G1inv

end AdalyFormal.DirichletMono
