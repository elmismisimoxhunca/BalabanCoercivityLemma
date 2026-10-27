import CvN5

/-!
# CvN5b -- the two endpoints of the path (lane cover_necessary_20261016)

* `Ginv_form`: `⟪x, Ginv x⟫ = ⟪W x, Δ W x⟫ + ‖T x‖² + ⟪x, Q*aQ x⟫` on `E₀` (3.122).
* `Ginv_psd_one` (θ = 0): at the constant configuration `U ≡ 1` the operator `Ginv` is positive semidefinite
  (`Δ(1) = D*χD`: the `Δ'` terms vanish because `Re U(∂p) - 1 = 0` and `Im U(∂p) = 0`).
* `Ginv_neg_flip` (θ = π): at `U = 1[b ↦ -1]`, with `b` based farther than `9 ell` from `Ω₁`, `b` a bond of `E₀`, and a plaquette
  `p₀ ∈ plaqIn Ω₀` having `b` as a boundary bond, the single-bond field `y = X δ_b` has
  `⟪y, Ginv y⟫ ≤ (a - 1) ‖X‖²`: `R D* y = 0` (so `T y = 0`, `W y = y`), the mass term is at most `a ‖X‖²`, and every plaquette
  contributes `cos π ‖X‖² = -‖X‖²` if it contains `b`, `0` otherwise.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace AdalyFormal.CoverNec

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply gradValueCovariant curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.SuTwoInner (inner_eq_trace)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

theorem contrib_flip (hL : ∀ μ, 1 ≤ L μ) (b : Bond L) (X : SuTwo) (p : PeriodicLatticePlaquette L) :
    ‖curlValueCovariant (Upi b) (Pi.single b X) p‖ ^ 2 +
        (1 / 2 : ℝ) * bilPlaq (Upi b) p (Pi.single b X) (Pi.single b X) =
      if b ∈ periodicPlaquetteBoundaryEdges p then -‖X‖ ^ 2 else 0 := by
  obtain ⟨z, ⟨⟨μ, ν⟩, hμν⟩⟩ := p
  simp only at hμν
  have hμν' : μ ≠ ν := ne_of_lt hμν
  have sμ := shift_ne hL z μ
  have sν := shift_ne hL z ν
  have d12 : ((periodicLatticeShift z μ, ν) : Bond L) ≠ (z, μ) := fun h => hμν' (congrArg Prod.snd h).symm
  have d13 : ((periodicLatticeShift z ν, μ) : Bond L) ≠ (z, μ) := fun h => sν (congrArg Prod.fst h)
  have d14 : ((z, ν) : Bond L) ≠ (z, μ) := fun h => hμν' (congrArg Prod.snd h).symm
  have d23 : ((periodicLatticeShift z ν, μ) : Bond L) ≠ (periodicLatticeShift z μ, ν) :=
    fun h => hμν' (congrArg Prod.snd h)
  have d24 : ((z, ν) : Bond L) ≠ (periodicLatticeShift z μ, ν) := fun h => sμ (congrArg Prod.fst h).symm
  have d34 : ((z, ν) : Bond L) ≠ (periodicLatticeShift z ν, μ) := fun h => hμν' (congrArg Prod.snd h).symm
  have hmem : b ∈ periodicPlaquetteBoundaryEdges ((z, ⟨(μ, ν), hμν⟩) : PeriodicLatticePlaquette L) ↔
      b = (z, μ) ∨ b = (periodicLatticeShift z μ, ν) ∨ b = (periodicLatticeShift z ν, μ) ∨ b = (z, ν) := by
    simp [periodicPlaquetteBoundaryEdges]
  rw [bilPlaq_apply, second_Upi, add_zero, firstBilPlaq_apply, curlMatLM_apply, curl_Upi, reHol_Upi]
  have key : ∀ C : SuTwo, ((C : M2m) * (C : M2m) = (X : M2m) * (X : M2m)) → ‖C‖ ^ 2 = ‖X‖ ^ 2 →
      ‖C‖ ^ 2 + (1 / 2 : ℝ) * (Matrix.trace (Complex.I • (C : M2m) * (Complex.I • (C : M2m)) *
        ((1 / 2 : ℂ) • ((-1 : M2m) + -1) - 1))).re = -‖X‖ ^ 2 := by
    intro C hC hn
    rw [half_neg_two, trace_flip, hC, hn]
    have := norm_sq_trace X
    linarith
  by_cases hb : b ∈ periodicPlaquetteBoundaryEdges ((z, ⟨(μ, ν), hμν⟩) : PeriodicLatticePlaquette L)
  · rw [if_pos hb]
    rcases hmem.1 hb with rfl | rfl | rfl | rfl
    · simp only [Pi.single_apply, Upi_coe, if_pos rfl, if_neg d12, if_neg d13, if_neg d14, add_zero, sub_zero,
        mul_one, one_mul, neg_mul, mul_neg]
      exact key X rfl rfl
    · simp only [Pi.single_apply, Upi_coe, if_pos rfl, if_neg d12.symm, if_neg d23, if_neg d24, zero_add, add_zero,
        sub_zero, mul_one, one_mul, neg_mul, mul_neg]
      exact key X rfl rfl
    · simp only [Pi.single_apply, Upi_coe, if_pos rfl, if_neg d13.symm, if_neg d23.symm, if_neg d34, zero_add,
        add_zero, sub_zero, zero_sub, mul_one, one_mul, neg_mul, mul_neg]
      refine key (-X) ?_ (by rw [norm_neg])
      simp only [NegMemClass.coe_neg, neg_mul_neg]
    · simp only [Pi.single_apply, Upi_coe, if_pos rfl, if_neg d14.symm, if_neg d24.symm, if_neg d34.symm, zero_add,
        add_zero, sub_zero, zero_sub, mul_one, one_mul, neg_mul, mul_neg]
      refine key (-X) ?_ (by rw [norm_neg])
      simp only [NegMemClass.coe_neg, neg_mul_neg]
  · rw [if_neg hb]
    have h1 : (z, μ) ≠ b := fun h => hb (hmem.2 (Or.inl h.symm))
    have h2 : (periodicLatticeShift z μ, ν) ≠ b := fun h => hb (hmem.2 (Or.inr (Or.inl h.symm)))
    have h3 : (periodicLatticeShift z ν, μ) ≠ b := fun h => hb (hmem.2 (Or.inr (Or.inr (Or.inl h.symm))))
    have h4 : (z, ν) ≠ b := fun h => hb (hmem.2 (Or.inr (Or.inr (Or.inr h.symm))))
    simp only [Pi.single_apply, if_neg h1, if_neg h2, if_neg h3, if_neg h4, sub_zero, add_zero, norm_zero,
      ZeroMemClass.coe_zero, smul_zero, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, mul_zero]
    norm_num

#print axioms contrib_flip

end AdalyFormal.CoverNec
