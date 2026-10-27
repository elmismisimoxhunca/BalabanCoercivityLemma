import NtCvON3

/-!
# CvON4 -- `H0` is bijective on the nested staggered family for every `|t| < pi` (lane omega/near)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG

variable {ell M R : ℕ}

theorem Pn_H0_bijective_even (hell3 : 3 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (htπ : |t| < Real.pi) :
    Function.Bijective (H0 (neLam M R) (Pn ell M R (by omega) a t).Q1) := by
  have hell : 0 < ell := by omega
  have S := nested_stagSetup hell3 (Or.inl hE) hdvd hM hR
  have hT := unit_temporal (Lu := neLu M R) hell hE (neC ell M R) t htπ S.hc1 (le_mul_self_c S.hc2)
  refine H0_temporal_bijective hell (unit_hdiv hdvd hM) (neLam M R) hT ?_
  show ∑ u ∈ range (neLu M R 0 + 1), avF (neC ell M R) ell (scaleUp ell 2 (neLu M R) 0 + 1) t u = 0
  refine avF_sum_zero (neC ell M R) ell (neLu M R 0 + 1) _ ?_ t
  rw [scaleUp_succ ell 2 (neLu M R) hell, mul_comm]

#print axioms Pn_H0_bijective_even

end AdalyFormal.CoverOmega
