import Adjoint
import AdalyFormal.Balaban.RMapLipschitz
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace EstimatesLayer.NormBounds
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.SuTwoLogExp (M2 su2Exp su2Angle)
open AdalyFormal.Balaban.Bch2
open AdalyFormal.Balaban.RMapLipschitz (norm_sq_eq_half_frobSq)
open AdalyFormal.Balaban.SuTwoInner
open OneStep124 (adOp gOp gInvOp expOp)
open AdalySI1.DexpRodrigues (adOp_apply_coe double_comm adOp_cube_apply)

/-- The principal group angle, NOT the unbounded radial coordinate. -/
def theta (Z : SuTwo) : ℝ := su2Angle (su2Exp (Z : M2))

theorem theta_eq_nu (Z : SuTwo) (h : nu (Z : M2) ≤ Real.pi) :
    theta Z = nu (Z : M2) := angle_exp Z.2 h

theorem norm_eq_nu (X : SuTwo) : ‖X‖ = nu (X : M2) := by
  have h := norm_sq_eq_half_frobSq X
  have h' := nu_sq (X : M2)
  nlinarith [norm_nonneg X, nu_nonneg (X : M2)]

theorem ad_self (Z : SuTwo) : adOp Z Z = 0 := by
  apply Subtype.ext
  simp [adOp_apply_coe]

theorem ad_neg (Z : SuTwo) : adOp (-Z) = -(adOp Z) := by
  apply ContinuousLinearMap.ext
  intro X
  apply Subtype.ext
  simp [adOp_apply_coe]
  abel

theorem ad_cube (Z X : SuTwo) :
    adOp Z (adOp Z (adOp Z X)) = (-4 * nu (Z : M2) ^ 2) • adOp Z X := by
  apply Subtype.ext
  exact adOp_cube_apply Z X

/-- Real rotation block: on the Frobenius-orthogonal plane, A² = -(2ν)² I. -/
theorem ad_square_perp (Z X : SuTwo) (h : ip (Z : M2) (X : M2) = 0) :
    adOp Z (adOp Z X) = (-(2 * nu (Z : M2)) ^ 2) • X := by
  apply Subtype.ext
  rw [double_comm, h]
  simp only [mul_zero, zero_smul, add_zero, Submodule.coe_smul]
  congr 1
  ring

theorem norm_ad_apply_le (Z X : SuTwo) :
    ‖adOp Z X‖ ≤ (2 * nu (Z : M2)) * ‖X‖ := by
  rw [norm_eq_nu, norm_eq_nu]
  have he : ((adOp Z X : SuTwo) : M2) = (2 : ℝ) • comm2 (Z : M2) (X : M2) := by
    rw [adOp_apply_coe, comm2, AdalyFormal.Balaban.RegularityGap.real_smul_eq, smul_smul]
    norm_num
  rw [he, nu_smul]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h := nu_comm2_le Z.2 X.2
  nlinarith

theorem norm_exp_apply (Z X : SuTwo) : ‖expOp (adOp Z) X‖ = ‖X‖ := by
  rw [← AdalySI1.Adjoint.rmap_su2Exp_apply_eq_expOp_ad]
  exact (RIsometry (su2Exp (Z : M2))).norm_map X

local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

theorem norm_ad_le (Z : SuTwo) : ‖adOp Z‖ ≤ 2 * nu (Z : M2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (nu_nonneg _))
  exact norm_ad_apply_le Z

theorem norm_exp_le (Z : SuTwo) : ‖expOp (adOp Z)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro X
  rw [norm_exp_apply, one_mul]

#print axioms theta_eq_nu
#print axioms norm_eq_nu
#print axioms ad_square_perp
#print axioms ad_cube
#print axioms norm_ad_apply_le
#print axioms norm_exp_apply
#print axioms norm_ad_le
#print axioms norm_exp_le
end EstimatesLayer.NormBounds
