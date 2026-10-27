import Foundations

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace EstimatesLayer.NormBounds
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.Bch2
open AdalyFormal.Balaban.SuTwoInner
open OneStep124 (adOp gOp gInvOp expOp)
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

private theorem op_neg_mul (A B : SuTwo →L[ℝ] SuTwo) : (-A) * B = -(A * B) := by
  rfl

private theorem op_mul_neg (A B : SuTwo →L[ℝ] SuTwo) : A * (-B) = -(A * B) := by
  apply ContinuousLinearMap.ext
  intro X
  exact map_neg A (B X)

/-- Normalized real quarter-turn. All decomposition theorems assume ν(Z)>0. -/
def J (Z : SuTwo) : SuTwo →L[ℝ] SuTwo := (1 / (2 * nu (Z : M2))) • adOp Z
/-- Perpendicular projection, constructed from the actual commutator. -/
def Q (Z : SuTwo) : SuTwo →L[ℝ] SuTwo := -(J Z * J Z)
/-- Radial projection. -/
def P (Z : SuTwo) : SuTwo →L[ℝ] SuTwo := 1 - Q Z

theorem J_cube (Z : SuTwo) (h : 0 < nu (Z : M2)) : J Z * J Z * J Z = -J Z := by
  apply ContinuousLinearMap.ext
  intro X
  simp only [J, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, map_smul, smul_smul]
  rw [ad_cube]
  simp only [smul_smul, ← neg_smul]
  congr 1
  field_simp [ne_of_gt h]
  <;> ring

theorem block_relations (Z : SuTwo) (h : 0 < nu (Z : M2)) :
    P Z + Q Z = 1 ∧ P Z * P Z = P Z ∧ Q Z * Q Z = Q Z ∧
    P Z * Q Z = 0 ∧ Q Z * P Z = 0 ∧
    J Z * P Z = 0 ∧ P Z * J Z = 0 ∧
    J Z * Q Z = J Z ∧ Q Z * J Z = J Z ∧ J Z * J Z = -Q Z := by
  have h3 := J_cube Z h
  have h4 : (J Z * J Z) * (J Z * J Z) = -(J Z * J Z) := by
    rw [← mul_assoc, h3, op_neg_mul]
  have hq : Q Z * Q Z = Q Z := by
    simp only [Q, op_neg_mul, op_mul_neg, neg_neg, h4]
  have hjq : J Z * Q Z = J Z := by
    rw [Q, op_mul_neg, ← mul_assoc, h3, neg_neg]
  have hqj : Q Z * J Z = J Z := by
    rw [Q, op_neg_mul, h3, neg_neg]
  refine ⟨?_, ?_, hq, ?_, ?_, ?_, ?_, hjq, hqj, ?_⟩
  · simp [P]
  · simp only [P, sub_mul, mul_sub, one_mul, mul_one, hq]
    abel
  · simp [P, sub_mul, hq]
  · simp [P, mul_sub, hq]
  · simp [P, mul_sub, hjq]
  · simp [P, sub_mul, hqj]
  · simp [Q]

theorem P_apply (Z X : SuTwo) (h : 0 < nu (Z : M2)) :
    P Z X = (ip (Z : M2) (X : M2) / (2 * nu (Z : M2) ^ 2)) • Z := by
  apply Subtype.ext
  simp only [P, Q, J, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smul_apply, map_smul, smul_smul, sub_neg_eq_add,
    Submodule.coe_add, Submodule.coe_smul]
  rw [AdalySI1.DexpRodrigues.double_comm]
  simp only [smul_add, smul_smul]
  have h1 : (1 / (2 * nu (Z : M2)) * (1 / (2 * nu (Z : M2)))) *
      (-4 * nu (Z : M2) ^ 2) = -1 := by field_simp [ne_of_gt h] <;> ring
  have h2 : (1 / (2 * nu (Z : M2)) * (1 / (2 * nu (Z : M2)))) *
      (2 * ip (Z : M2) (X : M2)) = ip (Z : M2) (X : M2) / (2 * nu (Z : M2) ^ 2) := by
    field_simp [ne_of_gt h]
    <;> ring
  rw [h1, h2]
  module

theorem P_axis (Z : SuTwo) : P Z Z = Z := by
  simp [P, Q, J, ContinuousLinearMap.mul_apply, ad_self]

theorem norm_J_le (Z : SuTwo) (h : 0 < nu (Z : M2)) : ‖J Z‖ ≤ 1 := by
  rw [J, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc (1 / (2 * nu (Z : M2))) * ‖adOp Z‖
      ≤ (1 / (2 * nu (Z : M2))) * (2 * nu (Z : M2)) :=
        mul_le_mul_of_nonneg_left (norm_ad_le Z) (by positivity)
    _ = 1 := by field_simp [ne_of_gt h]

theorem norm_Q_le (Z : SuTwo) (h : 0 < nu (Z : M2)) : ‖Q Z‖ ≤ 1 := by
  rw [Q, norm_neg]
  calc ‖J Z * J Z‖ ≤ ‖J Z‖ * ‖J Z‖ := norm_mul_le _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_J_le Z h) (norm_J_le Z h) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem norm_P_le (Z : SuTwo) (h : 0 < nu (Z : M2)) : ‖P Z‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro X
  rw [P_apply Z X h, norm_smul, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : 0 < 2 * nu (Z : M2) ^ 2), norm_eq_nu, one_mul]
  have hb := abs_ip_le Z.2 X.2
  rw [← norm_eq_nu X] at hb
  calc |ip (Z : M2) (X : M2)| / (2 * nu (Z : M2) ^ 2) * nu (Z : M2)
      ≤ (2 * (nu (Z : M2) * ‖X‖)) / (2 * nu (Z : M2) ^ 2) * nu (Z : M2) := by
        gcongr
    _ = ‖X‖ := by field_simp; <;> ring

/-- Every vector splits as radial plus perpendicular, with the stated radial coefficient. -/
theorem radial_perp_decomposition (Z X : SuTwo) (h : 0 < nu (Z : M2)) :
    X = P Z X + Q Z X ∧ ip (Z : M2) ((Q Z X : SuTwo) : M2) = 0 := by
  constructor
  · have hh := congrArg (fun T : SuTwo →L[ℝ] SuTwo => T X) (block_relations Z h).1
    simpa using hh.symm
  · have hh : Q Z X = X - P Z X := by simp [P]
    rw [hh, P_apply Z X h]
    change ip (Z : M2) ((X : M2) -
      (ip (Z : M2) (X : M2) / (2 * nu (Z : M2) ^ 2)) • (Z : M2)) = 0
    have hi : ∀ A B C : M2, ip A (B - C) = ip A B - ip A C := by
      intros
      simp only [ip, Matrix.sub_apply, Complex.sub_re, Complex.sub_im]
      ring
    rw [hi, ip_smul_right, ip_self]
    have hn : AdalyFormal.Balaban.RMapLipschitz.frobSq (Z : M2) = 2 * nu (Z : M2) ^ 2 := by
      linarith [nu_sq (Z : M2)]
    rw [hn]
    field_simp [ne_of_gt h]
    <;> ring

/-- The actual real rotation equations on the perpendicular summand.
Together with P_apply and radial_perp_decomposition this is a full real block description,
not merely a polynomial that might have extraneous roots. -/
theorem real_rotation_block (Z X : SuTwo) (h : 0 < nu (Z : M2)) :
    adOp Z (P Z X) = 0 ∧
    adOp Z (Q Z X) = (2 * nu (Z : M2)) • J Z X ∧
    adOp Z (J Z X) = (-2 * nu (Z : M2)) • Q Z X := by
  have ha : adOp Z = (2 * nu (Z : M2)) • J Z := by
    rw [J, smul_smul]
    have hc : (2 * nu (Z : M2)) * (1 / (2 * nu (Z : M2))) = 1 := by
      field_simp [ne_of_gt h]
    rw [hc, one_smul]
  rcases block_relations Z h with ⟨_, _, _, _, _, hjp, _, hjq, _, hjj⟩
  have hpapp := congrArg (fun T : SuTwo →L[ℝ] SuTwo => T X) hjp
  have hqapp := congrArg (fun T : SuTwo →L[ℝ] SuTwo => T X) hjq
  have hjapp := congrArg (fun T : SuTwo →L[ℝ] SuTwo => T X) hjj
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.neg_apply] at hpapp hqapp hjapp
  rw [ha]
  simp only [ContinuousLinearMap.smul_apply, hpapp, hqapp, hjapp, smul_zero, smul_neg]
  refine ⟨True.intro, True.intro, ?_⟩
  module

#print axioms radial_perp_decomposition
#print axioms real_rotation_block
#print axioms J_cube
#print axioms block_relations
#print axioms P_apply
#print axioms norm_J_le
#print axioms norm_Q_le
#print axioms norm_P_le
end EstimatesLayer.NormBounds
