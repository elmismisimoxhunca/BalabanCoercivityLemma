import RotationBlock

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

/-- This is the g from the certified SI1 definitions: g(t)=(1-exp(-t))/t. -/
theorem g_neg_block (Z : SuTwo) (h : 0 < nu (Z : M2)) :
    gOp (-(adOp Z)) = P Z +
      (Real.sin (nu (Z : M2)) * Real.cos (nu (Z : M2)) / nu (Z : M2)) • Q Z +
      (Real.sin (nu (Z : M2)) ^ 2 / nu (Z : M2)) • J Z := by
  have hz : Z ≠ 0 := by
    intro hz
    have : nu (Z : M2) = 0 := (nu_eq_zero_iff _).mpr (congrArg Subtype.val hz)
    linarith
  apply ContinuousLinearMap.ext
  intro X
  rw [AdalySI1.DexpRodrigues.gOp_neg_adOp_apply Z X hz]
  simp only [P, Q, J, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul,
    smul_smul, smul_neg, sub_neg_eq_add,
    AdalySI1.Adjoint.w_one_eq, AdalySI1.Adjoint.w_two_eq]
  rw [Real.sin_two_mul, Real.cos_two_mul]
  have ht := Real.sin_sq_add_cos_sq (nu (Z : M2))
  have ha : (1 - (2 * Real.cos (nu (Z : M2)) ^ 2 - 1)) /
      (4 * nu (Z : M2) ^ 2) =
      (Real.sin (nu (Z : M2)) ^ 2 / nu (Z : M2)) * (1 / (2 * nu (Z : M2))) := by
    field_simp [ne_of_gt h]
    nlinarith
  have hb : (2 * nu (Z : M2) - 2 * Real.sin (nu (Z : M2)) * Real.cos (nu (Z : M2))) /
      (8 * nu (Z : M2) ^ 3) =
      1 / (2 * nu (Z : M2)) * (1 / (2 * nu (Z : M2))) -
      (Real.sin (nu (Z : M2)) * Real.cos (nu (Z : M2)) / nu (Z : M2)) *
      (1 / (2 * nu (Z : M2)) * (1 / (2 * nu (Z : M2)))) := by
    field_simp [ne_of_gt h]
    <;> ring
  rw [ha, hb]
  module

/-- Multiplication in the real radial-plus-rotation algebra. -/
theorem block_mul (Z : SuTwo) (h : 0 < nu (Z : M2)) (a b c d : ℝ) :
    (P Z + a • Q Z + b • J Z) * (P Z + c • Q Z + d • J Z) =
      P Z + (a * c - b * d) • Q Z + (a * d + b * c) • J Z := by
  rcases block_relations Z h with ⟨_, hpp, hqq, hpq, hqp, hjp, hpj, hjq, hqj, hjj⟩
  apply ContinuousLinearMap.ext
  intro X
  have pp := congrArg (fun T : SuTwo →L[ℝ] SuTwo => T X) hpp
  have qq := congrArg (fun T : SuTwo →L[ℝ] SuTwo => T X) hqq
  have pq := congrArg (fun T : SuTwo →L[ℝ] SuTwo => T X) hpq
  have qp := congrArg (fun T : SuTwo →L[ℝ] SuTwo => T X) hqp
  have jp := congrArg (fun T : SuTwo →L[ℝ] SuTwo => T X) hjp
  have pj := congrArg (fun T : SuTwo →L[ℝ] SuTwo => T X) hpj
  have jq := congrArg (fun T : SuTwo →L[ℝ] SuTwo => T X) hjq
  have qj := congrArg (fun T : SuTwo →L[ℝ] SuTwo => T X) hqj
  have jj := congrArg (fun T : SuTwo →L[ℝ] SuTwo => T X) hjj
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.neg_apply] at pp qq pq qp jp pj jq qj jj
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, map_add, map_smul, pp, qq, pq, qp, jp, pj, jq, qj, jj]
  module

/-- A genuine two-sided inverse; sin(r)≠0 excludes ALL nonzero integer multiples of pi. -/
def inverseBlock (Z : SuTwo) : SuTwo →L[ℝ] SuTwo :=
  P Z + (nu (Z : M2) * Real.cos (nu (Z : M2)) / Real.sin (nu (Z : M2))) • Q Z +
    (-nu (Z : M2)) • J Z

theorem inverseBlock_spec (Z : SuTwo) (h : 0 < nu (Z : M2))
    (hs : Real.sin (nu (Z : M2)) ≠ 0) :
    gOp (-(adOp Z)) * inverseBlock Z = 1 ∧ inverseBlock Z * gOp (-(adOp Z)) = 1 := by
  have hc : (Real.sin (nu (Z : M2)) * Real.cos (nu (Z : M2)) / nu (Z : M2)) *
      (nu (Z : M2) * Real.cos (nu (Z : M2)) / Real.sin (nu (Z : M2))) -
      (Real.sin (nu (Z : M2)) ^ 2 / nu (Z : M2)) * (-nu (Z : M2)) = 1 := by
    field_simp [ne_of_gt h, hs]
    nlinarith [Real.sin_sq_add_cos_sq (nu (Z : M2))]
  have hd : (Real.sin (nu (Z : M2)) * Real.cos (nu (Z : M2)) / nu (Z : M2)) *
      (-nu (Z : M2)) + (Real.sin (nu (Z : M2)) ^ 2 / nu (Z : M2)) *
      (nu (Z : M2) * Real.cos (nu (Z : M2)) / Real.sin (nu (Z : M2))) = 0 := by
    field_simp [ne_of_gt h, hs]
    <;> ring
  rw [g_neg_block Z h, inverseBlock, block_mul Z h, block_mul Z h]
  constructor
  · rw [hc, hd]
    have hz : (0 : ℝ) • J Z = 0 := by ext X; simp
    rw [hz, one_smul, add_zero]
    exact (block_relations Z h).1
  · have hc' :
        (nu (Z : M2) * Real.cos (nu (Z : M2)) / Real.sin (nu (Z : M2))) *
        (Real.sin (nu (Z : M2)) * Real.cos (nu (Z : M2)) / nu (Z : M2)) -
        (-nu (Z : M2)) * (Real.sin (nu (Z : M2)) ^ 2 / nu (Z : M2)) = 1 := by
      nlinarith [hc]
    have hd' :
        (nu (Z : M2) * Real.cos (nu (Z : M2)) / Real.sin (nu (Z : M2))) *
        (Real.sin (nu (Z : M2)) ^ 2 / nu (Z : M2)) +
        (-nu (Z : M2)) *
        (Real.sin (nu (Z : M2)) * Real.cos (nu (Z : M2)) / nu (Z : M2)) = 0 := by
      nlinarith [hd]
    rw [hc', hd']
    have hz : (0 : ℝ) • J Z = 0 := by ext X; simp
    rw [hz, one_smul, add_zero]
    exact (block_relations Z h).1

theorem gInv_neg_block (Z : SuTwo) (h : 0 < nu (Z : M2))
    (hs : Real.sin (nu (Z : M2)) ≠ 0) : gInvOp (-(adOp Z)) = inverseBlock Z := by
  have hh := inverseBlock_spec Z h hs
  have hu : IsUnit (gOp (-(adOp Z))) := ⟨⟨_, inverseBlock Z, hh.1, hh.2⟩, rfl⟩
  rw [OneStep124.gInvOp]
  calc Ring.inverse (gOp (-(adOp Z))) =
      Ring.inverse (gOp (-(adOp Z))) * (gOp (-(adOp Z)) * inverseBlock Z) := by rw [hh.1, mul_one]
    _ = inverseBlock Z := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

#print axioms g_neg_block
#print axioms block_mul
#print axioms inverseBlock_spec
#print axioms gInv_neg_block
end EstimatesLayer.NormBounds
