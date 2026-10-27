import ChosenAxis
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HConstruction.Coeff
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.Bch2
open HConstruction.Circle
open EstimatesLayer.NormBounds
open OneStep124

 theorem assemble_add (x a z y b w : ℝ) :
    assemble x a z + assemble y b w = assemble (x+y) (a+b) (z+w) := by
  simp only [assemble, add_smul]; module
 theorem assemble_smul (r x a z : ℝ) :
    r • assemble x a z = assemble (r*x) (r*a) (r*z) := by
  simp only [assemble, smul_add, smul_smul]
 theorem assemble_neg (x a z : ℝ) : -assemble x a z = assemble (-x) (-a) (-z) := by
  simpa using assemble_smul (-1) x a z
 theorem assemble_sub (x a z y b w : ℝ) :
    assemble x a z - assemble y b w = assemble (x-y) (a-b) (z-w) := by
  rw [sub_eq_add_neg, assemble_neg, assemble_add]; rfl

 theorem J_axis_assemble (s x a z : ℝ) :
    J (s • pauliE2) (assemble x a z) = assemble (-(s/|s|)*z) 0 ((s/|s|)*x) := by
  simp only [J, nu_axis, ContinuousLinearMap.smul_apply, adOp_axis_assemble, assemble_smul]
  congr 1 <;> ring

 theorem Q_axis_assemble (s x a z : ℝ) (hs : s ≠ 0) :
    Q (s • pauliE2) (assemble x a z) = assemble x 0 z := by
  have hh : s^2 = |s|^2 := (sq_abs s).symm
  simp only [Q, ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply,
    J_axis_assemble, assemble_neg]
  congr 1 <;> field_simp <;> nlinarith [congrArg (fun t : ℝ => t*x) hh, congrArg (fun t : ℝ => t*z) hh]

 theorem P_axis_assemble (s x a z : ℝ) (hs : s ≠ 0) :
    P (s • pauliE2) (assemble x a z) = assemble 0 a 0 := by
  simp only [P, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    Q_axis_assemble s x a z hs, assemble_sub, sub_self, sub_zero]

 theorem g_neg_axis_assemble (s x a z : ℝ) (hs : s ≠ 0) :
    gOp (-(adOp (s • pauliE2))) (assemble x a z) =
      assemble
        ((Real.sin |s| * Real.cos |s| / |s|)*x - (s*Real.sin |s|^2 / |s|^2)*z)
        a
        ((s*Real.sin |s|^2 / |s|^2)*x + (Real.sin |s| * Real.cos |s| / |s|)*z) := by
  rw [g_neg_block _ (by rw [nu_axis]; exact abs_pos.mpr hs)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    nu_axis, P_axis_assemble s x a z hs, Q_axis_assemble s x a z hs,
    J_axis_assemble, assemble_smul, assemble_add]
  congr 1 <;> ring

 theorem gInv_neg_axis_assemble (s x a z : ℝ) (hs : s ≠ 0)
    (hcut : |s| < Real.pi) :
    gInvOp (-(adOp (s • pauliE2))) (assemble x a z) =
      assemble ((|s| * Real.cos |s| / Real.sin |s|)*x + s*z) a
        (-s*x + (|s| * Real.cos |s| / Real.sin |s|)*z) := by
  have hr : 0 < |s| := abs_pos.mpr hs
  rw [gInv_neg_block _ (by rw [nu_axis]; exact hr)
    (by rw [nu_axis]; exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hr hcut))]
  simp only [inverseBlock, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    nu_axis, P_axis_assemble s x a z hs, Q_axis_assemble s x a z hs,
    J_axis_assemble, assemble_smul, assemble_add]
  congr 1 <;> field_simp <;> ring

 theorem exp_axis_assemble (s x a z : ℝ) (hs : s ≠ 0) :
    expOp (adOp (s • pauliE2)) (assemble x a z) =
      assemble (Real.cos (2*|s|)*x - (s/|s|)*Real.sin (2*|s|)*z) a
        ((s/|s|)*Real.sin (2*|s|)*x + Real.cos (2*|s|)*z) := by
  have hz : s • pauliE2 ≠ 0 := by
    intro he
    have he' := congrArg (fun X : SuTwo => nu (X : M2)) he
    rw [nu_axis] at he'
    exact hs (abs_eq_zero.mp (he'.trans ((nu_eq_zero_iff _).mpr rfl)))
  rw [AdalySI1.Adjoint.expOp_adOp_apply _ _ hz]
  simp only [AdalySI1.Adjoint.w_one_eq, AdalySI1.Adjoint.w_two_eq,
    adOp_axis_assemble, nu_axis, assemble_smul, assemble_add]
  have hh : s^2 = |s|^2 := (sq_abs s).symm
  congr 1 <;> field_simp <;> (try rw [hh]) <;> ring

#print axioms g_neg_axis_assemble
#print axioms gInv_neg_axis_assemble
#print axioms exp_axis_assemble
end HConstruction.Coeff
