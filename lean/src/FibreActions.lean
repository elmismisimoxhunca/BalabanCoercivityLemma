import TransverseActions
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HConstruction.Coeff
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.SuTwoInner
open HConstruction.Circle
open HConstruction.NfRepair.Reproduced
open EstimatesLayer.NormBounds
open OneStep124

/-- An axial scalar and a complex transverse scalar, in the normalized source coordinates. -/
def FibreAction (T : SuTwo →L[ℝ] SuTwo) (u p q : ℝ) : Prop :=
  ∀ x a z, T (assemble x a z) = assemble (p*x-q*z) (u*a) (q*x+p*z)

theorem FibreAction.mul {T S : SuTwo →L[ℝ] SuTwo} {u p q v r t : ℝ}
    (hT : FibreAction T u p q) (hS : FibreAction S v r t) :
    FibreAction (T*S) (u*v) (p*r-q*t) (q*r+p*t) := by
  intro x a z
  rw [ContinuousLinearMap.mul_apply, hS, hT]
  congr 1 <;> ring

theorem FibreAction.sub {T S : SuTwo →L[ℝ] SuTwo} {u p q v r t : ℝ}
    (hT : FibreAction T u p q) (hS : FibreAction S v r t) :
    FibreAction (T-S) (u-v) (p-r) (q-t) := by
  intro x a z
  rw [ContinuousLinearMap.sub_apply, hT, hS, assemble_sub]
  congr 1 <;> ring

theorem FibreAction.smul {T : SuTwo →L[ℝ] SuTwo} {u p q : ℝ}
    (hT : FibreAction T u p q) (r : ℝ) : FibreAction (r • T) (r*u) (r*p) (r*q) := by
  intro x a z
  rw [ContinuousLinearMap.smul_apply, hT, assemble_smul]
  congr 1 <;> ring

theorem fibre_one : FibreAction (1 : SuTwo →L[ℝ] SuTwo) 1 1 0 := by
  intro x a z; simp

/-- Removable value explicitly retained; not division by zero interpreted as sinc. -/
def gReal (s : ℝ) : ℝ := if s = 0 then 1 else Real.sin |s| * Real.cos |s| / |s|
def gImag (s : ℝ) : ℝ := s * Real.sin |s|^2 / |s|^2
def invReal (s : ℝ) : ℝ := if s = 0 then 1 else |s| * Real.cos |s| / Real.sin |s|

theorem g_neg_action (s : ℝ) : FibreAction (gOp (-(adOp (s • pauliE2)))) 1 (gReal s) (gImag s) := by
  intro x a z
  by_cases hs : s = 0
  · subst s
    simp [gReal, gImag, AdalySI1.DexpRodrigues.adOp_zero_eq, AdalySI1.DexpRodrigues.gOp_zero_eq]
  · simpa [gReal, gImag, hs] using g_neg_axis_assemble s x a z hs

theorem gInv_neg_action (s : ℝ) (hs : |s| < Real.pi) :
    FibreAction (gInvOp (-(adOp (s • pauliE2)))) 1 (invReal s) (-s) := by
  intro x a z
  by_cases hz : s = 0
  · subst s
    simp [invReal, gInvOp, AdalySI1.DexpRodrigues.adOp_zero_eq, AdalySI1.DexpRodrigues.gOp_zero_eq]
  · simpa [invReal, hz] using gInv_neg_axis_assemble s x a z hz hs

theorem gInv_pos_action (s : ℝ) (hs : |s| < Real.pi) :
    FibreAction (gInvOp (adOp (s • pauliE2))) 1 (invReal s) s := by
  have h := gInv_neg_action (-s) (by simpa using hs)
  simpa [neg_smul, ad_neg, invReal] using h

theorem exp_action (s : ℝ) :
    FibreAction (expOp (adOp (s • pauliE2))) 1 (Real.cos (2*|s|))
      ((s/|s|)*Real.sin (2*|s|)) := by
  intro x a z
  by_cases hs : s = 0
  · subst s
    simp [AdalySI1.DexpRodrigues.adOp_zero_eq, AdalySI1.Adjoint.expOp_zero_eq]
  · simpa using exp_axis_assemble s x a z hs

theorem FibreAction.coordinates {T : SuTwo →L[ℝ] SuTwo} {u p q : ℝ}
    (hT : FibreAction T u p q) (X : SuTwo) :
    axisCoord (T X) = u * axisCoord X ∧
    transverseCoord (T X) = ((p : ℂ) + (q : ℂ)*Complex.I) * transverseCoord X := by
  rw [← assemble_coordinates X, hT]
  simp only [axisCoord_assemble, transverseCoord_assemble]
  constructor
  · trivial
  · apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Every such actual source operator intertwines every rotation in the background circle. -/
theorem FibreAction.circle {T : SuTwo →L[ℝ] SuTwo} {u p q : ℝ}
    (hT : FibreAction T u p q) (t : ℝ) (X : SuTwo) :
    T (RMap (rotElem t) X) = RMap (rotElem t) (T X) := by
  rw [← assemble_coordinates X, RMap_rot_assemble, hT, hT, RMap_rot_assemble]
  congr 1 <;> ring

#print axioms g_neg_action
#print axioms gInv_neg_action
#print axioms gInv_pos_action
#print axioms exp_action
#print axioms FibreAction.coordinates
#print axioms FibreAction.circle
end HConstruction.Coeff
