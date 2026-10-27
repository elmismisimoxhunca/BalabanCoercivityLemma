import LoopWords
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
namespace HConstruction.Circle
open HConstruction.NfRepair.Reproduced
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.DeltaKR66

def theta : ℝ := 2 * Real.arctan (1/16)

theorem theta_pos : 0 < theta := by
  unfold theta
  positivity

theorem theta_lt_pi : theta < Real.pi := by
  have := Real.arctan_lt_pi_div_two (1/16)
  unfold theta
  linarith

theorem cos_theta : Real.cos theta = 255/257 := by
  rw [theta, Real.cos_two_mul, Real.cos_sq_arctan]
  norm_num

theorem sin_theta : Real.sin theta = 32/257 := by
  rw [theta, Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  have h : Real.sqrt (1 + (1/16 : ℝ)^2) ^ 2 = 1 + (1/16 : ℝ)^2 :=
    Real.sq_sqrt (by positivity)
  have hn : Real.sqrt (1 + (1/16 : ℝ)^2) ≠ 0 := by positivity
  field_simp
  nlinarith

theorem angle_rot : su2Angle (rotElem (1/16)) = theta := by
  unfold su2Angle
  rw [rotElem_coe, trace_rotM_re]
  have h : 2 * rotA (1/16) / 2 = Real.cos theta := by rw [cos_theta]; norm_num [rotA]
  rw [h, Real.arccos_cos theta_pos.le theta_lt_pi.le]

theorem angle_rot_inv : su2Angle ((rotElem (1/16))⁻¹) = theta := by
  unfold su2Angle
  rw [coe_inv, Matrix.trace_conjTranspose]
  simp only [Complex.star_def, Complex.conj_re]
  exact angle_rot

theorem principal_log_rot : principalSuTwoLog (rotElem (1/16)) = theta • pauliE2 := by
  apply Subtype.ext
  change su2Log (rotElem (1/16)) = _
  rw [su2Log, su2Kappa, angle_rot, sin_theta]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotElem_coe, rotM, rotA, rotB, pauliE2, witnessM,
      Matrix.conjTranspose_apply, Complex.real_smul] <;> ring

theorem principal_log_rot_inv : principalSuTwoLog ((rotElem (1/16))⁻¹) = (-theta) • pauliE2 := by
  apply Subtype.ext
  change su2Log ((rotElem (1/16))⁻¹) = _
  rw [su2Log, su2Kappa, angle_rot_inv, sin_theta, coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotElem_coe, rotM, rotA, rotB, pauliE2, witnessM,
      Matrix.conjTranspose_apply, Complex.real_smul] <;> ring

theorem principalSuTwoLog_rotElem_zpow_small (n : ℤ)
    (hn : n = -1 ∨ n = 0 ∨ n = 1) :
    principalSuTwoLog ((rotElem (1/16)) ^ n) = ((n : ℝ) * (2 * Real.arctan (1/16))) • pauliE2 := by
  rcases hn with rfl | rfl | rfl
  · simpa [theta] using principal_log_rot_inv
  · apply Subtype.ext
    simp [principalSuTwoLog]
  · simpa [theta] using principal_log_rot

#print axioms principalSuTwoLog_rotElem_zpow_small
end HConstruction.Circle
