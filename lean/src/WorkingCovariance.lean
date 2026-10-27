import SmallSchur
import Neumann

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
noncomputable section
namespace HConstruction.TransversePos
open HConstruction.Covariance HConstruction.SmallNF HConstruction.Nonflat
open HConstruction.NfRepair HConstruction.NfRepair.Reproduced
open AdalyFormal.Balaban.RegularityHolonomy
attribute [local irreducible] workingThreshold baselineGap derivativeCeiling precisionU workingU

private theorem working_precision_lower (A : H) :
    (baselineGap/2)*‖A‖^2 ≤ (inner ℝ A (precisionU workingU 1 A) : ℝ) := by
  unfold workingU
  exact precision_small_lower workingThreshold (by rw [abs_of_pos workingThreshold_pos]) A

/-- The physical inverse chosen from the fully discharged source Schur gate. -/
def workingG0 : H →L[ℝ] H := Classical.choose Schur.workingG0_via_source_schur

theorem workingG0_right : (precisionU workingU 1).comp workingG0 = ContinuousLinearMap.id ℝ H := by
  ext A
  change precisionU workingU 1 (workingG0 A) = A
  unfold workingG0
  exact (Classical.choose_spec Schur.workingG0_via_source_schur).1 A

theorem workingG0_left : workingG0.comp (precisionU workingU 1) = ContinuousLinearMap.id ℝ H := by
  ext A
  change workingG0 (precisionU workingU 1 A) = A
  unfold workingG0
  exact (Classical.choose_spec Schur.workingG0_via_source_schur).2 A

attribute [local irreducible] workingG0

/-- Positivity is paid for the selected physical inverse, not assumed in its data. -/
theorem workingG0_positive (A : H) (hA : A ≠ 0) :
    (0 : ℝ) < inner ℝ A (workingG0 A) := by
  have hr := congrArg (fun T : H →L[ℝ] H => T A) workingG0_right
  change precisionU workingU 1 (workingG0 A) = A at hr
  have hz : workingG0 A ≠ 0 := by
    intro h
    rw [h, map_zero] at hr
    exact hA hr.symm
  have hp := working_precision_lower (workingG0 A)
  rw [hr, real_inner_comm] at hp
  exact lt_of_lt_of_le (mul_pos (by linarith [baselineGap_pos])
    (sq_pos_of_pos (norm_pos_iff.mpr hz))) hp

theorem workingG0_bound_apply (A : H) : ‖workingG0 A‖ ≤ (2/baselineGap)*‖A‖ := by
  have hl := working_precision_lower (workingG0 A)
  have hr := congrArg (fun T : H →L[ℝ] H => T A) workingG0_right
  change precisionU workingU 1 (workingG0 A) = A at hr
  rw [hr] at hl
  have hi := real_inner_le_norm (workingG0 A) A
  have hg := baselineGap_pos
  have hb : (baselineGap/2)*‖workingG0 A‖ ≤ ‖A‖ := by
    by_cases hz : workingG0 A = 0
    · simp [hz]
    · have hn := norm_pos_iff.mpr hz
      nlinarith
  calc
    ‖workingG0 A‖ ≤ (2*‖A‖)/baselineGap := (le_div_iff₀ hg).mpr (by linarith)
    _ = (2/baselineGap)*‖A‖ := by ring

/-- Unconditional physical G0 bound. This alone is not a G1 theorem. -/
theorem workingG0_norm : ‖workingG0‖ ≤ 2/baselineGap := by
  exact ContinuousLinearMap.opNorm_le_bound workingG0
    (le_of_lt (div_pos (by norm_num) baselineGap_pos)) workingG0_bound_apply

/-- Branch admission remains valid at the changed background. This is NOT
Theorem 3.12's regularity hypothesis (3.35)--(3.36). -/
theorem workingU_admitted : ∃ eps : ℝ, PlaquetteBound workingU eps ∧
    HConstruction.Nonflat.Reproduced.loopRhoPlaq eps 2 < Real.pi/2 := by
  unfold workingU
  apply (nonflatU_admission_iff workingThreshold).mpr
  have ht := workingThreshold_pos
  have hb := workingThreshold_le
  have hs : workingThreshold^2 ≤ (1/16 : ℝ)^2 := by nlinarith
  nlinarith

/-- A quantitative remaining gate, instantiated with the actual now-certified G0.
P is still an arbitrary operator: this does NOT identify it with the source
Delta'_pi + Delta_pi^(2), nor prove that source perturbation is small. -/
theorem working_neumann_gate (P : H →L[ℝ] H) (hP : ‖P‖ < baselineGap/2) :
    ‖P * workingG0‖ < 1 := by
  calc
    ‖P * workingG0‖ ≤ ‖P‖ * ‖workingG0‖ := norm_mul_le _ _
    _ ≤ ‖P‖ * (2/baselineGap) := mul_le_mul_of_nonneg_left workingG0_norm (norm_nonneg P)
    _ < (baselineGap/2) * (2/baselineGap) :=
      mul_lt_mul_of_pos_right hP (div_pos (by norm_num) baselineGap_pos)
    _ = 1 := by field_simp [ne_of_gt baselineGap_pos]

/-- Conditional series ONLY. No genuine G1/H1 closure is claimed. -/
theorem working_neumann_series (P : H →L[ℝ] H) (hP : ‖P‖ < baselineGap/2) :
    HConstruction.Covariance.Reproduced.gOneOfNeumann workingG0 P =
      ∑' n : ℕ, workingG0 * (P * workingG0)^n :=
  HConstruction.Covariance.Reproduced.gOneOfNeumann_eq_tsum _ _ (working_neumann_gate P hP)

#print axioms workingG0_right
#print axioms workingG0_left
#print axioms workingG0_positive
#print axioms workingG0_norm
#print axioms workingU_admitted
#print axioms working_neumann_gate
#print axioms working_neumann_series
end HConstruction.TransversePos
