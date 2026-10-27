import SmoothHessian
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section
namespace HConstruction.TransversePos
open HConstruction.Covariance HConstruction.SmallNF HConstruction.Nonflat HConstruction.Carrier
open HConstruction.NfRepair.Reproduced HConstruction.DRepair HConstruction.Circle
open HConstruction.SmallNF.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL Bond)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

def maskedFlatQ : H →L[ℝ] K := maskQ.comp (nativeLinearQ (trivialU witnessL) 2)

/-- Smooth, source-identified lower operator. It keeps the entire indefinite
Hessian; only the positive gauge and Q terms are decreased. -/
def lowerPrecision (t : ℝ) : H →L[ℝ] H :=
  deltaU (nonflatU t) + (1/16777217 : ℝ) • (dualGauge t).adjoint.comp (dualGauge t) +
    (8 : ℝ) • maskedFlatQ.adjoint.comp maskedFlatQ

theorem lowerPrecision_energy (t : ℝ) (A : H) :
    (inner ℝ A (lowerPrecision t A) : ℝ) =
      inner ℝ A (deltaU (nonflatU t) A) +
        (1/16777217 : ℝ) * ‖dualGauge t A‖^2 + 8*‖maskedFlatQ A‖^2 := by
  simp only [lowerPrecision, _root_.add_apply, _root_.smul_apply, inner_add_right,
    inner_smul_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

theorem lowerPrecision_le_actual (t : ℝ) (A : H) :
    (inner ℝ A (lowerPrecision t A) : ℝ) ≤ inner ℝ A (precisionU (nonflatU t) 1 A) := by
  have hg := fixed_gauge_dual_bound t A
  have hq := maskQ_norm_sq_le (nativeLinearQ (nonflatU t) 2 A)
  rw [maskedQ_flat] at hq
  rw [lowerPrecision_energy, precisionU, ← gaugeU_identity]
  simp only [_root_.add_apply, _root_.smul_apply, inner_add_right, inner_smul_right,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq, mul_one]
  change _ ≤ inner ℝ A (deltaU (nonflatU t) A) + ‖gaugeConstraintU (nonflatU t) A‖^2 +
    8*‖nativeLinearQ (nonflatU t) 2 A‖^2
  change ‖maskedFlatQ A‖^2 ≤ ‖nativeLinearQ (nonflatU t) 2 A‖^2 at hq
  linarith

theorem flat_reHolonomy (p : PeriodicLatticePlaquette witnessL) :
    reHolonomy (trivialU witnessL) p = 1 := by
  simp [reHolonomy, holonomyElemInv, holonomyElem, periodicPlaquetteHolonomy, AdalyFormal.Balaban.CovariantHjMinimizer.trivialU]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

theorem flat_imHolonomy (p : PeriodicLatticePlaquette witnessL) :
    imHolonomy (trivialU witnessL) p = 0 := by
  simp [imHolonomy, holonomyElemInv, holonomyElem, periodicPlaquetteHolonomy,
    AdalyFormal.Balaban.CovariantHjMinimizer.trivialU]

theorem correction_flat_zero (A B : H) : correctionBil (trivialU witnessL) A B = 0 := by
  simp only [correctionBil_apply, deltaPrimeBil_apply, deltaPrimeBilRaw_apply,
    bilPlaq_apply, firstBilPlaq_apply, secondBilPlaq_apply, pairBil_apply,
    flat_reHolonomy, flat_imHolonomy, sub_self, mul_zero, Matrix.trace_zero,
    Complex.zero_re, add_zero, Finset.sum_const_zero]

theorem deltaU_flat_energy (A : H) :
    (inner ℝ A (deltaU (trivialU witnessL) A) : ℝ) = ‖flatCurl A‖^2 := by
  simp only [deltaU, _root_.add_apply, inner_add_right, inner_fromBil, correction_flat_zero,
    add_zero, curlSquare_energy, covCurl_flat]

theorem lowerPrecision_zero_energy (A : H) :
    (inner ℝ A (lowerPrecision 0 A) : ℝ) = ‖flatCurl A‖^2 +
      (1/16777217 : ℝ) * ‖dualGauge 0 A‖^2 + 8*‖maskedFlatQ A‖^2 := by
  rw [lowerPrecision_energy]
  have he : nonflatU 0 = trivialU witnessL := nonflatU_zero_eq_trivial
  rw [he, deltaU_flat_energy]

/-- Unconditional strict positivity of the fixed leading term. Its gap does not
shrink with the background parameter. -/
theorem lowerPrecision_zero_positive (A : H) (hA : A ≠ 0) :
    (0 : ℝ) < inner ℝ A (lowerPrecision 0 A) := by
  rw [lowerPrecision_zero_energy]
  by_contra hn
  have h0 : ‖flatCurl A‖^2 = 0 := by
    nlinarith [sq_nonneg ‖flatCurl A‖, sq_nonneg ‖dualGauge 0 A‖, sq_nonneg ‖maskedFlatQ A‖]
  have h1 : ‖dualGauge 0 A‖^2 = 0 := by
    nlinarith [sq_nonneg ‖flatCurl A‖, sq_nonneg ‖dualGauge 0 A‖, sq_nonneg ‖maskedFlatQ A‖]
  have h2 : ‖maskedFlatQ A‖^2 = 0 := by
    nlinarith [sq_nonneg ‖flatCurl A‖, sq_nonneg ‖dualGauge 0 A‖, sq_nonneg ‖maskedFlatQ A‖]
  apply hA
  apply masked_joint_kernel A
  · exact norm_eq_zero.mp (by nlinarith [norm_nonneg (flatCurl A)])
  · apply dualGauge_zero_kernel
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (dualGauge 0 A)])
  · change maskedFlatQ A = 0
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (maskedFlatQ A)])

theorem smooth_lowerPrecision : ContDiff ℝ ⊤ lowerPrecision := by
  unfold lowerPrecision
  have hg : ContDiff ℝ ⊤ (fun t => (dualGauge t).adjoint.comp (dualGauge t)) :=
    ((ContinuousLinearMap.adjoint : (H →L[ℝ] S) ≃ₗᵢ[ℝ] (S →L[ℝ] H)).contDiff.comp
      smooth_dualGauge).clm_comp smooth_dualGauge
  exact (smooth_deltaU.add (hg.const_smul (1/16777217 : ℝ))).add contDiff_const

#print axioms lowerPrecision_le_actual
#print axioms lowerPrecision_zero_energy
#print axioms lowerPrecision_zero_positive
#print axioms smooth_lowerPrecision
end HConstruction.TransversePos
