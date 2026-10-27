import LowerPrecision
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section
namespace HConstruction.TransversePos
open HConstruction.Covariance HConstruction.SmallNF HConstruction.Nonflat HConstruction.DRepair
open HConstruction.NfRepair.Reproduced
open Set Metric
open AdalyFormal.Balaban.DeltaPrime (holonomyElem)
attribute [local irreducible] lowerPrecision

private theorem minimum_generic (T : H →L[ℝ] H) : ∃ A ∈ sphere (0 : H) 1,
    IsMinOn (fun X : H => (inner ℝ X (T X) : ℝ)) (sphere 0 1) A := by
  letI : Nontrivial H := ⟨⟨constantField, 0, constantField_nonzero⟩⟩
  have hn : (sphere (0 : H) 1).Nonempty := NormedSpace.sphere_nonempty.mpr (by norm_num)
  exact (isCompact_sphere (0 : H) 1).exists_isMinOn hn
    (continuous_id.inner T.continuous).continuousOn

private theorem minimum_exists : ∃ A ∈ sphere (0 : H) 1,
    IsMinOn (fun X : H => (inner ℝ X (lowerPrecision 0 X) : ℝ)) (sphere 0 1) A :=
  minimum_generic (lowerPrecision 0)

#print axioms minimum_exists

/-- The exact minimum of the fixed leading energy on the unit sphere. -/
def baselineMinimizer : H := Classical.choose minimum_exists
def baselineGap : ℝ := inner ℝ baselineMinimizer (lowerPrecision 0 baselineMinimizer)

theorem baselineMinimizer_norm : ‖baselineMinimizer‖ = 1 := by
  unfold baselineMinimizer
  simpa only [mem_sphere, dist_zero_right] using (Classical.choose_spec minimum_exists).1

theorem baselineGap_pos : 0 < baselineGap := by
  unfold baselineGap
  apply lowerPrecision_zero_positive
  intro h
  have hn := baselineMinimizer_norm
  rw [h, norm_zero] at hn
  norm_num at hn

theorem baselineGap_min (A : H) (hA : ‖A‖ = 1) :
    baselineGap ≤ (inner ℝ A (lowerPrecision 0 A) : ℝ) := by
  unfold baselineGap baselineMinimizer
  exact (Classical.choose_spec minimum_exists).2 (by simpa only [mem_sphere, dist_zero_right] using hA)

theorem baselineGap_lower (A : H) :
    baselineGap * ‖A‖^2 ≤ (inner ℝ A (lowerPrecision 0 A) : ℝ) := by
  by_cases hA : A = 0
  · simp [hA]
  have hn : ‖A‖ ≠ 0 := norm_ne_zero_iff.mpr hA
  have h := mul_le_mul_of_nonneg_left
    (baselineGap_min (‖A‖⁻¹ • A) (norm_smul_inv_norm (𝕜 := ℝ) hA)) (sq_nonneg ‖A‖)
  have he : ‖A‖^2 * (inner ℝ (‖A‖⁻¹ • A) (lowerPrecision 0 (‖A‖⁻¹ • A)) : ℝ) =
      inner ℝ A (lowerPrecision 0 A) := by
    rw [map_smul, inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    field_simp
  rw [he] at h
  simpa only [mul_comm] using h

#print axioms baselineGap_lower

private theorem maximum_exists : ∃ t ∈ Icc (-1 : ℝ) 1,
    IsMaxOn (fun s => ‖fderiv ℝ lowerPrecision s‖) (Icc (-1) 1) t := by
  exact isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num))
    ((smooth_lowerPrecision.continuous_fderiv (by simp)).norm.continuousOn)

#print axioms maximum_exists

/-- Exact maximum of the derivative operator norm on the fixed compact interval.
It involves only the smooth LOWER operator, not the moving orthogonal projector,
not g-inverse coefficients and not any numerical matrix. -/
def derivativeMaximizer : ℝ := Classical.choose maximum_exists
def derivativeCeiling : ℝ := ‖fderiv ℝ lowerPrecision derivativeMaximizer‖

theorem derivativeCeiling_nonneg : 0 ≤ derivativeCeiling := by
  exact norm_nonneg (fderiv ℝ lowerPrecision derivativeMaximizer)

theorem derivativeCeiling_bound (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖fderiv ℝ lowerPrecision t‖ ≤ derivativeCeiling :=
  (Classical.choose_spec maximum_exists).2 ht

/-- Certified O(|t|) bound for the ENTIRE source lower-precision perturbation.
In particular none of the indefinite curvature brackets is dropped. -/
theorem lowerPrecision_perturbation (t : ℝ) (ht : |t| ≤ 1) :
    ‖lowerPrecision t - lowerPrecision 0‖ ≤ derivativeCeiling * |t| := by
  have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => smooth_lowerPrecision.differentiable (by simp) x)
    derivativeCeiling_bound (by norm_num : (0:ℝ) ∈ Icc (-1:ℝ) 1) (abs_le.mp ht)
  simpa only [sub_zero, Real.norm_eq_abs] using h

/-- A precisely specified positive threshold. No assertion is made that this
threshold equals 1/16; both constants in the formula are unconditionally defined
and certified extrema of fixed, completely specified source operators. -/
def workingThreshold : ℝ := min (1/16) (baselineGap / (2*(derivativeCeiling+1)))

theorem workingThreshold_pos : 0 < workingThreshold := by
  apply lt_min (by norm_num)
  exact div_pos baselineGap_pos (by linarith [derivativeCeiling_nonneg])

theorem workingThreshold_le : workingThreshold ≤ (1/16 : ℝ) := min_le_left _ _

theorem threshold_absorption (t : ℝ) (ht : |t| ≤ workingThreshold) :
    derivativeCeiling * |t| ≤ baselineGap/2 := by
  have hden : 0 < 2*(derivativeCeiling+1) := by linarith [derivativeCeiling_nonneg]
  have h := ht.trans (min_le_right (1/16 : ℝ) (baselineGap / (2*(derivativeCeiling+1))))
  have hm := (le_div_iff₀ hden).mp h
  nlinarith [abs_nonneg t]

theorem precision_small_lower (t : ℝ) (ht : |t| ≤ workingThreshold) (A : H) :
    (baselineGap/2) * ‖A‖^2 ≤ (inner ℝ A (precisionU (nonflatU t) 1 A) : ℝ) := by
  have ht1 : |t| ≤ 1 := le_trans (ht.trans workingThreshold_le) (by norm_num)
  have hp := lowerPrecision_perturbation t ht1
  have habs := threshold_absorption t ht
  have hnorm : ‖lowerPrecision t - lowerPrecision 0‖ ≤ baselineGap/2 := hp.trans habs
  have hi := abs_real_inner_le_norm A ((lowerPrecision t - lowerPrecision 0) A)
  have hop := (lowerPrecision t - lowerPrecision 0).le_opNorm A
  have hi' : |(inner ℝ A ((lowerPrecision t - lowerPrecision 0) A) : ℝ)| ≤
      (baselineGap/2) * ‖A‖^2 := by
    calc
      _ ≤ ‖A‖ * ‖(lowerPrecision t - lowerPrecision 0) A‖ := hi
      _ ≤ ‖A‖ * (‖lowerPrecision t - lowerPrecision 0‖ * ‖A‖) :=
        mul_le_mul_of_nonneg_left hop (norm_nonneg A)
      _ ≤ (baselineGap/2)*‖A‖^2 := by
        nlinarith [mul_le_mul_of_nonneg_right hnorm (sq_nonneg ‖A‖)]
  have hl := (abs_le.mp hi').1
  simp only [_root_.sub_apply, inner_sub_right] at hl
  have hb := baselineGap_lower A
  have he := lowerPrecision_le_actual t A
  linarith

theorem precision_small_positive (t : ℝ) (ht : |t| ≤ workingThreshold) (A : H) (hA : A ≠ 0) :
    (0 : ℝ) < inner ℝ A (precisionU (nonflatU t) 1 A) := by
  have h := precision_small_lower t ht A
  have hp : 0 < (baselineGap/2)*‖A‖^2 :=
    mul_pos (by linarith [baselineGap_pos]) (sq_pos_of_pos (norm_pos_iff.mpr hA))
  exact lt_of_lt_of_le hp h

/-- Full-carrier positivity implies transverse positivity at the SAME parameter,
without identifying the nonflat transverse gauge or Q with flat operators. -/
theorem transverse_small_positive (t : ℝ) (ht : |t| ≤ workingThreshold) (A : H)
    (hA : HConstruction.Circle.bondTransverse A ≠ 0) :
    (0 : ℝ) < inner ℝ (HConstruction.Circle.bondTransverse A)
      (precisionU (nonflatU t) 1 (HConstruction.Circle.bondTransverse A)) :=
  precision_small_positive t ht _ hA

/-- No inverse, norm enclosure or positivity obligation is assumed. -/
theorem physicalG0_small (t : ℝ) (ht : |t| ≤ workingThreshold) : HasPhysicalG0 (nonflatU t) 1 := by
  obtain ⟨G,hr,hl,_⟩ := positive_inverse (precisionU (nonflatU t) 1) (precision_small_positive t ht)
  exact ⟨G,hr,hl⟩

def workingU := nonflatU workingThreshold

theorem workingU_nonflat : ∃ p, holonomyElem workingU p ≠ 1 :=
  nonflatU_has_curved_plaquette (ne_of_gt workingThreshold_pos)

theorem workingU_G0 : HasPhysicalG0 workingU 1 :=
  physicalG0_small workingThreshold (by rw [abs_of_pos workingThreshold_pos])

#print axioms baselineGap_pos
#print axioms baselineGap_lower
#print axioms derivativeCeiling_bound
#print axioms lowerPrecision_perturbation
#print axioms workingThreshold_pos
#print axioms precision_small_lower
#print axioms precision_small_positive
#print axioms transverse_small_positive
#print axioms physicalG0_small
#print axioms workingU_nonflat
#print axioms workingU_G0
end HConstruction.TransversePos
