import GaugeContinuity

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
noncomputable section
namespace HConstruction.G0CoerceFinal
open HConstruction.Covariance HConstruction.SmallNF HConstruction.TransversePos
open HConstruction.DRepair HConstruction.Nonflat HConstruction.NfRepair.Reproduced
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
attribute [local irreducible] baselineGap workingThreshold precisionU deltaPrimePi

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem isUnit_of_positive (T : E →L[ℝ] E)
    (h : ∀ X, X ≠ 0 → (0 : ℝ) < inner ℝ X (T X)) : IsUnit T := by
  obtain ⟨G,hR,hL,_⟩ := positive_inverse T h
  refine ⟨⟨T,G,?_,?_⟩,rfl⟩
  · apply ContinuousLinearMap.ext
    exact hR
  · apply ContinuousLinearMap.ext
    exact hL

theorem inverse_norm_of_lower (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hl : ∀ X, c*‖X‖^2 ≤ (inner ℝ X (T X) : ℝ)) : ‖Ring.inverse T‖ ≤ 1/c := by
  have hu : IsUnit T := isUnit_of_positive T (fun X hX =>
    lt_of_lt_of_le (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hX))) (hl X))
  apply ContinuousLinearMap.opNorm_le_bound _ (le_of_lt (one_div_pos.mpr hc))
  intro X
  have hr : T (Ring.inverse T X) = X :=
    congrArg (fun V : E →L[ℝ] E => V X) (Ring.mul_inverse_cancel _ hu)
  have h := hl (Ring.inverse T X)
  rw [hr] at h
  have hi := real_inner_le_norm (Ring.inverse T X) X
  have hb : c*‖Ring.inverse T X‖ ≤ ‖X‖ := by
    by_cases hz : Ring.inverse T X = 0
    · simp [hz]
    · have hn := norm_pos_iff.mpr hz
      nlinarith
  calc
    ‖Ring.inverse T X‖ ≤ ‖X‖/c := (le_div_iff₀ hc).mpr (by linarith)
    _ = (1/c)*‖X‖ := by ring

/-- Ordinary-kernel Neumann identification, with BOTH inverse gates visible. -/
theorem neumann_eq_inverse (T P : E →L[ℝ] E) (hT : IsUnit T) (hTP : IsUnit (T-P))
    (hn : ‖P * Ring.inverse T‖ < 1) :
    HConstruction.Covariance.Reproduced.gOneOfNeumann (Ring.inverse T) P = Ring.inverse (T-P) := by
  have he : T-P = (1-P*Ring.inverse T)*T := by
    rw [sub_mul, one_mul, mul_assoc, Ring.inverse_mul_cancel _ hT, mul_one]
  have hleft : HConstruction.Covariance.Reproduced.gOneOfNeumann (Ring.inverse T) P * (T-P) = 1 := by
    rw [he, ← mul_assoc,
      HConstruction.Covariance.Reproduced.gOneOfNeumann_cancel_right _ _ hn,
      Ring.inverse_mul_cancel _ hT]
  calc
    _ = (HConstruction.Covariance.Reproduced.gOneOfNeumann (Ring.inverse T) P * (T-P)) *
        Ring.inverse (T-P) := by rw [mul_assoc, Ring.mul_inverse_cancel _ hTP, mul_one]
    _ = Ring.inverse (T-P) := by rw [hleft, one_mul]
end General

def actualG0 (t : ℝ) : H →L[ℝ] H := Ring.inverse (precisionU (nonflatU t) 1)

theorem small_precision_unit (t : ℝ) (ht : |t| ≤ workingThreshold) :
    IsUnit (precisionU (nonflatU t) 1) :=
  isUnit_of_positive _ (precision_small_positive t ht)

theorem actualG0_right (t : ℝ) (ht : |t| ≤ workingThreshold) :
    precisionU (nonflatU t) 1 * actualG0 t = 1 :=
  Ring.mul_inverse_cancel _ (small_precision_unit t ht)

theorem actualG0_left (t : ℝ) (ht : |t| ≤ workingThreshold) :
    actualG0 t * precisionU (nonflatU t) 1 = 1 :=
  Ring.inverse_mul_cancel _ (small_precision_unit t ht)

theorem actualG0_norm (t : ℝ) (ht : |t| ≤ workingThreshold) :
    ‖actualG0 t‖ ≤ 2/baselineGap := by
  have h := inverse_norm_of_lower (precisionU (nonflatU t) 1) (baselineGap/2)
    (by linarith [baselineGap_pos]) (precision_small_lower t ht)
  unfold actualG0
  convert h using 1 <;> ring

theorem gauge_radius_exists : ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ,
    |t| < r → ‖deltaPrimePi (nonflatU t)‖ < baselineGap/4 := by
  have hz : deltaPrimePi (nonflatU 0) = 0 := by
    rw [nonflatU_zero_eq_trivial]
    exact deltaPrimePi_flat
  have hev : ∀ᶠ t in nhds (0 : ℝ), ‖deltaPrimePi (nonflatU t)‖ < baselineGap/4 :=
    (smoothAt_deltaPrimePi.continuousAt.norm).eventually
      (gt_mem_nhds (by
        change ‖deltaPrimePi (nonflatU 0)‖ < baselineGap/4
        rw [hz, norm_zero]
        linarith [baselineGap_pos]))
  obtain ⟨r,hr,hs⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨r,hr,fun t ht => hs (by simpa only [dist_zero_right, Real.norm_eq_abs] using ht)⟩

/-- A precisely defined, further positive shrinking. This is NOT an evaluated
rational threshold, and it does not assert that the original workingU qualifies. -/
def gaugeRadius : ℝ := Classical.choose gauge_radius_exists

def gaugeThreshold : ℝ := min workingThreshold (gaugeRadius/2)

theorem gaugeRadius_pos : 0 < gaugeRadius := (Classical.choose_spec gauge_radius_exists).1

theorem gaugeThreshold_pos : 0 < gaugeThreshold :=
  lt_min workingThreshold_pos (by linarith [gaugeRadius_pos])

theorem gaugeThreshold_le : gaugeThreshold ≤ workingThreshold := min_le_left _ _

theorem deltaPrimePi_small (t : ℝ) (ht : |t| ≤ gaugeThreshold) :
    ‖deltaPrimePi (nonflatU t)‖ < baselineGap/4 := by
  apply (Classical.choose_spec gauge_radius_exists).2 t
  change |t| < gaugeRadius
  have h := ht.trans (min_le_right workingThreshold (gaugeRadius/2))
  linarith [gaugeRadius_pos]

/-- Precision defining the paper's intermediate G, not G1. -/
def gaugePrecision (t : ℝ) : H →L[ℝ] H := precisionU (nonflatU t) 1 - deltaPrimePi (nonflatU t)

theorem gaugePrecision_lower (t : ℝ) (ht : |t| ≤ gaugeThreshold) (A : H) :
    (baselineGap/4)*‖A‖^2 ≤ (inner ℝ A (gaugePrecision t A) : ℝ) := by
  have h0 := precision_small_lower t (ht.trans gaugeThreshold_le) A
  have hP := (deltaPrimePi_small t ht).le
  have hinner := real_inner_le_norm A (deltaPrimePi (nonflatU t) A)
  have hop := (deltaPrimePi (nonflatU t)).le_opNorm A
  have hp : (inner ℝ A (deltaPrimePi (nonflatU t) A) : ℝ) ≤
      (baselineGap/4)*‖A‖^2 := by
    calc
      _ ≤ ‖A‖ * ‖deltaPrimePi (nonflatU t) A‖ := hinner
      _ ≤ ‖A‖ * (‖deltaPrimePi (nonflatU t)‖ * ‖A‖) :=
        mul_le_mul_of_nonneg_left hop (norm_nonneg A)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hP (sq_nonneg ‖A‖)]
  change (baselineGap/4)*‖A‖^2 ≤ inner ℝ A ((precisionU (nonflatU t) 1) A - deltaPrimePi (nonflatU t) A)
  rw [inner_sub_right]
  linarith

theorem gauge_neumann_gate (t : ℝ) (ht : |t| ≤ gaugeThreshold) :
    ‖deltaPrimePi (nonflatU t) * actualG0 t‖ < 1 := by
  have h0 := actualG0_norm t (ht.trans gaugeThreshold_le)
  have hP := deltaPrimePi_small t ht
  have hpos : 0 < 2/baselineGap := div_pos (by norm_num) baselineGap_pos
  calc
    _ ≤ ‖deltaPrimePi (nonflatU t)‖ * ‖actualG0 t‖ := norm_mul_le _ _
    _ ≤ ‖deltaPrimePi (nonflatU t)‖ * (2/baselineGap) :=
      mul_le_mul_of_nonneg_left h0 (norm_nonneg _)
    _ < (baselineGap/4) * (2/baselineGap) := mul_lt_mul_of_pos_right hP hpos
    _ < 1 := by field_simp [ne_of_gt baselineGap_pos]; linarith [baselineGap_pos]

/-- The printed (3.130) source perturbation has now been supplied. This is G,
NOT G1: no second-jet correction is set to zero at a nonflat background. -/
def gaugeG (t : ℝ) : H →L[ℝ] H :=
  HConstruction.Covariance.Reproduced.gOneOfNeumann (actualG0 t) (deltaPrimePi (nonflatU t))

theorem gaugePrecision_unit (t : ℝ) (ht : |t| ≤ gaugeThreshold) : IsUnit (gaugePrecision t) := by
  apply isUnit_of_positive
  intro A hA
  exact lt_of_lt_of_le (mul_pos (by linarith [baselineGap_pos])
    (sq_pos_of_pos (norm_pos_iff.mpr hA))) (gaugePrecision_lower t ht A)

theorem gaugeG_inverse (t : ℝ) (ht : |t| ≤ gaugeThreshold) :
    gaugeG t = Ring.inverse (gaugePrecision t) :=
  neumann_eq_inverse _ _ (small_precision_unit t (ht.trans gaugeThreshold_le))
    (gaugePrecision_unit t ht) (gauge_neumann_gate t ht)

theorem gaugeG_right (t : ℝ) (ht : |t| ≤ gaugeThreshold) : gaugePrecision t * gaugeG t = 1 := by
  rw [gaugeG_inverse t ht, Ring.mul_inverse_cancel _ (gaugePrecision_unit t ht)]

theorem gaugeG_left (t : ℝ) (ht : |t| ≤ gaugeThreshold) : gaugeG t * gaugePrecision t = 1 := by
  rw [gaugeG_inverse t ht, Ring.inverse_mul_cancel _ (gaugePrecision_unit t ht)]

theorem gaugeG_series (t : ℝ) (ht : |t| ≤ gaugeThreshold) :
    gaugeG t = ∑' n : ℕ, actualG0 t * (deltaPrimePi (nonflatU t) * actualG0 t)^n :=
  HConstruction.Covariance.Reproduced.gOneOfNeumann_eq_tsum _ _ (gauge_neumann_gate t ht)

theorem gaugeG_norm (t : ℝ) (ht : |t| ≤ gaugeThreshold) : ‖gaugeG t‖ ≤ 4/baselineGap := by
  rw [gaugeG_inverse t ht]
  convert inverse_norm_of_lower _ (baselineGap/4) (by linarith [baselineGap_pos])
    (gaugePrecision_lower t ht) using 1 <;> ring

theorem nonflat_gaugeG_exists :
    0 < gaugeThreshold ∧ HasPhysicalG0 (nonflatU gaugeThreshold) 1 ∧
    gaugePrecision gaugeThreshold * gaugeG gaugeThreshold = 1 ∧
    gaugeG gaugeThreshold * gaugePrecision gaugeThreshold = 1 := by
  have ht : |gaugeThreshold| ≤ gaugeThreshold := by rw [abs_of_pos gaugeThreshold_pos]
  exact ⟨gaugeThreshold_pos, physicalG0_small _ (ht.trans gaugeThreshold_le),
    gaugeG_right _ ht, gaugeG_left _ ht⟩

#print axioms deltaPrimePi_small
#print axioms gaugePrecision_lower
#print axioms gauge_neumann_gate
#print axioms gaugeG_series
#print axioms gaugeG_right
#print axioms gaugeG_left
#print axioms nonflat_gaugeG_exists
end HConstruction.G0CoerceFinal
