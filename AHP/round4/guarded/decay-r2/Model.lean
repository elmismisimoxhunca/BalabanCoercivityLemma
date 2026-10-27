
/-! An exact two-coordinate diagnostic. These are matrices, not replacements
for any pinned lattice operator and not a negative certificate. -/
namespace AdalyFormal.Round4.Guarded.DecayR2.Diagnostic

noncomputable def bulk (t d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, t; t, 1 + d]
noncomputable def correction (d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, d]
noncomputable def shift (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![t ^ 2 - 1, 0; 0, 0]
noncomputable def greenColumn (t d : ℝ) : Fin 2 → ℝ :=
  ![(1 + d) / (1 + d - t ^ 2), -t / (1 + d - t ^ 2)]
noncomputable def responseCoefficient (t d : ℝ) : ℝ := t ^ 2 * d / (1 + d - t ^ 2)

/-- D and Theta have exactly disjoint coordinate supports. -/
theorem disjoint_support (t d : ℝ) :
    shift t * correction d = 0 ∧ correction d * shift t = 0 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [shift, correction, Matrix.mul_apply, Fin.sum_univ_two]

/-- Both localized operators have a fixed positive Euclidean energy gap,
even while their coupling t and the correction d tend to zero. -/
theorem uniform_local_gaps {t d : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) (hd : 0 ≤ d)
    (x y : ℝ) :
    (1 / 2 : ℝ) * (x ^ 2 + y ^ 2) ≤ x ^ 2 + 2 * t * x * y + (1 + d) * y ^ 2 ∧
    (1 / 2 : ℝ) * (x ^ 2 + y ^ 2) ≤ x ^ 2 + 2 * t * x * y + y ^ 2 := by
  have h1 := mul_nonneg ht (sq_nonneg (x + y))
  have h2 := mul_nonneg (show 0 ≤ (1 / 2 : ℝ) - t by linarith)
    (add_nonneg (sq_nonneg x) (sq_nonneg y))
  have h3 := mul_nonneg hd (sq_nonneg y)
  constructor <;> nlinarith

/-- Localized positivity and exact support separation do not force a
positive all-carrier gap. The uncorrected all-carrier is nevertheless a unit. -/
theorem guarded_separation {t d : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 4) (hd : 0 < d) :
    IsUnit (bulk t d) ∧ IsUnit (bulk t d - correction d) ∧
    IsUnit (bulk t d + shift t) ∧ ¬ IsUnit (bulk t d + shift t - correction d) := by
  have htc : 0 < 1 - t ^ 2 := by nlinarith
  have htb : 0 < 1 + d - t ^ 2 := by linarith
  have hta : 0 < t ^ 2 * d := mul_pos (sq_pos_of_pos ht) hd
  have hB : (bulk t d).det = 1 + d - t ^ 2 := by
    simp [bulk, Matrix.det_fin_two]; ring
  have hC : (bulk t d - correction d).det = 1 - t ^ 2 := by
    simp [bulk, correction, Matrix.det_fin_two]; ring
  have hA : (bulk t d + shift t).det = t ^ 2 * d := by
    simp [bulk, shift, Matrix.det_fin_two]; ring
  have hAC : (bulk t d + shift t - correction d).det = 0 := by
    simp [bulk, shift, correction, Matrix.det_fin_two]; ring
  simp only [Matrix.isUnit_iff_isUnit_det, hB, hC, hA, hAC, isUnit_iff_ne_zero]
  exact ⟨htb.ne', htc.ne', hta.ne', not_not.mpr rfl⟩

/-- These are actual inverse images of the boundary basis vector, not
surrogate decay parameters. Uniqueness follows from the preceding units. -/
theorem green_columns {t d : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) (hd : 0 ≤ d) :
    (bulk t d).mulVec (greenColumn t d) = ![1, 0] ∧
    (bulk t d - correction d).mulVec (greenColumn t 0) = ![1, 0] := by
  have htb : 1 + d - t ^ 2 ≠ 0 := by nlinarith
  have htc : 1 - t ^ 2 ≠ 0 := by nlinarith
  constructor <;> ext i <;> fin_cases i <;>
    simp [bulk, correction, greenColumn, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    field_simp [htb, htc] <;> nlinarith

/-- Their interior coordinates decay linearly with the boundary-to-interior
coupling. t can in particular be chosen exponentially small. -/
theorem inverse_input_decay {t d : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) (hd : 0 ≤ d) :
    |greenColumn t d 1| ≤ 2 * t ∧ |greenColumn t 0 1| ≤ 2 * t := by
  have htb : 0 < 1 + d - t ^ 2 := by nlinarith
  have htc : 0 < 1 - t ^ 2 := by nlinarith
  simp only [greenColumn, Matrix.cons_val_one, Matrix.cons_val_zero, add_zero,
    abs_div, abs_neg, abs_of_nonneg ht, abs_of_pos htb, abs_of_pos htc]
  constructor
  · apply (div_le_iff₀ htb).mpr
    have h := mul_nonneg ht (show 0 ≤ 2 * (1 + d - t ^ 2) - 1 by nlinarith)
    nlinarith
  · apply (div_le_iff₀ htc).mpr
    have h := mul_nonneg ht (show 0 ≤ 2 * (1 - t ^ 2) - 1 by nlinarith)
    nlinarith

/-- K_B is a small nonzero scalar on the first axis while K_C is exactly zero. -/
theorem boundary_responses {t d : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) (hd : 0 ≤ d) :
    (![1, 0] + (shift t).mulVec (greenColumn t d) : Fin 2 → ℝ) =
        ![responseCoefficient t d, 0] ∧
    (![1, 0] + (shift t).mulVec (greenColumn t 0) : Fin 2 → ℝ) = 0 := by
  have htb : 1 + d - t ^ 2 ≠ 0 := by nlinarith
  have htc : 1 - t ^ 2 ≠ 0 := by nlinarith
  constructor <;> ext i <;> fin_cases i <;>
    simp [shift, greenColumn, responseCoefficient, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    field_simp [htb, htc] <;> nlinarith

/-- Arbitrarily small absolute return has inverse-relative size exactly one. -/
theorem relative_not_small {t d : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 4) (hd : 0 < d) :
    0 < responseCoefficient t d ∧ responseCoefficient t d ≤ 2 * t ^ 2 * d ∧
    |(responseCoefficient t d)⁻¹ * (0 - responseCoefficient t d)| = 1 := by
  have hden : 0 < 1 + d - t ^ 2 := by nlinarith
  have hpos : 0 < responseCoefficient t d :=
    div_pos (mul_pos (sq_pos_of_pos ht) hd) hden
  refine ⟨hpos, ?_, ?_⟩
  · apply (div_le_iff₀ hden).mpr
    have h := mul_nonneg (mul_nonneg (sq_nonneg t) hd.le)
      (show 0 ≤ 2 * (1 + d - t ^ 2) - 1 by nlinarith)
    dsimp [responseCoefficient]
    nlinarith
  · rw [zero_sub, mul_neg, inv_mul_cancel₀ hpos.ne', abs_neg, abs_one]

/-- The correction-visible all-carrier transfer grows reciprocally. Its
product with the correction and the exact C inverse input is exactly one. -/
theorem observed_amplification {t d : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 4) (hd : 0 < d) :
    (bulk t d + shift t).mulVec
      ![(t ^ 2 - 1) * (1 + d) / (t ^ 2 * d), (1 - t ^ 2) / (t * d)] =
        (shift t).mulVec ![1, 0] ∧
    ((1 - t ^ 2) / (t * d)) * d * (t / (1 - t ^ 2)) = 1 := by
  have htc : 1 - t ^ 2 ≠ 0 := by nlinarith
  constructor
  · ext i; fin_cases i <;>
      simp [bulk, shift, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      field_simp [ht.ne', hd.ne'] <;> ring
  · field_simp [ht.ne', hd.ne', htc]

/-- Any prescribed positive correction cap and positive transmission bound
permit the diagnostic separation. This is not the lattice cofinal quantifier. -/
theorem arbitrarily_small_separated_model (cap transmission : ℝ)
    (hcap : 0 < cap) (htrans : 0 < transmission) :
    ∃ t d : ℝ, 0 < t ∧ t ≤ 1 / 4 ∧ t < transmission ∧
      0 < d ∧ d ≤ 1 / 4 ∧ d < cap ∧
      shift t * correction d = 0 ∧ correction d * shift t = 0 ∧
      IsUnit (bulk t d) ∧ IsUnit (bulk t d - correction d) ∧
      IsUnit (bulk t d + shift t) ∧ ¬ IsUnit (bulk t d + shift t - correction d) ∧
      |greenColumn t d 1| ≤ 2 * t ∧ |greenColumn t 0 1| ≤ 2 * t ∧
      |(responseCoefficient t d)⁻¹ * (0 - responseCoefficient t d)| = 1 := by
  let t := min (transmission / 2) (1 / 4)
  let d := min (cap / 2) (1 / 4)
  have ht : 0 < t := lt_min (half_pos htrans) (by norm_num)
  have hd : 0 < d := lt_min (half_pos hcap) (by norm_num)
  have ht' : t ≤ 1 / 4 := min_le_right _ _
  have hd' : d ≤ 1 / 4 := min_le_right _ _
  have hsep := guarded_separation ht ht' hd
  have hdis := disjoint_support t d
  have hdec := inverse_input_decay ht.le ht' hd.le
  exact ⟨t, d, ht, ht', (min_le_left _ _).trans_lt (half_lt_self htrans),
    hd, hd', (min_le_left _ _).trans_lt (half_lt_self hcap), hdis.1, hdis.2,
    hsep.1, hsep.2.1, hsep.2.2.1, hsep.2.2.2, hdec.1, hdec.2,
    (relative_not_small ht ht' hd).2.2⟩

#print axioms bulk
#print axioms correction
#print axioms shift
#print axioms greenColumn
#print axioms responseCoefficient
#print axioms disjoint_support
#print axioms uniform_local_gaps
#print axioms guarded_separation
#print axioms green_columns
#print axioms inverse_input_decay
#print axioms boundary_responses
#print axioms relative_not_small
#print axioms observed_amplification
#print axioms arbitrarily_small_separated_model
end AdalyFormal.Round4.Guarded.DecayR2.Diagnostic
