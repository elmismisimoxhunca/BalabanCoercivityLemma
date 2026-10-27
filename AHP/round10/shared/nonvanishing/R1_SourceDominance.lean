import D1IVT

/-!
Finite neutral-source estimate, independent of any operator dictionary.
The tridiagonal source equations and a bound on the block jets imply nonvanishing.
This file does not assert that the frozen operators satisfy those hypotheses.
-/
set_option autoImplicit false

namespace AdalyFormal.Round10.Nonvanishing

open Finset

/-- Zero-padded left neighbor. -/
def left (a : ℕ → ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else a (j - 1)

/-- The source multiplier from the neutral tridiagonal reduction. -/
def sourceWeight (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  (if j = 0 then 1 else 0) - 2 * left a j + 2 * a (j + 1)

/-- Half the coupling, in the finite block reduction. -/
def sourcePairing (n : ℕ) (a v : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (n + 1), sourceWeight a j * v j

lemma sum_left_abs (n : ℕ) (a : ℕ → ℝ) :
    (∑ j ∈ range (n + 1), |left a j|) = ∑ j ∈ range n, |a j| := by
  rw [sum_range_succ']
  simp [left]

lemma sum_right_abs (n : ℕ) (a : ℕ → ℝ) (ha : a (n + 1) = 0) :
    (∑ j ∈ range (n + 1), |a (j + 1)|) =
      (∑ j ∈ range (n + 1), |a j|) - |a 0| := by
  have h := sum_range_succ' (fun j => |a j|) (n + 1)
  rw [sum_range_succ, ha, abs_zero, add_zero] at h
  linarith

lemma neighbor_sum_bound (n : ℕ) (a : ℕ → ℝ) (ha : a (n + 1) = 0) :
    (∑ j ∈ range (n + 1), |left a j|) +
        (∑ j ∈ range (n + 1), |a (j + 1)|) ≤
      2 * (∑ j ∈ range (n + 1), |a j|) - |a 0| := by
  rw [sum_left_abs, sum_right_abs n a ha]
  have h : (∑ j ∈ range n, |a j|) ≤ ∑ j ∈ range (n + 1), |a j| := by
    rw [sum_range_succ]
    exact le_add_of_nonneg_right (abs_nonneg _)
  linarith

/-- An l1 estimate for the exact finite tridiagonal source, with no sign assumptions. -/
theorem source_l1_bound (n : ℕ) (a : ℕ → ℝ) (ha : a (n + 1) = 0)
    (heq : ∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0) :
    2 * ((∑ j ∈ range (n + 1), |left a j|) +
      (∑ j ∈ range (n + 1), |a (j + 1)|)) ≤ (15 / 19 : ℝ) := by
  let S := ∑ j ∈ range (n + 1), |a j|
  let L := ∑ j ∈ range (n + 1), |left a j|
  let U := ∑ j ∈ range (n + 1), |a (j + 1)|
  have hpoint (j : ℕ) (hj : j ∈ range (n + 1)) :
      6 * |a j| ≤ (if j = 0 then (3 / 2 : ℝ) else 0) + |left a j| + |a (j + 1)| := by
    have e : 6 * a j = (if j = 0 then (3 / 2 : ℝ) else 0) - left a j - a (j + 1) := by
      have := heq j (mem_range.mp hj)
      linarith
    calc
      6 * |a j| = |6 * a j| := by rw [abs_mul]; norm_num
      _ = |(if j = 0 then (3 / 2 : ℝ) else 0) - left a j - a (j + 1)| := congrArg abs e
      _ ≤ |(if j = 0 then (3 / 2 : ℝ) else 0) - left a j| + |a (j + 1)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le ((if j = 0 then (3 / 2 : ℝ) else 0) - left a j) (-a (j + 1))
      _ ≤ |(if j = 0 then (3 / 2 : ℝ) else 0)| + |left a j| + |a (j + 1)| := by
        gcongr
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (if j = 0 then (3 / 2 : ℝ) else 0) (-left a j)
      _ = _ := by split_ifs <;> norm_num
  have hs := sum_le_sum hpoint
  have htotal : 6 * S ≤ (3 / 2 : ℝ) + L + U := by
    simpa [S, L, U, sum_add_distrib, ← mul_sum] using hs
  have hnb : L + U ≤ 2 * S - |a 0| := neighbor_sum_bound n a ha
  have hroot : (3 / 2 : ℝ) ≤ 6 * |a 0| + |a 1| := by
    have e := heq 0 (by omega)
    simp [left] at e
    calc
      (3 / 2 : ℝ) = |6 * a 0 + a 1| := by rw [e]; norm_num
      _ ≤ |6 * a 0| + |a 1| := abs_add_le _ _
      _ = _ := by rw [abs_mul]; norm_num
  have hfirst : |a 1| ≤ U := by
    exact single_le_sum (fun j _ => abs_nonneg (a (j + 1))) (by simp : 0 ∈ range (n + 1))
  have hu : U = S - |a 0| := sum_right_abs n a ha
  change 2 * (L + U) ≤ (15 / 19 : ℝ)
  linarith

lemma sourcePairing_decompose (n : ℕ) (a v : ℕ → ℝ) :
    sourcePairing n a v = v 0 +
      ∑ j ∈ range (n + 1), (-2 * left a j + 2 * a (j + 1)) * v j := by
  unfold sourcePairing sourceWeight
  simp_rw [show ∀ j : ℕ,
    ((if j = 0 then (1 : ℝ) else 0) - 2 * left a j + 2 * a (j + 1)) * v j =
    (if j = 0 then v 0 else 0) + (-2 * left a j + 2 * a (j + 1)) * v j by
      intro j
      split_ifs with hj <;> simp_all
      all_goals ring]
  simp [sum_add_distrib]

/-- A uniform relative error, using only the finite source equations and jet domination. -/
theorem sourcePairing_error (n : ℕ) (a v : ℕ → ℝ) (ha : a (n + 1) = 0)
    (heq : ∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0)
    (hv : ∀ j < n + 1, |v j| ≤ |v 0|) :
    |sourcePairing n a v - v 0| ≤ (15 / 19 : ℝ) * |v 0| := by
  rw [sourcePairing_decompose]
  have hpoint (j : ℕ) (hj : j ∈ range (n + 1)) :
      |(-2 * left a j + 2 * a (j + 1)) * v j| ≤
        (2 * (|left a j| + |a (j + 1)|)) * |v 0| := by
    rw [abs_mul]
    apply mul_le_mul _ (hv j (mem_range.mp hj)) (abs_nonneg _) (by positivity)
    calc
      |-2 * left a j + 2 * a (j + 1)| ≤ |-2 * left a j| + |2 * a (j + 1)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul]; norm_num; ring
  have hs := sum_le_sum hpoint
  have hb := mul_le_mul_of_nonneg_right (source_l1_bound n a ha heq) (abs_nonneg (v 0))
  have hh := abs_sum_le_sum_abs
    (fun j : ℕ => (-2 * left a j + 2 * a (j + 1)) * v j) (range (n + 1))
  have hs' : (∑ j ∈ range (n + 1), |(-2 * left a j + 2 * a (j + 1)) * v j|) ≤
      (2 * ((∑ j ∈ range (n + 1), |left a j|) +
        (∑ j ∈ range (n + 1), |a (j + 1)|))) * |v 0| := by
    simpa only [← sum_mul, ← mul_sum, ← sum_add_distrib] using hs
  have h := hh.trans (hs'.trans hb)
  simpa only [add_sub_cancel_left] using h

/-- The cancellation margin is at least 4/19 of the first jet. -/
theorem sourcePairing_lower (n : ℕ) (a v : ℕ → ℝ) (ha : a (n + 1) = 0)
    (heq : ∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0)
    (hv : ∀ j < n + 1, |v j| ≤ |v 0|) :
    (4 / 19 : ℝ) * |v 0| ≤ |sourcePairing n a v| := by
  have he := sourcePairing_error n a v ha heq hv
  have ht := abs_add_le (v 0 - sourcePairing n a v) (sourcePairing n a v)
  rw [sub_add_cancel, abs_sub_comm] at ht
  linarith

/-- The finite source's first coefficient is positive, without a limiting calculation. -/
theorem sourceWeight_zero_lower (n : ℕ) (a : ℕ → ℝ) (ha : a (n + 1) = 0)
    (heq : ∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0) :
    (4 / 19 : ℝ) ≤ sourceWeight a 0 := by
  let v : ℕ → ℝ := fun j => if j = 0 then 1 else 0
  have hv : ∀ j < n + 1, |v j| ≤ |v 0| := by
    intro j _
    simp only [v, if_pos rfl, abs_one]
    split_ifs <;> norm_num
  have he := sourcePairing_error n a v ha heq hv
  have hp : sourcePairing n a v = sourceWeight a 0 := by
    simp [sourcePairing, v]
  rw [hp] at he
  have ht := (abs_le.mp he).1
  norm_num [v] at ht
  linarith

/-- Nonvanishing of the block coupling; all block-identification premises stay explicit. -/
theorem sourcePairing_ne_zero (n : ℕ) (a v : ℕ → ℝ) (ha : a (n + 1) = 0)
    (heq : ∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0)
    (hv : ∀ j < n + 1, |v j| ≤ |v 0|) (hzero : v 0 ≠ 0) :
    sourcePairing n a v ≠ 0 := by
  intro hz
  have h := sourcePairing_error n a v ha heq hv
  rw [hz, zero_sub, abs_neg] at h
  have hp := abs_pos.mpr hzero
  linarith

/-- The same bound gives a fixed sign relative to the first jet. -/
theorem sourcePairing_same_sign (n : ℕ) (a v : ℕ → ℝ) (ha : a (n + 1) = 0)
    (heq : ∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0)
    (hv : ∀ j < n + 1, |v j| ≤ |v 0|) (hzero : v 0 ≠ 0) :
    0 < sourcePairing n a v * v 0 := by
  have he := sourcePairing_error n a v ha heq hv
  have hl := (abs_le.mp he).1
  have hu := (abs_le.mp he).2
  rcases lt_or_gt_of_ne hzero with hn | hp
  · rw [abs_of_neg hn] at hl hu
    exact mul_pos_of_neg_of_neg (by linarith) hn
  · rw [abs_of_pos hp] at hl hu
    exact mul_pos (by linarith) hp

/-- Explicit dictionary interface: these are unproved properties of the actual block. -/
def BlockSourceData (coupling : ℝ) : Prop :=
  ∃ (n : ℕ) (a v : ℕ → ℝ) (factor : ℝ),
    a (n + 1) = 0 ∧
    (∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0) ∧
    (∀ j < n + 1, |v j| ≤ |v 0|) ∧ v 0 ≠ 0 ∧
    factor ≠ 0 ∧ coupling = factor * sourcePairing n a v

/-- A block identification with the stated jet bounds suffices. It is not supplied here. -/
theorem coupling_ne_zero_of_blockSourceData (coupling : ℝ)
    (h : BlockSourceData coupling) : coupling ≠ 0 := by
  obtain ⟨n, a, v, factor, ha, heq, hv, hzero, hf, hform⟩ := h
  rw [hform]
  exact mul_ne_zero hf (sourcePairing_ne_zero n a v ha heq hv hzero)

#print axioms left
#print axioms sourceWeight
#print axioms sourcePairing
#print axioms sum_left_abs
#print axioms sum_right_abs
#print axioms neighbor_sum_bound
#print axioms source_l1_bound
#print axioms sourcePairing_decompose
#print axioms sourcePairing_error
#print axioms sourcePairing_lower
#print axioms sourceWeight_zero_lower
#print axioms sourcePairing_ne_zero
#print axioms sourcePairing_same_sign
#print axioms BlockSourceData
#print axioms coupling_ne_zero_of_blockSourceData

end AdalyFormal.Round10.Nonvanishing
