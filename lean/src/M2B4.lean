import Mathlib

/-!
# M2B4 -- a one-dimensional smooth cutoff by double moving average (m2_bridge_20261014, Layer B1)

`chi0 a b` = indicator of `[a, b)` on `ℕ`; `avg w g o = (1/w) Σ_{t<w} g (o + t)`; `prof a b w = avg w (avg w (chi0 a b))`.
Sliding-window identity `avg_step : avg w g (o+1) - avg w g o = (1/w)(g (o+w) - g o)` gives, with no calculus,
* `prof_first`  : `|prof (o+1) - prof o| ≤ 1/w`,
* `prof_second` : `|prof (o+2) + prof o - 2 prof (o+1)| ≤ 2/w²`,
* `prof_nonneg`, `prof_le_one`,
* `prof_support` : `prof o ≠ 0 → o < b ∧ a + 2 ≤ o + 2 w`,
* `prof_one` : `prof o = 1` when `a ≤ o` and `o + 2 w ≤ b + 1`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false

namespace AdalyFormal.M2Bridge

open Finset

noncomputable def chi0 (a b : ℕ) (o : ℕ) : ℝ := if a ≤ o ∧ o < b then 1 else 0

noncomputable def avg (w : ℕ) (g : ℕ → ℝ) (o : ℕ) : ℝ := (1 / (w : ℝ)) * ∑ t ∈ range w, g (o + t)

noncomputable def prof (a b w : ℕ) : ℕ → ℝ := avg w (avg w (chi0 a b))

theorem chi0_nonneg (a b o : ℕ) : 0 ≤ chi0 a b o := by unfold chi0; split_ifs <;> norm_num
theorem chi0_le_one (a b o : ℕ) : chi0 a b o ≤ 1 := by unfold chi0; split_ifs <;> norm_num

theorem avg_step (w : ℕ) (g : ℕ → ℝ) (o : ℕ) :
    avg w g (o + 1) - avg w g o = (1 / (w : ℝ)) * (g (o + w) - g o) := by
  unfold avg
  have h1 : ∑ t ∈ range (w + 1), g (o + t) = ∑ t ∈ range w, g (o + t) + g (o + w) := sum_range_succ _ _
  have h2 : ∑ t ∈ range (w + 1), g (o + t) = ∑ t ∈ range w, g (o + (t + 1)) + g (o + 0) := sum_range_succ' _ _
  have h3 : ∑ t ∈ range w, g (o + 1 + t) = ∑ t ∈ range w, g (o + (t + 1)) := by
    apply sum_congr rfl; intro t _; congr 1; ring
  rw [h3]
  have : ∑ t ∈ range w, g (o + (t + 1)) = ∑ t ∈ range w, g (o + t) + g (o + w) - g o := by
    simp only [add_zero] at h2; linarith
  rw [this]; ring

theorem avg_nonneg (w : ℕ) {g : ℕ → ℝ} (hg : ∀ o, 0 ≤ g o) (o : ℕ) : 0 ≤ avg w g o := by
  unfold avg
  apply mul_nonneg (by positivity)
  exact sum_nonneg (fun t _ => hg _)

theorem avg_le_one {w : ℕ} (hw : 1 ≤ w) {g : ℕ → ℝ} (hg : ∀ o, g o ≤ 1) (o : ℕ) : avg w g o ≤ 1 := by
  unfold avg
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have : ∑ t ∈ range w, g (o + t) ≤ ∑ _t ∈ range w, (1 : ℝ) := sum_le_sum (fun t _ => hg _)
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at this
  rw [div_mul_eq_mul_div, one_mul, div_le_one hw']
  exact this

theorem prof_nonneg (a b w o : ℕ) : 0 ≤ prof a b w o :=
  avg_nonneg w (fun o => avg_nonneg w (fun o => chi0_nonneg a b o) o) o

theorem prof_le_one {a b w : ℕ} (hw : 1 ≤ w) (o : ℕ) : prof a b w o ≤ 1 :=
  avg_le_one hw (fun o => avg_le_one hw (fun o => chi0_le_one a b o) o) o

theorem prof_first {a b w : ℕ} (hw : 1 ≤ w) (o : ℕ) :
    |prof a b w (o + 1) - prof a b w o| ≤ 1 / (w : ℝ) := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  unfold prof
  rw [avg_step]
  have h0 := avg_nonneg w (fun o => chi0_nonneg a b o) (o + w)
  have h1 := avg_le_one hw (fun o => chi0_le_one a b o) (o + w)
  have h2 := avg_nonneg w (fun o => chi0_nonneg a b o) o
  have h3 := avg_le_one hw (fun o => chi0_le_one a b o) o
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (w : ℝ))]
  have : |avg w (chi0 a b) (o + w) - avg w (chi0 a b) o| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  calc 1 / (w : ℝ) * |avg w (chi0 a b) (o + w) - avg w (chi0 a b) o| ≤ 1 / (w : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 1 / (w : ℝ) := by ring

theorem prof_second {a b w : ℕ} (hw : 1 ≤ w) (o : ℕ) :
    |prof a b w (o + 2) + prof a b w o - 2 * prof a b w (o + 1)| ≤ 2 / (w : ℝ) ^ 2 := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have e1 : prof a b w (o + 2) - prof a b w (o + 1) = (1 / (w : ℝ)) * (avg w (chi0 a b) (o + 1 + w) - avg w (chi0 a b) (o + 1)) := by
    unfold prof; rw [show o + 2 = (o + 1) + 1 by ring, avg_step]
  have e2 : prof a b w (o + 1) - prof a b w o = (1 / (w : ℝ)) * (avg w (chi0 a b) (o + w) - avg w (chi0 a b) o) := by
    unfold prof; rw [avg_step]
  have s1 : avg w (chi0 a b) (o + 1 + w) - avg w (chi0 a b) (o + w)
      = (1 / (w : ℝ)) * (chi0 a b (o + w + w) - chi0 a b (o + w)) := by
    rw [show o + 1 + w = (o + w) + 1 by ring, avg_step]
  have s2 : avg w (chi0 a b) (o + 1) - avg w (chi0 a b) o = (1 / (w : ℝ)) * (chi0 a b (o + w) - chi0 a b o) := avg_step _ _ _
  have key : prof a b w (o + 2) + prof a b w o - 2 * prof a b w (o + 1)
      = (1 / (w : ℝ)) * ((1 / (w : ℝ)) * (chi0 a b (o + w + w) - chi0 a b (o + w))
          - (1 / (w : ℝ)) * (chi0 a b (o + w) - chi0 a b o)) := by
    have : prof a b w (o + 2) + prof a b w o - 2 * prof a b w (o + 1)
        = (prof a b w (o + 2) - prof a b w (o + 1)) - (prof a b w (o + 1) - prof a b w o) := by ring
    rw [this, e1, e2, ← mul_sub]
    congr 1
    rw [← s1, ← s2]; ring
  rw [key]
  have c1 := chi0_nonneg a b (o + w + w); have c2 := chi0_le_one a b (o + w + w)
  have c3 := chi0_nonneg a b (o + w); have c4 := chi0_le_one a b (o + w)
  have c5 := chi0_nonneg a b o; have c6 := chi0_le_one a b o
  have hi : (0 : ℝ) < 1 / (w : ℝ) := by positivity
  have bound : |(1 / (w : ℝ)) * (chi0 a b (o + w + w) - chi0 a b (o + w))
          - (1 / (w : ℝ)) * (chi0 a b (o + w) - chi0 a b o)| ≤ 2 / (w : ℝ) := by
    have e : (1 / (w : ℝ)) * (chi0 a b (o + w + w) - chi0 a b (o + w))
          - (1 / (w : ℝ)) * (chi0 a b (o + w) - chi0 a b o)
        = (1 / (w : ℝ)) * ((chi0 a b (o + w + w) - chi0 a b (o + w)) - (chi0 a b (o + w) - chi0 a b o)) := by ring
    rw [e, abs_mul, abs_of_pos hi]
    have : |(chi0 a b (o + w + w) - chi0 a b (o + w)) - (chi0 a b (o + w) - chi0 a b o)| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    calc 1 / (w : ℝ) * |(chi0 a b (o + w + w) - chi0 a b (o + w)) - (chi0 a b (o + w) - chi0 a b o)|
        ≤ 1 / (w : ℝ) * 2 := mul_le_mul_of_nonneg_left this hi.le
      _ = 2 / (w : ℝ) := by ring
  rw [abs_mul, abs_of_pos hi]
  calc 1 / (w : ℝ) * |(1 / (w : ℝ)) * (chi0 a b (o + w + w) - chi0 a b (o + w))
          - (1 / (w : ℝ)) * (chi0 a b (o + w) - chi0 a b o)| ≤ 1 / (w : ℝ) * (2 / (w : ℝ)) :=
        mul_le_mul_of_nonneg_left bound hi.le
    _ = 2 / (w : ℝ) ^ 2 := by field_simp

theorem avg_ne_zero {w : ℕ} {g : ℕ → ℝ} {o : ℕ} (h : avg w g o ≠ 0) : ∃ t < w, g (o + t) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold avg
  rw [sum_eq_zero (fun t ht => hn t (mem_range.mp ht)), mul_zero]

theorem prof_support {a b w o : ℕ} (h : prof a b w o ≠ 0) : o < b ∧ a + 2 ≤ o + 2 * w := by
  unfold prof at h
  obtain ⟨t, ht, h1⟩ := avg_ne_zero h
  obtain ⟨t', ht', h2⟩ := avg_ne_zero h1
  unfold chi0 at h2
  by_cases hc : a ≤ o + t + t' ∧ o + t + t' < b
  · constructor <;> omega
  · exact absurd (by simp [hc]) h2

theorem avg_eq_one {w : ℕ} (hw : 1 ≤ w) {g : ℕ → ℝ} {o : ℕ} (h : ∀ t < w, g (o + t) = 1) : avg w g o = 1 := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  unfold avg
  rw [sum_congr rfl (fun t ht => h t (mem_range.mp ht))]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  field_simp

theorem prof_one {a b w o : ℕ} (hw : 1 ≤ w) (hao : a ≤ o) (hob : o + 2 * w ≤ b + 1) : prof a b w o = 1 := by
  unfold prof
  apply avg_eq_one hw
  intro t ht
  apply avg_eq_one hw
  intro t' ht'
  unfold chi0
  rw [if_pos]
  constructor <;> omega

end AdalyFormal.M2Bridge

#print axioms AdalyFormal.M2Bridge.avg_step
#print axioms AdalyFormal.M2Bridge.prof_first
#print axioms AdalyFormal.M2Bridge.prof_second
#print axioms AdalyFormal.M2Bridge.prof_support
#print axioms AdalyFormal.M2Bridge.prof_one
