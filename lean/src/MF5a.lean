import Mathlib

/-!
# MF5a -- the 1D linear profile of the flat BOND right inverse (Mathlib only).

`gprof n t = (4 − 2n + 6t)/(n+1)` for `t < n`, `0` otherwise. Its two moments:
  `Σ_{s<n} (s+1) g(s) = n²`   (own block, weights of the `n`-line average),
  `Σ_{s<n} (n−1−s) g(s) = 0`  (the next block, read by the previous row),
and the two pair-sum identities that turn the line average `Σ_{r<n} Σ_{i<n}` into these moments.
`|g| ≤ 4`.
-/
set_option autoImplicit false

namespace AdalyFormal.M0Finish

open Finset

noncomputable def gprof (n t : ℕ) : ℝ := if t < n then (4 - 2 * (n : ℝ) + 6 * (t : ℝ)) / ((n : ℝ) + 1) else 0

theorem sum_range_id_real (n : ℕ) : ∑ s ∈ range n, (s : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

theorem sum_range_sq_real (n : ℕ) :
    ∑ s ∈ range n, (s : ℝ) ^ 2 = (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

theorem gprof_moment_own (n : ℕ) : ∑ s ∈ range n, ((s : ℝ) + 1) * gprof n s = (n : ℝ) ^ 2 := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h : ∀ s ∈ range n, ((s : ℝ) + 1) * gprof n s
      = (6 / ((n : ℝ) + 1)) * (s : ℝ) ^ 2 + ((10 - 2 * (n : ℝ)) / ((n : ℝ) + 1)) * (s : ℝ)
        + (4 - 2 * (n : ℝ)) / ((n : ℝ) + 1) := by
    intro s hs
    rw [gprof, if_pos (mem_range.mp hs)]
    field_simp; ring
  rw [sum_congr rfl h, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, card_range,
    sum_range_id_real, sum_range_sq_real, nsmul_eq_mul]
  field_simp; ring

theorem gprof_moment_next (n : ℕ) : ∑ s ∈ range n, ((n : ℝ) - 1 - (s : ℝ)) * gprof n s = 0 := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h : ∀ s ∈ range n, ((n : ℝ) - 1 - (s : ℝ)) * gprof n s
      = (-6 / ((n : ℝ) + 1)) * (s : ℝ) ^ 2 + ((8 * (n : ℝ) - 10) / ((n : ℝ) + 1)) * (s : ℝ)
        + ((n : ℝ) - 1) * (4 - 2 * (n : ℝ)) / ((n : ℝ) + 1) := by
    intro s hs
    rw [gprof, if_pos (mem_range.mp hs)]
    field_simp; ring
  rw [sum_congr rfl h, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, card_range,
    sum_range_id_real, sum_range_sq_real, nsmul_eq_mul]
  field_simp; ring

theorem abs_gprof_le (n t : ℕ) : |gprof n t| ≤ 4 := by
  unfold gprof
  split_ifs with h
  · have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [abs_div, abs_of_pos hn1, div_le_iff₀ hn1, abs_le]
    have ht : (t : ℝ) + 1 ≤ n := by exact_mod_cast h
    have ht0 : (0 : ℝ) ≤ t := by positivity
    constructor <;> nlinarith
  · simp

theorem gprof_eq_zero (n t : ℕ) (h : n ≤ t) : gprof n t = 0 := by
  unfold gprof; rw [if_neg (by omega)]

/-- `Σ_{i<n} Σ_{j<i+1} h j = Σ_{j<n} (n − j) h j` -/
theorem sum_tri_le (h : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range (i + 1), h j = ∑ j ∈ range n, ((n : ℝ) - (j : ℝ)) * h j := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, ih, sum_range_succ (fun j => (((m + 1 : ℕ) : ℝ) - (j : ℝ)) * h j)]
      have : ∑ j ∈ range m, (((m + 1 : ℕ) : ℝ) - (j : ℝ)) * h j
          = ∑ j ∈ range m, ((m : ℝ) - (j : ℝ)) * h j + ∑ j ∈ range m, h j := by
        rw [← sum_add_distrib]; refine sum_congr rfl (fun j _ => ?_); push_cast; ring
      rw [this, sum_range_succ]
      push_cast; ring

/-- `Σ_{i<n} Σ_{s<i} f s = Σ_{s<n} (n − 1 − s) f s` -/
theorem sum_tri_lt (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, ∑ s ∈ range i, f s = ∑ s ∈ range n, ((n : ℝ) - 1 - (s : ℝ)) * f s := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, ih, sum_range_succ (fun s => (((m + 1 : ℕ) : ℝ) - 1 - (s : ℝ)) * f s)]
      have : ∑ s ∈ range m, (((m + 1 : ℕ) : ℝ) - 1 - (s : ℝ)) * f s
          = ∑ s ∈ range m, ((m : ℝ) - 1 - (s : ℝ)) * f s + ∑ s ∈ range m, f s := by
        rw [← sum_add_distrib]; refine sum_congr rfl (fun s _ => ?_); push_cast; ring
      rw [this]
      push_cast; ring

/-- the line average over the OWN block: `Σ_{r<n} Σ_{i<n} [r+i<n] f(r+i) = Σ_{s<n} (s+1) f s` -/
theorem pair_own (f : ℕ → ℝ) (n : ℕ) :
    ∑ r ∈ range n, ∑ i ∈ range n, (if r + i < n then f (r + i) else 0)
      = ∑ s ∈ range n, ((s : ℝ) + 1) * f s := by
  -- reflect r ↦ n-1-r
  rw [← sum_range_reflect]
  have h1 : ∀ r ∈ range n, ∑ i ∈ range n, (if n - 1 - r + i < n then f (n - 1 - r + i) else 0)
      = ∑ j ∈ range (r + 1), f (n - 1 - j) := by
    intro r hr
    have hr' : r < n := mem_range.mp hr
    have e1 : ∑ i ∈ range n, (if n - 1 - r + i < n then f (n - 1 - r + i) else 0)
        = ∑ i ∈ range (r + 1), f (n - 1 - r + i) := by
      rw [← sum_filter]
      congr 1
      ext i; simp only [mem_filter, mem_range]; omega
    rw [e1, ← sum_range_reflect]
    refine sum_congr rfl (fun i hi => ?_)
    have := mem_range.mp hi
    congr 1; omega
  rw [sum_congr rfl h1, sum_tri_le (fun j => f (n - 1 - j)) n]
  rw [← sum_range_reflect]
  refine sum_congr rfl (fun s hs => ?_)
  have hs' := mem_range.mp hs
  have e2 : n - 1 - (n - 1 - s) = s := by omega
  rw [e2]
  have e3 : ((n - 1 - s : ℕ) : ℝ) = (n : ℝ) - 1 - (s : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [e3]; ring

/-- the line average over the NEXT block: `Σ_{r<n} Σ_{i<n} [n ≤ r+i] f(r+i−n) = Σ_{s<n} (n−1−s) f s` -/
theorem pair_next (f : ℕ → ℝ) (n : ℕ) :
    ∑ r ∈ range n, ∑ i ∈ range n, (if n ≤ r + i then f (r + i - n) else 0)
      = ∑ s ∈ range n, ((n : ℝ) - 1 - (s : ℝ)) * f s := by
  rw [← sum_range_reflect]
  have h1 : ∀ r ∈ range n, ∑ i ∈ range n, (if n ≤ n - 1 - r + i then f (n - 1 - r + i - n) else 0)
      = ∑ i ∈ range n, (if r < i then f (i - 1 - r) else 0) := by
    intro r hr
    have hr' : r < n := mem_range.mp hr
    refine sum_congr rfl (fun i hi => ?_)
    have hi' := mem_range.mp hi
    by_cases h : r < i
    · rw [if_pos (by omega), if_pos h]; congr 1; omega
    · rw [if_neg (by omega), if_neg h]
  rw [sum_congr rfl h1, sum_comm]
  have h2 : ∀ i ∈ range n, ∑ r ∈ range n, (if r < i then f (i - 1 - r) else 0) = ∑ s ∈ range i, f s := by
    intro i hi
    have hi' := mem_range.mp hi
    have e1 : ∑ r ∈ range n, (if r < i then f (i - 1 - r) else 0) = ∑ r ∈ range i, f (i - 1 - r) := by
      rw [← sum_filter]
      congr 1
      ext r; simp only [mem_filter, mem_range]; omega
    rw [e1]
    exact sum_range_reflect f i
  rw [sum_congr rfl h2, sum_tri_lt]

#print axioms gprof_moment_own
#print axioms gprof_moment_next
#print axioms abs_gprof_le
#print axioms gprof_eq_zero
#print axioms sum_tri_le
#print axioms sum_tri_lt
#print axioms pair_own
#print axioms pair_next

end AdalyFormal.M0Finish
