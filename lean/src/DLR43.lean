import MF5b

/-!
# DL43 -- the SMOOTH 1D profiles of the bond right inverse, and the profile-generic cyclic identities

`tprof n t = 12(n−t)(t+1)(5t+4−2n)/((n+1)(n+2)(n+3))` (longitudinal, `t < n`; `0` beyond):
  `Σ_{s<n}(s+1)τ(s) = n²`, `Σ_{s<n}(n−1−s)τ(s) = 0` (the two moments of MF5a's `gprof`: biorthogonal to the `n`-line average),
  `|τ| ≤ 9`, `|τ(t+1)−τ(t)| ≤ 72/n` (`t+1 < n`), `|τ(0)|, |τ(n−1)| ≤ 72/n` — CONTINUOUS at the scale `1/n` across block faces.
`pprof n t = 6(t+1)(n−t)/((n+1)(n+2))` (transverse): `Σ_{s<n} φ(s) = n`, `|φ| ≤ 3/2`, differences and end values `≤ 6/n`.
`SProf n f F D` packages: support in `[0,n)`, `|f| ≤ F`, differences/ends `≤ D/n`.
`core_line_g`, `core_ind_g` : MF5b's cyclic identities for an arbitrary profile with the right moments.
`cyc_step_le` : on a cycle of length `N ≥ n`, `|f((t+1) mod N) − f(t)| ≤ 2D/n`, and it vanishes unless `t < n ∨ t = N−1`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

open Finset
open AdalyFormal.M0Finish (pair_own pair_next cases_of_dvd sum_range_id_real sum_range_sq_real)

theorem sum_range_cube_real (n : ℕ) : ∑ s ∈ range n, (s : ℝ) ^ 3 = ((n : ℝ) * ((n : ℝ) - 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

theorem sum_range_four_real (n : ℕ) :
    ∑ s ∈ range n, (s : ℝ) ^ 4
      = (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * (3 * (n : ℝ) ^ 2 - 3 * (n : ℝ) - 1) / 30 := by
  induction n with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

/-! ## the profiles -/

/-- the longitudinal profile -/
noncomputable def tprof (n t : ℕ) : ℝ :=
  if t < n then 12 * ((n : ℝ) - t) * ((t : ℝ) + 1) * (5 * (t : ℝ) + 4 - 2 * n)
    / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) else 0

/-- the transverse profile -/
noncomputable def pprof (n t : ℕ) : ℝ :=
  if t < n then 6 * ((t : ℝ) + 1) * ((n : ℝ) - t) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) else 0

theorem tprof_eq_zero (n t : ℕ) (h : n ≤ t) : tprof n t = 0 := by unfold tprof; rw [if_neg (by omega)]
theorem pprof_eq_zero (n t : ℕ) (h : n ≤ t) : pprof n t = 0 := by unfold pprof; rw [if_neg (by omega)]

theorem tprof_moment_own (n : ℕ) : ∑ s ∈ range n, ((s : ℝ) + 1) * tprof n s = (n : ℝ) ^ 2 := by
  have hD : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by positivity
  have h : ∀ s ∈ range n, ((s : ℝ) + 1) * tprof n s
      = (12 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) * (-5) * (s : ℝ) ^ 4
        + (12 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) * (7 * ((n : ℝ) - 2)) * (s : ℝ) ^ 3
        + (12 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) * (-2 * (n : ℝ) ^ 2 + 18 * n - 13) * (s : ℝ) ^ 2
        + (12 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) * (-4 * (n : ℝ) ^ 2 + 15 * n - 4) * (s : ℝ)
        + (12 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) * (-2 * (n : ℝ) * ((n : ℝ) - 2)) := by
    intro s hs
    rw [tprof, if_pos (mem_range.mp hs)]
    field_simp; ring
  rw [sum_congr rfl h]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  rw [sum_range_four_real, sum_range_cube_real, sum_range_sq_real, sum_range_id_real]
  field_simp; ring

theorem tprof_moment_next (n : ℕ) : ∑ s ∈ range n, ((n : ℝ) - 1 - (s : ℝ)) * tprof n s = 0 := by
  have hD : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by positivity
  have h : ∀ s ∈ range n, ((n : ℝ) - 1 - (s : ℝ)) * tprof n s
      = (12 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) * 5 * (s : ℝ) ^ 4
        + (12 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) * (-2 * (6 * (n : ℝ) - 7)) * (s : ℝ) ^ 3
        + (12 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) * (9 * (n : ℝ) ^ 2 - 27 * n + 13) * (s : ℝ) ^ 2
        + (12 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)))
            * (-2 * (n : ℝ) ^ 3 + 15 * (n : ℝ) ^ 2 - 19 * n + 4) * (s : ℝ)
        + (12 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) * (-2 * (n : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 1)) := by
    intro s hs
    rw [tprof, if_pos (mem_range.mp hs)]
    field_simp; ring
  rw [sum_congr rfl h]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  rw [sum_range_four_real, sum_range_cube_real, sum_range_sq_real, sum_range_id_real]
  field_simp; ring

theorem pprof_sum (n : ℕ) : ∑ s ∈ range n, pprof n s = (n : ℝ) := by
  have hD : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  have h : ∀ s ∈ range n, pprof n s
      = (6 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) * (-1) * (s : ℝ) ^ 2
        + (6 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) * ((n : ℝ) - 1) * (s : ℝ)
        + (6 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) * (n : ℝ) := by
    intro s hs
    rw [pprof, if_pos (mem_range.mp hs)]
    field_simp; ring
  rw [sum_congr rfl h]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  rw [sum_range_sq_real, sum_range_id_real]
  field_simp; ring

/-! ## bounds -/

theorem abs_tprof_le (n t : ℕ) : |tprof n t| ≤ 9 := by
  unfold tprof
  split_ifs with h
  · have hD : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by positivity
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    have ht : (t : ℝ) + 1 ≤ n := by exact_mod_cast h
    have ht0 : (0 : ℝ) ≤ t := by positivity
    set A : ℝ := (n : ℝ) - t
    set B : ℝ := (t : ℝ) + 1
    set C : ℝ := 5 * (t : ℝ) + 4 - 2 * n
    have hA : 1 ≤ A := by simp only [A]; linarith
    have hB : 1 ≤ B := by simp only [B]; linarith
    have hAB : A + B = (n : ℝ) + 1 := by simp only [A, B]; ring
    have hab0 : 0 ≤ A * B := by positivity
    have hab : A * B ≤ ((n : ℝ) + 1) ^ 2 / 4 := by nlinarith [sq_nonneg (A - B)]
    have hC : |C| ≤ 3 * n := by
      rw [abs_le]; simp only [C]; constructor <;> linarith
    have hn0 : (0 : ℝ) ≤ n := by positivity
    rw [show 12 * A * B * C = 12 * (A * B) * C by ring, abs_mul, abs_mul, abs_of_nonneg hab0, abs_of_pos (by norm_num : (0:ℝ) < 12)]
    calc 12 * (A * B) * |C| ≤ 12 * (((n : ℝ) + 1) ^ 2 / 4) * (3 * n) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hab (by norm_num)) hC (abs_nonneg _) (by positivity)
      _ ≤ 9 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by nlinarith
  · simp

theorem abs_pprof_le (n t : ℕ) : |pprof n t| ≤ 3 / 2 := by
  unfold pprof
  split_ifs with h
  · have hD : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    have ht : (t : ℝ) + 1 ≤ n := by exact_mod_cast h
    have ht0 : (0 : ℝ) ≤ t := by positivity
    have h1 : 0 ≤ 6 * ((t : ℝ) + 1) * ((n : ℝ) - t) := by
      have : 0 ≤ (n : ℝ) - t := by linarith
      positivity
    rw [abs_of_nonneg h1]
    nlinarith [sq_nonneg ((t : ℝ) + 1 - ((n : ℝ) - t))]
  · simp; norm_num

theorem tprof_step (n t : ℕ) (h : t + 1 < n) :
    tprof n (t + 1) - tprof n t
      = -12 * (2 * (n : ℝ) ^ 2 - 14 * n * t - 18 * n + 15 * (t : ℝ) ^ 2 + 33 * t + 18)
          / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  unfold tprof
  rw [if_pos h, if_pos (by omega)]
  have hD : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by positivity
  push_cast
  field_simp
  ring

theorem tprof_step_le (n t : ℕ) (h : t + 1 < n) : |tprof n (t + 1) - tprof n t| ≤ 72 / n := by
  rw [tprof_step n t h]
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by positivity
  have ht : (t : ℝ) + 2 ≤ n := by exact_mod_cast (show t + 2 ≤ n by omega)
  have ht0 : (0 : ℝ) ≤ t := by positivity
  set p : ℝ := 2 * (n : ℝ) ^ 2 - 14 * n * t - 18 * n + 15 * (t : ℝ) ^ 2 + 33 * t + 18 with hp
  have hp1 : p ≤ 6 * ((n : ℝ) + 1) * ((n : ℝ) + 3) := by
    rw [hp]; nlinarith
  have hp2 : -(6 * ((n : ℝ) + 1) * ((n : ℝ) + 3)) ≤ p := by
    rw [hp]; nlinarith [sq_nonneg (30 * (t : ℝ) + 33 - 14 * n)]
  rw [abs_div, abs_of_pos hD, abs_mul, abs_of_neg (by norm_num : (-12 : ℝ) < 0), div_le_div_iff₀ hD hn]
  have hpa : |p| ≤ 6 * ((n : ℝ) + 1) * ((n : ℝ) + 3) := abs_le.mpr ⟨hp2, hp1⟩
  calc -(-12 : ℝ) * |p| * n ≤ 12 * (6 * ((n : ℝ) + 1) * ((n : ℝ) + 3)) * n := by
        have : -(-12 : ℝ) = 12 := by norm_num
        rw [this]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpa (by norm_num)) hn.le
    _ ≤ 72 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by nlinarith

theorem tprof_first_le (n : ℕ) (hn : 0 < n) : |tprof n 0| ≤ 72 / n := by
  unfold tprof
  rw [if_pos hn]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by positivity
  rw [abs_div, abs_of_pos hD, div_le_div_iff₀ hD hnr]
  push_cast
  have e : 12 * ((n : ℝ) - 0) * (0 + 1) * (5 * 0 + 4 - 2 * n) = 24 * n * (2 - n) := by ring
  rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 24 * n)]
  have h2 : |2 - (n : ℝ)| ≤ n + 2 := by rw [abs_le]; constructor <;> linarith
  calc 24 * (n : ℝ) * |2 - (n : ℝ)| * n ≤ 24 * n * (n + 2) * n := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) hnr.le
    _ ≤ 72 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by nlinarith

theorem tprof_last_le (n : ℕ) (hn : 0 < n) : |tprof n (n - 1)| ≤ 72 / n := by
  unfold tprof
  rw [if_pos (by omega)]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by positivity
  rw [abs_div, abs_of_pos hD, div_le_div_iff₀ hD hnr]
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hc]
  have e : 12 * ((n : ℝ) - ((n : ℝ) - 1)) * ((n : ℝ) - 1 + 1) * (5 * ((n : ℝ) - 1) + 4 - 2 * n) = 12 * n * (3 * n - 1) := by
    ring
  rw [e]
  have h1 : 0 ≤ 12 * (n : ℝ) * (3 * n - 1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : 0 ≤ 3 * (n : ℝ) - 1 := by linarith
    positivity
  rw [abs_of_nonneg h1]
  nlinarith

theorem pprof_step (n t : ℕ) (h : t + 1 < n) :
    pprof n (t + 1) - pprof n t = 6 * ((n : ℝ) - 2 * t - 2) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  unfold pprof
  rw [if_pos h, if_pos (by omega)]
  have hD : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  push_cast
  field_simp
  ring

theorem pprof_step_le (n t : ℕ) (h : t + 1 < n) : |pprof n (t + 1) - pprof n t| ≤ 6 / n := by
  rw [pprof_step n t h]
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  have ht : (t : ℝ) + 2 ≤ n := by exact_mod_cast (show t + 2 ≤ n by omega)
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hq : |(n : ℝ) - 2 * t - 2| ≤ n := by rw [abs_le]; constructor <;> linarith
  rw [abs_div, abs_of_pos hD, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6), div_le_div_iff₀ hD hn]
  calc 6 * |(n : ℝ) - 2 * t - 2| * n ≤ 6 * n * n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num)) hn.le
    _ ≤ 6 * (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by nlinarith

theorem pprof_first_le (n : ℕ) (hn : 0 < n) : |pprof n 0| ≤ 6 / n := by
  unfold pprof
  rw [if_pos hn]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  rw [abs_div, abs_of_pos hD, div_le_div_iff₀ hD hnr]
  push_cast
  rw [show 6 * ((0 : ℝ) + 1) * ((n : ℝ) - 0) = 6 * n by ring, abs_of_nonneg (by positivity)]
  nlinarith

theorem pprof_last_le (n : ℕ) (hn : 0 < n) : |pprof n (n - 1)| ≤ 6 / n := by
  unfold pprof
  rw [if_pos (by omega)]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  rw [abs_div, abs_of_pos hD, div_le_div_iff₀ hD hnr]
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hc, show 6 * ((n : ℝ) - 1 + 1) * ((n : ℝ) - ((n : ℝ) - 1)) = 6 * n by ring, abs_of_nonneg (by positivity)]
  nlinarith

/-! ## the smooth-profile package -/

/-- a profile supported in `[0,n)`, bounded by `F`, with steps and end values `≤ D/n` -/
structure SProf (n : ℕ) (f : ℕ → ℝ) (F D : ℝ) : Prop where
  pos : 0 < n
  zero : ∀ t, n ≤ t → f t = 0
  bnd : ∀ t, |f t| ≤ F
  step : ∀ t, t + 1 < n → |f (t + 1) - f t| ≤ D / n
  first : |f 0| ≤ D / n
  last : |f (n - 1)| ≤ D / n

theorem sprof_tprof (n : ℕ) (hn : 0 < n) : SProf n (tprof n) 9 72 :=
  ⟨hn, tprof_eq_zero n, abs_tprof_le n, tprof_step_le n, tprof_first_le n hn, tprof_last_le n hn⟩

theorem sprof_pprof (n : ℕ) (hn : 0 < n) : SProf n (pprof n) (3 / 2) 6 :=
  ⟨hn, pprof_eq_zero n, abs_pprof_le n, pprof_step_le n, pprof_first_le n hn, pprof_last_le n hn⟩

theorem SProf.F_nonneg {n : ℕ} {f : ℕ → ℝ} {F D : ℝ} (h : SProf n f F D) : 0 ≤ F :=
  le_trans (abs_nonneg _) (h.bnd 0)

theorem SProf.D_nonneg {n : ℕ} {f : ℕ → ℝ} {F D : ℝ} (h : SProf n f F D) : 0 ≤ D := by
  have h1 := le_trans (abs_nonneg _) h.first
  have hn : (0 : ℝ) < n := by exact_mod_cast h.pos
  rwa [le_div_iff₀ hn, zero_mul] at h1

/-- **the cyclic step**: on a cycle of length `N ≥ n`, `|f((t+1) mod N) − f(t)| ≤ 2D/n` for every `t < N`, and the step vanishes
unless `t < n` or `t = N − 1`. -/
theorem cyc_step_le {n : ℕ} {f : ℕ → ℝ} {F D : ℝ} (h : SProf n f F D) (N t : ℕ) (hnN : n ≤ N) (ht : t < N) :
    |f ((t + 1) % N) - f t| ≤ (if t < n ∨ t = N - 1 then 2 * D / n else 0) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast h.pos
  have hD := h.D_nonneg
  have hDn : 0 ≤ D / n := by positivity
  by_cases h1 : t + 1 < N
  · rw [Nat.mod_eq_of_lt h1]
    by_cases h2 : t + 1 < n
    · rw [if_pos (Or.inl (by omega))]
      have := h.step t h2
      have e : 2 * D / n = D / n + D / n := by ring
      rw [e]; linarith
    · by_cases h3 : t + 1 = n
      · rw [if_pos (Or.inl (by omega)), h.zero (t + 1) (by omega), zero_sub, abs_neg]
        have e : t = n - 1 := by omega
        rw [e]
        have := h.last
        have e2 : 2 * D / n = D / n + D / n := by ring
        rw [e2]; linarith
      · rw [h.zero (t + 1) (by omega), h.zero t (by omega), sub_zero, abs_zero]
        split_ifs <;> positivity
  · have htN : t = N - 1 := by omega
    have e0 : (t + 1) % N = 0 := by rw [show t + 1 = N by omega, Nat.mod_self]
    rw [e0, if_pos (Or.inr htN)]
    by_cases h4 : t < n
    · -- N = n: f 0 − f(n−1)
      have e : t = n - 1 := by omega
      rw [e]
      have h5 := h.first
      have h6 := h.last
      calc |f 0 - f (n - 1)| ≤ |f 0| + |f (n - 1)| := abs_sub _ _
        _ ≤ D / n + D / n := add_le_add h5 h6
        _ = 2 * D / n := by ring
    · rw [h.zero t (by omega), sub_zero]
      have := h.first
      have e2 : 2 * D / n = D / n + D / n := by ring
      rw [e2]; linarith

/-! ## the profile-generic cyclic identities (MF5b with an arbitrary profile) -/

theorem point_cases_g (g : ℕ → ℝ) (N n D r i : ℕ) (hz : ∀ t, n ≤ t → g t = 0) (hr : r < n) (hi : i < n)
    (hcase : (D = 0 ∧ N = n) ∨ (D = 0 ∧ 2 * n ≤ N) ∨ (0 < D ∧ D + n = N ∧ 2 * n ≤ N) ∨ (n ≤ D ∧ D + 2 * n ≤ N)) :
    g ((D + r + i) % N)
      = (if D = 0 then (if r + i < n then g (r + i) else 0) else 0)
        + (if (D + n) % N = 0 then (if n ≤ r + i then g (r + i - n) else 0) else 0) := by
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · subst h1; subst h2
    have eA : (0 + N) % N = 0 := by rw [Nat.zero_add, Nat.mod_self]
    rw [eA]
    by_cases h : r + i < N
    · have eB : (0 + r + i) % N = r + i := by rw [Nat.zero_add, Nat.mod_eq_of_lt h]
      rw [eB, if_pos rfl, if_pos h, if_pos rfl, if_neg (by omega)]; ring
    · have eB : (0 + r + i) % N = r + i - N := by
        rw [Nat.zero_add, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [eB, if_pos rfl, if_neg h, if_pos rfl, if_pos (by omega)]; ring
  · subst h1
    have hn0 : 0 < n := by omega
    have eA : (0 + n) % N = n := by rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
    have eB : (0 + r + i) % N = r + i := by rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [eA, eB, if_pos rfl, if_neg (by omega : n ≠ 0)]
    by_cases h : r + i < n
    · rw [if_pos h]; ring
    · rw [if_neg h, hz (r + i) (by omega)]; ring
  · have eA : (D + n) % N = 0 := by rw [h2, Nat.mod_self]
    rw [eA, if_neg (by omega : D ≠ 0), if_pos rfl]
    by_cases h : n ≤ r + i
    · have eB : (D + r + i) % N = r + i - n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      rw [eB, if_pos h]; ring
    · have eB : (D + r + i) % N = D + r + i := Nat.mod_eq_of_lt (by omega)
      rw [eB, hz _ (by omega), if_neg h]; ring
  · have eA : (D + n) % N = D + n := Nat.mod_eq_of_lt (by omega)
    have eB : (D + r + i) % N = D + r + i := Nat.mod_eq_of_lt (by omega)
    rw [eA, eB, hz _ (by omega), if_neg (by omega : D ≠ 0), if_neg (by omega : D + n ≠ 0)]; ring

/-- the line average sees only its own block, for any profile with the two moments -/
theorem core_line_g (g : ℕ → ℝ) (N n D : ℕ) (hz : ∀ t, n ≤ t → g t = 0)
    (m1 : ∑ s ∈ range n, ((s : ℝ) + 1) * g s = (n : ℝ) ^ 2)
    (m2 : ∑ s ∈ range n, ((n : ℝ) - 1 - (s : ℝ)) * g s = 0)
    (hn : 0 < n) (hN : n ∣ N) (hD : n ∣ D) (hDN : D < N) :
    ∑ r ∈ range n, ∑ i ∈ range n, g ((D + r + i) % N) = if D = 0 then (n : ℝ) ^ 2 else 0 := by
  have hc := cases_of_dvd N n D hn hN hD hDN
  have hpt : ∀ r ∈ range n, ∀ i ∈ range n, g ((D + r + i) % N)
      = (if D = 0 then (if r + i < n then g (r + i) else 0) else 0)
        + (if (D + n) % N = 0 then (if n ≤ r + i then g (r + i - n) else 0) else 0) :=
    fun r hr i hi => point_cases_g g N n D r i hz (mem_range.mp hr) (mem_range.mp hi) hc
  rw [sum_congr rfl (fun r hr => sum_congr rfl (fun i hi => hpt r hr i hi))]
  simp only [sum_add_distrib]
  have hA : ∑ r ∈ range n, ∑ i ∈ range n, (if D = 0 then (if r + i < n then g (r + i) else 0) else 0)
      = if D = 0 then (n : ℝ) ^ 2 else 0 := by
    split_ifs with h
    · rw [pair_own g n, m1]
    · simp
  have hB : ∑ r ∈ range n, ∑ i ∈ range n,
      (if (D + n) % N = 0 then (if n ≤ r + i then g (r + i - n) else 0) else 0) = 0 := by
    split_ifs with h
    · rw [pair_next g n, m2]
    · simp
  rw [hA, hB, add_zero]

/-- the transverse block average, for any profile with mass `n` -/
theorem core_ind_g (g : ℕ → ℝ) (N n D : ℕ) (hz : ∀ t, n ≤ t → g t = 0)
    (m0 : ∑ s ∈ range n, g s = (n : ℝ))
    (hn : 0 < n) (hN : n ∣ N) (hD : n ∣ D) (hDN : D < N) :
    ∑ r ∈ range n, g ((D + r) % N) = if D = 0 then (n : ℝ) else 0 := by
  have hc := cases_of_dvd N n D hn hN hD hDN
  by_cases h0 : D = 0
  · subst h0
    rw [if_pos rfl]
    have hnN : n ≤ N := Nat.le_of_dvd (by omega) hN
    have : ∀ r ∈ range n, g ((0 + r) % N) = g r := by
      intro r hr
      have hr' := mem_range.mp hr
      rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [sum_congr rfl this, m0]
  · rw [if_neg h0]
    have : ∀ r ∈ range n, g ((D + r) % N) = 0 := by
      intro r hr
      have hr' := mem_range.mp hr
      rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
      · exact absurd h1 h0
      · exact absurd h1 h0
      · have hDn : n ≤ D := by
          obtain ⟨m, hm⟩ := hD
          rcases Nat.eq_zero_or_pos m with hm0 | hm0
          · subst hm0; simp at hm; omega
          · rw [hm]; exact Nat.le_mul_of_pos_right n hm0
        rw [Nat.mod_eq_of_lt (by omega), hz _ (by omega)]
      · rw [Nat.mod_eq_of_lt (by omega), hz _ (by omega)]
    rw [sum_congr rfl this]; simp

#print axioms sum_range_cube_real
#print axioms sum_range_four_real
#print axioms tprof_moment_own
#print axioms tprof_moment_next
#print axioms pprof_sum
#print axioms abs_tprof_le
#print axioms abs_pprof_le
#print axioms tprof_step_le
#print axioms tprof_first_le
#print axioms tprof_last_le
#print axioms pprof_step_le
#print axioms pprof_first_le
#print axioms pprof_last_le
#print axioms sprof_tprof
#print axioms sprof_pprof
#print axioms cyc_step_le
#print axioms point_cases_g
#print axioms core_line_g
#print axioms core_ind_g

end AdalyFormal.DLayer
