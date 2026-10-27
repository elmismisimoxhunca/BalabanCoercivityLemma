import MF5a

/-!
# MF5b -- the cyclic 1D identities of the flat BOND right inverse (Mathlib only).

On a cycle of length `N` with `n ∣ N`, for a cyclic offset `D` with `n ∣ D`, `D < N`:
* `core_line`  : `Σ_{r<n} Σ_{i<n} gprof n ((D+r+i) % N) = if D = 0 then n² else 0`   (the `n`-line average sees only its own block),
* `core_ind`   : `Σ_{r<n} [ (D+r) % N < n ] = if D = 0 then n else 0`                (transverse block indicator).
-/
set_option autoImplicit false

namespace AdalyFormal.M0Finish

open Finset

theorem point_cases (N n D r i : ℕ) (hr : r < n) (hi : i < n)
    (hcase : (D = 0 ∧ N = n) ∨ (D = 0 ∧ 2 * n ≤ N) ∨ (0 < D ∧ D + n = N ∧ 2 * n ≤ N) ∨ (n ≤ D ∧ D + 2 * n ≤ N)) :
    gprof n ((D + r + i) % N)
      = (if D = 0 then (if r + i < n then gprof n (r + i) else 0) else 0)
        + (if (D + n) % N = 0 then (if n ≤ r + i then gprof n (r + i - n) else 0) else 0) := by
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
    · rw [if_neg h, gprof_eq_zero n (r + i) (by omega)]; ring
  · have eA : (D + n) % N = 0 := by rw [h2, Nat.mod_self]
    rw [eA, if_neg (by omega : D ≠ 0), if_pos rfl]
    by_cases h : n ≤ r + i
    · have eB : (D + r + i) % N = r + i - n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      rw [eB, if_pos h]; ring
    · have eB : (D + r + i) % N = D + r + i := Nat.mod_eq_of_lt (by omega)
      rw [eB, gprof_eq_zero n _ (by omega), if_neg h]; ring
  · have eA : (D + n) % N = D + n := Nat.mod_eq_of_lt (by omega)
    have eB : (D + r + i) % N = D + r + i := Nat.mod_eq_of_lt (by omega)
    rw [eA, eB, gprof_eq_zero n _ (by omega), if_neg (by omega : D ≠ 0), if_neg (by omega : D + n ≠ 0)]; ring

theorem cases_of_dvd (N n D : ℕ) (hn : 0 < n) (hN : n ∣ N) (hD : n ∣ D) (hDN : D < N) :
    (D = 0 ∧ N = n) ∨ (D = 0 ∧ 2 * n ≤ N) ∨ (0 < D ∧ D + n = N ∧ 2 * n ≤ N) ∨ (n ≤ D ∧ D + 2 * n ≤ N) := by
  obtain ⟨Nu, rfl⟩ := hN
  obtain ⟨m, rfl⟩ := hD
  have hm : m < Nu := by
    by_contra h; push_neg at h
    have := Nat.mul_le_mul_left n h; omega
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    rcases Nat.lt_or_ge Nu 2 with h2 | h2
    · left; refine ⟨by simp, ?_⟩
      have : Nu = 1 := by omega
      subst this; simp
    · right; left; refine ⟨by simp, ?_⟩
      have := Nat.mul_le_mul_left n h2; linarith
  · right; right
    have hn1 : n ≤ n * m := by have := Nat.mul_le_mul_left n h0; linarith
    rcases Nat.lt_or_ge (m + 1) Nu with h3 | h3
    · right
      have := Nat.mul_le_mul_left n (show m + 2 ≤ Nu by omega)
      refine ⟨hn1, ?_⟩
      have e : n * (m + 2) = n * m + 2 * n := by ring
      linarith
    · left
      have hNu : Nu = m + 1 := by omega
      subst hNu
      refine ⟨by positivity, by ring, ?_⟩
      have := Nat.mul_le_mul_left n (show 2 ≤ m + 1 by omega); linarith

/-- **the line average sees only its own block** (cyclic, every `N` with `n ∣ N`). -/
theorem core_line (N n D : ℕ) (hn : 0 < n) (hN : n ∣ N) (hD : n ∣ D) (hDN : D < N) :
    ∑ r ∈ range n, ∑ i ∈ range n, gprof n ((D + r + i) % N) = if D = 0 then (n : ℝ) ^ 2 else 0 := by
  have hc := cases_of_dvd N n D hn hN hD hDN
  have hpt : ∀ r ∈ range n, ∀ i ∈ range n, gprof n ((D + r + i) % N)
      = (if D = 0 then (if r + i < n then gprof n (r + i) else 0) else 0)
        + (if (D + n) % N = 0 then (if n ≤ r + i then gprof n (r + i - n) else 0) else 0) :=
    fun r hr i hi => point_cases N n D r i (mem_range.mp hr) (mem_range.mp hi) hc
  rw [sum_congr rfl (fun r hr => sum_congr rfl (fun i hi => hpt r hr i hi))]
  simp only [sum_add_distrib]
  have hA : ∑ r ∈ range n, ∑ i ∈ range n, (if D = 0 then (if r + i < n then gprof n (r + i) else 0) else 0)
      = if D = 0 then (n : ℝ) ^ 2 else 0 := by
    split_ifs with h
    · rw [pair_own (gprof n) n, gprof_moment_own]
    · simp
  have hB : ∑ r ∈ range n, ∑ i ∈ range n,
      (if (D + n) % N = 0 then (if n ≤ r + i then gprof n (r + i - n) else 0) else 0) = 0 := by
    split_ifs with h
    · rw [pair_next (gprof n) n, gprof_moment_next]
    · simp
  rw [hA, hB, add_zero]

/-- **transverse block indicator** -/
theorem core_ind (N n D : ℕ) (hn : 0 < n) (hN : n ∣ N) (hD : n ∣ D) (hDN : D < N) :
    ∑ r ∈ range n, (if (D + r) % N < n then (1 : ℝ) else 0) = if D = 0 then (n : ℝ) else 0 := by
  have hc := cases_of_dvd N n D hn hN hD hDN
  by_cases h0 : D = 0
  · subst h0
    rw [if_pos rfl]
    have : ∀ r ∈ range n, (if (0 + r) % N < n then (1 : ℝ) else 0) = 1 := by
      intro r hr
      have hr' := mem_range.mp hr
      have hnN : n ≤ N := Nat.le_of_dvd (by omega) hN
      rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega), if_pos hr']
    rw [sum_congr rfl this]; simp
  · rw [if_neg h0]
    have : ∀ r ∈ range n, (if (D + r) % N < n then (1 : ℝ) else 0) = 0 := by
      intro r hr
      have hr' := mem_range.mp hr
      rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2, h3⟩ | ⟨h1, h2⟩
      · exact absurd h1 h0
      · exact absurd h1 h0
      · rw [Nat.mod_eq_of_lt (by omega), if_neg (by omega)]
      · rw [Nat.mod_eq_of_lt (by omega), if_neg (by omega)]
    rw [sum_congr rfl this]; simp

#print axioms point_cases
#print axioms cases_of_dvd
#print axioms core_line
#print axioms core_ind

end AdalyFormal.M0Finish
