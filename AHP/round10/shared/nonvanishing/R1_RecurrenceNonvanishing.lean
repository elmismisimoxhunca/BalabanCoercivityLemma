import D1IVT

/-!
Cofinal nonvanishing for a reversible scalar recurrence.
The recurrence must concern the scalar coupling itself, not merely the collar mode.
-/
set_option autoImplicit false

namespace AdalyFormal.Round10.Nonvanishing

open Finset

/-- A reversible scalar recurrence cannot first become identically zero at a positive index. -/
theorem recurrence_zero_tail_step {K : Type*} [Field K]
    (d : ℕ) (c u : ℕ → K) (hc : c 0 ≠ 0)
    (hr : ∀ n, u (n + (d + 1)) = ∑ i ∈ range (d + 1), c i * u (n + i))
    (N : ℕ) (hz : ∀ n, N + 1 ≤ n → u n = 0) : u N = 0 := by
  have hs : (∑ i ∈ range (d + 1), c i * u (N + i)) = c 0 * u N := by
    rw [sum_eq_single 0]
    · simp
    · intro i _ hi
      rw [hz (N + i) (by omega), mul_zero]
    · simp
  have h := hr N
  rw [hz (N + (d + 1)) (by omega), hs] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hc

/-- Eventual zero is identically zero for a recurrence with nonzero oldest coefficient. -/
theorem recurrence_eq_zero_of_zero_tail {K : Type*} [Field K]
    (d : ℕ) (c u : ℕ → K) (hc : c 0 ≠ 0)
    (hr : ∀ n, u (n + (d + 1)) = ∑ i ∈ range (d + 1), c i * u (n + i))
    (N : ℕ) (hz : ∀ n, N ≤ n → u n = 0) : ∀ n, u n = 0 := by
  induction N with
  | zero => exact fun n => hz n (Nat.zero_le n)
  | succ N ih =>
      apply ih
      intro n hn
      by_cases h : N + 1 ≤ n
      · exact hz n h
      · have hn' : n = N := by omega
        subst n
        exact recurrence_zero_tail_step d c u hc hr N hz

/-- One nonzero value of a reversible recurrence gives unboundedly many nonzero values. -/
theorem recurrence_cofinal_nonzero {K : Type*} [Field K]
    (d : ℕ) (c u : ℕ → K) (hc : c 0 ≠ 0)
    (hr : ∀ n, u (n + (d + 1)) = ∑ i ∈ range (d + 1), c i * u (n + i))
    (k : ℕ) (hk : u k ≠ 0) : ∀ N, ∃ n, N ≤ n ∧ u n ≠ 0 := by
  intro N
  by_contra h
  push Not at h
  exact hk (recurrence_eq_zero_of_zero_tail d c u hc hr N h k)

/-- A dictionary may provide this record for the coupling restricted to even radii. -/
def RadiusRecurrenceData (coupling : ℕ → ℕ → ℝ) (q : ℕ) : Prop :=
  ∃ (d : ℕ) (c : ℕ → ℝ) (k : ℕ), c 0 ≠ 0 ∧
    (∀ n, coupling q (2 * (n + (d + 1) + 9)) =
      ∑ i ∈ range (d + 1), c i * coupling q (2 * (n + i + 9))) ∧
    coupling q (2 * (k + 9)) ≠ 0

/-- No uniform radius bound or prescribed sign is needed. -/
theorem radius_cofinal_nonzero (coupling : ℕ → ℕ → ℝ) (q : ℕ)
    (h : RadiusRecurrenceData coupling q) :
    ∀ R₀, ∃ R, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ coupling q R ≠ 0 := by
  obtain ⟨d, c, k, hc, hr, hk⟩ := h
  intro R₀
  obtain ⟨n, hn, hne⟩ := recurrence_cofinal_nonzero d c
    (fun n => coupling q (2 * (n + 9))) hc hr k hk R₀
  refine ⟨2 * (n + 9), ?_, dvd_mul_right 2 (n + 9), ?_, hne⟩ <;> omega

/-- Nested cofinality from the per-scale recurrence certificates. -/
theorem dyadic_cofinal_nonzero (coupling : ℕ → ℕ → ℝ)
    (h : ∀ j₀, ∃ j, j₀ ≤ j ∧ RadiusRecurrenceData coupling (2 ^ j)) :
    ∀ j₀, ∃ j, j₀ ≤ j ∧ ∀ R₀, ∃ R,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ coupling (2 ^ j) R ≠ 0 := by
  intro j₀
  obtain ⟨j, hj, hd⟩ := h j₀
  exact ⟨j, hj, radius_cofinal_nonzero coupling (2 ^ j) hd⟩

/-- The finite linear-recurrence package fits the same result. -/
theorem mathlib_recurrence_cofinal_nonzero {K : Type*} [Field K]
    (d : ℕ) (C : LinearRecurrence K)
    (hd : C.order = d + 1) (hc : C.coeffs ⟨0, by omega⟩ ≠ 0)
    (u : ℕ → K) (hu : C.IsSolution u) (k : ℕ) (hk : u k ≠ 0) :
    ∀ N, ∃ n, N ≤ n ∧ u n ≠ 0 := by
  rcases C with ⟨order, coeffs⟩
  change order = d + 1 at hd
  subst order
  let c : ℕ → K := fun i => if hi : i < d + 1 then coeffs ⟨i, hi⟩ else 0
  have hc' : c 0 ≠ 0 := by simpa [c] using hc
  apply recurrence_cofinal_nonzero d c u hc' _ k hk
  intro n
  have h := hu n
  change u (n + (d + 1)) = ∑ i : Fin (d + 1), coeffs i * u (n + i) at h
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [c, Fin.is_lt, dif_pos, Fin.eta] using h

#print axioms recurrence_zero_tail_step
#print axioms recurrence_eq_zero_of_zero_tail
#print axioms recurrence_cofinal_nonzero
#print axioms RadiusRecurrenceData
#print axioms radius_cofinal_nonzero
#print axioms dyadic_cofinal_nonzero
#print axioms mathlib_recurrence_cofinal_nonzero

end AdalyFormal.Round10.Nonvanishing
