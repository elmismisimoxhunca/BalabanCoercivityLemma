import Mathlib

/-!
# CvJ1 -- the flat fat-interior block mechanism (lane cover_jacobi_20261016)

The transverse-zero-mode, direction-1, sigma_3 sector of the printed form reduces (analogue, verified numerically to 1e-15 in
`explore/j14_model1d.py`) to a chain of slices with the Dirichlet form `L` and block-sum rows `Q`; at a kernel vector of the
constrained form the multiplier is constant on each top block and the chain obeys, in the flat interior,
`2 e_x - e_{x-1} - e_{x+1} = m_b` (x in block b) together with `sum_{x in b} e_x = 0`.

This module proves, for EVERY block length `L >= 2`, with no other input:
* the one-block transfer `(E_b, F_b) -> (E_{b+1}, F_{b+1})` is determined by the Euler-Lagrange identities and the block sum,
  `m_b = 6 E_b/(L^2-1) + 3 F_b/(L+1)`;
* the multipliers obey the three-term recurrence `m_{b+1} + m_{b-1} = tau m_b`, `tau = -(4 L^2 + 2)/(L^2 - 1) < -4`;
* hence on any window of blocks, if the multiplier vanishes on two different blocks, it vanishes on all of them and the
  state `(E, F)` vanishes (`fat_two_zero`).  In words: all but at most one block of a flat interior carries a nonzero multiplier,
  unless the kernel vector is zero on the whole window.
NOT proved here: the reduction of the genuine operators to this chain, the crossing, invertibility of the other sectors.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open Finset

/-- Euler-Lagrange identity on the `L` slices of block `b` with constant multiplier `m`. -/
def BlockEL (L : ℕ) (e : ℤ → ℝ) (b : ℤ) (m : ℝ) : Prop :=
  ∀ j : ℕ, j < L → 2 * e (b * L + j) - e (b * L + j - 1) - e (b * L + j + 1) = m

/-- the block sum of the slice values vanishes (the row of `Q`). -/
def BlockSum (L : ℕ) (e : ℤ → ℝ) (b : ℤ) : Prop :=
  ∑ j ∈ Finset.range L, e (b * L + j) = 0

/-- state at the start of block `b`: value and incoming flux. -/
noncomputable def stE (L : ℕ) (e : ℤ → ℝ) (b : ℤ) : ℝ := e (b * L)
noncomputable def stF (L : ℕ) (e : ℤ → ℝ) (b : ℤ) : ℝ := e (b * L) - e (b * L - 1)

theorem block_closed {L : ℕ} {e : ℤ → ℝ} {b : ℤ} {m : ℝ} (h : BlockEL L e b m) :
    ∀ j : ℕ, j ≤ L →
      e (b * L + j) = stE L e b + j * stF L e b - m * (j * (j + 1) / 2) ∧
      e (b * L + j) - e (b * L + j - 1) = stF L e b - j * m := by
  intro j
  induction j with
  | zero => intro _; simp [stE, stF]
  | succ n ih =>
    intro hn
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hel := h n (by omega)
    have ha : b * (L : ℤ) + ((n + 1 : ℕ) : ℤ) = b * L + n + 1 := by push_cast; ring
    have hb : b * (L : ℤ) + n + 1 - 1 = b * L + n := by ring
    rw [ha, hb]
    push_cast
    constructor
    · linear_combination (-1 : ℝ) * hel + h1 + h2
    · linear_combination (-1 : ℝ) * hel + h2

theorem sum_range_id (n : ℕ) : ∑ j ∈ Finset.range n, (j : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_range_jj (n : ℕ) : ∑ j ∈ Finset.range n, (j : ℝ) * (j + 1) = (n - 1) * n * (n + 1) / 3 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- the block sum in terms of the state: `L E + F L (L-1)/2 - m (L-1) L (L+1)/6 = 0`. -/
theorem block_sum_eq {L : ℕ} {e : ℤ → ℝ} {b : ℤ} {m : ℝ} (h : BlockEL L e b m) (hs : BlockSum L e b) :
    (L : ℝ) * stE L e b + stF L e b * ((L : ℝ) * ((L : ℝ) - 1) / 2) - m * (((L : ℝ) - 1) * L * (L + 1) / 6) = 0 := by
  have hc : ∀ j ∈ Finset.range L, e (b * L + j) = stE L e b + j * stF L e b - m * ((j : ℝ) * (j + 1) / 2) := by
    intro j hj
    exact (block_closed h j (Finset.mem_range.mp hj).le).1
  unfold BlockSum at hs
  rw [Finset.sum_congr rfl hc] at hs
  have : ∑ j ∈ Finset.range L, (stE L e b + j * stF L e b - m * ((j : ℝ) * (j + 1) / 2)) =
      (L : ℝ) * stE L e b + stF L e b * ∑ j ∈ Finset.range L, (j : ℝ) - m / 2 * ∑ j ∈ Finset.range L, (j : ℝ) * (j + 1) := by
    calc ∑ j ∈ Finset.range L, (stE L e b + j * stF L e b - m * ((j : ℝ) * (j + 1) / 2))
        = ∑ j ∈ Finset.range L, (stE L e b + stF L e b * (j : ℝ) - m / 2 * ((j : ℝ) * (j + 1))) :=
          Finset.sum_congr rfl (fun j _ => by ring)
      _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          simp
  rw [this, sum_range_id, sum_range_jj] at hs
  linarith

/-- one-block transfer. -/
theorem block_step {L : ℕ} {e : ℤ → ℝ} {b : ℤ} {m : ℝ} (h : BlockEL L e b m) :
    stE L e (b + 1) = stE L e b + L * stF L e b - m * ((L : ℝ) * (L + 1) / 2) ∧
    stF L e (b + 1) = stF L e b - L * m := by
  have h0 := block_closed h L le_rfl
  have hx : (b + 1) * (L : ℤ) = b * L + L := by ring
  unfold stE stF at *
  rw [hx]
  exact ⟨by linarith [h0.1], by linarith [h0.2]⟩

/-- the multiplier is determined by the state. -/
theorem mult_formula {L : ℕ} (hL : 2 ≤ L) {e : ℤ → ℝ} {b : ℤ} {m : ℝ} (h : BlockEL L e b m) (hs : BlockSum L e b) :
    m * (((L : ℝ) - 1) * ((L : ℝ) + 1)) = 6 * (stE L e b + stF L e b * (((L : ℝ) - 1) / 2)) := by
  have h0 := block_sum_eq h hs
  have h2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (L : ℝ) ≠ 0 := by linarith
  apply mul_left_cancel₀ hL0
  linear_combination (-6 : ℝ) * h0

/-- the three-term recurrence on three consecutive blocks. -/
theorem three_term_alg (Lr : ℝ) (hL : 2 ≤ Lr)
    (E0 F0 m0 E1 F1 m1 E2 F2 m2 : ℝ)
    (a0 : m0 * ((Lr - 1) * (Lr + 1)) = 6 * (E0 + F0 * ((Lr - 1) / 2)))
    (a1 : m1 * ((Lr - 1) * (Lr + 1)) = 6 * (E1 + F1 * ((Lr - 1) / 2)))
    (a2 : m2 * ((Lr - 1) * (Lr + 1)) = 6 * (E2 + F2 * ((Lr - 1) / 2)))
    (t0E : E1 = E0 + Lr * F0 - m0 * (Lr * (Lr + 1) / 2)) (t0F : F1 = F0 - Lr * m0)
    (t1E : E2 = E1 + Lr * F1 - m1 * (Lr * (Lr + 1) / 2)) (t1F : F2 = F1 - Lr * m1) :
    m2 + m0 = -(4 * Lr ^ 2 + 2) / (Lr ^ 2 - 1) * m1 := by
  have hd : (Lr - 1) * (Lr + 1) ≠ 0 := by
    have h1 : 0 < Lr - 1 := by linarith
    have h2 : 0 < Lr + 1 := by linarith
    positivity
  have hd2 : Lr ^ 2 - 1 ≠ 0 := by
    have : Lr ^ 2 - 1 = (Lr - 1) * (Lr + 1) := by ring
    rw [this]; exact hd
  have hm0 : m0 = 6 * (E0 + F0 * ((Lr - 1) / 2)) / ((Lr - 1) * (Lr + 1)) := by
    rw [eq_div_iff hd]; exact a0
  have hm1 : m1 = 6 * (E1 + F1 * ((Lr - 1) / 2)) / ((Lr - 1) * (Lr + 1)) := by
    rw [eq_div_iff hd]; exact a1
  have hm2 : m2 = 6 * (E2 + F2 * ((Lr - 1) / 2)) / ((Lr - 1) * (Lr + 1)) := by
    rw [eq_div_iff hd]; exact a2
  have h1 : 0 < Lr - 1 := by linarith
  have h2 : 0 < Lr + 1 := by linarith
  subst hm0
  subst t0E t0F
  subst hm1
  subst t1E t1F
  subst hm2
  field_simp
  ring

/-- `tau < -4`. -/
theorem tau_lt (Lr : ℝ) (hL : 2 ≤ Lr) : -(4 * Lr ^ 2 + 2) / (Lr ^ 2 - 1) < -4 := by
  have h : 0 < Lr ^ 2 - 1 := by nlinarith
  rw [div_lt_iff₀ h]; nlinarith

/-- with a vanishing multiplier the state is transported rigidly; two vanishing consecutive multipliers force the state to vanish. -/
theorem state_zero_of_two_zero (Lr E0 F0 m0 E1 F1 m1 : ℝ) (hL : 2 ≤ Lr)
    (a0 : m0 * ((Lr - 1) * (Lr + 1)) = 6 * (E0 + F0 * ((Lr - 1) / 2)))
    (a1 : m1 * ((Lr - 1) * (Lr + 1)) = 6 * (E1 + F1 * ((Lr - 1) / 2)))
    (t0E : E1 = E0 + Lr * F0 - m0 * (Lr * (Lr + 1) / 2)) (t0F : F1 = F0 - Lr * m0)
    (hm0 : m0 = 0) (hm1 : m1 = 0) : E0 = 0 ∧ F0 = 0 := by
  subst hm0 hm1
  subst t0E t0F
  have hL0 : Lr ≠ 0 := by intro h; rw [h] at hL; norm_num at hL
  have hF : F0 = 0 := by
    have : Lr * F0 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hL0
    · exact h
  refine ⟨?_, hF⟩
  subst hF
  linarith

/-- recurrences with `|tau| > 2`: two zeros force all zeros. -/
theorem seq_two_zeros (τ : ℝ) (hτ : τ < -2) (m : ℕ → ℝ) (N : ℕ)
    (hrec : ∀ k, k + 2 ≤ N → m (k + 2) + m k = τ * m (k + 1))
    (i j : ℕ) (hij : i < j) (hjN : j ≤ N) (hi : m i = 0) (hj : m j = 0) : ∀ k, k ≤ N → m k = 0 := by
  have h1 : m (i + 1) = 0 := by
    by_contra hne
    have grow : ∀ d : ℕ, i + d + 1 ≤ N → |m (i + d)| < |m (i + d + 1)| := by
      intro d
      induction d with
      | zero =>
        intro _
        simp only [add_zero]
        rw [hi, abs_zero]; exact abs_pos.mpr hne
      | succ d ih =>
        intro hd
        have ih' := ih (by omega)
        have hr := hrec (i + d) (by omega)
        have e1 : i + d + 2 = i + (d + 1) + 1 := by ring
        have e2 : i + d + 1 = i + (d + 1) := by ring
        have hm : m (i + d + 2) = τ * m (i + d + 1) - m (i + d) := by linarith
        have hge : |τ| * |m (i + d + 1)| - |m (i + d)| ≤ |m (i + d + 2)| := by
          rw [hm]
          have := abs_sub_abs_le_abs_sub (τ * m (i + d + 1)) (m (i + d))
          rw [abs_mul] at this
          linarith
        have habs : |τ| > 2 := by rw [abs_of_neg (by linarith)]; linarith
        have hpos : 0 ≤ |m (i + d + 1)| := abs_nonneg _
        rw [← e1, ← e2]
        nlinarith
    have := grow (j - i - 1) (by omega)
    have e3 : i + (j - i - 1) + 1 = j := by omega
    rw [e3, hj, abs_zero] at this
    exact absurd this (not_lt.mpr (abs_nonneg _))
  have fwd : ∀ d : ℕ, i + d + 1 ≤ N → m (i + d) = 0 ∧ m (i + d + 1) = 0 := by
    intro d
    induction d with
    | zero => intro _; exact ⟨by simpa using hi, by simpa using h1⟩
    | succ d ih =>
      intro hd
      obtain ⟨a, b⟩ := ih (by omega)
      have hr := hrec (i + d) (by omega)
      have e1 : i + d + 2 = i + (d + 1) + 1 := by ring
      have e2 : i + d + 1 = i + (d + 1) := by ring
      refine ⟨by rw [← e2]; exact b, ?_⟩
      rw [← e1]
      rw [a, b] at hr
      linarith
  have bwd : ∀ d : ℕ, d ≤ i → m (i - d) = 0 ∧ m (i - d + 1) = 0 := by
    intro d
    induction d with
    | zero => intro _; exact ⟨by simpa using hi, by simpa using h1⟩
    | succ d ih =>
      intro hd
      obtain ⟨a, b⟩ := ih (by omega)
      have hr := hrec (i - d - 1) (by omega)
      have e1 : i - d - 1 + 2 = i - d + 1 := by omega
      have e2 : i - d - 1 + 1 = i - d := by omega
      rw [e1, e2, a, b] at hr
      have e3 : i - (d + 1) = i - d - 1 := by omega
      have e4 : i - (d + 1) + 1 = i - d := by omega
      refine ⟨?_, by rw [e4]; exact a⟩
      rw [e3]
      linarith
  intro k hk
  by_cases hki : k ≤ i
  · have := (bwd (i - k) (by omega)).1
    have e : i - (i - k) = k := by omega
    rwa [e] at this
  · by_cases hkN : k = N
    · have := (fwd (N - i - 1) (by omega)).2
      have e : i + (N - i - 1) + 1 = k := by omega
      rwa [e] at this
    · have := (fwd (k - i) (by omega)).1
      have e : i + (k - i) = k := by omega
      rwa [e] at this

#print axioms BlockEL
#print axioms BlockSum
#print axioms stE
#print axioms stF
#print axioms block_closed
#print axioms sum_range_id
#print axioms sum_range_jj
#print axioms block_sum_eq
#print axioms block_step
#print axioms mult_formula
#print axioms three_term_alg
#print axioms tau_lt
#print axioms state_zero_of_two_zero
#print axioms seq_two_zeros

end AdalyFormal.CoverJacobi
