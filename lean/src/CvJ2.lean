import CvJ1

/-!
# CvJ2 -- the window theorem for a flat fat interior (lane cover_jacobi_20261016)

`fat_two_zero`: on a window of `N + 1 >= 3` consecutive flat blocks of any length `L >= 2` that satisfy the Euler-Lagrange identities
and the block-sum rows, if the multiplier vanishes on two different blocks of the window then it vanishes on every block of the window
and the chain value `e` vanishes on every slice of the blocks `b0, ..., b0 + N - 1`.  Contrapositive (the form used downstream):
a kernel vector that is not identically zero on the window has a nonzero multiplier on all but at most one block of the window.
NOT proved: the reduction of the genuine operators to this chain, the crossing, the other sectors.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

theorem fat_two_zero {L : ℕ} (hL : 2 ≤ L) (e : ℤ → ℝ) (m : ℤ → ℝ) (b0 : ℤ) (N : ℕ)
    (hEL : ∀ k : ℕ, k ≤ N → BlockEL L e (b0 + k) (m (b0 + k)))
    (hS : ∀ k : ℕ, k ≤ N → BlockSum L e (b0 + k))
    (i j : ℕ) (hij : i < j) (hjN : j ≤ N) (hi : m (b0 + i) = 0) (hj : m (b0 + j) = 0) :
    (∀ k : ℕ, k ≤ N → m (b0 + k) = 0) ∧
      (∀ k : ℕ, k < N → stE L e (b0 + k) = 0 ∧ stF L e (b0 + k) = 0 ∧ ∀ x : ℕ, x < L → e ((b0 + k) * L + x) = 0) := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hrec : ∀ k : ℕ, k + 2 ≤ N → m (b0 + ((k + 2 : ℕ) : ℤ)) + m (b0 + k) = -(4 * (L : ℝ) ^ 2 + 2) / ((L : ℝ) ^ 2 - 1) * m (b0 + ((k + 1 : ℕ) : ℤ)) := by
    intro k hk
    have e1 : b0 + ((k + 1 : ℕ) : ℤ) = (b0 + k) + 1 := by push_cast; ring
    have e2 : b0 + ((k + 2 : ℕ) : ℤ) = (b0 + k) + 1 + 1 := by push_cast; ring
    have h0 := hEL k (by omega)
    have h1 := hEL (k + 1) (by omega)
    have h2 := hEL (k + 2) (by omega)
    have s0 := hS k (by omega)
    have s1 := hS (k + 1) (by omega)
    have s2 := hS (k + 2) (by omega)
    rw [e1] at h1 s1 ⊢
    rw [e2] at h2 s2 ⊢
    have t0 := block_step h0
    have t1 := block_step h1
    exact three_term_alg (L : ℝ) hL2 _ _ _ _ _ _ _ _ _
      (mult_formula hL h0 s0) (mult_formula hL h1 s1) (mult_formula hL h2 s2) t0.1 t0.2 t1.1 t1.2
  have hseq := seq_two_zeros (-(4 * (L : ℝ) ^ 2 + 2) / ((L : ℝ) ^ 2 - 1)) (by have := tau_lt (L : ℝ) hL2; linarith)
    (fun k => m (b0 + k)) N hrec i j hij hjN hi hj
  refine ⟨hseq, ?_⟩
  intro k hk
  have e1 : b0 + ((k + 1 : ℕ) : ℤ) = (b0 + k) + 1 := by push_cast; ring
  have h0 := hEL k (by omega)
  have h1 := hEL (k + 1) (by omega)
  have s0 := hS k (by omega)
  have s1 := hS (k + 1) (by omega)
  have hm0 := hseq k (by omega)
  have hm1 := hseq (k + 1) (by omega)
  rw [e1] at h1 s1 hm1
  have t0 := block_step h0
  obtain ⟨hE, hF⟩ := state_zero_of_two_zero (L : ℝ) _ _ _ _ _ _ hL2 (mult_formula hL h0 s0) (mult_formula hL h1 s1)
    t0.1 t0.2 hm0 hm1
  refine ⟨hE, hF, ?_⟩
  intro x hx
  have hc := (block_closed h0 x hx.le).1
  rw [hc, hE, hF, hm0]
  ring


#print axioms fat_two_zero

end AdalyFormal.CoverJacobi
