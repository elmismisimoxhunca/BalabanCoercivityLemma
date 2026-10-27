import CvJ2
import CvJ3

/-!
# CvJ5 -- the window theorem at an ARBITRARY start, and the state-zero propagation (lane cover_jacobi_20261016)

* `StateZero e x`: `e x = 0` and `e x - e (x-1) = 0` (the zero state at the cut before slice `x`).
* `fat_two_zero_s`: for flat rows `[s0 + kL, s0 + (k+1)L)`, `k <= N`, of equal length `L >= 2` (Euler-Lagrange + row sum): if the multiplier `m k`
  vanishes for two different `k` then it vanishes for every `k <= N` and the state vanishes at every cut `s0 + kL`, `k <= N`
  (CvJ2 states this only for starts `b L`; the chain's rows start at arbitrary offsets).
* `chain_back_prop`, `chain_fwd_prop`: if each row `i < K` propagates a zero state backward (resp. forward) then a zero state at the cut `st K`
  forces zero states at all cuts `st i`, `i <= K` (resp. `i >= K`), with `e = 0` on the rows crossed.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

def StateZero (e : ℤ → ℝ) (x : ℤ) : Prop := e x = 0 ∧ e x - e (x - 1) = 0

theorem fat_two_zero_s {L : ℕ} (hL : 2 ≤ L) (e : ℤ → ℝ) (m : ℕ → ℝ) (s0 : ℤ) (N : ℕ) (hN : 1 ≤ N)
    (hEL : ∀ k : ℕ, k ≤ N → BlockELs (s0 + (k : ℤ) * L) L e (m k))
    (hS : ∀ k : ℕ, k ≤ N → BlockSums (s0 + (k : ℤ) * L) L e)
    (i j : ℕ) (hij : i < j) (hjN : j ≤ N) (hi : m i = 0) (hj : m j = 0) :
    (∀ k : ℕ, k ≤ N → m k = 0) ∧ (∀ k : ℕ, k ≤ N → StateZero e (s0 + (k : ℤ) * L)) := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hnext : ∀ k : ℕ, (s0 + (k : ℤ) * L) + L = s0 + ((k + 1 : ℕ) : ℤ) * L := by
    intro k; push_cast; ring
  have hrec : ∀ k : ℕ, k + 2 ≤ N → m (k + 2) + m k = -(4 * (L : ℝ) ^ 2 + 2) / ((L : ℝ) ^ 2 - 1) * m (k + 1) := by
    intro k hk
    have h0 := hEL k (by omega)
    have h1 := hEL (k + 1) (by omega)
    have h2 := hEL (k + 2) (by omega)
    have s0' := hS k (by omega)
    have s1 := hS (k + 1) (by omega)
    have s2 := hS (k + 2) (by omega)
    have t0 := blocks_step h0
    have t1 := blocks_step h1
    rw [hnext k] at t0
    rw [hnext (k + 1)] at t1
    exact three_term_alg (L : ℝ) hL2 _ _ _ _ _ _ _ _ _
      (blocks_mult hL h0 s0') (blocks_mult hL h1 s1) (blocks_mult hL h2 s2) t0.1 t0.2 t1.1 t1.2
  have hseq := seq_two_zeros (-(4 * (L : ℝ) ^ 2 + 2) / ((L : ℝ) ^ 2 - 1)) (by have := tau_lt (L : ℝ) hL2; linarith)
    m N hrec i j hij hjN hi hj
  refine ⟨hseq, ?_⟩
  intro k hk
  by_cases hkN : k < N
  · have h0 := hEL k (by omega)
    have h1 := hEL (k + 1) (by omega)
    have s0' := hS k (by omega)
    have s1 := hS (k + 1) (by omega)
    have t0 := blocks_step h0
    rw [hnext k] at t0
    obtain ⟨hE, hF⟩ := state_zero_of_two_zero (L : ℝ) _ _ _ _ _ _ hL2 (blocks_mult hL h0 s0') (blocks_mult hL h1 s1)
      t0.1 t0.2 (hseq k (by omega)) (hseq (k + 1) (by omega))
    exact ⟨hE, hF⟩
  · have hkeq : k = N := by omega
    subst hkeq
    obtain ⟨N', rfl⟩ : ∃ N', k = N' + 1 := ⟨k - 1, by omega⟩
    have h0 := hEL N' (by omega)
    have s0' := hS N' (by omega)
    have hz : StateZero e (s0 + (N' : ℤ) * L) := by
      by_cases hN' : N' + 1 ≤ N'
      · omega
      · -- state at N' from the case k = N' < N'+1
        have h1 := hEL (N' + 1) le_rfl
        have s1 := hS (N' + 1) le_rfl
        have t0 := blocks_step h0
        rw [hnext N'] at t0
        obtain ⟨hE, hF⟩ := state_zero_of_two_zero (L : ℝ) _ _ _ _ _ _ hL2 (blocks_mult hL h0 s0') (blocks_mult hL h1 s1)
          t0.1 t0.2 (hseq N' (by omega)) (hseq (N' + 1) le_rfl)
        exact ⟨hE, hF⟩
    obtain ⟨_, hE1, hF1, _⟩ := blocks_fwd_zero hL h0 s0' hz.1 hz.2
    rw [hnext N'] at hE1 hF1
    exact ⟨hE1, by simpa [hnext N'] using hF1⟩

/-- backward propagation of a zero state across a sequence of rows. -/
theorem chain_back_prop (e : ℤ → ℝ) (st : ℕ → ℤ) (ln : ℕ → ℕ) (K : ℕ)
    (hback : ∀ i, i < K → StateZero e (st (i + 1)) →
      StateZero e (st i) ∧ ∀ j : ℕ, j ≤ ln i → e (st i + j) = 0)
    (hz : StateZero e (st K)) :
    ∀ d : ℕ, d ≤ K → StateZero e (st (K - d)) ∧
      ∀ i : ℕ, K - d ≤ i → i < K → ∀ j : ℕ, j ≤ ln i → e (st i + j) = 0 := by
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨by simpa using hz, ?_⟩
    intro i hi hik; omega
  | succ d ih =>
    intro hd
    obtain ⟨hs, hrows⟩ := ih (by omega)
    have hi : K - (d + 1) < K := by omega
    have hnext : K - (d + 1) + 1 = K - d := by omega
    have hs' : StateZero e (st (K - (d + 1) + 1)) := by rw [hnext]; exact hs
    obtain ⟨hs0, hrow0⟩ := hback (K - (d + 1)) hi hs'
    refine ⟨hs0, ?_⟩
    intro i hi1 hi2 j hj
    by_cases heq : i = K - (d + 1)
    · subst heq; exact hrow0 j hj
    · exact hrows i (by omega) hi2 j hj

/-- forward propagation of a zero state across a sequence of rows. -/
theorem chain_fwd_prop (e : ℤ → ℝ) (st : ℕ → ℤ) (ln : ℕ → ℕ) (K R : ℕ)
    (hfwd : ∀ i, K ≤ i → i < R → StateZero e (st i) →
      StateZero e (st (i + 1)) ∧ ∀ j : ℕ, j ≤ ln i → e (st i + j) = 0)
    (hz : StateZero e (st K)) :
    ∀ d : ℕ, K + d ≤ R → StateZero e (st (K + d)) ∧
      ∀ i : ℕ, K ≤ i → i < K + d → ∀ j : ℕ, j ≤ ln i → e (st i + j) = 0 := by
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨by simpa using hz, ?_⟩
    intro i hi hik; omega
  | succ d ih =>
    intro hd
    obtain ⟨hs, hrows⟩ := ih (by omega)
    obtain ⟨hs1, hrow1⟩ := hfwd (K + d) (by omega) (by omega) hs
    refine ⟨by simpa [Nat.add_assoc] using hs1, ?_⟩
    intro i hi1 hi2 j hj
    by_cases heq : i = K + d
    · subst heq; exact hrow1 j hj
    · exact hrows i hi1 (by omega) j hj


#print axioms StateZero
#print axioms fat_two_zero_s
#print axioms chain_back_prop
#print axioms chain_fwd_prop

end AdalyFormal.CoverJacobi
