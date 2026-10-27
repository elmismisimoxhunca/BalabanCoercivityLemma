import CvOK6

/-!
# CvOK8 -- the multipliers of a radical vector satisfy the three-term recurrence on a flat window; consequently two window rows have different multipliers (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open Finset
open AdalyFormal.CoverJacobi

variable {n a b : ℕ}

theorem window_rec {L : ℕ} (hL : 2 ≤ L) (e : ℤ → ℝ) (m : ℕ → ℝ) (s0 : ℤ) (N : ℕ)
    (hEL : ∀ k : ℕ, k ≤ N → BlockELs (s0 + (k : ℤ) * L) L e (m k))
    (hS : ∀ k : ℕ, k ≤ N → BlockSums (s0 + (k : ℤ) * L) L e) :
    ∀ k : ℕ, k + 2 ≤ N → m (k + 2) + m k = -(4 * (L : ℝ) ^ 2 + 2) / ((L : ℝ) ^ 2 - 1) * m (k + 1) := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hnext : ∀ k : ℕ, (s0 + (k : ℤ) * L) + L = s0 + ((k + 1 : ℕ) : ℤ) * L := by
    intro k; push_cast; ring
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

/-- the window multipliers of a radical vector of the chain form. -/
theorem chain_window_rec {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) (C : ℕ) (c : ℝ)
    (hC1 : 1 ≤ C) (hC2 : C + 1 < n) {e : Fin n → ℝ} (he : e ∈ Vsub rowOf)
    (hrad : ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF C c e d = 0)
    {i0 : ℕ} (hC : st i0 = C) (hL : 3 ≤ ln i0)
    {i1 N Lw : ℕ} (hi1 : i0 < i1) (hi1N : i1 + N + b < R) (hLw : ∀ k, k ≤ N → ln (i1 + k) = Lw) (hLw2 : 2 ≤ Lw) :
    ∀ k : ℕ, k + 2 ≤ N → rowMu C c e st (i1 + k + 2) + rowMu C c e st (i1 + k) =
      -(4 * (Lw : ℝ) ^ 2 + 2) / ((Lw : ℝ) ^ 2 - 1) * rowMu C c e st (i1 + k + 1) := by
  have hright : ∀ i, i0 < i → ∀ j, st i + j ≥ C + 3 := by
    intro i hi j
    have h1' := st_monoD g (show i0 + 1 ≤ i by omega)
    have h2 := g.stS i0
    omega
  have hflat_of : ∀ i, i < R → i0 < i → BlockELs (st i : ℤ) (ln i) (nx e) (rowMu C c e st i) := by
    intro i hi hcase
    apply rowEL_flatD g C c hC1 hC2 hrad hi
    intro j hj
    have := hright i hcase j; omega
  have hsum_of : ∀ i, i < R → BlockSums (st i : ℤ) (ln i) (nx e) := fun i hi => rowSum_of_memD g he hi
  have hstw := st_add_windowD g i1 Lw N hLw
  have := window_rec hLw2 (nx e) (fun k => rowMu C c e st (i1 + k)) (st i1 : ℤ) N
    (fun k hk => by
      have := hflat_of (i1 + k) (by omega) (by omega)
      rw [hstw k hk, hLw k hk] at this
      exact this)
    (fun k hk => by
      have := hsum_of (i1 + k) (by omega)
      rw [hstw k hk, hLw k hk] at this
      exact this)
  intro k hk
  have h := this k hk
  simpa [Nat.add_assoc] using h

#print axioms chain_window_rec

end AdalyFormal.CoverOmega
