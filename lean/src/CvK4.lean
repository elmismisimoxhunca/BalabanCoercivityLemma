import CvK3
import CvJ5

/-!
# CvK4 -- the tail of the chain kernel cannot vanish on two rows of a flat window (lane cover_jacobi_20261016)

`chain_tail`: let `e != 0` be a radical vector of the constrained chain form at layer weight `c` (the layer slice `C = st i0` is the first slice of the
row `i0 >= 1`, `ln i0 >= 3`; `c != 0`; `(L-2)(L+3)/6 + 1/c != 0`, i.e. `c != c_loc`).  Let `i1 > i0` and `N >= 1` with `i1 + N < R` and all rows `i1, .., i1+N` of the same length.
Then the row multipliers `rowMu (i1 + a)`, `rowMu (i1 + b)` (`a < b <= N`) cannot both vanish.
Proof: two zeros give (CvJ5 `fat_two_zero_s`) a zero state at the window start; zero states propagate backward through the flat rows (CvJ3), the layer row (CvJ4, uses `c != c_loc`)
and the pre-layer row, to the left end, and forward through the flat rows to the right end; so `e = 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open Finset

variable {n : ℕ}

theorem st_add_window {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeom n R st ln rowOf) (i1 Lw N : ℕ)
    (hLw : ∀ k, k ≤ N → ln (i1 + k) = Lw) : ∀ k, k ≤ N → (st (i1 + k) : ℤ) = (st i1 : ℤ) + (k : ℤ) * Lw := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := g.stS (i1 + k)
    have h3 := hLw k (by omega)
    have : st (i1 + (k + 1)) = st (i1 + k) + Lw := by rw [← Nat.add_assoc, h2, h3]
    rw [this]; push_cast; rw [h1]; ring

theorem chain_tail {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeom n R st ln rowOf) (C : ℕ) (c : ℝ)
    (hC1 : 1 ≤ C) (hC2 : C + 1 < n) {e : Fin n → ℝ} (he : e ∈ Vsub rowOf) (hne : e ≠ 0)
    (hrad : ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF C c e d = 0)
    {i0 : ℕ} (hi0 : i0 < R) (hi01 : 1 ≤ i0) (hC : st i0 = C) (hL : 3 ≤ ln i0)
    (hc : c ≠ 0) (hnl : ((ln i0 : ℝ) - 2) * ((ln i0 : ℝ) + 3) / 6 + 1 / c ≠ 0)
    {i1 N Lw : ℕ} (hi1 : i0 < i1) (hN : 1 ≤ N) (hi1N : i1 + N < R) (hLw : ∀ k, k ≤ N → ln (i1 + k) = Lw)
    {a b : ℕ} (hab : a < b) (hbN : b ≤ N)
    (ha : rowMu C c e st (i1 + a) = 0) (hb : rowMu C c e st (i1 + b) = 0) : False := by
  have hLw2 : 2 ≤ Lw := by
    have := g.ln2 (i1 + 0) (by omega)
    rwa [hLw 0 (Nat.zero_le _)] at this
  have hcastS : ∀ i, (st (i + 1) : ℤ) = (st i : ℤ) + (ln i : ℤ) := by
    intro i; rw [g.stS i]; push_cast; ring
  -- flat rows away from the layer
  have hright : ∀ i, i0 < i → ∀ j, st i + j ≥ C + 3 := by
    intro i hi j
    have h1 := st_mono g (show i0 + 1 ≤ i by omega)
    have h2 := g.stS i0
    omega
  have hleft : ∀ i, i + 1 < i0 → ∀ j, j < ln i → st i + j + 2 ≤ C := by
    intro i hi j hj
    have h1 := st_mono g (show i + 1 ≤ i0 - 1 by omega)
    have h2 := g.stS i
    have h3 := g.stS (i0 - 1)
    have h4 := g.ln2 (i0 - 1) (by omega)
    have e1 : i0 - 1 + 1 = i0 := by omega
    rw [e1, hC] at h3
    omega
  have hflat_of : ∀ i, i < R → (i0 < i ∨ i + 1 < i0) →
      BlockELs (st i : ℤ) (ln i) (nx e) (rowMu C c e st i) := by
    intro i hi hcase
    apply rowEL_flat g C c hC1 hC2 hrad hi
    intro j hj
    rcases hcase with h | h
    · have := hright i h j; omega
    · have := hleft i h j hj; omega
  have hsum_of : ∀ i, i < R → BlockSums (st i : ℤ) (ln i) (nx e) := fun i hi => rowSum_of_mem g he hi
  -- the window: two zero multipliers force the zero state at the window start
  have hstw := st_add_window g i1 Lw N hLw
  have hwin := fat_two_zero_s hLw2 (nx e) (fun k => rowMu C c e st (i1 + k)) (st i1 : ℤ) N hN
    (fun k hk => by
      have := hflat_of (i1 + k) (by omega) (Or.inl (by omega))
      rw [hstw k hk, hLw k hk] at this
      exact this)
    (fun k hk => by
      have := hsum_of (i1 + k) (by omega)
      rw [hstw k hk, hLw k hk] at this
      exact this)
    a b hab hbN ha hb
  have hz0 : StateZero (nx e) (st i1 : ℤ) := by
    have := hwin.2 0 (Nat.zero_le _)
    simpa using this
  have hback : ∀ i, i < i1 → StateZero (nx e) (st (i + 1) : ℤ) →
      StateZero (nx e) (st i : ℤ) ∧ ∀ j : ℕ, j ≤ ln i → nx e ((st i : ℤ) + j) = 0 := by
    intro i hi hz
    have hiR : i < R := by omega
    rw [hcastS i] at hz
    obtain ⟨hE, hF⟩ := hz
    by_cases hflat : i0 < i ∨ i + 1 < i0
    · have h := blocks_back_zero (g.ln2 i hiR) (hflat_of i hiR hflat) (hsum_of i hiR) hE hF
      exact ⟨⟨h.2.1, h.2.2.1⟩, fun j hj => h.2.2.2 j hj⟩
    · by_cases hi_eq : i = i0
      · subst hi_eq
        have hel := rowEL_layer g C c hC1 hC2 hrad hiR hC hL
        have hsum' : BlockSums (C : ℤ) (ln i) (nx e) := by rw [← hC]; exact hsum_of i hiR
        have hE' : nx e ((C : ℤ) + (ln i : ℤ)) = 0 := by rw [← hC]; exact hE
        have hF' : nx e ((C : ℤ) + (ln i : ℤ)) - nx e ((C : ℤ) + (ln i : ℤ) - 1) = 0 := by rw [← hC]; exact hF
        obtain ⟨_, hrow, hprev⟩ := layerRow_zero hL hc hel hsum' hE' hF' hnl
        have h0 : nx e (C : ℤ) = 0 := by simpa using hrow 0 (Nat.zero_le _)
        refine ⟨⟨by rw [hC]; exact h0, by rw [hC, h0, hprev]; ring⟩, ?_⟩
        intro j hj
        rw [hC]; exact hrow j hj
      · have hi_prev : i + 1 = i0 := by omega
        have hz' : nx e (C : ℤ) = 0 ∧ nx e (C : ℤ) - nx e ((C : ℤ) - 1) = 0 := by
          have e1 : st (i + 1) = C := by rw [hi_prev, hC]
          have e2 : (st i : ℤ) + (ln i : ℤ) = (C : ℤ) := by rw [← hcastS i, e1]
          rw [e2] at hE hF
          exact ⟨hE, hF⟩
        have hel : BlockELs (st i : ℤ) (ln i) (nx e) (rowMu C c e st i) := by
          have := rowEL_prev g C c hC1 hC2 hrad hi0 hi01 hC hz'
          have e1 : i0 - 1 = i := by omega
          rw [e1] at this
          exact this
        have h := blocks_back_zero (g.ln2 i hiR) hel (hsum_of i hiR) hE hF
        exact ⟨⟨h.2.1, h.2.2.1⟩, fun j hj => h.2.2.2 j hj⟩
  have hfwd : ∀ i, i1 ≤ i → i < R → StateZero (nx e) (st i : ℤ) →
      StateZero (nx e) (st (i + 1) : ℤ) ∧ ∀ j : ℕ, j ≤ ln i → nx e ((st i : ℤ) + j) = 0 := by
    intro i hi hiR hz
    have h := blocks_fwd_zero (g.ln2 i hiR) (hflat_of i hiR (Or.inl (by omega))) (hsum_of i hiR) hz.1 hz.2
    rw [hcastS i]
    exact ⟨⟨h.2.1, h.2.2.1⟩, fun j hj => h.2.2.2 j hj⟩
  have hbk := chain_back_prop (nx e) (fun i => (st i : ℤ)) ln i1 hback hz0 i1 le_rfl
  have hfw := chain_fwd_prop (nx e) (fun i => (st i : ℤ)) ln i1 R hfwd hz0 (R - i1) (by omega)
  apply hne
  funext x
  obtain ⟨i, hiR, h1, h2⟩ := g.cover x.val x.2
  have hx : nx e (x.val : ℤ) = 0 := by
    have hj : x.val - st i ≤ ln i := by omega
    have hcast : (x.val : ℤ) = (st i : ℤ) + ((x.val - st i : ℕ) : ℤ) := by omega
    rw [hcast]
    by_cases hlt : i < i1
    · exact hbk.2 i (by simp) hlt _ hj
    · exact hfw.2 i (by omega) (by omega) _ hj
  have := nx_nat e x.val x.2
  rw [this] at hx
  simpa using hx


#print axioms st_add_window
#print axioms chain_tail

end AdalyFormal.CoverJacobi
