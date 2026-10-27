import NuE4

/-!
# SoE4 -- the negative test vector `tvec` on two adjacent rows of any length `L ≥ 4` (lane sites_only_20261019)

`NuE4.tvec s n` is supported on the 8 positions `s+1 .. s+8`; with the profile `(1,1,0,-2 | 2,0,-1,-1)` its sums over the 4-blocks `[s+1,s+4]`, `[s+5,s+8]` vanish.  If the left row
of length `L ≥ 4` ends at `s+4` and the right row of length `L` starts at `s+5`, the support lies inside the two rows, so `tvec s n` has zero sum on EVERY row
(`tvec_mem_Vsub_L`), and `qF1 (s+4) c (tvec s n) = 28 - 16 (1 - c)` (`NuE4.qF1_tvec`) is unchanged.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.SitesOnly

open Finset
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.NcwdhTwo

section
variable {n : ℕ}

theorem tvec_mem_Vsub_L {R a b : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) (s L : ℕ) (hn : s + 10 ≤ n) (hL : 4 ≤ L)
    {i0 : ℕ} (hi0 : i0 + 1 < R) (hst : st i0 + L = s + 5) (hl0 : ln i0 = L) (hl1 : ln (i0 + 1) = L) :
    tvec s n ∈ Vsub rowOf := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 4 := ⟨L - 4, by omega⟩
  intro r
  have hs1 : st (i0 + 1) = s + 5 := by rw [g.stS i0, hl0]; exact hst
  have hs2 : st (i0 + 2) = s + 5 + (L' + 4) := by rw [show i0 + 2 = i0 + 1 + 1 by ring, g.stS (i0 + 1), hs1, hl1]
  by_cases hrR : r < R
  · rw [filter_sum_rowD g hrR]
    have key : ∑ j : Fin (ln r), tvec s n ⟨st r + j.val, by have := j.2; have := row_lt_nD g hrR; omega⟩ =
        ∑ j ∈ Finset.range (ln r), tvs (st r + j - s) :=
      Fin.sum_univ_eq_sum_range (fun j => tvs (st r + j - s)) (ln r)
    rw [key]
    by_cases hr0 : r = i0
    · subst hr0
      rw [hl0]
      rw [Finset.sum_range_add]
      have h0 : ∑ j ∈ Finset.range L', tvs (st r + j - s) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [show st r + j - s = 0 by omega]
        simp [tvs]
      have hh : ∀ k : ℕ, st r + (L' + k) - s = 1 + k := fun k => by omega
      simp only [h0, hh, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num [tvs]
    · by_cases hr1 : r = i0 + 1
      · subst hr1
        rw [hl1]
        rw [Nat.add_comm L' 4, Finset.sum_range_add]
        have hh4 : ∑ k ∈ Finset.range L', tvs (st (i0 + 1) + (4 + k) - s) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          rw [tvs_zero_of_big (by omega)]
        rw [hh4, add_zero]
        have hh : ∀ j : ℕ, st (i0 + 1) + j - s = 5 + j := fun j => by rw [hs1]; omega
        simp only [hh, Finset.sum_range_succ, Finset.sum_range_zero]
        norm_num [tvs]
      · apply Finset.sum_eq_zero
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rcases lt_or_gt_of_ne hr0 with h | h
        · have h1 := st_monoD g (show r + 1 ≤ i0 by omega)
          have h2 := g.stS r
          rw [show st r + j - s = 0 by omega]
          simp [tvs]
        · have h1 : i0 + 2 ≤ r := by omega
          have h2 := st_monoD g h1
          rw [tvs_zero_of_big (by omega)]
  · apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exfalso
    obtain ⟨i, hiR, h1, h2⟩ := g.cover x.val x.2
    have := (g.row i hiR x.val x.2).mpr ⟨h1, h2⟩
    omega

end

#print axioms tvec_mem_Vsub_L

end AdalyFormal.SitesOnly
