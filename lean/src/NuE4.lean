import NuC6

/-!
# NuE4 -- the explicit negative test vector on two adjacent length-4 rows around the layer edge (lane ncwdh_ell2_20261018)

`tvec s n`: `tvs (x - s)` with `tvs = (0, 1, 1, 0, -2 | 2, 0, -1, -1, 0, ..)`: row sums `0` on the rows `[s+1, s+4]` and `[s+5, s+8]`.
`qF1 (s+4) c (tvec s n) = 28 - 16 (1 - c)`, negative at `c = -4/5`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega

/-- the profile `(0, 1, 1, 0, -2, 2, 0, -1, -1, 0, ...)`. -/
def tvs : ℕ → ℝ
  | 1 => 1
  | 2 => 1
  | 4 => -2
  | 5 => 2
  | 7 => -1
  | 8 => -1
  | _ => 0

theorem tvs_zero_of_big {k : ℕ} (h : 9 ≤ k) : tvs k = 0 := by
  unfold tvs
  split <;> first | omega | rfl

section
variable {n : ℕ}

/-- the test vector. -/
def tvec (s n : ℕ) : Fin n → ℝ := fun x => tvs (x.val - s)

theorem ex_tvec (s : ℕ) (hn : s + 9 ≤ n) (z : ℕ) : ex (tvec s n) z = tvs (z - s) := by
  unfold ex tvec
  by_cases hz : z < n
  · rw [dif_pos hz]
  · rw [dif_neg hz]
    exact (tvs_zero_of_big (by omega)).symm

theorem dlt_tvec (s : ℕ) (hn : s + 9 ≤ n) (y : ℕ) : dlt (tvec s n) y = tvs (y + 1 - s) - tvs (y - s) := by
  unfold dlt; rw [ex_tvec s hn, ex_tvec s hn]

theorem aF_tvec (s : ℕ) (hn : s + 10 ≤ n) : aF (tvec s n) = 28 := by
  unfold aF
  have hsup : ∀ y ∈ range (n - 1), y ∉ Finset.Ico s (s + 9) → (dlt (tvec s n) y) ^ 2 = 0 := by
    intro y _ hy
    rw [dlt_tvec s (by omega)]
    simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hy
    rcases hy with h | h
    · rw [show y + 1 - s = 0 by omega, show y - s = 0 by omega]; simp [tvs]
    · rw [tvs_zero_of_big (by omega), tvs_zero_of_big (by omega)]; ring
  have hsub : Finset.Ico s (s + 9) ⊆ range (n - 1) := by
    intro y hy; simp only [Finset.mem_Ico, Finset.mem_range] at hy ⊢; omega
  rw [← Finset.sum_subset hsub (fun y hy hn' => hsup y hy hn')]
  rw [Finset.sum_Ico_eq_sum_range, show s + 9 - s = 9 by omega]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h : ∀ k : ℕ, dlt (tvec s n) (s + k) = tvs (k + 1) - tvs k := by
    intro k
    rw [dlt_tvec s (by omega)]
    rw [show s + k + 1 - s = k + 1 by omega, show s + k - s = k by omega]
  simp only [h]
  norm_num [tvs]

theorem dlt_tvec_layer (s : ℕ) (hn : s + 9 ≤ n) : dlt (tvec s n) (s + 4) = 4 := by
  rw [dlt_tvec s hn, show s + 4 + 1 - s = 5 by omega, show s + 4 - s = 4 by omega]
  norm_num [tvs]

theorem qF1_tvec (s : ℕ) (hn : s + 10 ≤ n) (c : ℝ) : qF1 (s + 4) c (tvec s n) = 28 - 16 * (1 - c) := by
  unfold qF1 bF1
  rw [aF_tvec s hn, dlt_tvec_layer s (by omega)]
  ring

theorem qF1_tvec_neg (s : ℕ) (hn : s + 10 ≤ n) : qF1 (s + 4) (-4 / 5) (tvec s n) < 0 := by
  rw [qF1_tvec s hn]; norm_num

/-- the test vector has zero sum on the two length-4 rows `[s+1, s+4]`, `[s+5, s+8]` and vanishes elsewhere. -/
theorem tvec_mem_Vsub {R a b : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) (s : ℕ) (hn : s + 10 ≤ n)
    {i0 : ℕ} (hi0 : i0 + 1 < R) (hst : st i0 = s + 1) (hl0 : ln i0 = 4) (hl1 : ln (i0 + 1) = 4) :
    tvec s n ∈ Vsub rowOf := by
  intro r
  have hs1 : st (i0 + 1) = s + 5 := by rw [g.stS i0, hst, hl0]
  have hs2 : st (i0 + 2) = s + 9 := by rw [show i0 + 2 = i0 + 1 + 1 by ring, g.stS (i0 + 1), hs1, hl1]
  by_cases hrR : r < R
  · rw [filter_sum_rowD g hrR]
    have key : ∑ j : Fin (ln r), tvec s n ⟨st r + j.val, by have := j.2; have := row_lt_nD g hrR; omega⟩ =
        ∑ j ∈ Finset.range (ln r), tvs (st r + j - s) :=
      Fin.sum_univ_eq_sum_range (fun j => tvs (st r + j - s)) (ln r)
    rw [key]
    by_cases hr0 : r = i0
    · subst hr0
      rw [hl0]
      have hh : ∀ j : ℕ, st r + j - s = 1 + j := fun j => by rw [hst]; omega
      simp only [hh, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num [tvs]
    · by_cases hr1 : r = i0 + 1
      · subst hr1
        rw [hl1]
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

end AdalyFormal.NcwdhTwo
