import CvK5
import CvK6

/-!
# CvK7 -- the pole of the chain model: crossing, simplicity of the zero, nonvanishing tail multiplier (lane cover_jacobi_20261016)

`chain_pole`: for a row geometry whose layer row `i0` (`>= 1`, with a row after it) has length `k + 3` and starts at the layer slice `C = K + 1`, there is a layer weight
`c* in (c_loc, 1)`, `c* != 0` and a nonzero vector `e*` of the constraint space with `q c* e* = 0` and radical identity, such that for every flat window of `N + 1` rows
of equal length to the right of the layer row the row multipliers `rowMu (i1 + a)`, `rowMu (i1 + b)` (`a < b <= N`) are NOT both zero.
Everything is about the abstract 1D chain; the identification with the genuine operators is NOT done here.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open Finset

variable {n : ℕ}

theorem e1vec_mem {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeom n R st ln rowOf) {i0 K k r : ℕ}
    (hi0 : i0 < R) (hC : st i0 = K + 1) (hL : ln i0 = k + 3) (hn : n = (K + 1) + (k + 3) + r) :
    e1vec (K + 1) (k + 3) n ∈ Vsub rowOf := by
  intro rr
  by_cases hrr : rr = i0
  · subst hrr
    rw [filter_sum_row g hi0]
    have hle := row_lt_n g hi0
    have hterm : ∀ j : Fin (ln rr), e1vec (K + 1) (k + 3) n ⟨st rr + j.val, by have := j.2; omega⟩ =
        locVec (k + 2) (k + 2 - j.val) := by
      intro j
      have hj := j.2
      unfold e1vec
      rw [if_pos (by simp only []; omega)]
      simp only []
      rw [show k + 3 - 1 = k + 2 by omega, show K + 1 + (k + 3) - 1 - (st rr + j.val) = k + 2 - j.val by omega]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    rw [Fin.sum_univ_eq_sum_range (fun j => locVec (k + 2) (k + 2 - j)) (ln rr), hL]
    have := Finset.sum_range_reflect (fun j => locVec (k + 2) j) (k + 3)
    rw [show k + 3 - 1 = k + 2 by omega] at this
    rw [show ∑ j ∈ Finset.range (k + 3), locVec (k + 2) (k + 2 - j) = ∑ j ∈ Finset.range (k + 3), locVec (k + 2) j from this]
    exact locVec_sum (k + 2)
  · apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    unfold e1vec
    rw [if_neg]
    intro hcond
    have hle := row_lt_n g hi0
    have := (g.row i0 hi0 x.val x.2).mpr ⟨by omega, by omega⟩
    exact hrr (hx.symm.trans this)

theorem hnl_of_gt (k : ℕ) (cs : ℝ) (h1 : cLoc (k + 2) < cs) (h0 : cs ≠ 0) :
    ((k + 3 : ℕ) - 2 : ℝ) * (((k + 3 : ℕ) : ℝ) + 3) / 6 + 1 / cs ≠ 0 := by
  have hA : 0 < ((k : ℝ) + 1) * ((k : ℝ) + 6) := by positivity
  have hc : cLoc (k + 2) = -6 / (((k : ℝ) + 1) * ((k : ℝ) + 6)) := by
    unfold cLoc; push_cast
    rw [show ((k : ℝ) + 2 - 1) = (k : ℝ) + 1 by ring, show ((k : ℝ) + 2 + 4) = (k : ℝ) + 6 by ring]
  have hval : ((k + 3 : ℕ) - 2 : ℝ) * (((k + 3 : ℕ) : ℝ) + 3) / 6 = ((k : ℝ) + 1) * ((k : ℝ) + 6) / 6 := by
    push_cast; ring
  rw [hval]
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · intro hzero
    -- cs < 0 and -6/A < cs  =>  1/cs < -A/6
    have hlt : 1 / cs < 1 / (-6 / (((k : ℝ) + 1) * ((k : ℝ) + 6))) := by
      apply one_div_lt_one_div_of_neg_of_lt hneg
      rw [← hc]; exact h1
    have : 1 / (-6 / (((k : ℝ) + 1) * ((k : ℝ) + 6))) = -(((k : ℝ) + 1) * ((k : ℝ) + 6)) / 6 := by
      field_simp
    rw [this] at hlt
    linarith
  · intro hzero
    have : 0 < 1 / cs := by positivity
    have h6 : 0 < ((k : ℝ) + 1) * ((k : ℝ) + 6) / 6 := by positivity
    linarith

theorem chain_pole {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeom n R st ln rowOf)
    {i0 K k r : ℕ} (hi01 : 1 ≤ i0) (hi0R : i0 + 1 < R) (hC : st i0 = K + 1) (hL : ln i0 = k + 3)
    (hn : n = (K + 1) + (k + 3) + r)
    {i1 N Lw : ℕ} (hi1 : i0 < i1) (hN : 1 ≤ N) (hi1N : i1 + N < R) (hLw : ∀ j, j ≤ N → ln (i1 + j) = Lw) :
    ∃ cs : ℝ, cLoc (k + 2) < cs ∧ cs < 1 ∧ cs ≠ 0 ∧ ∃ es : Fin n → ℝ, es ∈ Vsub rowOf ∧ es ≠ 0 ∧
      qF (K + 1) cs es = 0 ∧ (∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF (K + 1) cs es d = 0) ∧
      ∀ a b : ℕ, a < b → b ≤ N → ¬ (rowMu (K + 1) cs es st (i1 + a) = 0 ∧ rowMu (K + 1) cs es st (i1 + b) = 0) := by
  have hi0 : i0 < R := by omega
  have hC1 : 1 ≤ K + 1 := by omega
  have hC2 : K + 1 + 1 < n := by omega
  have he1 := e1vec_mem g hi0 hC hL hn
  have hneg : qF (K + 1) (cLoc (k + 2)) (e1vec (K + 1) (k + 3) n) < 0 := by
    have := qF_e1vec K k r (cLoc (k + 2))
    subst hn
    rw [this]
    exact locEnergy_neg k
  have hc1 : cLoc (k + 2) < 1 := lt_trans (cLoc_neg k) one_pos
  obtain ⟨cs, h1, h2, ⟨es, hes, hne, h0⟩, hpsd, hpos, hrad⟩ :=
    chain_crossing rowOf (K + 1) (cLoc (k + 2)) hc1 (e1vec (K + 1) (k + 3) n) he1 hneg
  have hcs0 : cs ≠ 0 := by
    intro hz
    rw [hz] at h0
    exact hne (qF_zero_eq_zero g (K + 1) hC1 hC2 hi01 hi0R hC hes h0)
  refine ⟨cs, h1, h2, hcs0, es, hes, hne, h0, hrad es hes h0, ?_⟩
  intro a b hab hbN ⟨ha, hb⟩
  have hL3 : 3 ≤ ln i0 := by omega
  have hnl : ((ln i0 : ℝ) - 2) * ((ln i0 : ℝ) + 3) / 6 + 1 / cs ≠ 0 := by
    rw [hL]
    exact hnl_of_gt k cs h1 hcs0
  exact chain_tail g (K + 1) cs hC1 hC2 hes hne (hrad es hes h0) hi0 hi01 hC hL3 hcs0 hnl hi1 hN hi1N hLw hab hbN ha hb


#print axioms e1vec_mem
#print axioms hnl_of_gt
#print axioms chain_pole

end AdalyFormal.CoverJacobi
