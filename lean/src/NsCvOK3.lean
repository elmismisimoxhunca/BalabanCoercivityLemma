import NsCvOK2
import CvK6

/-!
# CvOK3 -- uniqueness of the radical vector from the left collar (lane omega)

For the relaxed row geometry (`RowGeomD n R a b`; the first `a >= 1` rows are singleton collar rows), a radical vector `e` of the constrained chain form at a layer weight `c ≠ 0`
with the layer nondegeneracy `hnl` that has `nx e a = 0` (first free slice) vanishes: forward propagation of the zero state through the flat rows, the row before the layer
(`prevRow_fwd_zero`), the layer row (`layer_fwd_zero`), and the flat rows after it; the right collar rows vanish by their row sums.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open Finset
open AdalyFormal.CoverJacobi

variable {n a b : ℕ}

theorem st_left {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) : ∀ i, i ≤ a → st i = i := by
  intro i
  induction i with
  | zero => intro _; exact g.st0
  | succ i ih =>
    intro hi
    rw [g.stS, ih (by omega), g.lnL i (by omega)]

/-- all left collar slices of a vector in the constraint space vanish. -/
theorem collar_left_zero {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) {e : Fin n → ℝ} (he : e ∈ Vsub rowOf)
    (hR : a ≤ R) : ∀ x, x < a → nx e (x : ℤ) = 0 := by
  intro x hx
  have h := rowSum_of_memD g he (show x < R by omega)
  unfold BlockSums at h
  rw [g.lnL x hx, st_left g x hx.le] at h
  simpa using h

theorem radical_zero_of_first {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) (C : ℕ) (c : ℝ)
    (hC1 : 1 ≤ C) (hC2 : C + 1 < n) {e : Fin n → ℝ} (he : e ∈ Vsub rowOf)
    (hrad : ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF C c e d = 0)
    {i0 : ℕ} (ha1 : 1 ≤ a) (hia : a + 1 ≤ i0) (hi0b : i0 + b < R) (hC : st i0 = C) (hL : 3 ≤ ln i0)
    (hc : c ≠ 0) (hnl : ((ln i0 : ℝ) - 2) * ((ln i0 : ℝ) + 3) / 6 + 1 / c ≠ 0)
    (h1 : nx e (a : ℤ) = 0) : e = 0 := by
  have hnpos : 0 < n := by omega
  have hb1 : 1 ≤ b ∨ b = 0 := by omega
  have hcastS : ∀ i, (st (i + 1) : ℤ) = (st i : ℤ) + (ln i : ℤ) := by
    intro i; rw [g.stS i]; push_cast; ring
  have hsta : st a = a := st_left g a le_rfl
  have hright : ∀ i, i0 < i → ∀ j, st i + j ≥ C + 3 := by
    intro i hi j
    have h1' := st_monoD g (show i0 + 1 ≤ i by omega)
    have h2 := g.stS i0
    omega
  have hprevln : 2 ≤ ln (i0 - 1) := g.lnI (i0 - 1) (by omega) (by omega)
  have hleft : ∀ i, i + 1 < i0 → ∀ j, j < ln i → st i + j + 2 ≤ C := by
    intro i hi j hj
    have h1' := st_monoD g (show i + 1 ≤ i0 - 1 by omega)
    have h2 := g.stS i
    have h3 := g.stS (i0 - 1)
    have e1 : i0 - 1 + 1 = i0 := by omega
    rw [e1, hC] at h3
    omega
  have hflat_of : ∀ i, i < R → (i0 < i ∨ i + 1 < i0) →
      BlockELs (st i : ℤ) (ln i) (nx e) (rowMu C c e st i) := by
    intro i hi hcase
    apply rowEL_flatD g C c hC1 hC2 hrad hi
    intro j hj
    rcases hcase with h | h
    · have := hright i h j; omega
    · have := hleft i h j hj; omega
  have hsum_of : ∀ i, i < R → BlockSums (st i : ℤ) (ln i) (nx e) := fun i hi => rowSum_of_memD g he hi
  have hcol := collar_left_zero g he (by omega)
  have hz1 : StateZero (nx e) (st a : ℤ) := by
    rw [hsta]
    refine ⟨h1, ?_⟩
    have : nx e ((a : ℤ) - 1) = 0 := by
      have := hcol (a - 1) (by omega)
      have e1 : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
      rw [e1] at this; exact this
    rw [h1, this]; ring
  -- forward step
  have hfwd : ∀ i, a ≤ i → i < R → StateZero (nx e) (st i : ℤ) →
      StateZero (nx e) (st (i + 1) : ℤ) ∧ ∀ j : ℕ, j ≤ ln i → nx e ((st i : ℤ) + j) = 0 := by
    intro i hi1 hiR hz
    by_cases hflat : i0 < i ∨ i + 1 < i0
    · by_cases hint : i + b < R
      · have hL2 := g.lnI i hi1 hint
        have h := blocks_fwd_zero hL2 (hflat_of i hiR hflat) (hsum_of i hiR) hz.1 hz.2
        rw [hcastS i]
        exact ⟨⟨h.2.1, h.2.2.1⟩, fun j hj => h.2.2.2 j hj⟩
      · -- right collar: singleton rows vanish by their row sums
        have hl1 : ln i = 1 := g.lnR i (by omega) hiR
        have hz_i : nx e (st i : ℤ) = 0 := by
          have := hsum_of i hiR
          unfold BlockSums at this
          rw [hl1] at this
          simpa using this
        rw [hcastS i, hl1]
        simp only [Nat.cast_one]
        have hnext : nx e ((st i : ℤ) + 1) = 0 := by
          by_cases hi1R : i + 1 < R
          · have hl1' : ln (i + 1) = 1 := g.lnR (i + 1) (by omega) hi1R
            have := hsum_of (i + 1) hi1R
            unfold BlockSums at this
            rw [hl1'] at this
            have e1 : (st (i + 1) : ℤ) = (st i : ℤ) + 1 := by rw [hcastS i, hl1]; norm_num
            rw [e1] at this
            simpa using this
          · have hiR1 : i + 1 = R := by omega
            have hsR : st (i + 1) = n := by rw [hiR1]; exact g.stR
            have hx : (st i : ℤ) + 1 = (n : ℤ) := by rw [← hsR, hcastS i, hl1]; norm_num
            rw [hx, nx_n e hnpos]
            have hn1 : (n : ℤ) - 1 = (st i : ℤ) := by omega
            rw [hn1]; exact hz_i
        refine ⟨⟨hnext, ?_⟩, ?_⟩
        · have e2 : (st i : ℤ) + 1 - 1 = (st i : ℤ) := by ring
          rw [e2, hnext, hz_i]; ring
        · intro j hj
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
          · simpa using hz_i
          · simpa using hnext
    · by_cases hprev : i + 1 = i0
      · have hi_ln := g.lnI i hi1 (by omega)
        have hel_raw := rowEL_rawD g C c hC1 hC2 hrad hiR
        have hend : st i + ln i = C := by
          have := g.stS i
          rw [hprev, hC] at this
          omega
        have hBE : BlockELs (st i : ℤ) (ln i - 1) (nx e) (rowMu C c e st i) := by
          intro j hj
          have h := hel_raw j (by omega)
          have w1 : Wt C c (((st i + j : ℕ) : ℤ) - 1) = 1 := by unfold Wt; rw [if_neg]; omega
          have w2 : Wt C c ((st i + j : ℕ) : ℤ) = 1 := by unfold Wt; rw [if_neg]; omega
          rw [w1, w2] at h
          push_cast at h
          linarith
        obtain ⟨hm0, hrowz⟩ := prevRow_fwd_zero hi_ln hBE (hsum_of i hiR) hz.1 hz.2
        have hlastEL := hel_raw (ln i - 1) (by omega)
        have hsl : st i + (ln i - 1) = C - 1 := by omega
        rw [hsl] at hlastEL
        have hC1' : ((C - 1 : ℕ) : ℤ) = (C : ℤ) - 1 := by omega
        have w1 : Wt C c (((C - 1 : ℕ) : ℤ) - 1) = 1 := by unfold Wt; rw [if_neg]; omega
        have w2 : Wt C c ((C - 1 : ℕ) : ℤ) = c := by unfold Wt; rw [if_pos]; left; exact hC1'
        rw [w1, w2, hm0] at hlastEL
        have eC1 : nx e ((C : ℤ) - 1) = 0 := by
          have := hrowz (ln i - 1) (by omega)
          have e1 : (st i : ℤ) + ((ln i - 1 : ℕ) : ℤ) = (C : ℤ) - 1 := by omega
          rw [e1] at this; exact this
        have eC2 : nx e ((C : ℤ) - 1 - 1) = 0 := by
          have := hrowz (ln i - 2) (by omega)
          have e1 : (st i : ℤ) + ((ln i - 2 : ℕ) : ℤ) = (C : ℤ) - 1 - 1 := by omega
          rw [e1] at this; exact this
        rw [hC1'] at hlastEL
        have e3 : (C : ℤ) - 1 + 1 = (C : ℤ) := by ring
        rw [e3, eC1, eC2] at hlastEL
        have eCz : nx e (C : ℤ) = 0 := by
          have : c * (nx e (C : ℤ)) = 0 := by linarith
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h hc
          · exact h
        rw [hcastS i]
        have hx : (st i : ℤ) + (ln i : ℤ) = (C : ℤ) := by omega
        rw [hx]
        refine ⟨⟨eCz, by rw [eC1, eCz]; ring⟩, ?_⟩
        intro j hj
        rcases Nat.lt_or_ge j (ln i) with hjl | hjg
        · exact hrowz j hjl
        · have : j = ln i := by omega
          subst this
          rw [hx]; exact eCz
      · have hiL : i = i0 := by omega
        subst hiL
        have hel := rowEL_layerD g C c hC1 hC2 hrad hiR hC hL
        have hsum' : BlockSums (C : ℤ) (ln i) (nx e) := by rw [← hC]; exact hsum_of i hiR
        have hE' : nx e (C : ℤ) = 0 := by rw [← hC]; exact hz.1
        have hF' : nx e (C : ℤ) - nx e ((C : ℤ) - 1) = 0 := by rw [← hC]; exact hz.2
        obtain ⟨_, hrow, hF2⟩ := layer_fwd_zero hL hc hel hsum' hE' hF' hnl
        rw [hcastS i, hC]
        refine ⟨⟨hrow (ln i) le_rfl, hF2⟩, fun j hj => ?_⟩
        exact hrow j hj
  have hfw := chain_fwd_prop (nx e) (fun i => (st i : ℤ)) ln a R (fun i hi hiR hz => hfwd i hi hiR hz) hz1 (R - a) (by omega)
  funext x
  obtain ⟨i, hiR, h1', h2'⟩ := g.cover x.val x.2
  have hx : nx e (x.val : ℤ) = 0 := by
    by_cases hia' : i < a
    · have : x.val < a := by
        have := st_left g (i + 1) (by omega)
        have h3 := g.stS i
        omega
      exact hcol x.val this
    · have hj : x.val - st i ≤ ln i := by omega
      have hcast : (x.val : ℤ) = (st i : ℤ) + ((x.val - st i : ℕ) : ℤ) := by omega
      rw [hcast]
      exact hfw.2 i (by omega) (by omega) _ hj
  have := nx_nat e x.val x.2
  rw [this] at hx
  simpa using hx

#print axioms radical_zero_of_first

end AdalyFormal.CoverOmega
