import CvOK3
import CvK4

/-!
# CvOK4 -- a radical vector with zero state at a window row vanishes; the multipliers on a flat window cannot vanish on two rows (relaxed rows) (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open Finset
open AdalyFormal.CoverJacobi

variable {n a b : ℕ}

theorem st_add_windowD {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) (i1 Lw N : ℕ)
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

/-- zero state at row `i1 > i0` forces the radical vector to vanish. -/
theorem radical_zero_of_state {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) (C : ℕ) (c : ℝ)
    (hC1 : 1 ≤ C) (hC2 : C + 1 < n) {e : Fin n → ℝ} (he : e ∈ Vsub rowOf)
    (hrad : ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF C c e d = 0)
    {i0 : ℕ} (ha1 : 1 ≤ a) (hia : a + 1 ≤ i0) (hC : st i0 = C) (hL : 3 ≤ ln i0)
    (hc : c ≠ 0) (hnl : ((ln i0 : ℝ) - 2) * ((ln i0 : ℝ) + 3) / 6 + 1 / c ≠ 0)
    {i1 : ℕ} (hi1 : i0 < i1) (hi1b : i1 + b < R) (hz0 : StateZero (nx e) (st i1 : ℤ)) : e = 0 := by
  have hnpos : 0 < n := by omega
  have hi1R : i1 < R := by omega
  have hi0R : i0 + 1 < R := by omega
  have hcastS : ∀ i, (st (i + 1) : ℤ) = (st i : ℤ) + (ln i : ℤ) := by
    intro i; rw [g.stS i]; push_cast; ring
  have hcol := collar_left_zero g he (show a ≤ R by omega)
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
  -- backward step
  have hback : ∀ i, i < i1 → StateZero (nx e) (st (i + 1) : ℤ) →
      StateZero (nx e) (st i : ℤ) ∧ ∀ j : ℕ, j ≤ ln i → nx e ((st i : ℤ) + j) = 0 := by
    intro i hi hz
    have hiR : i < R := by omega
    rw [hcastS i] at hz
    obtain ⟨hE, hF⟩ := hz
    by_cases hi0' : i < a
    · have hl1 : ln i = 1 := g.lnL i hi0'
      have hsi : st i = i := st_left g i hi0'.le
      have hzi : nx e (i : ℤ) = 0 := hcol i hi0'
      rw [hl1, hsi] at hE hF ⊢
      simp only [Nat.cast_one] at hE hF ⊢
      refine ⟨⟨hzi, ?_⟩, ?_⟩
      · by_cases hi00 : i = 0
        · subst hi00
          rw [show ((0 : ℕ) : ℤ) - 1 = -1 by norm_num, nx_neg_one e hnpos]
          simp only [Nat.cast_zero] at hzi ⊢
          rw [hzi]; ring
        · have := hcol (i - 1) (by omega)
          have e1 : ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 := by omega
          rw [e1] at this
          rw [hzi, this]; ring
      · intro j hj
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
        · simpa using hzi
        · simpa using hE
    · have hi1' : a ≤ i := by omega
      have hL2 := g.lnI i hi1' (by omega)
      by_cases hflat : i0 < i ∨ i + 1 < i0
      · have h := blocks_back_zero hL2 (hflat_of i hiR hflat) (hsum_of i hiR) hE hF
        exact ⟨⟨h.2.1, h.2.2.1⟩, fun j hj => h.2.2.2 j hj⟩
      · by_cases hi_eq : i = i0
        · subst hi_eq
          have hel := rowEL_layerD g C c hC1 hC2 hrad hiR hC hL
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
            have e2 : (st i : ℤ) + (ln i : ℤ) = (C : ℤ) := by rw [← hcastS i, hi_prev, hC]
            rw [e2] at hE hF
            exact ⟨hE, hF⟩
          have hel : BlockELs (st i : ℤ) (ln i) (nx e) (rowMu C c e st i) := by
            have := rowEL_prevD g C c hC1 hC2 hrad (show i0 < R by omega) (by omega) hC hz'
            have e1 : i0 - 1 = i := by omega
            rw [e1] at this
            exact this
          have h := blocks_back_zero hL2 hel (hsum_of i hiR) hE hF
          exact ⟨⟨h.2.1, h.2.2.1⟩, fun j hj => h.2.2.2 j hj⟩
  -- forward step
  have hfwd : ∀ i, i1 ≤ i → i < R → StateZero (nx e) (st i : ℤ) →
      StateZero (nx e) (st (i + 1) : ℤ) ∧ ∀ j : ℕ, j ≤ ln i → nx e ((st i : ℤ) + j) = 0 := by
    intro i hi hiR hz
    have hfl : i0 < i ∨ i + 1 < i0 := Or.inl (by omega)
    by_cases hint : i + b < R
    · have hL2 := g.lnI i (by omega) hint
      have h := blocks_fwd_zero hL2 (hflat_of i hiR hfl) (hsum_of i hiR) hz.1 hz.2
      rw [hcastS i]
      exact ⟨⟨h.2.1, h.2.2.1⟩, fun j hj => h.2.2.2 j hj⟩
    · have hl1 : ln i = 1 := g.lnR i (by omega) hiR
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
  have hbk := chain_back_prop (nx e) (fun i => (st i : ℤ)) ln i1 hback hz0 i1 le_rfl
  have hfw := chain_fwd_prop (nx e) (fun i => (st i : ℤ)) ln i1 R hfwd hz0 (R - i1) (by omega)
  funext x
  obtain ⟨i, hiR, h1', h2'⟩ := g.cover x.val x.2
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

#print axioms radical_zero_of_state

end AdalyFormal.CoverOmega
