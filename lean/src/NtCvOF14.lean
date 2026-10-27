import NtCvOF13
import NtCvOG9
import NsCvOK8
import NtWin1

/-!
# CvOF14 -- the Z-chain at the nested instance: crossing `cs`, window index `p ∈ {0, ell}` (window of `ell+1` rows; `NtWin1.seq_pair_ne`), saddles with `qF_c < M0` (lane omega; fork ncwdh_small_ell_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.StatementLane (scaleUp)

variable {ell M R : ℕ}

theorem nested_Zchain (hg : NGeo ell M R) (hell3 : 3 ≤ ell) (hMe : ell + 1 ≤ M) :
    ∃ cs : ℝ, -1 < cs ∧ cs < 1 ∧ IsCrossingN ell M R cs ∧ ∃ i1 p : ℕ, p + 1 ≤ ell + 1 ∧ (p = 0 ∨ p = ell) ∧ i1 + (ell + 1) + R * M < RN hg ∧
      (∀ j, j ≤ ell + 1 → neP0 ell M R + stN ell M R (i1 + j) = ell ^ 2 * (u0N M R + j)) ∧
      (∀ j, j ≤ ell + 1 → lnN ell M R (i1 + j) = ell ^ 2) ∧
      ∀ M0 : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, cs < c → c < cs + ε → c ≤ 1 →
        ∃ e : Fin (nN ell M R) → ℝ,
          (∀ d : Fin (nN ell M R) → ℝ, d ∈ Vsub (rowOfN ell M R) → BF (neC ell M R - neP0 ell M R) c e d = 0) ∧
          (∀ j, j ≤ 2 → ∀ r, isRowN ell M R j r →
            fSum ell j (fe (neP0 ell M R) e) r = (ell : ℝ) ^ j * rhoY ell (gU M R p) j r) ∧
          qF (neC ell M R - neP0 ell M R) c e < M0 := by
  obtain ⟨i0, i1, K, k, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := nested_chain_data hg hMe
  have G := nested_rowGeom hg
  have hRM := hg.cRM
  have hCK : neC ell M R - neP0 ell M R = K + 1 := by omega
  rw [hCK]
  obtain ⟨cs, hcs1, hcs2, hcs0, es, hes, hne, h0, hpsd, hpos, hradE, hker, hwin⟩ :=
    chain_poleD G (i0 := i0) (K := K) (k := k) (r := r) hRM hRM (by omega) (by omega) h3 h4 h5 (i1 := i1) (N := ell + 1) (Lw := ell ^ 2)
      h7 (by omega) h8 h9
  have hcsm1 : -1 < cs := lt_of_le_of_lt (cLoc_ge k) hcs1
  have hcross : IsCrossingN ell M R cs := by
    simp only [IsCrossingN, hCK]
    exact ⟨hcs2, ⟨es, hes, hne, h0⟩, hpsd, hpos⟩
  -- the window multipliers: a 3-term recurrence forces one of the two windows (0,1), (ell,ell+1) to have different values
  have hrec := chain_window_rec G (K + 1) cs (by omega) (by omega) hes hradE h3 (by omega) h7 h8 h9 (by nlinarith)
  have hell2 : 9 ≤ ell ^ 2 := by nlinarith
  have hτ : 2 < (4 * ((ell ^ 2 : ℕ) : ℝ) ^ 2 + 2) / (((ell ^ 2 : ℕ) : ℝ) ^ 2 - 1) := by
    have : (9 : ℝ) ≤ ((ell ^ 2 : ℕ) : ℝ) := by exact_mod_cast hell2
    rw [lt_div_iff₀ (by nlinarith)]
    nlinarith
  obtain ⟨p, hp1, hp2, hpne⟩ : ∃ p : ℕ, p + 1 ≤ ell + 1 ∧ (p = 0 ∨ p = ell) ∧
      rowMu (K + 1) cs es (stN ell M R) (i1 + p) ≠ rowMu (K + 1) cs es (stN ell M R) (i1 + p + 1) := by
    by_contra hcon
    push_neg at hcon
    have e0 := hcon 0 (by omega) (Or.inl rfl)
    have e1 := hcon ell (by omega) (Or.inr rfl)
    have hz := AdalyFormal.CoverOmega.Win.seq_pair_ne ((4 * ((ell ^ 2 : ℕ) : ℝ) ^ 2 + 2) / (((ell ^ 2 : ℕ) : ℝ) ^ 2 - 1)) hτ
      (fun k => rowMu (K + 1) cs es (stN ell M R) (i1 + k)) ell (by omega)
      (fun k hk => by
        have := hrec k hk
        rw [neg_div] at this
        simpa [add_assoc] using this)
      (by simpa using e0) (by simpa [add_assoc] using e1)
    exact hwin 0 1 (by omega) (by omega) ⟨by simpa using hz.1, by simpa using hz.2⟩
  have hp8 : i1 + p + 1 < RN hg := by omega
  have hP : BF (K + 1) cs (f0N ell M R i1 p) es ≠ 0 := by
    rw [BF_f0N hg _ _ _ hp8]
    have : (0 : ℝ) < (ell : ℝ) ^ 2 := by positivity
    exact mul_ne_zero this.ne' (sub_ne_zero.mpr hpne)
  have hV0 : ∀ c : ℝ, cs < c → c ≤ 1 → ∀ d : Fin (nN ell M R) → ℝ, d ∈ Vsub (rowOfN ell M R) → 0 ≤ qF (K + 1) c d := by
    intro c hc1 hc2 d hd
    by_cases hd0 : d = 0
    · subst hd0; simp [qF, bF, dlt, ex]; exact Finset.sum_nonneg (fun y _ => sq_nonneg _)
    · exact (hpos c hc1 hc2 d hd hd0).le
  have hbF : 0 < bF (K + 1) es := by
    have hc : cs < (cs + 1) / 2 := by linarith
    have := hpos ((cs + 1) / 2) hc (by linarith) es hes hne
    rw [qF_affine (K + 1) ((cs + 1) / 2) cs es, h0] at this
    have h2 : 0 < ((cs + 1) / 2 - cs) := by linarith
    by_contra hb
    have : bF (K + 1) es ≤ 0 := not_lt.mp hb
    nlinarith
  refine ⟨cs, hcsm1, hcs2, hcross, i1, p, hp1, hp2, h8, h10, h9, fun M0 => ?_⟩
  obtain ⟨ε, hε, hbl⟩ := blowup_bound (K + 1) (Vsub (rowOfN ell M R)) cs es (f0N ell M R i1 p) hes hcsm1.le h0 hbF hP hV0 M0
  refine ⟨ε, hε, fun c hc1 hc2 hc3 => ?_⟩
  obtain ⟨e, he1, he2⟩ := exists_saddle (K + 1) c (Vsub (rowOfN ell M R)) (fun d hd hd0 => hpos c hc1 hc3 d hd hd0) (f0N ell M R i1 p)
  exact ⟨e, he2, hS_nested hg h8 h10 h9 hp1 e he1, hbl c hc1 hc2 hc3 e he1 he2⟩

#print axioms nested_Zchain

end AdalyFormal.CoverOmega
