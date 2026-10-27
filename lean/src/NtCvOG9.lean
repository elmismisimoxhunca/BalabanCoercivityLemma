import NsCvOG8

/-!
# CvOG9 -- `nested_chain_data` (lane omega; fork ncwdh_small_ell_20261018: window of `ell + 1` consecutive `ell²`-rows, hypothesis `ell + 1 ≤ M`)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open AdalyFormal.CoverNested

variable {ell M R : ℕ}

/-- `fat_bounds` for the longer window `j ≤ M` (only `j ≤ M` is used). -/
theorem fat_bounds2 (hg : NGeo ell M R) {j : ℕ} (hjM : j ≤ M) :
    neA ell M R ≤ ell ^ 2 * (u0N M R + j) ∧ ell ^ 2 * (u0N M R + j) < neB ell M R := by
  have hM0 : 0 < M := by have := hg.cRM; exact Nat.pos_of_ne_zero (by intro h0; rw [h0] at this; simp at this)
  have hRM := hg.hell
  unfold u0N neA neB
  constructor
  · nlinarith [Nat.mul_le_mul hRM hRM, Nat.zero_le (ell * ell * (R * M)), Nat.zero_le (ell * ell * M)]
  · have h1 : 1 ≤ R * M := hg.cRM
    nlinarith [Nat.mul_le_mul hRM hRM, Nat.mul_le_mul_left (ell * ell) hjM, Nat.zero_le (ell * ell * (R * M)), Nat.mul_le_mul_left (ell * ell) h1, Nat.mul_le_mul_left (ell * ell) hM0]

theorem fat_reg2b (hg : NGeo ell M R) {j : ℕ} (hjM : j ≤ M) :
    isRowN ell M R 2 (ell ^ 2 * (u0N M R + j)) := by
  simp only [isRowN]
  refine ⟨⟨u0N M R + j, rfl⟩, ?_⟩
  simp only [reg2]
  right
  exact fat_bounds2 hg hjM

theorem fat_rows2 (hg : NGeo ell M R) {W : ℕ} (hW : W ≤ M) {i1 : ℕ} (hi1 : neP0 ell M R + stN ell M R i1 = ell ^ 2 * u0N M R) :
    ∀ j, j ≤ W → neP0 ell M R + stN ell M R (i1 + j) = ell ^ 2 * (u0N M R + j) := by
  intro j
  induction j with
  | zero => intro _; simpa using hi1
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have hreg : isRowN ell M R 2 (neP0 ell M R + stN ell M R (i1 + j)) := by
      rw [h1]; exact fat_reg2b hg (by omega)
    have hl := stN_level2_succ hg hreg
    have e : stN ell M R (i1 + (j + 1)) = stN ell M R (i1 + j) + lnN ell M R (i1 + j) := by
      rw [← Nat.add_assoc]; exact stN_succ _
    have e2 : ell ^ 2 * (u0N M R + (j + 1)) = ell ^ 2 * (u0N M R + j) + ell ^ 2 := by ring
    rw [e, hl]; omega

theorem nested_chain_data (hg : NGeo ell M R) (hM : ell + 1 ≤ M) :
    ∃ i0 i1 K k r : ℕ, R * M + 1 ≤ i0 ∧ i0 + R * M < RN hg ∧ stN ell M R i0 = K + 1 ∧ lnN ell M R i0 = k + 3 ∧
      nN ell M R = (K + 1) + (k + 3) + r ∧ neC ell M R = neP0 ell M R + (K + 1) ∧
      i0 < i1 ∧ i1 + (ell + 1) + R * M < RN hg ∧ (∀ j, j ≤ ell + 1 → lnN ell M R (i1 + j) = ell ^ 2) ∧
      (∀ j, j ≤ ell + 1 → neP0 ell M R + stN ell M R (i1 + j) = ell ^ 2 * (u0N M R + j)) ∧ k + 3 = ell ^ 2 := by
  have hP := hg.hP0P1; have h1 := hg.hP1A; have h2 := hg.hAB'; have h3 := hg.hB'A; have h4 := hg.hAB
  have h5 := hg.hBQ1; have h6 := hg.hQ1Q0
  have hell := hg.hell
  have hlo := layer_lo hg
  have hhi := layer_hi hg
  have hRM : iQ_RN hg = iQ_RN hg := rfl
  -- layer row
  obtain ⟨iC, hiCR, hiC⟩ := hit_C hg
  have hCQ : neC ell M R < neQ0 ell M R := by
    have : neC ell M R + ell ^ 2 ≤ neB' ell M R := hhi
    omega
  have hell2 : 4 ≤ ell ^ 2 := by nlinarith
  have hCreg : isRowN ell M R 2 (neP0 ell M R + stN ell M R iC) := by
    rw [hiC]
    simp only [isRowN]
    exact ⟨layer_dvd hg, by simp only [reg2]; left; exact ⟨hlo, by omega⟩⟩
  have hlnC := stN_level2_succ hg hCreg
  have hstC : stN ell M R iC = neC ell M R - neP0 ell M R := by omega
  -- order facts
  have hiCRN : iC < RN hg := by
    by_contra h
    have : iC = RN hg := by omega
    rw [this, RN_hit hg] at hiC
    omega
  have hQ1C : neC ell M R < neQ1 ell M R := by
    have : neC ell M R + ell ^ 2 ≤ neB' ell M R := hhi
    omega
  have hCiQ : iC < iQ hg := by
    by_contra h
    have := stN_mono hg (show iQ hg ≤ iC by omega)
    have := iQ_hit hg
    omega
  have hai : R * M + 1 ≤ iC := by
    by_contra h
    have := stN_mono hg (show iC ≤ R * M by omega)
    have hl := stN_left hg (R * M) le_rfl
    have := hg.cP
    have : neC ell M R ≥ neA' ell M R := hlo
    omega
  -- window
  have hu0 : ell ^ 2 ∣ ell ^ 2 * u0N M R := dvd_mul_right _ _
  have hMpos : 0 < M := Nat.pos_of_ne_zero (by intro h0; have := hg.cRM; rw [h0] at this; simp at this)
  have hTA : neA ell M R ≤ ell ^ 2 * u0N M R := by
    have := (fat_bounds2 hg (j := 0) (by omega)).1
    simpa using this
  have hTB : ell ^ 2 * (u0N M R + (ell + 1)) < neB ell M R := (fat_bounds2 hg (j := ell + 1) hM).2
  have hTle : ell ^ 2 * u0N M R ≤ ell ^ 2 * (u0N M R + (ell + 1)) := Nat.mul_le_mul_left _ (by omega)
  have hT0 : neP0 ell M R < ell ^ 2 * u0N M R := by omega
  have hTQ : ell ^ 2 * u0N M R ≤ neQ0 ell M R := by omega
  obtain ⟨i1, hi1R, hi1⟩ := hit_aligned2 hg hu0 hT0 hTQ
  have hrows := fat_rows2 hg hM hi1
  refine ⟨iC, i1, neC ell M R - neP0 ell M R - 1, ell ^ 2 - 3, nN ell M R - (neC ell M R - neP0 ell M R) - ell ^ 2, hai, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrows, ?_⟩
  · have := iQ_RN hg; omega
  · omega
  · omega
  · -- n = ...
    have hs := stN_mono hg (show iC + 1 ≤ RN hg by omega)
    rw [stN_succ, hlnC, stN_RN hg] at hs
    omega
  · omega
  · -- i0 < i1
    by_contra h
    have := stN_mono hg (show i1 ≤ iC by omega)
    have : neC ell M R < ell ^ 2 * u0N M R := by omega
    omega
  · -- window inside
    have hlt : i1 + (ell + 1) < iQ hg := by
      by_contra h
      have := stN_mono hg (show iQ hg ≤ i1 + (ell + 1) by omega)
      have h2' := hrows (ell + 1) (by omega)
      have := iQ_hit hg
      omega
    have := iQ_RN hg
    omega
  · intro j hj
    have hreg : isRowN ell M R 2 (neP0 ell M R + stN ell M R (i1 + j)) := by
      rw [hrows j (by omega)]; exact fat_reg2b hg (by omega)
    exact stN_level2_succ hg hreg
  · omega

#print axioms nested_chain_data

end AdalyFormal.CoverOmega
