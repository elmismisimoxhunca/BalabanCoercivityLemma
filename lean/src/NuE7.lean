import NuE6
import NuZ1
import NtCvOF11

/-!
# NuE7 -- chain rows at the layer edge and the window of four rows inside `Λ` (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)

section
variable [CfData]
variable {M R : ℕ}

theorem layer_isRow2 (hg : NGeo 2 M R) (hdvd : 2 ∣ M) (hM : 0 < M) :
    isRowN 2 M R 2 (neC0 2 M R + 1) ∧ isRowN 2 M R 2 (neC0 2 M R + 1 - 4) := by
  have hcf := CfData.hcf
  obtain ⟨m, hm⟩ := hdvd
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := vals2 M R
  have hv := neC0_val2 (R := R) hM
  have hK : CfData.cf * M = 2 * (CfData.cf * m) := by rw [hm]; ring
  have hK10 : 10 * M ≤ CfData.cf * M := Nat.mul_le_mul_right _ hcf
  have hX := hg.cRM
  constructor
  · simp only [isRowN, reg2]
    refine ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
  · simp only [isRowN, reg2]
    refine ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩

/-- the two rows around the central layer edge are consecutive rows `i0, i0+1` of the chain. -/
theorem layer_rows2 (hg : NGeo 2 M R) (hdvd : 2 ∣ M) (hM : 0 < M) :
    ∃ i0, i0 + 1 < RN hg ∧ neP0 2 M R + stN 2 M R i0 = neC0 2 M R + 1 - 4 ∧ lnN 2 M R i0 = 4 ∧ lnN 2 M R (i0 + 1) = 4 := by
  obtain ⟨hrow1, hrow0⟩ := layer_isRow2 hg hdvd hM
  obtain ⟨i, hiR, hi1, hi2⟩ := chain_row_of_isRowN hg (j := 2) le_rfl hrow1
  obtain ⟨i', hi'R, hi'1, hi'2⟩ := chain_row_of_isRowN hg (j := 2) le_rfl hrow0
  have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
  rw [h4] at hi2 hi'2
  have hsucc : stN 2 M R (i' + 1) = stN 2 M R i := by
    rw [stN_succ, hi'2]
    have := layer_isRow2 hg hdvd hM
    have hv1 : neC0 2 M R + 1 ≥ 4 := by
      have := neC0_val2 (R := R) hM; have := hg.cRM; omega
    omega
  have hii : i' + 1 = i := stN_inj hg hsucc
  refine ⟨i', by omega, hi'1, hi'2, ?_⟩
  rw [hii]; exact hi2


theorem win_isRow2 (hg : NGeo 2 M R) (hM4 : 4 ≤ M) {k : ℕ} (hk : k ≤ 3) :
    isRowN 2 M R 2 (4 * (neLo M R + k)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := vals2 M R
  have hX := hg.cRM
  simp only [isRowN, reg2]
  refine ⟨by norm_num, Or.inr ⟨by omega, by omega⟩⟩

/-- four consecutive length-4 rows at the unit slices `lo, .., lo+3` of `Λ`, away from the collars. -/
theorem window_rows2 (hg : NGeo 2 M R) (hM4 : 4 ≤ M) :
    ∃ i1, R * M ≤ i1 ∧ i1 + 3 + R * M < RN hg ∧ (∀ k, k ≤ 3 → lnN 2 M R (i1 + k) = 4) ∧
      (∀ k, k ≤ 3 → neP0 2 M R + stN 2 M R (i1 + k) = 4 * (neLo M R + k)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := vals2 M R
  have hX := hg.cRM
  have hT0 : neP0 2 M R < 4 * neLo M R := by omega
  have hTQ : 4 * neLo M R ≤ neQ0 2 M R := by omega
  obtain ⟨i1, hi1R, hi1⟩ := hit_aligned2 hg (T := 4 * neLo M R) (by norm_num) hT0 hTQ
  have hrows : ∀ k, k ≤ 4 → neP0 2 M R + stN 2 M R (i1 + k) = 4 * (neLo M R + k) := by
    intro k
    induction k with
    | zero => intro _; simpa using hi1
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hreg : isRowN 2 M R 2 (neP0 2 M R + stN 2 M R (i1 + k)) := by
        rw [h1]; exact win_isRow2 hg hM4 (by omega)
      have hl := stN_level2_succ hg hreg
      have e : stN 2 M R (i1 + (k + 1)) = stN 2 M R (i1 + k) + lnN 2 M R (i1 + k) := by
        rw [← Nat.add_assoc]; exact stN_succ _
      have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
      rw [h4] at hl
      rw [e, hl]; omega
  have hln : ∀ k, k ≤ 3 → lnN 2 M R (i1 + k) = 4 := by
    intro k hk
    have hreg : isRowN 2 M R 2 (neP0 2 M R + stN 2 M R (i1 + k)) := by
      rw [hrows k (by omega)]; exact win_isRow2 hg hM4 hk
    have hl := stN_level2_succ hg hreg
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rwa [h4] at hl
  have hlt : i1 < RN hg := by
    rcases Nat.lt_or_ge i1 (RN hg) with h | h
    · exact h
    · have : i1 = RN hg := le_antisymm hi1R h
      rw [this, RN_hit hg] at hi1
      omega
  have hlowc : R * M ≤ i1 := by
    by_contra hcon
    push Not at hcon
    have := stN_left hg i1 hcon.le
    omega
  have hiQ : i1 + 3 < iQ hg := by
    by_contra hcon
    push Not at hcon
    have h1 := stN_mono hg hcon
    have h2 := iQ_hit hg
    have h3 := hrows 3 (by omega)
    omega
  refine ⟨i1, hlowc, ?_, hln, fun k hk => hrows k (by omega)⟩
  have := iQ_RN hg
  omega

end

end AdalyFormal.NcwdhTwo
