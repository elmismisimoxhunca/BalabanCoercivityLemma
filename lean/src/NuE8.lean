import NuE7
import NuC6

/-!
# NuE8 -- the chain of the nested instance at `ell = 2`: first crossing, null vector, overlap with an aligned-pair defect (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)

section
variable [CfData]
variable {M R : ℕ}

/-- the pair defect: `+1` at the first slice of chain row `i1 + p`, `-1` at the first slice of row `i1 + p + 1`. -/
noncomputable def f0pair (hg : NGeo 2 M R) (i1 p : ℕ) (hp : i1 + p + 1 < RN hg) : Fin (nN 2 M R) → ℝ :=
  (Pi.single ⟨stN 2 M R (i1 + p), by
      have := stN_strictMono hg (show i1 + p < RN hg by omega); rw [stN_RN hg] at this; exact this⟩ 1 : Fin (nN 2 M R) → ℝ) -
  (Pi.single ⟨stN 2 M R (i1 + p + 1), by
      have := stN_strictMono hg (show i1 + p + 1 < RN hg by omega); rw [stN_RN hg] at this; exact this⟩ 1 : Fin (nN 2 M R) → ℝ)

theorem BF1_f0pair (hg : NGeo 2 M R) (Cc : ℕ) (c : ℝ) (es : Fin (nN 2 M R) → ℝ) {i1 p : ℕ} (hp : i1 + p + 1 < RN hg) :
    BF1 Cc c es (f0pair hg i1 p hp) = rowMu1 Cc c es (stN 2 M R) (i1 + p) - rowMu1 Cc c es (stN 2 M R) (i1 + p + 1) := by
  have h1 : stN 2 M R (i1 + p) < nN 2 M R := by
    have := stN_strictMono hg (show i1 + p < RN hg by omega); rw [stN_RN hg] at this; exact this
  have h2 : stN 2 M R (i1 + p + 1) < nN 2 M R := by
    have := stN_strictMono hg (show i1 + p + 1 < RN hg by omega); rw [stN_RN hg] at this; exact this
  unfold f0pair
  rw [sub_eq_add_neg, BF1_add_right]
  have : (-(Pi.single (⟨stN 2 M R (i1 + p + 1), h2⟩ : Fin (nN 2 M R)) (1 : ℝ)) : Fin (nN 2 M R) → ℝ) =
      (-1 : ℝ) • Pi.single (⟨stN 2 M R (i1 + p + 1), h2⟩ : Fin (nN 2 M R)) (1 : ℝ) := by simp
  rw [this, BF1_smul_right]
  unfold rowMu1
  rw [dif_pos h1, dif_pos h2]
  ring

/-- **the chain of the nested instance at `ell = 2`.**  There is a first crossing `cs ∈ (-4/5, 0)` with a nonzero null vector `es` of `qF1` on the constraint space,
`qF1` positive definite above `cs`, and an aligned pair of rows (unit slices `lo + p, lo + p + 1`, `p ∈ {0, 2}`, `lo` even) of the window in `Λ` on which the
row multipliers of `es` differ. -/
theorem chain_instance (hdvd : 2 ∣ M) (hM4 : 4 ≤ M) (hR : 1 ≤ R) :
    ∃ cs : ℝ, -4 / 5 < cs ∧ cs < 0 ∧
      (∀ e : Fin (nN 2 M R) → ℝ, e ∈ Vsub (rowOfN 2 M R) → 0 ≤ qF1 (neC0 2 M R - neP0 2 M R) cs e) ∧
      (∀ c : ℝ, cs < c → c ≤ 1 → ∀ e : Fin (nN 2 M R) → ℝ, e ∈ Vsub (rowOfN 2 M R) → e ≠ 0 →
        0 < qF1 (neC0 2 M R - neP0 2 M R) c e) ∧
      ∃ es : Fin (nN 2 M R) → ℝ, es ∈ Vsub (rowOfN 2 M R) ∧ es ≠ 0 ∧ qF1 (neC0 2 M R - neP0 2 M R) cs es = 0 ∧
        ∃ i1 p : ℕ, (p = 0 ∨ p = 2) ∧ R * M ≤ i1 ∧ i1 + 3 + R * M < RN (nGeo_two (le_refl 2) hdvd (by omega) hR) ∧
          (∀ k, k ≤ 3 → lnN 2 M R (i1 + k) = 4) ∧ (∀ k, k ≤ 3 → neP0 2 M R + stN 2 M R (i1 + k) = 4 * (neLo M R + k)) ∧
          ∃ hp : i1 + p + 1 < RN (nGeo_two (le_refl 2) hdvd (by omega) hR),
            BF1 (neC0 2 M R - neP0 2 M R) cs es (f0pair (nGeo_two (le_refl 2) hdvd (by omega) hR) i1 p hp) ≠ 0 := by
  have hM : 0 < M := by omega
  have hg := nGeo_two (le_refl 2) hdvd hM hR
  have hcf := CfData.hcf
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := vals2 M R
  have hv := neC0_val2 (R := R) hM
  have hX := hg.cRM
  have hK10 : 10 * M ≤ CfData.cf * M := Nat.mul_le_mul_right _ hcf
  have hR1 : M ≤ R * M := Nat.le_mul_of_pos_left _ hR
  have g := nested_rowGeom hg
  -- layer rows
  obtain ⟨i0, hi0R, hi0st, hi0l0, hi0l1⟩ := layer_rows2 hg hdvd hM
  set Cc := neC0 2 M R - neP0 2 M R with hCc
  have hCc4 : 4 ≤ Cc := by omega
  have hCn : Cc + 1 < nN 2 M R := by unfold nN; omega
  have hn10 : (Cc - 4) + 10 ≤ nN 2 M R := by unfold nN; omega
  have hst : stN 2 M R i0 = (Cc - 4) + 1 := by omega
  have hmem := tvec_mem_Vsub g (Cc - 4) hn10 hi0R hst hi0l0 hi0l1
  have hneg := qF1_tvec_neg (Cc - 4) hn10
  rw [show Cc - 4 + 4 = Cc by omega] at hneg
  obtain ⟨cs, h1, h2, ⟨es, hes, hne, h0⟩, hpsd, hpos, hradall⟩ :=
    chain_crossing1 (rowOfN 2 M R) Cc (-4 / 5) (by norm_num) (tvec (Cc - 4) (nN 2 M R)) hmem hneg
  have hrad := hradall es hes h0
  have hcsneg : cs < 0 := cs_neg g (ha := by omega) (hb := by omega) Cc hCn hes hne h0
  have hcs0 : cs ≠ 0 := hcsneg.ne
  -- window
  obtain ⟨i1, hlow, hhigh, hln, hpos1⟩ := window_rows2 hg hM4
  have hi1 : i0 + 1 < i1 := by
    by_contra hcon
    push Not at hcon
    have hmono := stN_mono hg (show i1 ≤ i0 + 1 by omega)
    have hh := hpos1 0 (by omega)
    simp only [add_zero] at hh
    have hs1 : stN 2 M R (i0 + 1) = stN 2 M R i0 + 4 := by rw [stN_succ, hi0l0]
    have hv1 : neC0 2 M R + 1 ≥ 4 := by omega
    omega
  have hover := chain_overlap g Cc cs hcs0 hCn hi0R (by
    have := hi0st; have := hi0l0; omega) hes hne hrad hi1 (by omega) (by omega) hln
  refine ⟨cs, h1, hcsneg, hpsd, hpos, es, hes, hne, h0, i1, ?_⟩
  rcases hover with hov | hov
  · refine ⟨0, Or.inl rfl, hlow, hhigh, hln, hpos1, ?_⟩
    have hp : i1 + 0 + 1 < RN hg := by omega
    refine ⟨hp, ?_⟩
    rw [BF1_f0pair hg Cc cs es hp]
    intro hz
    apply hov
    simpa using sub_eq_zero.mp hz
  · refine ⟨2, Or.inr rfl, hlow, hhigh, hln, hpos1, ?_⟩
    have hp : i1 + 2 + 1 < RN hg := by omega
    refine ⟨hp, ?_⟩
    rw [BF1_f0pair hg Cc cs es hp]
    intro hz
    apply hov
    have := sub_eq_zero.mp hz
    simpa [Nat.add_assoc] using this

end

end AdalyFormal.NcwdhTwo
