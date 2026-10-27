import SoE7
import SoE4
import SoC6
import NuE8

/-!
# SoE8 -- the chain of the nested instance for general `ell >= 3` at the decoupled layer: first crossing, null vector, overlap with an aligned-pair defect (lane sites_only_20261019)

Same statement as `NuE8.chain_instance` with: rows of length `ell^2`, layer at `soC ell M R c`, window of four rows at the unit slices `u0N + (ell - 3) + k` (= `neLo + ell - 2 + k`),
so that the pair of slices `(uE, uE+1)` with `uE = u0N + (ell-3) + p`, `p ∈ {0, 2}`, has `uE % ell ∈ {ell - 2, 0}` (both slices inside one `ell`-block).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.NcwdhTwo

section
variable [CfData]
variable {ell M R : ℕ}

/-- numeric bounds of the decoupled layer position. -/
theorem soC_bounds {c : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) :
    neP0 ell M R + ell ^ 2 ≤ soC ell M R c + 1 ∧ neP0 ell M R + 4 ≤ soC ell M R c ∧ soC ell M R c + 10 ≤ neQ0 ell M R ∧
      soC ell M R c + 1 < neB' ell M R := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := SitesOnly.so_vals hell hM hR hrel hc
  have hsucc := soC_succ (ell := ell) (M := M) (R := R) hell hM (by omega : 1 ≤ c)
  have hMe : ell ≤ M := Nat.le_of_dvd hM hdvd
  have h1 : ell * ell ≤ ell * M := Nat.mul_le_mul_left ell hMe
  have hY1 : 0 < ell * M := Nat.mul_pos (by omega) hM
  have h2 : ell * M ≤ ell * (ell * M) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have hcm1 : 1 * (ell * M) ≤ (c - 1) * (ell * M) := Nat.mul_le_mul_right _ (by omega)
  have hsq : ell ^ 2 = ell * ell := pow_two ell
  have h4 : 4 ≤ ell * ell := by nlinarith
  rw [hsq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- the pair defect: `+1` at the first slice of chain row `i1 + p`, `-1` at the first slice of row `i1 + p + 1`. -/
noncomputable def f0pair (hg : NGeo ell M R) (i1 p : ℕ) (hp : i1 + p + 1 < RN hg) : Fin (nN ell M R) → ℝ :=
  (Pi.single ⟨stN ell M R (i1 + p), by
      have := stN_strictMono hg (show i1 + p < RN hg by omega); rw [stN_RN hg] at this; exact this⟩ 1 : Fin (nN ell M R) → ℝ) -
  (Pi.single ⟨stN ell M R (i1 + p + 1), by
      have := stN_strictMono hg (show i1 + p + 1 < RN hg by omega); rw [stN_RN hg] at this; exact this⟩ 1 : Fin (nN ell M R) → ℝ)

theorem BF1_f0pair (hg : NGeo ell M R) (Cc : ℕ) (c : ℝ) (es : Fin (nN ell M R) → ℝ) {i1 p : ℕ} (hp : i1 + p + 1 < RN hg) :
    BF1 Cc c es (f0pair hg i1 p hp) = rowMu1 Cc c es (stN ell M R) (i1 + p) - rowMu1 Cc c es (stN ell M R) (i1 + p + 1) := by
  have h1 : stN ell M R (i1 + p) < nN ell M R := by
    have := stN_strictMono hg (show i1 + p < RN hg by omega); rw [stN_RN hg] at this; exact this
  have h2 : stN ell M R (i1 + p + 1) < nN ell M R := by
    have := stN_strictMono hg (show i1 + p + 1 < RN hg by omega); rw [stN_RN hg] at this; exact this
  unfold f0pair
  rw [sub_eq_add_neg, BF1_add_right]
  have : (-(Pi.single (⟨stN ell M R (i1 + p + 1), h2⟩ : Fin (nN ell M R)) (1 : ℝ)) : Fin (nN ell M R) → ℝ) =
      (-1 : ℝ) • Pi.single (⟨stN ell M R (i1 + p + 1), h2⟩ : Fin (nN ell M R)) (1 : ℝ) := by simp
  rw [this, BF1_smul_right]
  unfold rowMu1
  rw [dif_pos h1, dif_pos h2]
  ring

/-- **the chain of the nested instance for `ell ≥ 3` at the decoupled layer.**  First crossing `cs ∈ (-4/5, 0)` with a nonzero null vector `es` of `qF1` on the constraint space,
`qF1` positive definite above `cs`, and an aligned pair of rows (unit slices `uE, uE + 1`, `uE = u0N + (ell-3) + p`, `p ∈ {0, 2}`) of the window in `Λ` on which the row multipliers of `es` differ. -/
theorem chain_instance_S {c : ℕ} (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) :
    ∃ cs : ℝ, -4 / 5 < cs ∧ cs < 0 ∧
      (∀ e : Fin (nN ell M R) → ℝ, e ∈ Vsub (rowOfN ell M R) → 0 ≤ qF1 (soC ell M R c - neP0 ell M R) cs e) ∧
      (∀ c' : ℝ, cs < c' → c' ≤ 1 → ∀ e : Fin (nN ell M R) → ℝ, e ∈ Vsub (rowOfN ell M R) → e ≠ 0 →
        0 < qF1 (soC ell M R c - neP0 ell M R) c' e) ∧
      ∃ es : Fin (nN ell M R) → ℝ, es ∈ Vsub (rowOfN ell M R) ∧ es ≠ 0 ∧ qF1 (soC ell M R c - neP0 ell M R) cs es = 0 ∧
        ∃ i1 p : ℕ, (p = 0 ∨ p = 2) ∧ R * M ≤ i1 ∧ i1 + 3 + R * M < RN (nGeo_two (by omega : 2 ≤ ell) hdvd hM hR) ∧
          (∀ k, k ≤ 3 → lnN ell M R (i1 + k) = ell ^ 2) ∧
          (∀ k, k ≤ 3 → neP0 ell M R + stN ell M R (i1 + k) = ell ^ 2 * (u0N M R + (ell - 3) + k)) ∧
          ∃ hp : i1 + p + 1 < RN (nGeo_two (by omega : 2 ≤ ell) hdvd hM hR),
            BF1 (soC ell M R c - neP0 ell M R) cs es (f0pair (nGeo_two (by omega : 2 ≤ ell) hdvd hM hR) i1 p hp) ≠ 0 := by
  have hell2 : 2 ≤ ell := by omega
  have hg := nGeo_two hell2 hdvd hM hR
  have hMe : ell ≤ M := Nat.le_of_dvd hM hdvd
  have hX := hg.cRM
  have g := nested_rowGeom hg
  obtain ⟨b1, b2, b3, b4⟩ := soC_bounds hell2 hdvd hM hR hrel hc
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell2 hM hR
  have hsq : ell ^ 2 = ell * ell := pow_two ell
  have hL4 : 4 ≤ ell ^ 2 := by rw [hsq]; nlinarith
  -- layer rows
  obtain ⟨i0, hi0R, hi0st, hi0l0, hi0l1⟩ := layer_rows_so hg hdvd hM hR hrel hc
  set Cc := soC ell M R c - neP0 ell M R with hCc
  have hCc4 : 4 ≤ Cc := by omega
  have hCn : Cc + 1 < nN ell M R := by
    have := (cpos_soC hell2 hM hR hrel hc).hlt
    unfold nN; omega
  have hn10 : (Cc - 4) + 10 ≤ nN ell M R := by unfold nN; omega
  have hst : stN ell M R i0 + ell ^ 2 = (Cc - 4) + 5 := by omega
  have hmem := tvec_mem_Vsub_L g (Cc - 4) (ell ^ 2) hn10 hL4 hi0R hst hi0l0 hi0l1
  have hneg := NcwdhTwo.qF1_tvec_neg (Cc - 4) hn10
  rw [show Cc - 4 + 4 = Cc by omega] at hneg
  obtain ⟨cs, h1, h2, ⟨es, hes, hne, h0⟩, hpsd, hpos, hradall⟩ :=
    chain_crossing1 (rowOfN ell M R) Cc (-4 / 5) (by norm_num) (tvec (Cc - 4) (nN ell M R)) hmem hneg
  have hrad := hradall es hes h0
  have hcsneg : cs < 0 := cs_neg g (ha := by omega) (hb := by omega) Cc hCn hes hne h0
  have hcs0 : cs ≠ 0 := hcsneg.ne
  -- window
  obtain ⟨i1, hlow, hhigh, hln, hpos1⟩ := window_rows_so hg hell3 hMe
  have hTA : neA ell M R ≤ ell ^ 2 * (u0N M R + (ell - 3)) := (fat_bounds hg hMe (j := ell - 3) (by omega)).1
  have hi1 : i0 + 1 < i1 := by
    by_contra hcon
    push Not at hcon
    have hmono := stN_mono hg (show i1 ≤ i0 + 1 by omega)
    have hh := hpos1 0 (by omega)
    simp only [add_zero] at hh
    have hs1 : stN ell M R (i0 + 1) = stN ell M R i0 + ell ^ 2 := by rw [stN_succ, hi0l0]
    have hB'A := hg.hB'A
    omega
  have hover := chain_overlap_L (L := ell ^ 2) (by omega) g Cc cs hcs0 hCn hi0R (by
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

#print axioms chain_instance_S

end AdalyFormal.SitesOnly
