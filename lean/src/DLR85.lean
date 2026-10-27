import DLR84

/-!
# DL85 -- numerics, part 1: explicit bounds on the derived constants of the SITE and `Γ` Combes–Thomas structures

Generic (any `SiteHyp`/`GamHyp` whose numeric fields satisfy the stated bounds), at the FIXED weight slope `θ = θ₀ = 10⁻⁴⁵`:
`SiteSmall H θ` : `1/7 ≤ c ≤ 1/6`, `δD ≤ 2θ`, `δQ ≤ 4θ`, `m = 1`;  `GamSmall G θ` : site small, `q = 1`, `cG ≥ 4.5·10⁻¹¹`.
Bounds: `K0 ≤ 270θ`, `K1 ≤ 90θ`, `epsX ≤ 2200θ`, `epsDX ≤ 720θ`; `nX ≤ 7.01`, `nDX ≤ 2.66`, `kF ≤ 2.68`, `dF ≤ 740θ`,
`gi ≤ 2.23·10¹⁰`, `dGam ≤ 31000θ`, `dGi ≤ 1.55·10²⁵θ`, `dT ≤ 3·10²⁶θ`, `kZ ≤ 1.2·10¹³`, `kDZ ≤ 3.9·10¹²`, `dZ ≤ 2.1·10²⁷θ`,
`dDZ ≤ 8·10²⁶θ`, `dW ≤ 8.1·10²⁶θ`.  (Exploration: num/numchoice.py; nothing there is a premise.)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.DLayer

/-- the fixed Combes–Thomas slope of the witness -/
local notation "θ₀" => ((1 : ℝ) / 10 ^ 45)

theorem sqrt_le_of (x y : ℝ) (hy : 0 ≤ y) (h : x ≤ y ^ 2) : Real.sqrt x ≤ y := by
  rw [show y = Real.sqrt (y ^ 2) from (Real.sqrt_sq hy).symm]; exact Real.sqrt_le_sqrt h

/-- the small-parameter regime of a site structure -/
structure SiteSmall {S E Y : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] (H : SiteHyp S E Y) : Prop where
  hc1 : 1 / 7 ≤ H.c
  hc2 : H.c ≤ 1 / 6
  hD : H.δD ≤ 2 * θ₀
  hQ : H.δQ ≤ 4 * θ₀
  hm : H.m = 1

namespace SiteSmall
variable {S E Y : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] {H : SiteHyp S E Y} (h : SiteSmall H)
include h

theorem cpos : 0 < H.c := lt_of_lt_of_le (by norm_num) h.hc1
theorem inv_c : 1 / H.c ≤ 7 := by
  rw [div_le_iff₀ h.cpos]; linarith [h.hc1]
theorem sqrt48 : Real.sqrt (48 / H.c) ≤ 18.4 := by
  refine sqrt_le_of _ _ (by norm_num) ?_
  rw [div_le_iff₀ h.cpos]; nlinarith [h.hc1]
theorem sqrt12 : Real.sqrt (12 / H.c) ≤ 9.2 := by
  refine sqrt_le_of _ _ (by norm_num) ?_
  rw [div_le_iff₀ h.cpos]; nlinarith [h.hc1]
theorem sqrtc_ge : 0.377 ≤ Real.sqrt H.c := by
  rw [show (0.377 : ℝ) = Real.sqrt (0.377 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by nlinarith [h.hc1])
theorem inv_sqrtc : 1 / Real.sqrt H.c ≤ 2.66 := by
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) h.sqrtc_ge)]; nlinarith [h.sqrtc_ge]

theorem K0_le : H.K0 1 ≤ 270 * θ₀ := by
  unfold SiteHyp.K0
  rw [h.hm]
  have hD0 := H.hδD; have hQ0 := H.hδQ
  have h1 : Real.sqrt (48 / H.c) * H.δD ≤ 18.4 * (2 * θ₀) :=
    mul_le_mul h.sqrt48 h.hD hD0 (by norm_num)
  have h8 : 8 / H.c ≤ 56 := by have := h.inv_c; rw [div_le_iff₀ h.cpos] at this ⊢; linarith
  have h4 : 4 / H.c ≤ 28 := by have := h.inv_c; rw [div_le_iff₀ h.cpos] at this ⊢; linarith
  have hD2 : H.δD ^ 2 ≤ (2 * θ₀) ^ 2 := pow_le_pow_left₀ hD0 h.hD 2
  have hQ2 : H.δQ ^ 2 ≤ (4 * θ₀) ^ 2 := pow_le_pow_left₀ hQ0 h.hQ 2
  have h2 : 8 / H.c * H.δD ^ 2 ≤ 56 * (2 * θ₀) ^ 2 := mul_le_mul h8 hD2 (sq_nonneg _) (by norm_num)
  have h3 : 4 / H.c * 1 * (2 * 1 * H.δQ + H.δQ ^ 2) ≤ 28 * (2 * (4 * θ₀) + (4 * θ₀) ^ 2) := by
    rw [mul_one]
    refine mul_le_mul h4 ?_ (by positivity) (by norm_num)
    nlinarith [mul_le_mul h.hQ h.hQ hQ0 (by norm_num)]
  nlinarith

theorem K1_le : H.K1 1 ≤ 90 * θ₀ := by
  unfold SiteHyp.K1
  rw [h.hm]
  have hD0 := H.hδD; have hQ0 := H.hδQ
  have hs24 : Real.sqrt 24 ≤ 4.9 := sqrt_le_of _ _ (by norm_num) (by norm_num)
  have h1 : Real.sqrt 24 * H.δD ≤ 4.9 * (2 * θ₀) := mul_le_mul hs24 h.hD hD0 (by norm_num)
  have hD2 : H.δD ^ 2 ≤ (2 * θ₀) ^ 2 := pow_le_pow_left₀ hD0 h.hD 2
  have h2 : 2 * Real.sqrt (12 / H.c) * H.δD ^ 2 ≤ 2 * 9.2 * (2 * θ₀) ^ 2 := by
    have := mul_le_mul h.sqrt12 hD2 (sq_nonneg _) (by norm_num); nlinarith
  have h3 : Real.sqrt (12 / H.c) * 1 * (2 * 1 * H.δQ + H.δQ ^ 2) ≤ 9.2 * (2 * (4 * θ₀) + (4 * θ₀) ^ 2) := by
    rw [mul_one]
    refine mul_le_mul h.sqrt12 ?_ (by positivity) (by norm_num)
    nlinarith [mul_le_mul h.hQ h.hQ hQ0 (by norm_num)]
  nlinarith

theorem epsX_le : H.epsX 1 ≤ 2200 * θ₀ := by
  unfold SiteHyp.epsX
  have hD0 := H.hδD; have hQ0 := H.hδQ
  have h4 : 4 / H.c ≤ 28 := by have := h.inv_c; rw [div_le_iff₀ h.cpos] at this ⊢; linarith
  have hqc : 1 / Real.sqrt H.c ≤ 2.66 := h.inv_sqrtc
  have hqc' : 1 / H.c ≤ 7 := h.inv_c
  have hK := h.K0_le
  have hK0 := H.K0_nonneg 1 zero_le_one
  have t1 : 4 / H.c * H.δQ ≤ 28 * (4 * θ₀) := mul_le_mul h4 h.hQ hQ0 (by norm_num)
  have t2 : 4 / H.c * H.δD * (1 / Real.sqrt H.c) ≤ 28 * (2 * θ₀) * 2.66 :=
    mul_le_mul (mul_le_mul h4 h.hD hD0 (by norm_num)) hqc (by positivity) (by positivity)
  have t3 : H.K0 1 * (1 / H.c) ≤ 270 * θ₀ * 7 := mul_le_mul hK hqc' (div_nonneg zero_le_one h.cpos.le) (by positivity)
  nlinarith

theorem epsDX_le : H.epsDX 1 ≤ 720 * θ₀ := by
  unfold SiteHyp.epsDX
  have hD0 := H.hδD; have hQ0 := H.hδQ
  have hqc : 1 / Real.sqrt H.c ≤ 2.66 := h.inv_sqrtc
  have hqc' : 1 / H.c ≤ 7 := h.inv_c
  have hK := h.K1_le
  have hK0 := H.K1_nonneg 1 zero_le_one
  have t1 : Real.sqrt (12 / H.c) * H.δQ ≤ 9.2 * (4 * θ₀) := mul_le_mul h.sqrt12 h.hQ hQ0 (by norm_num)
  have t2 : Real.sqrt (12 / H.c) * H.δD * (1 / Real.sqrt H.c) ≤ 9.2 * (2 * θ₀) * 2.66 :=
    mul_le_mul (mul_le_mul h.sqrt12 h.hD hD0 (by norm_num)) hqc (by positivity) (by positivity)
  have t3 : H.K1 1 * (1 / H.c) ≤ 90 * θ₀ * 7 := mul_le_mul hK hqc' (div_nonneg zero_le_one h.cpos.le) (by positivity)
  nlinarith

end SiteSmall

/-- the small-parameter regime of a `Γ` structure -/
structure GamSmall {S E Y : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] (G : GamHyp S E Y) : Prop where
  site : SiteSmall G.toSiteHyp
  hq : G.q = 1
  hcG : 4.5e-11 ≤ G.cG

namespace GamSmall
variable {S E Y : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] {G : GamHyp S E Y} (h : GamSmall G)
include h

theorem eX : G.H.epsX G.q ≤ 2200 * θ₀ := by rw [h.hq]; exact h.site.epsX_le
theorem eDX : G.H.epsDX G.q ≤ 720 * θ₀ := by rw [h.hq]; exact h.site.epsDX_le
theorem eX0 : 0 ≤ G.H.epsX G.q := G.H.epsX_nonneg G.q G.hq
theorem eDX0 : 0 ≤ G.H.epsDX G.q := by
  unfold SiteHyp.epsDX
  exact add_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) G.hδQ)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) G.hδD) (div_nonneg G.hq (Real.sqrt_nonneg _))))
    (mul_nonneg (G.H.K1_nonneg G.q G.hq) (div_nonneg G.hq G.hc.le))
theorem qc : G.q / G.c ≤ 7 := by rw [h.hq]; exact h.site.inv_c
theorem qsc : G.q / Real.sqrt G.c ≤ 2.66 := by rw [h.hq]; exact h.site.inv_sqrtc

theorem nX_le : G.nX ≤ 7.01 := by
  unfold GamHyp.nX
  have := h.qc; have := h.eX;
  nlinarith
theorem nDX_le : G.nDX ≤ 2.67 := by
  unfold GamHyp.nDX
  have := h.qsc; have := h.eDX;
  nlinarith
theorem kF_le : G.kF ≤ 2.68 := by
  unfold GamHyp.kF
  have h1 := h.nDX_le; have h2 := h.nX_le; have hD := h.site.hD;
  have h3 : G.δD * G.nX ≤ (2 * θ₀) * 7.01 :=
    mul_le_mul hD h2 (G.consts_nonneg.1) (by positivity)
  nlinarith
theorem dF_le : G.dF ≤ 740 * θ₀ := by
  unfold GamHyp.dF
  have h2 := h.nX_le; have hD := h.site.hD
  have h3 : G.δD * G.nX ≤ (2 * θ₀) * 7.01 := mul_le_mul hD h2 (G.consts_nonneg.1) (by positivity)
  have := h.eDX
  nlinarith
theorem gi_le : G.gi ≤ 2.23e10 := by
  unfold GamHyp.gi
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) h.hcG)]
  nlinarith [h.hcG]
theorem dGam_le : G.dGam ≤ 31000 * θ₀ := by
  unfold GamHyp.dGam
  have h1 := h.eX; have h0 := h.eX0; have hq := h.qc
  have hqc0 : 0 ≤ G.q / G.c := by have := G.hq; have := G.hc; positivity
  have t1 : 2 * G.H.epsX G.q * (G.q / G.c) ≤ 2 * (2200 * θ₀) * 7 :=
    mul_le_mul (by linarith) hq hqc0 (by positivity)
  have t2 : G.H.epsX G.q ^ 2 ≤ (2200 * θ₀) ^ 2 := pow_le_pow_left₀ h0 h1 2
  nlinarith
theorem dGi_le : G.dGi ≤ 1.55e25 * θ₀ := by
  unfold GamHyp.dGi
  have hcG := h.hcG
  have hcGp : 0 < G.cG := lt_of_lt_of_le (by norm_num) hcG
  rw [div_le_iff₀ (by positivity)]
  have h1 := h.dGam_le
  have h2 : (4.5e-11 : ℝ) ^ 2 ≤ G.cG ^ 2 := pow_le_pow_left₀ (by norm_num) hcG 2
  have h3 : 1.55e25 * θ₀ * (4.5e-11) ^ 2 ≤ 1.55e25 * θ₀ * G.cG ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith
theorem dT_le : G.dT ≤ 3e26 * θ₀ := by
  unfold GamHyp.dT
  obtain ⟨hnX0, hnDX0, hkF0, hdF0, hgi0, hdGi0⟩ := G.consts_nonneg
  have heX := h.eX; have heX0 := h.eX0; have hgi := h.gi_le; have hkF := h.kF_le; have hdGi := h.dGi_le
  have hdF := h.dF_le; have hq := h.qc; have hD := h.site.hD
  have hqc0 : 0 ≤ G.q / G.c := by have := G.hq; have := G.hc; positivity
  have t1 : G.H.epsX G.q * G.gi * G.kF ≤ (2200 * θ₀) * 2.23e10 * 2.68 :=
    mul_le_mul (mul_le_mul heX hgi hgi0 (by positivity)) hkF hkF0 (by positivity)
  have t2 : G.q / G.c * G.dGi * G.kF ≤ 7 * (1.55e25 * θ₀) * 2.68 :=
    mul_le_mul (mul_le_mul hq hdGi hdGi0 (by positivity)) hkF hkF0 (by positivity)
  have t3 : G.q / G.c * G.gi * G.dF ≤ 7 * 2.23e10 * (740 * θ₀) :=
    mul_le_mul (mul_le_mul hq hgi hgi0 (by positivity)) hdF hdF0 (by positivity)
  nlinarith
theorem kZ_le : G.kZ ≤ 1.2e13 := by
  unfold GamHyp.kZ
  obtain ⟨hnX0, hnDX0, hkF0, hdF0, hgi0, hdGi0⟩ := G.consts_nonneg
  have h4 : 4 / G.c ≤ 28 := by have := h.site.inv_c; rw [div_le_iff₀ h.site.cpos] at this ⊢; linarith
  have t1 : 4 / G.c * G.nX * G.gi * G.kF ≤ 28 * 7.01 * 2.23e10 * 2.68 :=
    mul_le_mul (mul_le_mul (mul_le_mul h4 h.nX_le hnX0 (by norm_num)) h.gi_le hgi0 (by positivity)) h.kF_le hkF0
      (by positivity)
  have := h.site.sqrt48
  nlinarith
theorem kDZ_le : G.kDZ ≤ 3.9e12 := by
  unfold GamHyp.kDZ
  obtain ⟨hnX0, hnDX0, hkF0, hdF0, hgi0, hdGi0⟩ := G.consts_nonneg
  have hs24 : Real.sqrt 24 ≤ 4.9 := sqrt_le_of _ _ (by norm_num) (by norm_num)
  have t1 : Real.sqrt (12 / G.c) * G.nX * G.gi * G.kF ≤ 9.2 * 7.01 * 2.23e10 * 2.68 :=
    mul_le_mul (mul_le_mul (mul_le_mul h.site.sqrt12 h.nX_le hnX0 (by norm_num)) h.gi_le hgi0 (by positivity))
      h.kF_le hkF0 (by positivity)
  nlinarith

theorem dZ_le : G.dZ ≤ 2.1e27 * θ₀ := by
  unfold GamHyp.dZ
  obtain ⟨hnX0, hnDX0, hkF0, hdF0, hgi0, hdGi0⟩ := G.consts_nonneg
  have hD := h.site.hD; have hD0 := G.hδD
  have hic := h.site.inv_c; have hisc := h.site.inv_sqrtc
  have hc0 := h.site.cpos
  have hsc0 : 0 < Real.sqrt G.c := Real.sqrt_pos.mpr hc0
  have h8 : 8 / G.c ≤ 56 := by rw [div_le_iff₀ hc0] at hic ⊢; linarith
  have h4 : 4 / G.c ≤ 28 := by rw [div_le_iff₀ hc0] at hic ⊢; linarith
  have hK := h.site.K0_le; have hK0 := G.H.K0_nonneg 1 zero_le_one
  have hqone : G.q = 1 := h.hq
  rw [hqone] at *
  have hqc' : 1 / G.c ≤ 7 := hic
  have hK1 : G.H.K0 1 / Real.sqrt G.c ≤ 270 * θ₀ * 2.66 := by
    rw [div_eq_mul_one_div]; exact mul_le_mul hK hisc (by positivity) (by positivity)
  have hK2 : G.H.K0 1 / G.c ≤ 270 * θ₀ * 7 := by
    rw [div_eq_mul_one_div]; exact mul_le_mul hK hqc' (by positivity) (by positivity)
  have hA : 4 / G.c * G.δD / Real.sqrt G.c ≤ 28 * (2 * θ₀) * 2.66 := by
    rw [div_eq_mul_one_div]; exact mul_le_mul (mul_le_mul h4 hD hD0 (by norm_num)) hisc (by positivity) (by positivity)
  have hB : (4 / G.c * G.δD / Real.sqrt G.c + G.H.K0 1 / G.c) * G.nX * G.gi * G.kF
      ≤ (28 * (2 * θ₀) * 2.66 + 270 * θ₀ * 7) * 7.01 * 2.23e10 * 2.68 := by
    have h0 : 0 ≤ 4 / G.c * G.δD / Real.sqrt G.c + G.H.K0 1 / G.c := by positivity
    exact mul_le_mul (mul_le_mul (mul_le_mul (add_le_add hA hK2) h.nX_le hnX0 (by positivity)) h.gi_le hgi0
      (by positivity)) h.kF_le hkF0 (by positivity)
  have hC : 1 / G.c * G.H.epsX 1 * G.gi * G.kF ≤ 7 * (2200 * θ₀) * 2.23e10 * 2.68 := by
    have := h.site.epsX_le; have h0 := G.H.epsX_nonneg 1 zero_le_one
    exact mul_le_mul (mul_le_mul (mul_le_mul hqc' this h0 (by norm_num)) h.gi_le hgi0 (by positivity)) h.kF_le hkF0
      (by positivity)
  have hDd : 1 / G.c * (1 / G.c) * G.dGi * G.kF ≤ 7 * 7 * (1.55e25 * θ₀) * 2.68 :=
    mul_le_mul (mul_le_mul (mul_le_mul hqc' hqc' (by positivity) (by norm_num)) h.dGi_le hdGi0 (by positivity))
      h.kF_le hkF0 (by positivity)
  have hE : 1 / G.c * (1 / G.c) * G.gi * G.dF ≤ 7 * 7 * 2.23e10 * (740 * θ₀) :=
    mul_le_mul (mul_le_mul (mul_le_mul hqc' hqc' (by positivity) (by norm_num)) h.gi_le hgi0 (by positivity))
      h.dF_le hdF0 (by positivity)
  have hF : 8 / G.c * G.δD ≤ 56 * (2 * θ₀) := mul_le_mul h8 hD hD0 (by norm_num)
  nlinarith

theorem dDZ_le : G.dDZ ≤ 8e26 * θ₀ := by
  unfold GamHyp.dDZ
  obtain ⟨hnX0, hnDX0, hkF0, hdF0, hgi0, hdGi0⟩ := G.consts_nonneg
  have hD := h.site.hD; have hD0 := G.hδD
  have hic := h.site.inv_c; have hisc := h.site.inv_sqrtc
  have hc0 := h.site.cpos
  have hK := h.site.K1_le; have hK0 := G.H.K1_nonneg 1 zero_le_one
  have hqone : G.q = 1 := h.hq
  rw [hqone] at *
  have hK1 : G.H.K1 1 / Real.sqrt G.c ≤ 90 * θ₀ * 2.66 := by
    rw [div_eq_mul_one_div]; exact mul_le_mul hK hisc (by positivity) (by positivity)
  have hK2 : G.H.K1 1 / G.c ≤ 90 * θ₀ * 7 := by
    rw [div_eq_mul_one_div]; exact mul_le_mul hK hic (by positivity) (by positivity)
  have hA : Real.sqrt (12 / G.c) * G.δD / Real.sqrt G.c ≤ 9.2 * (2 * θ₀) * 2.66 := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul h.site.sqrt12 hD hD0 (by norm_num)) hisc (by positivity) (by positivity)
  have hB : (Real.sqrt (12 / G.c) * G.δD / Real.sqrt G.c + G.H.K1 1 / G.c) * G.nX * G.gi * G.kF
      ≤ (9.2 * (2 * θ₀) * 2.66 + 90 * θ₀ * 7) * 7.01 * 2.23e10 * 2.68 := by
    have h0 : 0 ≤ Real.sqrt (12 / G.c) * G.δD / Real.sqrt G.c + G.H.K1 1 / G.c := by positivity
    exact mul_le_mul (mul_le_mul (mul_le_mul (add_le_add hA hK2) h.nX_le hnX0 (by positivity)) h.gi_le hgi0
      (by positivity)) h.kF_le hkF0 (by positivity)
  have hC : 1 / Real.sqrt G.c * G.H.epsX 1 * G.gi * G.kF ≤ 2.66 * (2200 * θ₀) * 2.23e10 * 2.68 := by
    have := h.site.epsX_le; have h0 := G.H.epsX_nonneg 1 zero_le_one
    exact mul_le_mul (mul_le_mul (mul_le_mul hisc this h0 (by norm_num)) h.gi_le hgi0 (by positivity)) h.kF_le hkF0
      (by positivity)
  have hDd : 1 / Real.sqrt G.c * (1 / G.c) * G.dGi * G.kF ≤ 2.66 * 7 * (1.55e25 * θ₀) * 2.68 :=
    mul_le_mul (mul_le_mul (mul_le_mul hisc hic (by positivity) (by norm_num)) h.dGi_le hdGi0 (by positivity))
      h.kF_le hkF0 (by positivity)
  have hE : 1 / Real.sqrt G.c * (1 / G.c) * G.gi * G.dF ≤ 2.66 * 7 * 2.23e10 * (740 * θ₀) :=
    mul_le_mul (mul_le_mul (mul_le_mul hisc hic (by positivity) (by norm_num)) h.gi_le hgi0 (by positivity))
      h.dF_le hdF0 (by positivity)
  have hF : 2 * Real.sqrt (12 / G.c) * G.δD ≤ 2 * 9.2 * (2 * θ₀) := by
    have := mul_le_mul h.site.sqrt12 hD hD0 (by norm_num); nlinarith
  nlinarith

theorem dW_le : G.dW ≤ 8.1e26 * θ₀ := by
  unfold GamHyp.dW
  have := h.dDZ_le
  have hkZ := h.kZ_le
  have hkZ0 : 0 ≤ G.kZ := by unfold GamHyp.kZ; obtain ⟨hnX0, -, hkF0, -, hgi0, -⟩ := G.consts_nonneg; have := G.hc; positivity
  have t1 : G.δD * G.kZ ≤ (2 * θ₀) * 1.2e13 := mul_le_mul h.site.hD hkZ hkZ0 (by positivity)
  nlinarith

end GamSmall

#print axioms SiteSmall.epsX_le
#print axioms GamSmall.dT_le
#print axioms GamSmall.dZ_le
#print axioms GamSmall.dDZ_le
#print axioms GamSmall.dW_le

end AdalyFormal.DLayer
