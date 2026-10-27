/-
Scalar majorants for the E1/E2/E3 first-cut smallness bounds.

Regime: 0 ≤ r ≤ ρ ≤ π/2. This stays away from the -I cut at π (the first
cut; every nonzero integer multiple of π is singular). Endpoint ρ ≤ π/2 is
NON-STRICT. Printed (109) inequalities are STRICT in the field variables;
this file does not mention those.

No operator theory, no lattice geometry, no k-uniformity.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace EstimatesLayer.E1E3
open Real

/-- Jordan: on `(0, π/2]`, `r / sin r ≤ π/2`. The upper endpoint is NON-STRICT. -/
theorem r_div_sin_le {r : ℝ} (h0 : 0 < r) (hπ : r ≤ π / 2) :
    r / sin r ≤ π / 2 := by
  have hj := mul_le_sin (le_of_lt h0) hπ
  have hden : 0 < 2 / π * r := by positivity
  have hcmp : r / sin r ≤ r / (2 / π * r) :=
    div_le_div_of_nonneg_left (le_of_lt h0) hden hj
  have hsimp : r / (2 / π * r) = π / 2 := by field_simp [ne_of_gt h0]
  rwa [hsimp] at hcmp

/-- `sin r ≥ r cos r` on `[0, π/2]`. At `π/2` this is `1 ≥ 0`; inside, `r ≤ tan r`. -/
theorem sin_sub_mul_cos_nonneg {r : ℝ} (h0 : 0 ≤ r) (hπ : r ≤ π / 2) :
    0 ≤ sin r - r * cos r := by
  rcases eq_or_lt_of_le hπ with hEq | hlt
  · subst hEq
    simp [sin_pi_div_two, cos_pi_div_two]
  · rcases eq_or_lt_of_le h0 with h00 | hpos
    · simp [← h00]
    · have hc : 0 < cos r :=
        cos_pos_of_mem_Ioo ⟨lt_trans (neg_neg_of_pos (half_pos pi_pos)) hpos, hlt⟩
      have ht := le_tan (le_of_lt hpos) hlt
      rw [tan_eq_sin_div_cos, le_div_iff₀ hc] at ht
      linarith

/-- Coefficient gap for the inverse block: `|r cos r / sin r - 1| ≤ (π/2) r`. -/
theorem r_cos_over_sin_sub_one_le {r : ℝ} (h0 : 0 < r) (hπ : r ≤ π / 2) :
    |r * cos r / sin r - 1| ≤ (π / 2) * r := by
  have hrπ : r < π := lt_of_le_of_lt hπ (half_lt_self pi_pos)
  have hs : 0 < sin r := sin_pos_of_pos_of_lt_pi h0 hrπ
  have hnum := sin_sub_mul_cos_nonneg (le_of_lt h0) hπ
  have hrew : r * cos r / sin r - 1 = -((sin r - r * cos r) / sin r) := by
    field_simp [ne_of_gt hs]
    ring
  rw [hrew, abs_neg, abs_of_nonneg (div_nonneg hnum (le_of_lt hs))]
  have hsin_le : sin r ≤ r := le_of_lt (sin_lt h0)
  have hcos_lip : |cos r - 1| ≤ |r| := by
    have h := lipschitzWith_cos.dist_le_mul r 0
    simpa [dist_eq_norm, Real.norm_eq_abs, cos_zero, sub_zero] using h
  have hrabs : |r| = r := abs_of_nonneg (le_of_lt h0)
  have h1cos : 1 - cos r ≤ r := by
    have hswap : |cos r - 1| = 1 - cos r := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr (cos_le_one r))
    rw [hswap, hrabs] at hcos_lip
    exact hcos_lip
  have hnum_le : sin r - r * cos r ≤ r * r := by
    calc sin r - r * cos r
        ≤ r - r * cos r := sub_le_sub_right hsin_le _
      _ = r * (1 - cos r) := by ring
      _ ≤ r * r := mul_le_mul_of_nonneg_left h1cos (le_of_lt h0)
  have hj := mul_le_sin (le_of_lt h0) hπ
  have hden : 0 < 2 / π * r := by positivity
  have hstep1 : (sin r - r * cos r) / sin r ≤ (r * r) / sin r :=
    div_le_div_of_nonneg_right hnum_le (le_of_lt hs)
  have hstep2 : (r * r) / sin r ≤ (r * r) / (2 / π * r) :=
    div_le_div_of_nonneg_left (mul_nonneg (le_of_lt h0) (le_of_lt h0)) hden hj
  have hsimp : (r * r) / (2 / π * r) = (π / 2) * r := by field_simp [ne_of_gt h0]
  calc (sin r - r * cos r) / sin r
      ≤ (r * r) / sin r := hstep1
    _ ≤ (r * r) / (2 / π * r) := hstep2
    _ = (π / 2) * r := hsimp

/-- Uniform majorant of `1 + r + r/|sin r|` on `(0, ρ]` with `ρ ≤ π/2`. -/
def gInvMajorant (ρ : ℝ) : ℝ := 1 + ρ + π / 2

theorem gInvMajorant_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ gInvMajorant ρ := by
  dsimp [gInvMajorant]
  linarith [pi_pos]

theorem inv_scalar_le_majorant {r ρ : ℝ} (h0 : 0 < r) (hr : r ≤ ρ) (hπ : ρ ≤ π / 2) :
    1 + r + r / |sin r| ≤ gInvMajorant ρ := by
  have hrπ : r ≤ π / 2 := hr.trans hπ
  have hsin : 0 < sin r :=
    sin_pos_of_pos_of_lt_pi h0 (lt_of_le_of_lt hrπ (half_lt_self pi_pos))
  rw [abs_of_pos hsin]
  have hj := r_div_sin_le h0 hrπ
  dsimp [gInvMajorant]
  linarith

/-- Gap majorant for `‖E1‖`. Vanishes at `ρ = 0`. -/
def e1Majorant (ρ : ℝ) : ℝ :=
  (exp (2 * ρ) - 1) * gInvMajorant ρ + ρ * (1 + π / 2)

/-- Gap majorant for `‖E2‖` and `‖E3‖`. Vanishes at `ρ = 0`. -/
def e2Majorant (ρ : ℝ) : ℝ := e1Majorant ρ + (exp (2 * ρ) - 1)

theorem exp_two_rho_sub_one_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ exp (2 * ρ) - 1 :=
  sub_nonneg.mpr (one_le_exp (by linarith))

theorem e1Majorant_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ e1Majorant ρ := by
  dsimp [e1Majorant]
  have h1 := exp_two_rho_sub_one_nonneg hρ
  have h2 := gInvMajorant_nonneg hρ
  have h3 : 0 ≤ ρ * (1 + π / 2) := mul_nonneg hρ (by linarith [pi_pos])
  nlinarith

theorem e2Majorant_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ e2Majorant ρ := by
  dsimp [e2Majorant]
  linarith [e1Majorant_nonneg hρ, exp_two_rho_sub_one_nonneg hρ]

theorem gInvMajorant_mono {a b : ℝ} (hab : a ≤ b) :
    gInvMajorant a ≤ gInvMajorant b := by
  dsimp [gInvMajorant]; linarith

theorem e1Majorant_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    e1Majorant a ≤ e1Majorant b := by
  have h1 : exp (2 * a) - 1 ≤ exp (2 * b) - 1 :=
    sub_le_sub_right (exp_le_exp.mpr (by linarith)) 1
  have h2 := gInvMajorant_mono hab
  have h3 : a * (1 + π / 2) ≤ b * (1 + π / 2) :=
    mul_le_mul_of_nonneg_right hab (by linarith [pi_pos])
  dsimp [e1Majorant]
  have hA := exp_two_rho_sub_one_nonneg ha
  have hB := gInvMajorant_nonneg (le_trans ha hab)
  nlinarith

theorem e2Majorant_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    e2Majorant a ≤ e2Majorant b := by
  dsimp [e2Majorant]
  have h1 := e1Majorant_mono ha hab
  have h2 : exp (2 * a) - 1 ≤ exp (2 * b) - 1 :=
    sub_le_sub_right (exp_le_exp.mpr (by linarith)) 1
  linarith

/-- Inverse-block remainder: `|c - 1| + r ≤ ρ (1 + π/2)`. -/
theorem inverse_gap_scalar {r ρ : ℝ} (h0 : 0 < r) (hr : r ≤ ρ) (hπ : ρ ≤ π / 2) :
    |r * cos r / sin r - 1| + r ≤ ρ * (1 + π / 2) := by
  have hgap := r_cos_over_sin_sub_one_le h0 (hr.trans hπ)
  have hlin : (π / 2) * r + r = r * (1 + π / 2) := by ring
  have hρ : r * (1 + π / 2) ≤ ρ * (1 + π / 2) :=
    mul_le_mul_of_nonneg_right hr (by linarith [pi_pos])
  linarith

#print axioms r_div_sin_le
#print axioms sin_sub_mul_cos_nonneg
#print axioms r_cos_over_sin_sub_one_le
#print axioms inv_scalar_le_majorant
#print axioms e1Majorant_mono
#print axioms inverse_gap_scalar
end EstimatesLayer.E1E3
