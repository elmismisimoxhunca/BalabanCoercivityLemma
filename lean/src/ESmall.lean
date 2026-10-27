/-
Smallness of the genuine `Coeff124` operators E1, E2, E3 on the ball ν ≤ ρ ≤ π/2.

Printed CMP98 (109) uses α₀, α₁ (strict inequalities on plaquettes / bond
coordinates). Campaign documents also write ε₀, ε₁. This file introduces an
explicit alias and an *unproved* one-step radius interface
`intendedRho = min(π/2, eps0 + ell * eps1)`. The linear combination is NOT
derived from (109); it is the coarsest dimensionally reasonable one-step
placeholder. No uniformity in averaging depth k is claimed.
-/
import OperatorGaps
import T1MainSegment

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace EstimatesLayer.E1E3
open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.Bch2
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open OneStep124
open EstimatesLayer.NormBounds
open AdalySI1.DexpRodrigues (adOp_zero_eq gOp_zero_eq)
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

/-- `(n : ℝ) * (1/n) ≤ 1` even at `n = 0` (where Lean's division gives 0). -/
theorem nat_mul_inv_le (n : ℕ) : (n : ℝ) * (1 / (n : ℝ)) ≤ 1 := by
  by_cases h : n = 0
  · subst h; simp
  · have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
    rw [mul_one_div, div_self this]

theorem nu_Z_le {ell m : ℕ} (D : LogData L ell m) (c : CoarseBond L (ell * m)) {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (h : ∀ u ∈ unitSitesOf ell (ell * m) c.1.1,
      nu ((D.Zx c u.1 : SuTwo) : M2) ≤ ρ) :
    nu ((D.Z c : SuTwo) : M2) ≤ ρ := by
  set S := unitSitesOf ell (ell * m) c.1.1
  set w : ℝ := 1 / (S.card : ℝ)
  have hw0 : 0 ≤ w := div_nonneg zero_le_one (Nat.cast_nonneg _)
  rw [← norm_eq_nu, LogData.Z]
  have hsum : ‖∑ u ∈ S, w • D.Zx c u.1‖ ≤ ∑ u ∈ S, ‖w • D.Zx c u.1‖ :=
    norm_sum_le _ _
  have hterm : ∀ u ∈ S, ‖w • D.Zx c u.1‖ = w * nu ((D.Zx c u.1 : SuTwo) : M2) := by
    intro u _hu
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw0, norm_eq_nu]
  have hrew : ∑ u ∈ S, ‖w • D.Zx c u.1‖ = ∑ u ∈ S, w * nu ((D.Zx c u.1 : SuTwo) : M2) :=
    Finset.sum_congr rfl hterm
  have hle : ∑ u ∈ S, w * nu ((D.Zx c u.1 : SuTwo) : M2) ≤ ∑ u ∈ S, w * ρ :=
    Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (h u hu) hw0
  have hconst : ∑ u ∈ S, w * ρ = (S.card : ℝ) * (w * ρ) := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hcard : (S.card : ℝ) * w ≤ 1 := nat_mul_inv_le _
  have hfin : (S.card : ℝ) * (w * ρ) ≤ ρ := by
    have : (S.card : ℝ) * (w * ρ) = ((S.card : ℝ) * w) * ρ := by ring
    rw [this]
    calc ((S.card : ℝ) * w) * ρ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hcard hρ
      _ = ρ := one_mul ρ
  calc ‖∑ u ∈ S, w • D.Zx c u.1‖
      ≤ ∑ u ∈ S, ‖w • D.Zx c u.1‖ := hsum
    _ = ∑ u ∈ S, w * nu ((D.Zx c u.1 : SuTwo) : M2) := hrew
    _ ≤ ∑ u ∈ S, w * ρ := hle
    _ = (S.card : ℝ) * (w * ρ) := hconst
    _ ≤ ρ := hfin

/-- Smallness of the genuine E1 operator. Hypotheses are on the two logs only. -/
theorem E1_norm_le {ell m : ℕ}
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (D : LogData L ell m) (c : CoarseBond L (ell * m)) (x : PeriodicLatticeSite L) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Real.pi / 2)
    (hZ : nu ((D.Z c : SuTwo) : M2) ≤ ρ)
    (hZx : nu ((D.Zx c x : SuTwo) : M2) ≤ ρ) :
    ‖(Coeff124.ofBackground ell m V D).E1 c x‖ ≤ e1Majorant ρ := by
  simpa [Coeff124.ofBackground] using E1_operators_norm_le (D.Z c) (D.Zx c x) hρ0 hρ hZ hZx

/-- Smallness of the genuine E2 operator. Hypotheses are on the two logs only. -/
theorem E2_norm_le {ell m : ℕ}
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (D : LogData L ell m) (c : CoarseBond L (ell * m)) (x : PeriodicLatticeSite L) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Real.pi / 2)
    (hZ : nu ((D.Z c : SuTwo) : M2) ≤ ρ)
    (hZx : nu ((D.Zx c x : SuTwo) : M2) ≤ ρ) :
    ‖(Coeff124.ofBackground ell m V D).E2 c x‖ ≤ e2Majorant ρ := by
  simpa [Coeff124.ofBackground] using E2_operators_norm_le (D.Z c) (D.Zx c x) hρ0 hρ hZ hZx

theorem E1_norm_le_of_block {ell m : ℕ}
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (D : LogData L ell m) (c : CoarseBond L (ell * m)) (x : PeriodicLatticeSite L) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Real.pi / 2)
    (hZx_pt : nu ((D.Zx c x : SuTwo) : M2) ≤ ρ)
    (hZx_blk : ∀ u ∈ unitSitesOf ell (ell * m) c.1.1,
      nu ((D.Zx c u.1 : SuTwo) : M2) ≤ ρ) :
    ‖(Coeff124.ofBackground ell m V D).E1 c x‖ ≤ e1Majorant ρ :=
  E1_norm_le V D c x hρ0 hρ (nu_Z_le D c hρ0 hZx_blk) hZx_pt

theorem E2_norm_le_of_block {ell m : ℕ}
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (D : LogData L ell m) (c : CoarseBond L (ell * m)) (x : PeriodicLatticeSite L) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Real.pi / 2)
    (hZx_pt : nu ((D.Zx c x : SuTwo) : M2) ≤ ρ)
    (hZx_blk : ∀ u ∈ unitSitesOf ell (ell * m) c.1.1,
      nu ((D.Zx c u.1 : SuTwo) : M2) ≤ ρ) :
    ‖(Coeff124.ofBackground ell m V D).E2 c x‖ ≤ e2Majorant ρ :=
  E2_norm_le V D c x hρ0 hρ (nu_Z_le D c hρ0 hZx_blk) hZx_pt

theorem sum_weight_one {ell m : ℕ} {c : CoarseBond L (ell * m)}
    (hpos : 0 < (unitSitesOf ell (ell * m) c.1.1).card) :
    ∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
      (1 / ((unitSitesOf ell (ell * m) c.1.1).card : ℝ)) = (1 : ℝ) := by
  set S := unitSitesOf ell (ell * m) c.1.1
  have hne : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
  simp [Finset.sum_const, nsmul_eq_mul]
  field_simp [hne]

theorem sum_weight_one_smul {ell m : ℕ} {c : CoarseBond L (ell * m)}
    (hpos : 0 < (unitSitesOf ell (ell * m) c.1.1).card) :
    ∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
      (1 / ((unitSitesOf ell (ell * m) c.1.1).card : ℝ)) •
        (1 : SuTwo →L[ℝ] SuTwo) = 1 := by
  have hsum := sum_weight_one (c := c) hpos
  rw [← Finset.sum_smul, hsum, one_smul]

/-- Smallness of the genuine E3 operator. Requires a nonempty averaging block. -/
theorem E3_norm_le {ell m : ℕ}
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (D : LogData L ell m) (c : CoarseBond L (ell * m)) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Real.pi / 2)
    (hZx : ∀ u ∈ unitSitesOf ell (ell * m) c.1.1,
      nu ((D.Zx c u.1 : SuTwo) : M2) ≤ ρ)
    (hpos : 0 < (unitSitesOf ell (ell * m) c.1.1).card) :
    ‖(Coeff124.ofBackground ell m V D).E3 c‖ ≤ e2Majorant ρ := by
  set S := unitSitesOf ell (ell * m) c.1.1
  set w : ℝ := 1 / (S.card : ℝ)
  have hw0 : 0 ≤ w := div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hZ : nu ((D.Z c : SuTwo) : M2) ≤ ρ := nu_Z_le D c hρ0 hZx
  have hg : ‖gOp (-(adOp (D.Z c))) - 1‖ ≤ Real.exp (2 * ρ) - 1 :=
    (norm_gOp_sub_one_le (-(adOp (D.Z c)))).trans (exp_two_rho_gap_of_ad (D.Z c) hρ0 hZ)
  have hU1 : ‖expOp (adOp (D.Z c)) - 1‖ ≤ Real.exp (2 * ρ) - 1 :=
    (norm_expOp_sub_one_le (adOp (D.Z c))).trans (exp_two_rho_gap_of_ad_pos (D.Z c) hρ0 hZ)
  set avg : SuTwo →L[ℝ] SuTwo :=
    ∑ u ∈ S, w • gInvOp (adOp (D.Zx c u.1))
  have hE3 : (Coeff124.ofBackground ell m V D).E3 c =
      expOp (adOp (D.Z c)) - gOp (-(adOp (D.Z c))) * avg := by
    simp [Coeff124.ofBackground, avg, w, S]
  have hone := sum_weight_one_smul (c := c) hpos
  have havg1 : avg - 1 = ∑ u ∈ S, w • (gInvOp (adOp (D.Zx c u.1)) - 1) := by
    have h1 : ∑ u ∈ S, w • (1 : SuTwo →L[ℝ] SuTwo) = (1 : SuTwo →L[ℝ] SuTwo) := hone
    calc avg - 1
        = (∑ u ∈ S, w • gInvOp (adOp (D.Zx c u.1))) -
            ∑ u ∈ S, w • (1 : SuTwo →L[ℝ] SuTwo) := by rw [h1]
      _ = ∑ u ∈ S, (w • gInvOp (adOp (D.Zx c u.1)) -
            w • (1 : SuTwo →L[ℝ] SuTwo)) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ u ∈ S, w • (gInvOp (adOp (D.Zx c u.1)) - 1) := by
            refine Finset.sum_congr rfl ?_
            intro u _hu
            exact (smul_sub w _ _).symm
  have havg_norm : ‖avg‖ ≤ gInvMajorant ρ := by
    have hsum : ‖avg‖ ≤ ∑ u ∈ S, ‖w • gInvOp (adOp (D.Zx c u.1))‖ := norm_sum_le _ _
    have hterm : ∀ u ∈ S, ‖w • gInvOp (adOp (D.Zx c u.1))‖ ≤ w * gInvMajorant ρ := by
      intro u hu
      have hb := norm_gInv_pos_le_of_ball (D.Zx c u.1) hρ0 hρ (hZx u hu)
      have : ‖w • gInvOp (adOp (D.Zx c u.1))‖ = w * ‖gInvOp (adOp (D.Zx c u.1))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw0]
      rw [this]
      exact mul_le_mul_of_nonneg_left hb hw0
    have hrew : ∑ u ∈ S, ‖w • gInvOp (adOp (D.Zx c u.1))‖ ≤ ∑ u ∈ S, w * gInvMajorant ρ :=
      Finset.sum_le_sum hterm
    have hconst : ∑ u ∈ S, w * gInvMajorant ρ = (S.card : ℝ) * (w * gInvMajorant ρ) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    have hne : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
    have hw1 : (S.card : ℝ) * w = 1 := by dsimp [w]; field_simp [hne]
    have : (S.card : ℝ) * (w * gInvMajorant ρ) = gInvMajorant ρ := by
      rw [← mul_assoc, hw1, one_mul]
    linarith
  have havg1_norm : ‖avg - 1‖ ≤ ρ * (1 + Real.pi / 2) := by
    have hsum : ‖avg - 1‖ ≤ ∑ u ∈ S, ‖w • (gInvOp (adOp (D.Zx c u.1)) - 1)‖ := by
      rw [havg1]; exact norm_sum_le _ _
    have hterm : ∀ u ∈ S,
        ‖w • (gInvOp (adOp (D.Zx c u.1)) - 1)‖ ≤ w * (ρ * (1 + Real.pi / 2)) := by
      intro u hu
      have hb := norm_gInv_pos_sub_one_le (D.Zx c u.1) hρ0 hρ (hZx u hu)
      have : ‖w • (gInvOp (adOp (D.Zx c u.1)) - 1)‖ =
          w * ‖gInvOp (adOp (D.Zx c u.1)) - 1‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw0]
      rw [this]
      exact mul_le_mul_of_nonneg_left hb hw0
    have hrew : ∑ u ∈ S, ‖w • (gInvOp (adOp (D.Zx c u.1)) - 1)‖ ≤
        ∑ u ∈ S, w * (ρ * (1 + Real.pi / 2)) := Finset.sum_le_sum hterm
    have hconst : ∑ u ∈ S, w * (ρ * (1 + Real.pi / 2)) =
        (S.card : ℝ) * (w * (ρ * (1 + Real.pi / 2))) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    have hne : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
    have hw1 : (S.card : ℝ) * w = 1 := by dsimp [w]; field_simp [hne]
    have : (S.card : ℝ) * (w * (ρ * (1 + Real.pi / 2))) = ρ * (1 + Real.pi / 2) := by
      rw [← mul_assoc, hw1, one_mul]
    linarith
  have hsplit : gOp (-(adOp (D.Z c))) * avg - 1 =
      (gOp (-(adOp (D.Z c))) - 1) * avg + (avg - 1) := mul_sub_one_eq
  have hA := exp_two_rho_sub_one_nonneg hρ0
  have hM := gInvMajorant_nonneg hρ0
  have hprod : ‖gOp (-(adOp (D.Z c))) - 1‖ * ‖avg‖ ≤
      (Real.exp (2 * ρ) - 1) * gInvMajorant ρ :=
    mul_le_mul hg havg_norm (norm_nonneg _) hA
  have hgavg : ‖gOp (-(adOp (D.Z c))) * avg - 1‖ ≤ e1Majorant ρ := by
    have h1 : ‖(gOp (-(adOp (D.Z c))) - 1) * avg + (avg - 1)‖ ≤
        ‖(gOp (-(adOp (D.Z c))) - 1) * avg‖ + ‖avg - 1‖ := norm_add_le _ _
    have h2 : ‖(gOp (-(adOp (D.Z c))) - 1) * avg‖ ≤
        ‖gOp (-(adOp (D.Z c))) - 1‖ * ‖avg‖ := ContinuousLinearMap.opNorm_comp_le _ _
    rw [hsplit]
    dsimp [e1Majorant]
    linarith [h1, h2, hprod, havg1_norm]
  have : ‖expOp (adOp (D.Z c)) - gOp (-(adOp (D.Z c))) * avg‖ ≤ e2Majorant ρ := by
    have htri : ‖expOp (adOp (D.Z c)) - gOp (-(adOp (D.Z c))) * avg‖ ≤
        ‖expOp (adOp (D.Z c)) - 1‖ + ‖gOp (-(adOp (D.Z c))) * avg - 1‖ := by
      have hrew : expOp (adOp (D.Z c)) - gOp (-(adOp (D.Z c))) * avg =
          (expOp (adOp (D.Z c)) - 1) - (gOp (-(adOp (D.Z c))) * avg - 1) :=
        (sub_sub_sub_cancel_right (expOp (adOp (D.Z c)))
          (gOp (-(adOp (D.Z c))) * avg) 1).symm
      rw [hrew]
      exact norm_sub_le _ _
    dsimp [e2Majorant]
    linarith [htri, hU1, hgavg]
  simpa [hE3] using this

/-! ## Printed (109) packaging. Geometric implication is NOT proved. -/

/-- Printed CMP98 (109) thresholds. Paper uses Greek **alpha**, not epsilon. -/
structure Thresholds109 where
  alpha0 : ℝ
  alpha1 : ℝ
  alpha0_nonneg : 0 ≤ alpha0
  alpha1_nonneg : 0 ≤ alpha1

/-- Campaign alias `ε₀` for printed `α₀`. -/
abbrev Thresholds109.eps0 (t : Thresholds109) : ℝ := t.alpha0
/-- Campaign alias `ε₁` for printed `α₁`. -/
abbrev Thresholds109.eps1 (t : Thresholds109) : ℝ := t.alpha1

/-- Coarse one-step radius interface. NOT derived from (109).
    `ell` is the one-step block scale in `LogData`, not iterated depth `k`. -/
def intendedRho (t : Thresholds109) (ell : ℕ) : ℝ :=
  min (Real.pi / 2) (t.eps0 + (ell : ℝ) * t.eps1)

theorem intendedRho_nonneg (t : Thresholds109) (ell : ℕ) :
    0 ≤ intendedRho t ell :=
  le_min (div_nonneg (le_of_lt Real.pi_pos) (by norm_num))
    (add_nonneg t.alpha0_nonneg (mul_nonneg (Nat.cast_nonneg _) t.alpha1_nonneg))

theorem intendedRho_le_half (t : Thresholds109) (ell : ℕ) :
    intendedRho t ell ≤ Real.pi / 2 :=
  min_le_left _ _

/-- If the one-step logs lie in the `intendedRho` ball, E1 is bounded by
    `e1Majorant (min(π/2, eps0 + ell*eps1))`. The ball membership is an extra
    hypothesis, not a consequence of (109) proved here. -/
theorem E1_norm_le_of_intended {ell m : ℕ}
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (D : LogData L ell m) (c : CoarseBond L (ell * m)) (x : PeriodicLatticeSite L)
    (t : Thresholds109)
    (hZ : nu ((D.Z c : SuTwo) : M2) ≤ intendedRho t ell)
    (hZx : nu ((D.Zx c x : SuTwo) : M2) ≤ intendedRho t ell) :
    ‖(Coeff124.ofBackground ell m V D).E1 c x‖ ≤ e1Majorant (intendedRho t ell) :=
  E1_norm_le V D c x (intendedRho_nonneg t ell) (intendedRho_le_half t ell) hZ hZx

theorem E2_norm_le_of_intended {ell m : ℕ}
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (D : LogData L ell m) (c : CoarseBond L (ell * m)) (x : PeriodicLatticeSite L)
    (t : Thresholds109)
    (hZ : nu ((D.Z c : SuTwo) : M2) ≤ intendedRho t ell)
    (hZx : nu ((D.Zx c x : SuTwo) : M2) ≤ intendedRho t ell) :
    ‖(Coeff124.ofBackground ell m V D).E2 c x‖ ≤ e2Majorant (intendedRho t ell) :=
  E2_norm_le V D c x (intendedRho_nonneg t ell) (intendedRho_le_half t ell) hZ hZx

theorem E3_norm_le_of_intended {ell m : ℕ}
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (D : LogData L ell m) (c : CoarseBond L (ell * m))
    (t : Thresholds109)
    (hZx : ∀ u ∈ unitSitesOf ell (ell * m) c.1.1,
      nu ((D.Zx c u.1 : SuTwo) : M2) ≤ intendedRho t ell)
    (hpos : 0 < (unitSitesOf ell (ell * m) c.1.1).card) :
    ‖(Coeff124.ofBackground ell m V D).E3 c‖ ≤ e2Majorant (intendedRho t ell) :=
  E3_norm_le V D c (intendedRho_nonneg t ell) (intendedRho_le_half t ell) hZx hpos

/-! ## Vanishing when the two logs coincide, strictly inside the principal ball. -/

theorem isUnit_gOp_neg_ad (Z : SuTwo) (h : nu (Z : M2) < Real.pi) :
    IsUnit (gOp (-(adOp Z))) := by
  by_cases hz : Z = 0
  · subst hz
    rw [adOp_zero_eq, neg_zero, gOp_zero_eq]
    exact isUnit_one
  · have hr := nu_pos_of_ne_zero Z hz
    have hs : Real.sin (nu (Z : M2)) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hr h)
    refine ⟨⟨gOp (-(adOp Z)), inverseBlock Z, ?_, ?_⟩, rfl⟩
    · exact (inverseBlock_spec Z hr hs).1
    · exact (inverseBlock_spec Z hr hs).2

/-- Exact vanishing of the E1 combination when `Zx = Z`, under the STRICT cut
    avoidance `ν(Z) < π`. This is an identity, not a quantitative bound. -/
theorem E1_operators_eq_zero (Z : SuTwo) (h : nu (Z : M2) < Real.pi) :
    gOp (-(adOp Z)) * gInvOp (-(adOp Z)) - 1 = 0 := by
  have hu := isUnit_gOp_neg_ad Z h
  rw [gInvOp, Ring.mul_inverse_cancel _ hu, sub_self]

theorem E1_eq_zero_of_eq {ell m : ℕ}
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (D : LogData L ell m) (c : CoarseBond L (ell * m)) (x : PeriodicLatticeSite L)
    (heq : D.Zx c x = D.Z c) (h : nu ((D.Z c : SuTwo) : M2) < Real.pi) :
    (Coeff124.ofBackground ell m V D).E1 c x = 0 := by
  simpa [Coeff124.ofBackground, heq] using E1_operators_eq_zero (D.Z c) h

#print axioms nu_Z_le
#print axioms E1_norm_le
#print axioms E2_norm_le
#print axioms E3_norm_le
#print axioms E1_norm_le_of_intended
#print axioms E2_norm_le_of_intended
#print axioms E3_norm_le_of_intended
#print axioms E1_eq_zero_of_eq
end EstimatesLayer.E1E3
