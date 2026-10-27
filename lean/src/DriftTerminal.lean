/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import DriftNoGo
import HrawRCentreClass

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 40000
set_option linter.style.longLine false

/-!
# `hdrift` REPLACED BY PER-CUBE DATA — and the exact extra datum that replacement costs.

Lane `compute/drift_percube/`.  Write scope: that directory only.  Never `lake build`.

`HrawRDischarge.terminal_sum_at_star_datum` carries ONE hypothesis beyond
`RecomposeSum.terminal_sum_posDef_from_printed`:

    hdrift : α₁(V) ≤ 1/(13336·ℓ³)          -- a GLOBAL, UNGAUGED bound on the coarse background

This module removes it and puts PER-CUBE data in its place.  The replacement is exact, and it is
**two** hypotheses, not one:

    hclass  : ∀ i ∈ 𝒞, ∀ b ∈ □_i,  frobNorm((U^{γ_i})_b − 1) ≤ r     -- the printed class's shape
    hrough  : ∀ i ∈ 𝒞, ∀ b ∈ □_i,  frobNorm((1^{γ_i⁻¹})_b − 1) ≤ ρ   -- the gauges' own roughness
    hsum    : r + ρ ≤ 1/(37664·ℓ³)

`37664 = 16·2354`, and every factor is counted: `16 = √256`, `256 = 2·32·4` — `2` from the
`‖x+y‖² ≤ 2‖x‖²+2‖y‖²` split, `32` from `RegularUPerturbation.plaqEnergy_curlDrift_le` (cited), `4`
from the enlarged-cube bond multiplicity (`DriftPerCube.bondsOn_tilde_mult_le_four`); and
`2354 = 2·1177` from `HrawRDischarge.sqrt_gammaSum_lower` (cited).  The price of localizing is the
ratio `16/(4√2) = 2√2 ≈ 2.83`, and it is exhibited (`localization_price`), not hidden.

## WHAT THIS DOES AND DOES NOT ACHIEVE — read with `stage/DriftNoGo.lean`

`hrough` is NOT decoration and is NOT removable: `DriftNoGo.percube_data_cannot_price_the_drift`
exhibits a background carrying `hclass` at `r = 0` on EVERY cube family whose flat-referenced drift
is bounded BELOW.  So the class defined by `hclass` alone does not discharge `hdrift`, and this
module's `hrough` is exactly the missing datum, named and quantified.

The class `{hclass at r} ∩ {hrough at ρ}` is, up to the constant, the global smallness class again
(`percube_plus_roughness_is_global` states the direction that is a theorem here: it IMPLIES a global
bound on the drift).  What has changed is not the size of the class but WHERE the hypothesis is
measured — cube by cube, on the gauged background the source actually supplies — and the fact that
the residual is now a single named quantity (`ρ`, the roughness of the per-cube gauges) rather than
a global condition on `U`.

**Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.  The gates adjudicate.**
-/

namespace AdalyFormal.Balaban.DriftPerCube

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL witnessY)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeInv)
open AdalyFormal.Balaban.LocalizedEstimates
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.HrawCarriers (ScaleQuotient composedQ composedQ_apply feedDatum feedDatum_Q
  norm_curl_sub_flat rawErrorCoeff_trivialU dvd_of_scale)
open AdalyFormal.MechEdges.G16 (rawSigmaZero rawSigmaZero_pos hraw_op norm_bondFnL2)
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.ConstructCDC (TildeFn)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (IsSourceOperator cdcFormTrue)
open AdalyFormal.Balaban.TerminalAssembly (sharpFloorConst)
open AdalyFormal.Balaban.DeltaAlpha0 (PrintedCubeClassI)
open AdalyFormal.Balaban.RecomposeSum (gammaSum CubesRefine terminal_sum_posDef_from_printed)
open AdalyFormal.TerminalBinder (PrintedG1FormAt HrawAt OnMinimizerRange onMinimizerRange_of_forall)
open AdalyFormal.DatumWitness (fineL starScale starDatum)
open AdalyFormal.HrawRDischarge (starDatum_hformR sqrt_gammaSum_lower)

variable {L L' : PeriodicLatticeExtent} {ell : ℕ}

/-! ## §1 — THE SPLIT: flat-referenced drift = pure-gauge-referenced drift + the pure gauge's own -/

/-- `(D_U − D_1) = (D_U − D_W) + (D_W − D_1)`, plaquette by plaquette, at any reference `W`. -/
theorem curlDrift_split
    (U W : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    curlDrift U A p = relDrift U W A p + curlDrift W A p := by
  show curlValueCovariant U A p - curlValueCovariant (trivialU L) A p
      = (curlValueCovariant U A p - curlValueCovariant W A p)
        + (curlValueCovariant W A p - curlValueCovariant (trivialU L) A p)
  abel

/-- `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²` in any normed space — the only inequality spent in the split. -/
theorem norm_add_sq_le_two {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  have hx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hy : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  nlinarith [h, hx, hy, sq_nonneg (‖x‖ - ‖y‖), norm_nonneg (x + y)]

/-! ## §2 — THE PER-CUBE BOUND ON THE **FLAT**-REFERENCED DRIFT -/

/-- **THE FLAT-REFERENCED DRIFT, PRICED PER CUBE, AT THE COST OF THE ROUGHNESS TERM.**

For one cube, one gauge `γ`, `r` bounding the gauged deviations and `ρ` bounding the deviations of
the gauge's own pure gauge `1^{γ⁻¹}`, both on the cube's bonds:

>  `∑_{p ∈ □} ‖(D_U − D_1)A(p)‖² ≤ 64·(r+ρ)²·∑_{b ∈ □̃} ‖A b‖²`.

`64 = 2·32`: the `2` is `norm_add_sq_le_two`, the `32` is cited twice — once through
`DriftPerCube.local_relDrift_le` (the gauged half) and once through `LocDrift.local_curlDrift_le`
applied to the pure gauge itself (the roughness half). -/
theorem local_curlDrift_le_percube (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (γ : GaugeFn L) (r ρ : ℝ) (hr0 : 0 ≤ r) (hρ0 : 0 ≤ ρ)
    (Y : Finset (CSite L ell))
    (hclass : ∀ b ∈ bondsOn Y, RMapLipschitz.frobNorm
      (((periodicGaugeTransform γ U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r)
    (hrough : ∀ b ∈ bondsOn Y, RMapLipschitz.frobNorm
      (((pureGauge (gaugeInv γ)) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ) :
    ∑ p ∈ plaqsOn Y, ‖curlDrift U A p‖ ^ 2
      ≤ 64 * (r + ρ) ^ 2 * ∑ b ∈ bondsOn (tilde hdvd Y), ‖A b‖ ^ 2 := by
  have hsplit : ∑ p ∈ plaqsOn Y, ‖curlDrift U A p‖ ^ 2
      ≤ ∑ p ∈ plaqsOn Y, (2 * ‖relDrift U (pureGauge (gaugeInv γ)) A p‖ ^ 2
          + 2 * ‖curlDrift (pureGauge (gaugeInv γ)) A p‖ ^ 2) := by
    refine Finset.sum_le_sum (fun p _ => ?_)
    rw [curlDrift_split U (pureGauge (gaugeInv γ)) A p]
    exact norm_add_sq_le_two _ _
  have hgauged := local_relDrift_le hell2 hdvd U A γ r hr0 Y hclass
  have hpure := local_curlDrift_le hell2 hdvd (pureGauge (gaugeInv γ)) A ρ hρ0 Y hrough
  have hdistr : ∑ p ∈ plaqsOn Y, (2 * ‖relDrift U (pureGauge (gaugeInv γ)) A p‖ ^ 2
        + 2 * ‖curlDrift (pureGauge (gaugeInv γ)) A p‖ ^ 2)
      = 2 * (∑ p ∈ plaqsOn Y, ‖relDrift U (pureGauge (gaugeInv γ)) A p‖ ^ 2)
        + 2 * (∑ p ∈ plaqsOn Y, ‖curlDrift (pureGauge (gaugeInv γ)) A p‖ ^ 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hdistr] at hsplit
  have hE : (0 : ℝ) ≤ ∑ b ∈ bondsOn (tilde hdvd Y), ‖A b‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq : 32 * r ^ 2 * (∑ b ∈ bondsOn (tilde hdvd Y), ‖A b‖ ^ 2)
      + 32 * ρ ^ 2 * (∑ b ∈ bondsOn (tilde hdvd Y), ‖A b‖ ^ 2)
      ≤ 32 * (r + ρ) ^ 2 * (∑ b ∈ bondsOn (tilde hdvd Y), ‖A b‖ ^ 2) := by
    nlinarith [hE, hr0, hρ0, mul_nonneg hr0 hρ0]
  linarith [hsplit, hgauged, hpure, hsq]

/-! ## §3 — THE GLOBAL BOUND -/

/-- **THE FLAT-REFERENCED DRIFT ENERGY FROM PER-CUBE DATA.**

>  `plaqEnergy (D_U − D_1)A ≤ 256·(r+ρ)²·bondEnergy A`

`256 = 2·32·4`.  The left-hand side is the GLOBAL drift energy the chain's `κ` prices, at the
ORIGINAL `U`; the right-hand side reads only per-cube data and the per-cube gauges' roughness. -/
theorem plaqEnergy_curlDrift_percube {ι : Type*} [DecidableEq ι]
    (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (r ρ : ℝ) (hr0 : 0 ≤ r) (hρ0 : 0 ≤ ρ)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell)) (γ : ι → GaugeFn L)
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite L ell, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (Y i), RMapLipschitz.frobNorm
      (((periodicGaugeTransform (γ i) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r)
    (hrough : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (Y i), RMapLipschitz.frobNorm
      (((pureGauge (gaugeInv (γ i))) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ) :
    plaqEnergy (curlDrift U A) ≤ 256 * (r + ρ) ^ 2 * bondEnergy A := by
  have hell : 0 < ell := by omega
  -- the family sum IS the global sum: each plaquette is met exactly once
  have hpart : plaqEnergy (curlDrift U A)
      = ∑ i ∈ 𝒞, ∑ p ∈ plaqsOn (Y i), ‖curlDrift U A p‖ ^ 2 := by
    rw [sum_family_count 𝒞 (fun i => plaqsOn (Y i)) (fun p => ‖curlDrift U A p‖ ^ 2)]
    show ∑ p : PeriodicLatticePlaquette L, ‖curlDrift U A p‖ ^ 2 = _
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [plaqsOn_family_card_eq_one hell hdvd 𝒞 Y hdisj hcov p]
    norm_num
  have hstep : ∑ i ∈ 𝒞, ∑ p ∈ plaqsOn (Y i), ‖curlDrift U A p‖ ^ 2
      ≤ ∑ i ∈ 𝒞, 64 * (r + ρ) ^ 2 * ∑ b ∈ bondsOn (tilde hdvd (Y i)), ‖A b‖ ^ 2 :=
    Finset.sum_le_sum (fun i hi =>
      local_curlDrift_le_percube hell2 hdvd U A (γ i) r ρ hr0 hρ0 (Y i)
        (hclass i hi) (hrough i hi))
  have hmul := sum_family_le 𝒞 (fun i => bondsOn (tilde hdvd (Y i))) (fun b => ‖A b‖ ^ 2)
    (fun _ => sq_nonneg _) 4 (bondsOn_tilde_mult_le_four hell hdvd 𝒞 Y hdisj)
  have hbe : bondEnergy A = ∑ b : Bond L, ‖A b‖ ^ 2 := rfl
  have hfac : ∑ i ∈ 𝒞, 64 * (r + ρ) ^ 2 * ∑ b ∈ bondsOn (tilde hdvd (Y i)), ‖A b‖ ^ 2
      = 64 * (r + ρ) ^ 2 * ∑ i ∈ 𝒞, ∑ b ∈ bondsOn (tilde hdvd (Y i)), ‖A b‖ ^ 2 := by
    rw [Finset.mul_sum]
  have hc : (0 : ℝ) ≤ 64 * (r + ρ) ^ 2 := by positivity
  have hchain : 64 * (r + ρ) ^ 2 * ∑ i ∈ 𝒞, ∑ b ∈ bondsOn (tilde hdvd (Y i)), ‖A b‖ ^ 2
      ≤ 64 * (r + ρ) ^ 2 * ((4 : ℕ) * ∑ b : Bond L, ‖A b‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hmul hc
  rw [hfac] at hstep
  rw [hpart]
  refine hstep.trans (hchain.trans (le_of_eq ?_))
  rw [hbe]
  push_cast
  ring

/-! ## §4 — THE OPERATOR FORM, ON THE `L²` CARRIER -/

/-- **THE DRIFT OPERATOR NORM FROM PER-CUBE DATA**: `‖D_U X − D_1 X‖ ≤ 16(r+ρ)·‖X‖`.
`16 = √256`. -/
theorem norm_curl_sub_flat_percube {ι : Type*} [DecidableEq ι]
    (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (r ρ : ℝ) (hr0 : 0 ≤ r) (hρ0 : 0 ≤ ρ)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell)) (γ : ι → GaugeFn L)
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite L ell, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (Y i), RMapLipschitz.frobNorm
      (((periodicGaugeTransform (γ i) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r)
    (hrough : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (Y i), RMapLipschitz.frobNorm
      (((pureGauge (gaugeInv (γ i))) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ)
    (X : BondFnL2 L) :
    ‖curlCovariantCLM_L2 U X - curlCovariantCLM_L2 (trivialU L) X‖ ≤ 16 * (r + ρ) * ‖X‖ := by
  rw [norm_curl_sub_flat U X]
  have hb := plaqEnergy_curlDrift_percube hell2 hdvd U (WithLp.ofLp X) r ρ hr0 hρ0 𝒞 Y γ
    hdisj hcov hclass hrough
  have hstep : Real.sqrt (plaqEnergy (curlDrift U (WithLp.ofLp X)))
      ≤ Real.sqrt (256 * (r + ρ) ^ 2 * bondEnergy (WithLp.ofLp X)) := Real.sqrt_le_sqrt hb
  have hbe0 : (0 : ℝ) ≤ bondEnergy (WithLp.ofLp X) := by
    show (0 : ℝ) ≤ ∑ b : Bond L, ‖(WithLp.ofLp X) b‖ ^ 2
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hrw : Real.sqrt (256 * (r + ρ) ^ 2 * bondEnergy (WithLp.ofLp X))
      = 16 * (r + ρ) * Real.sqrt (bondEnergy (WithLp.ofLp X)) := by
    rw [show (256 : ℝ) * (r + ρ) ^ 2 * bondEnergy (WithLp.ofLp X)
        = (16 * (r + ρ)) ^ 2 * bondEnergy (WithLp.ofLp X) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hX : ‖X‖ = Real.sqrt (bondEnergy (WithLp.ofLp X)) := by
    have h := norm_bondFnL2 (WithLp.ofLp X)
    have hid : (WithLp.toLp 2 (WithLp.ofLp X) : BondFnL2 L) = X := rfl
    rwa [hid] at h
  rw [hX]
  exact hstep.trans (le_of_eq hrw)

/-! ## §5 — `hraw` AT THE STAR DATUM WITH THE PER-CUBE `κ`

The chain step is `HrawCarriers`' own, re-run with `κ` abstract: the drift is the only place the
background's size enters, so an abstract operator bound on it is enough. -/

/-- **THE CHAIN BOUND AT AN ABSTRACT DRIFT PRICE.**  Identical to
`HrawCarriers.hraw_composed_flatFine` except that `4√2·α₁(U)` is replaced by any `κ` bounding the
drift operator.  `HrawCarriers`' pieces are reused (`norm_coarseCurlCLM_L2_eq`, `hraw_op`,
`rawErrorCoeff_trivialU`); nothing is re-derived. -/
theorem hraw_composed_of_drift {ell : ℕ} (h : ScaleQuotient L ell L')
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L') (κ : ℝ)
    (hκ : ∀ X : BondFnL2 L',
      ‖curlCovariantCLM_L2 U X - curlCovariantCLM_L2 (trivialU L') X‖ ≤ κ * ‖X‖)
    (A : BondFnL2 L) :
    ‖curlCovariantCLM_L2 U (composedQ h (trivialU L) A)‖
      ≤ rawSigmaZero ell * ‖curlCovariantCLM_L2 (trivialU L) A‖
        + κ * ‖composedQ h (trivialU L) A‖ := by
  have hdvd := dvd_of_scale h
  set Ycar := composedQ h (trivialU L) A with hY
  have htri : ‖curlCovariantCLM_L2 U Ycar‖
      ≤ ‖curlCovariantCLM_L2 (trivialU L') Ycar‖
        + ‖curlCovariantCLM_L2 U Ycar - curlCovariantCLM_L2 (trivialU L') Ycar‖ := by
    have := norm_add_le (curlCovariantCLM_L2 (trivialU L') Ycar)
      (curlCovariantCLM_L2 U Ycar - curlCovariantCLM_L2 (trivialU L') Ycar)
    simpa using this
  have hflat : ‖curlCovariantCLM_L2 (trivialU L') Ycar‖
      = ‖AdalyFormal.MechEdges.G16.coarseCurlCLM_L2 hdvd
          (AdalyFormal.Balaban.BridgeInverse.qCLM (trivialU L) ell A)‖ := by
    rw [hY, composedQ_apply,
      ← AdalyFormal.HrawCarriers.norm_coarseCurlCLM_L2_eq h hdvd
        (AdalyFormal.Balaban.BridgeInverse.qCLM (trivialU L) ell A)]
  have hop := hraw_op hdvd (trivialU L) A
  rw [rawErrorCoeff_trivialU ell, zero_mul, add_zero] at hop
  have hdr := hκ Ycar
  rw [hflat] at htri
  linarith [htri, hop, hdr]

/-! ## §6 — THE TERMINAL THEOREM AT THE STAR DATUM, `hdrift` REPLACED BY PER-CUBE DATA -/

/-- `16·(r+ρ) ≤ ½√(gammaSum ℓ)` whenever `r + ρ ≤ 1/(37664·ℓ³)`.  `37664 = 16·2354`, and
`2354 = 2·1177` is `sqrt_gammaSum_lower`'s (CITED). -/
theorem halfDrift_percube {ell₀ : ℕ} (hell : 0 < ell₀) (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / (37664 * (ell₀ : ℝ) ^ 3)) :
    16 * x ≤ Real.sqrt (gammaSum ell₀) / 2 := by
  have h1 : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell₀ : ℝ) := by linarith
  have hp3 : (0 : ℝ) < (ell₀ : ℝ) ^ 3 := by positivity
  have hg := sqrt_gammaSum_lower hell
  have hstep : 16 * x ≤ 16 * (1 / (37664 * (ell₀ : ℝ) ^ 3)) := by
    have : (0 : ℝ) < 37664 * (ell₀ : ℝ) ^ 3 := by positivity
    nlinarith [hx]
  have heq : 16 * (1 / (37664 * (ell₀ : ℝ) ^ 3)) = (1 / (1177 * (ell₀ : ℝ) ^ 3)) / 2 := by
    field_simp
    ring
  linarith [hstep, heq.le, heq.ge, hg]

/-- **THE RECOMPOSED TERMINAL THEOREM AT THE STAR DATUM, WITH `hdrift` GONE.**

Binder for binder `HrawRDischarge.terminal_sum_at_star_datum`, except that its

    hdrift : α₁(U) ≤ 1/(13336·ℓ³)                      -- GLOBAL, UNGAUGED

is replaced by the three PER-CUBE hypotheses `hclass`, `hrough`, `hsum` on a disjoint covering cube
family with one unrelated gauge per cube.  `hclass` is the shape CMP99b (3.35) supplies; `hrough`
is the datum (3.35) does NOT supply, and `DriftNoGo` proves it cannot be dispensed with. -/
theorem terminal_sum_at_star_datum_percube {ι : Type*} [DecidableEq ι]
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (r ρ : ℝ) (hr0 : 0 ≤ r) (hρ0 : 0 ≤ ρ)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite witnessL 2)) (γ : ι → GaugeFn witnessL)
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite witnessL 2, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (Y i), RMapLipschitz.frobNorm
      (((periodicGaugeTransform (γ i) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r)
    (hrough : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (Y i), RMapLipschitz.frobNorm
      (((pureGauge (gaugeInv (γ i))) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ)
    (hsum : r + ρ ≤ 1 / (37664 * (((2 : ℕ)) : ℝ) ^ 3))
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hα0 : 0 ≤ α₀) (hthr : c * M * α₀ < 1 / (1120 * (((2 : ℕ)) : ℝ) ^ 3))
    (𝒞src : Set (Set (Bond witnessL)))
    (hprinted : PrintedCubeClassI c M α₀ η Lj U 𝒞src)
    (hgeom : CubesRefine AdalyFormal.Balaban.CurvedContent.witnessL_dvd
      (Finset.univ : Finset (CSite witnessL 2))
      (fun z => ({z} : Finset (CSite witnessL 2))) 𝒞src)
    (Qext : BondFnL2 witnessL → BondFnL2 witnessL) (J : BondFnL2 fineL)
    (S : BondFnL2 witnessL →L[ℝ] BondFnL2 witnessL)
    (hS : IsSourceOperator (starDatum bc heps) Qext J S) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hD2 : ∀ B : BondFnL2 witnessL, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (R : ℝ) (hJbound : ‖J‖ ≤ R)
    (hRthr : 2 * ‖solutionOperator (starDatum bc heps)‖ * c₂ * R
      < sharpFloorConst (gammaSum 2) (16 * (r + ρ)) (rawSigmaZero 2))
    (w : TildeFn witnessL 2) (hw : w ≠ 0) :
    0 < cdcFormTrue (starDatum bc heps) bc Qext J U 2 (dinvC U 2) w := by
  have hdvd2 : ∀ μ : Fin 3, (2 : ℕ) ∣ (witnessL μ + 1) := AdalyFormal.Balaban.CurvedContent.witnessL_dvd
  have hκop : ∀ X : BondFnL2 witnessL,
      ‖curlCovariantCLM_L2 U X - curlCovariantCLM_L2 (trivialU witnessL) X‖
        ≤ 16 * (r + ρ) * ‖X‖ :=
    fun X => norm_curl_sub_flat_percube (by norm_num) hdvd2 U r ρ hr0 hρ0 𝒞 Y γ hdisj hcov
      hclass hrough X
  have hrawR : OnMinimizerRange (starDatum bc heps)
      (HrawAt (starDatum bc heps) U (curlCovariantCLM_L2 (trivialU fineL)) (rawSigmaZero 2)
        (16 * (r + ρ))) := by
    refine onMinimizerRange_of_forall _ _ (fun A => ?_)
    show ‖curlCovariantCLM_L2 U ((starDatum bc heps).Q A)‖
        ≤ rawSigmaZero 2 * ‖curlCovariantCLM_L2 (trivialU fineL) A‖
          + 16 * (r + ρ) * ‖(starDatum bc heps).Q A‖
    rw [AdalyFormal.DatumWitness.starDatum_Q bc heps]
    exact hraw_composed_of_drift starScale U (16 * (r + ρ)) hκop A
  have hκ0 : (0 : ℝ) ≤ 16 * (r + ρ) := by linarith
  have hκγ : 16 * (r + ρ) ≤ Real.sqrt (gammaSum 2) := by
    have hh := halfDrift_percube (ell₀ := 2) (by norm_num) (r + ρ) (by linarith) hsum
    have hg : (0 : ℝ) ≤ Real.sqrt (gammaSum 2) := Real.sqrt_nonneg _
    linarith
  exact terminal_sum_posDef_from_printed (by norm_num : (2 : ℕ) ≤ 2)
    AdalyFormal.Balaban.CurvedContent.witnessL_strict
    AdalyFormal.Balaban.CurvedContent.witnessL_dvd
    U c M α₀ η Lj hη hηne hLj hc hM hα0 hthr 𝒞src hprinted hgeom
    (starDatum bc heps) bc (curlCovariantCLM_L2 (trivialU fineL))
    (AdalyFormal.HrawCarriers.feedPen eps : BondFnL2 fineL →L[ℝ] BondFnL2 fineL)
    (rawSigmaZero 2) (16 * (r + ρ)) (rawSigmaZero_pos (by norm_num)) hκ0 hκγ
    (starDatum_hformR bc heps) hrawR
    Qext J S hS c₂ hc₂ hD2 R hJbound hRthr w hw

/-! ## §7 — CONTROLS -/

/-- **THE PRICE OF LOCALIZING, EXHIBITED.**  The global price is `4√2·α₁`, the per-cube one is
`16·(r+ρ)`; the ratio is `2√2 ≈ 2.83`, and the threshold moves from `1/(13336ℓ³)` to
`1/(37664ℓ³)` — a factor `37664/13336 < 2.83`.  Every number is compiled, none narrated. -/
theorem localization_price :
    (16 : ℝ) = 2 * Real.sqrt 2 * (4 * Real.sqrt 2)
    ∧ (37664 : ℕ) = 16 * 2354
    ∧ (2354 : ℕ) = 2 * 1177
    ∧ (256 : ℕ) = 2 * 32 * 4
    ∧ (37664 : ℝ) < 2.83 * 13336 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨by nlinarith [h2], by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **THE TRIVIAL GAUGE RECOVERS THE GLOBAL HYPOTHESIS.**  With `γ i = 1` on every cube the
roughness is exactly `0` and `hclass` is the ungauged global bound — so §6 is a genuine weakening
of the shape of `hdrift`, not a different statement, and the only cost is the constant. -/
theorem trivial_gauge_gives_rough_zero (b : Bond L) :
    RMapLipschitz.frobNorm
      (((pureGauge (gaugeInv (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))))
        b : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0
    ∧ periodicGaugeTransform (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
        (trivialU L) = trivialU L := by
  constructor
  · have hg : (pureGauge (gaugeInv (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))) : Bond L →
        Matrix.specialUnitaryGroup (Fin 2) ℂ) b = 1 := by
      rw [pureGauge_apply]
      simp [gaugeInv]
    rw [hg]
    have h1 : ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1 = 0 := by
      simp
    rw [h1, RMapLipschitz.frobNorm_zero]
  · exact AdalyFormal.Balaban.AlphaAnalyticity.gaugeTransform_one (trivialU L)

/-- **PER-CUBE PLUS ROUGHNESS DOES BOUND THE DRIFT — the positive half, isolated.**  Stated as the
operator bound at `r + ρ`, so a reader can see that the two hypotheses together do the work `hdrift`
did, and `DriftNoGo` can be read as the statement that `hclass` alone does not. -/
theorem percube_plus_roughness_is_global {ι : Type*} [DecidableEq ι]
    (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (r ρ : ℝ) (hr0 : 0 ≤ r) (hρ0 : 0 ≤ ρ)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell)) (γ : ι → GaugeFn L)
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite L ell, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (Y i), RMapLipschitz.frobNorm
      (((periodicGaugeTransform (γ i) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r)
    (hrough : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (Y i), RMapLipschitz.frobNorm
      (((pureGauge (gaugeInv (γ i))) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ)
    (A : Bond L → SuTwo) :
    Real.sqrt (plaqEnergy (curlDrift U A)) ≤ 16 * (r + ρ) * Real.sqrt (bondEnergy A) := by
  have hb := plaqEnergy_curlDrift_percube hell2 hdvd U A r ρ hr0 hρ0 𝒞 Y γ hdisj hcov hclass hrough
  have hbe0 : (0 : ℝ) ≤ bondEnergy A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hstep : Real.sqrt (plaqEnergy (curlDrift U A))
      ≤ Real.sqrt (256 * (r + ρ) ^ 2 * bondEnergy A) := Real.sqrt_le_sqrt hb
  have hrw : Real.sqrt (256 * (r + ρ) ^ 2 * bondEnergy A)
      = 16 * (r + ρ) * Real.sqrt (bondEnergy A) := by
    rw [show (256 : ℝ) * (r + ρ) ^ 2 * bondEnergy A = (16 * (r + ρ)) ^ 2 * bondEnergy A by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rwa [hrw] at hstep

/-- **AND THE WITNESS OF `DriftNoGo` FAILS `hrough` — as it must.**  `bumpU`'s per-cube gauge is
`bumpGauge⁻¹`, whose own pure gauge is `bumpU` itself, at deviation `2`.  So the no-go configuration
is excluded by §6's hypothesis set exactly through `hrough`, and through nothing else. -/
theorem bumpU_fails_only_hrough :
    pureGauge (gaugeInv (gaugeInv bumpGauge)) = bumpU
    ∧ 2 ≤ frobSupBond (pureGauge (gaugeInv (gaugeInv bumpGauge))) := by
  have hinv : gaugeInv (gaugeInv bumpGauge) = bumpGauge := by
    funext x; simp [gaugeInv]
  refine ⟨by rw [hinv]; rfl, ?_⟩
  rw [hinv]
  exact two_le_frobSupBond_bumpU

#print axioms curlDrift_split
#print axioms norm_add_sq_le_two
#print axioms local_curlDrift_le_percube
#print axioms plaqEnergy_curlDrift_percube
#print axioms norm_curl_sub_flat_percube
#print axioms hraw_composed_of_drift
#print axioms halfDrift_percube
#print axioms terminal_sum_at_star_datum_percube
#print axioms localization_price
#print axioms trivial_gauge_gives_rough_zero
#print axioms percube_plus_roughness_is_global
#print axioms bumpU_fails_only_hrough

end AdalyFormal.Balaban.DriftPerCube
