/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import HrawROpNorm
import RecompClass
import DatumWitness
import AdalyFormal.HoleHunt.CenterBlindness

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.longLine false

/-!
# `HrawRDischarge.lean` — `hrawR` DISCHARGED AT THE STAR DATUM, AND WHAT IT COSTS

Lane `compute/hrawr_discharge/`.  Write scope: that directory only.  Never `lake build`.

`RecomposeSum.terminal_sum_posDef_from_printed` carries two covariance-side binders:

    hformR : OnMinimizerRange D (PrintedG1FormAt D (usedAt bc 0) d pen)     -- [SOURCE] (3.128)
    hrawR  : OnMinimizerRange D (HrawAt D U d σ₀ κ)                          -- [OURS]

`hrawR` is the drift-priced chain bound.  This file discharges BOTH at
`compute/datum_witness/`'s star datum `D*`, with numeric `σ₀` and `κ`, and states the recomposed
terminal theorem there with the two binders gone.

## THE FOUR THINGS ESTABLISHED, AND WHICH OF THEM IS NEW

1. **§1 (`HrawROpNorm`)** `‖D_U‖ ≤ 4`: the operator-norm form of a count already in the tree.
2. **§2** `‖H₁‖ ≤ √65` at `D*`, with a NUMERIC admissible `ε` (`ε ≥ 1024 + a`).  This is
   `compute/datum_witness/` SCOPE §5 R1, whose two missing inputs were "`‖rInv‖ = ℓ³` not imported"
   and "an operator-norm bound on `curlCovariantCLM_L2`".  Both are supplied here.
3. **§3** `hrawR` at `D*`: `σ₀ = ℓ^{-1/2}`, `κ = 4√2·α₁(U)`, holding for EVERY coarse background
   `U` with no hypothesis at all.  The discharge itself is unconditional; only its COMPOSITION into
   the terminal chain needs `κ ≤ ½√(gammaSum ℓ)`, i.e. smallness.
4. **§5** the drift price `4√2·α₁(U)` is **NOT SHARP, and the gap is exactly the centre**.  At
   `U ≡ −1` — the very background `GaugeInvPrinted.printed_class_does_not_reach_the_consumer` uses
   to separate the printed per-cube class from the global one — the drift-priced `κ` is `8√2`, a
   thousand times past the threshold, while the TRUE `κ` is `0`.  §5 proves this and upgrades §3's
   discharge to a centre-blind class, strictly larger than `{α₁(U) ≤ ...}`.

**Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.**
-/

namespace AdalyFormal.HrawRDischarge

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration
  PeriodicLatticePlaquette periodicLatticeShift)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.Balaban.CovariantOperators (curlValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg)
open AdalyFormal.Balaban.AlphaAnalyticity (centerU frobSupBond_centerU negOneElem)
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.ConstructCDC (TildeFn)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (IsSourceOperator cdcFormTrue)
open AdalyFormal.Balaban.TerminalAssembly (sharpFloorConst)
open AdalyFormal.Balaban.DeltaAlpha0 (PrintedCubeClassI)
open AdalyFormal.Balaban.RecomposeSum (gammaSum gammaSum_pos gammaSum_lower CubesRefine
  terminal_sum_posDef_from_printed)
open AdalyFormal.TerminalBinder (PrintedG1FormAt HrawAt OnMinimizerRange onMinimizerRange_of_forall
  feedDatumGen)
open AdalyFormal.HrawCarriers (ScaleQuotient composedQ feedDatum feedDatum_Q feedDatum_hraw
  feedDatum_isPrintedG1Form feedPen sqrt_two_le)
open AdalyFormal.MechEdges.G16 (rawSigmaZero rawSigmaZero_pos)
open AdalyFormal.DatumWitness (fineL starScale starDatum starDatum_Q)
open QSurjRInverse (rInvComposed norm_H1_le_transport_uniform)
open AdalyFormal.HoleHunt.CenterBlindness (negI negI_coe RMap_negI flipSign centralFlipConfig
  RMap_centralFlipConfig)

/-! ## §2 — `‖H₁‖` AT THE STAR DATUM, NUMERICALLY: `compute/datum_witness/` R1, CLOSED

`datum_witness/SCOPE.md` §5 R1 reads: the `‖H₁‖` bound is available "once `‖rInv‖ = ℓ³` is imported
and an operator-norm bound on `curlCovariantCLM_L2` is supplied".  `QSurjRInverse` supplies the
first (`opNorm_rInvComposed`, EXACTLY `ℓ³`), `HrawROpNorm` §1 the second (`≤ 4`). -/

/-- The star datum IS the general-fine datum at a FLAT fine background: `feedGinv` and
`feedGinvGen … (trivialU)` are the same three summands, so the two `build`s agree definitionally.
Stated (and proved by `rfl`) so that `QSurjRInverse`'s `‖H₁‖` machinery — which is written for
`feedDatumGen` — applies to `starDatum` without a transport argument. -/
theorem starDatum_eq_feedDatumGen (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) :
    starDatum bc heps = feedDatumGen starScale (trivialU fineL) heps (le_of_lt bc.a_pos) := rfl

/-- **`‖H₁‖ ≤ √65` AT `D*`, WITH THE `ε`-THRESHOLD A NUMBER.**

`ε ≥ 1024 + a` suffices, and `1024 = 16·ℓ⁶` at `ℓ = 2` is `4²·(ℓ³)²`: the `4` is `‖D‖`
(`HrawROpNorm.opNorm_curl_le_four`) and the `ℓ³` is `‖R‖` (`QSurjRInverse.opNorm_rInvComposed`,
EXACT).  `65 = ℓ⁶ + 1`.

Nothing on either side mentions the background, the source, or the coarse lattice. -/
theorem starDatum_norm_H1_le_sqrt65 (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (hbig : 1024 + bc.a ≤ eps) :
    ‖solutionOperator (starDatum bc heps)‖ ≤ Real.sqrt 65 := by
  have hb : ‖(curlCovariantCLM_L2 (trivialU fineL)).comp
      (rInvComposed starScale (trivialU fineL))‖ ^ 2 + bc.a ≤ eps := by
    refine hbig_of_eps_ge starScale (trivialU fineL) bc.a eps ?_
    have h64 : (16 : ℝ) * (((2 : ℕ) : ℝ)) ^ 6 = 1024 := by norm_num
    rw [h64]
    exact hbig
  have h := norm_H1_le_transport_uniform starScale (trivialU fineL) heps (le_of_lt bc.a_pos) hb
  rw [starDatum_eq_feedDatumGen bc heps]
  refine le_trans h (le_of_eq ?_)
  norm_num

/-- **AND THEREFORE `‖H₁‖ ≤ 9`** — the rational form every downstream threshold wants. -/
theorem starDatum_norm_H1_le_nine (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (hbig : 1024 + bc.a ≤ eps) :
    ‖solutionOperator (starDatum bc heps)‖ ≤ 9 := by
  refine le_trans (starDatum_norm_H1_le_sqrt65 bc heps hbig) ?_
  have h : (65 : ℝ) ≤ 9 ^ 2 := by norm_num
  calc Real.sqrt 65 ≤ Real.sqrt (9 ^ 2) := Real.sqrt_le_sqrt h
    _ = 9 := Real.sqrt_sq (by norm_num)

/-- **THE `ε` WINDOW IS NONEMPTY** — exhibited, so §2 is not conditional on something unmet. -/
theorem eps_window_inhabited (bc : BaseConstant) :
    ∃ eps : ℝ, 0 < eps ∧ 1024 + bc.a ≤ eps :=
  ⟨1024 + bc.a, by have := bc.a_pos; linarith, le_rfl⟩

/-! ## §3 — `hrawR` AT THE STAR DATUM

`HrawFeed.feedDatum_hraw` (REUSED) is already the pointwise bound at `feedDatum`, UNIVERSALLY in
`A` and at EVERY coarse background.  So at `D*` the minimiser-range binder is not merely
dischargeable — the universal binder is, and the weakening `TerminalBinder` §1 performs is not
needed here.  Both forms are recorded, because the recomposed chain consumes the weaker one. -/

/-- **THE POINTWISE (UNIVERSAL) FORM AT `D*`.**  `σ₀ = ℓ^{-1/2}`, `κ = 4√2·α₁(U)`; no hypothesis on
`U`, on `t`, or on `ε`. -/
theorem starDatum_hraw (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (A : BondFnL2 fineL) :
    HrawAt (starDatum bc heps) U (curlCovariantCLM_L2 (trivialU fineL)) (rawSigmaZero 2)
      (4 * Real.sqrt 2 * frobSupBond U) A :=
  feedDatum_hraw starScale heps (le_of_lt bc.a_pos) U A

/-- **`hrawR` AT `D*`** — the binder of `terminal_sum_posDef_from_printed`, discharged. -/
theorem starDatum_hrawR (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    OnMinimizerRange (starDatum bc heps)
      (HrawAt (starDatum bc heps) U (curlCovariantCLM_L2 (trivialU fineL)) (rawSigmaZero 2)
        (4 * Real.sqrt 2 * frobSupBond U)) :=
  onMinimizerRange_of_forall _ _ (starDatum_hraw bc heps U)

/-- **`hformR` AT `D*`** — the other covariance binder, also a theorem here: `feedDatum`'s `G₁⁻¹` is
BUILT as `‖∂₁A‖² + ε‖A‖² + a‖QA‖²`, so (3.128) holds as an EQUALITY with `d = ∂₁`, `pen = √ε·I`
(`HrawFeed.feedDatum_isPrintedG1Form`, REUSED).  `usedAt bc 0 = bc.a` definitionally. -/
theorem starDatum_hformR (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) :
    OnMinimizerRange (starDatum bc heps)
      (PrintedG1FormAt (starDatum bc heps) (usedAt bc 0)
        (curlCovariantCLM_L2 (trivialU fineL))
        (feedPen eps : BondFnL2 fineL →L[ℝ] BondFnL2 fineL)) :=
  fun B => feedDatum_isPrintedG1Form starScale heps (le_of_lt bc.a_pos) _

/-! ## §4 — THE ARITHMETIC THAT LETS `κ` INTO THE RECOMPOSED FLOOR

`terminal_sum_posDef_from_printed` needs `κ ≤ √(gammaSum ℓ)`, and a non-degenerate floor needs the
half-drift `κ ≤ ½√(gammaSum ℓ)`.  Every constant below is counted, none fitted:

* `gammaSum ℓ ≥ 1/(1383840·ℓ⁶)` — `RecompFloor.gammaSum_lower`, CITED (`1383840 = 4·345960`);
* `1177² = 1385329 ≥ 1383840`, so `√(gammaSum ℓ) ≥ 1/(1177·ℓ³)`;
* `√2 ≤ 1.4143` — `HrawCarriers.sqrt_two_le`, CITED;
* `4·1.4143·2354 = 13317.05… ≤ 13336`, which is why the SAME rational `1/(13336·ℓ³)` that
  `TerminalBinder.halfDrift_split` uses against `gammaBrick` also clears `gammaSum`'s half — even
  though `gammaSum = gammaBrick/4`, i.e. the target is `2×` tighter.  The margin is `0.14%` and is
  exhibited here rather than asserted. -/

/-- `√(gammaSum ℓ) ≥ 1/(1177·ℓ³)`. -/
theorem sqrt_gammaSum_lower {ell : ℕ} (hell : 0 < ell) :
    1 / (1177 * (ell : ℝ) ^ 3) ≤ Real.sqrt (gammaSum ell) := by
  have h1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell : ℝ) := by linarith
  have hp6 : (0 : ℝ) < (ell : ℝ) ^ 6 := by positivity
  have hlow := gammaSum_lower hell
  have hrw : (1 / (1177 * (ell : ℝ) ^ 3)) ^ 2 = 1 / (1385329 * (ell : ℝ) ^ 6) := by
    have hne : ((ell : ℝ)) ≠ 0 := ne_of_gt h0
    field_simp
    ring
  have hcmp : (1 : ℝ) / (1385329 * (ell : ℝ) ^ 6) ≤ 1 / (1383840 * (ell : ℝ) ^ 6) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hp6]
  have hsq : (1 / (1177 * (ell : ℝ) ^ 3)) ^ 2 ≤ gammaSum ell := by
    rw [hrw]; linarith
  have h2 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity)] at h2

/-- **THE HALF-DRIFT HYPOTHESIS FOR THE SUMMATION FLOOR.**  `α₁ ≤ 1/(13336·ℓ³) ⟹ 4√2·α₁ ≤
½√(gammaSum ℓ)`. -/
theorem halfDrift_sum {ell : ℕ} (hell : 0 < ell) (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / (13336 * (ell : ℝ) ^ 3)) :
    4 * Real.sqrt 2 * x ≤ Real.sqrt (gammaSum ell) / 2 := by
  have h1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell : ℝ) := by linarith
  have hp3 : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  have hs := sqrt_two_le
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hg := sqrt_gammaSum_lower hell
  have hstep1 : 4 * Real.sqrt 2 * x ≤ 4 * 1.4143 * (1 / (13336 * (ell : ℝ) ^ 3)) := by
    have hA : 4 * Real.sqrt 2 ≤ 4 * 1.4143 := by linarith
    have hB : (0 : ℝ) ≤ 4 * Real.sqrt 2 := by positivity
    nlinarith [hx, hx0, hA, hB]
  have hstep2 : 4 * 1.4143 * (1 / (13336 * (ell : ℝ) ^ 3))
      ≤ (1 / (1177 * (ell : ℝ) ^ 3)) / 2 := by
    have hL : 4 * 1.4143 * (1 / (13336 * (ell : ℝ) ^ 3))
        = (4 * 1.4143) / (13336 * (ell : ℝ) ^ 3) := by ring
    have hR : (1 / (1177 * (ell : ℝ) ^ 3)) / 2 = 1 / (2354 * (ell : ℝ) ^ 3) := by
      have hne : ((ell : ℝ)) ≠ 0 := ne_of_gt h0
      field_simp
      ring
    rw [hL, hR, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hp3]
  linarith

/-- And the weaker form the headline literally asks for. -/
theorem drift_le_sqrt_gammaSum {ell : ℕ} (hell : 0 < ell) (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / (13336 * (ell : ℝ) ^ 3)) :
    4 * Real.sqrt 2 * x ≤ Real.sqrt (gammaSum ell) := by
  have h := halfDrift_sum hell x hx0 hx
  have hg : (0 : ℝ) ≤ Real.sqrt (gammaSum ell) := Real.sqrt_nonneg _
  linarith

/-! ## §5 — THE DRIFT PRICE IS NOT SHARP: THE CENTRE

`AlphaAnalyticity.centerU` (`U ≡ −1`) is the tree's own separator between the printed per-cube class
and the global one (`GaugeInvPrinted.printed_class_does_not_reach_the_consumer`).  It has
`α₁ = 2√2` (`frobSupBond_centerU`, CITED), the LARGEST value the quantity takes, so the drift price
`4√2·α₁ = 16` is `10⁵` times past `½√(gammaSum 2)`.

**And yet `hrawR` holds there with `κ = 0`.**  The covariant curl depends on `U` only through
`RMap(U b)`, and `RMap` is blind to the centre (`HoleHunt.CenterBlindness.RMap_negI`, REUSED, NOT
rebuilt).  So `α₁` is the wrong invariant for this binder, and §5b upgrades §3's discharge to the
centre-blind class, which strictly contains `{α₁ ≤ 1/(13336ℓ³)}`. -/

/-- **THE CURL IS BLIND TO A CENTRAL FLIP**, plaquette by plaquette.  The flip `ε` is arbitrary per
bond, so this covers every one of the `2^{#bonds}` central relatives of `U`. -/
theorem curlValueCovariant_centralFlip {L : PeriodicLatticeExtent} (ε : Bond L → Bool)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    curlValueCovariant (centralFlipConfig ε U) A p = curlValueCovariant U A p := by
  show A (p.1, p.2.1.1)
      + RMap (centralFlipConfig ε U (p.1, p.2.1.1))
          (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
      - RMap (centralFlipConfig ε U (p.1, p.2.1.2))
          (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))
      - A (p.1, p.2.1.2) = _
  rw [RMap_centralFlipConfig ε U (p.1, p.2.1.1), RMap_centralFlipConfig ε U (p.1, p.2.1.2)]
  rfl

/-- The same at the `BondFnL2 → PlaqFnL2` operator. -/
theorem curlCovariantCLM_L2_centralFlip {L : PeriodicLatticeExtent} (ε : Bond L → Bool)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (X : BondFnL2 L) :
    curlCovariantCLM_L2 (centralFlipConfig ε U) X = curlCovariantCLM_L2 U X := by
  set A : Bond L → SuTwo := WithLp.ofLp X with hA
  have hX : (WithLp.toLp 2 A : BondFnL2 L) = X := rfl
  rw [← hX, curlCovariantCLM_L2_toLp, curlCovariantCLM_L2_toLp]
  exact congrArg (WithLp.toLp 2) (funext (fun p => curlValueCovariant_centralFlip ε U A p))

/-- **`HrawAt` IS A CENTRE-BLIND STATEMENT.**  Same `D`, same `d`, same `σ₀`, same `κ`, same `A`:
the two sides are literally the same inequality. -/
theorem hrawAt_centralFlip {Hs : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
    {L : PeriodicLatticeExtent} {P₁ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (ε : Bond L → Bool)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Hs →L[ℝ] P₁) (σ₀ κ : ℝ) (A : Hs) :
    HrawAt D (centralFlipConfig ε U) d σ₀ κ A ↔ HrawAt D U d σ₀ κ A := by
  constructor
  · intro hh
    show ‖curlCovariantCLM_L2 U (D.Q A)‖ ≤ σ₀ * ‖d A‖ + κ * ‖D.Q A‖
    rw [← curlCovariantCLM_L2_centralFlip ε U (D.Q A)]
    exact hh
  · intro hh
    show ‖curlCovariantCLM_L2 (centralFlipConfig ε U) (D.Q A)‖ ≤ σ₀ * ‖d A‖ + κ * ‖D.Q A‖
    rw [curlCovariantCLM_L2_centralFlip ε U (D.Q A)]
    exact hh

/-! ### §5b — THE CENTRE-BLIND DISCHARGE -/

/-- **`hrawR` AT `D*` FOR EVERY CENTRAL RELATIVE OF A SMALL BACKGROUND.**  The drift is priced by
`α₁(V)`, the SMALL representative, while the background `Δ_k` is evaluated at is the flipped
`centralFlipConfig ε V`, whose own `α₁` may be as large as `2√2`. -/
theorem starDatum_hrawR_centerBlind (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (ε : Bond witnessL → Bool)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    OnMinimizerRange (starDatum bc heps)
      (HrawAt (starDatum bc heps) (centralFlipConfig ε V)
        (curlCovariantCLM_L2 (trivialU fineL)) (rawSigmaZero 2)
        (4 * Real.sqrt 2 * frobSupBond V)) :=
  fun B => (hrawAt_centralFlip (starDatum bc heps) ε V _ _ _ _).mpr
    (starDatum_hraw bc heps V _)

/-- **THE DRIFT PRICE AT `U ≡ −1` IS `16`.**  `α₁(centerU) = 2√2` (`AlphaAnalyticity`,
`frobSupBond_centerU`, CITED — the LARGEST value the quantity takes on `SU(2)`), so
`4√2·2√2 = 8·2 = 16` exactly. -/
theorem drift_price_at_centerU :
    4 * Real.sqrt 2 * frobSupBond (centerU witnessL) = 16 := by
  rw [frobSupBond_centerU]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h2]

/-- `centerU = ` every link flipped, from the flat configuration. -/
theorem centerU_eq_flip {L : PeriodicLatticeExtent} :
    centerU L = centralFlipConfig (fun _ => true) (trivialU L) := by
  funext b
  show negOneElem = flipSign true * (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
  rw [mul_one]
  show negOneElem = negI
  exact Subtype.ext rfl

/-- **THE HEADLINE OF §5.**  At `U ≡ −1`, at the star datum:

* the drift-priced `κ` is `4√2·α₁ = 4√2·2√2 = 16`, which does NOT meet `½√(gammaSum 2)`;
* the binder nevertheless holds with `κ = 0`.

So the smallness hypothesis §6 carries is a property of the CHOSEN price, not of the binder. -/
theorem starDatum_hrawR_at_centerU (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) :
    OnMinimizerRange (starDatum bc heps)
      (HrawAt (starDatum bc heps) (centerU witnessL)
        (curlCovariantCLM_L2 (trivialU fineL)) (rawSigmaZero 2) 0)
    ∧ 4 * Real.sqrt 2 * frobSupBond (centerU witnessL) = 16 := by
  refine ⟨?_, drift_price_at_centerU⟩
  have h := starDatum_hrawR_centerBlind bc heps (fun _ => true) (trivialU witnessL)
  rw [AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU witnessL, mul_zero] at h
  rw [centerU_eq_flip]
  exact h

/-- **AND THE PRICE IS PAST THE THRESHOLD BY MORE THAN A FACTOR `10⁵`.**  `½√(gammaSum 2) ≤
½·√(gammaBrick 2)` and `gammaSum 2 ≤ 1/360·1/32`, so the half-threshold is below `1/1000`, while the
drift price at `U ≡ −1` is `16`.  Stated as the explicit failure of the hypothesis §6 would need. -/
theorem centerU_drift_price_fails :
    ¬ (4 * Real.sqrt 2 * frobSupBond (centerU witnessL)
        ≤ Real.sqrt (gammaSum 2) / 2) := by
  intro hcon
  rw [drift_price_at_centerU] at hcon
  -- `gammaSum 2 = gammaBrick 2 / 4` and `gammaBrick ℓ ≤ (1/360)·ℓ⁻⁵ ≤ 1/360`
  have hup : gammaSum 2 ≤ 1 / 360 := by
    unfold gammaSum AdalyFormal.Balaban.TerminalCompose.gammaBrick
    norm_num
  have hs : Real.sqrt (gammaSum 2) ≤ 1 := by
    have h1 : Real.sqrt (gammaSum 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_one] at h1
  linarith

/-! ## §6 — THE RECOMPOSED TERMINAL THEOREM AT THE STAR DATUM, `hrawR` AND `hformR` DISCHARGED

`RecomposeSum.terminal_sum_posDef_from_printed` is reproduced binder for binder EXCEPT that

* `D`, `d`, `pen`, `σ₀`, `κ` are no longer free — they are `D*`, `∂₁`, `√ε·I`, `ℓ^{-1/2}` and
  `4√2·α₁(V)`;
* `hσ₀`, `hκ`, `hκγ`, `hformR`, `hrawR` are GONE — all five are theorems here;
* one hypothesis is ADDED, `hdrift : α₁(V) ≤ 1/(13336·ℓ³)`, and §5 shows what it is really buying.

`U` is presented as `centralFlipConfig ε V`: `ε` is arbitrary and `ε = fun _ => false` recovers
`U = V`, so nothing is lost by writing it this way, while the class of admissible `U` is strictly
larger than `{α₁(U) ≤ 1/(13336·ℓ³)}` (§5, `centerU`). -/
theorem terminal_sum_at_star_datum
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (ε : Bond witnessL → Bool)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (hdrift : frobSupBond V ≤ 1 / (13336 * (((2 : ℕ)) : ℝ) ^ 3))
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hα0 : 0 ≤ α₀) (hthr : c * M * α₀ < 1 / (1120 * (((2 : ℕ)) : ℝ) ^ 3))
    (𝒞src : Set (Set (Bond witnessL)))
    (hprinted : PrintedCubeClassI c M α₀ η Lj (centralFlipConfig ε V) 𝒞src)
    (hgeom : CubesRefine AdalyFormal.Balaban.CurvedContent.witnessL_dvd
      (Finset.univ : Finset (AdalyFormal.Balaban.LocalizedEstimates.CSite witnessL 2))
      (fun z => ({z} : Finset (AdalyFormal.Balaban.LocalizedEstimates.CSite witnessL 2))) 𝒞src)
    (Qext : BondFnL2 witnessL → BondFnL2 witnessL) (J : BondFnL2 fineL)
    (S : BondFnL2 witnessL →L[ℝ] BondFnL2 witnessL)
    (hS : IsSourceOperator (starDatum bc heps) Qext J S) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hD2 : ∀ B : BondFnL2 witnessL, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (R : ℝ) (hJbound : ‖J‖ ≤ R)
    (hRthr : 2 * ‖solutionOperator (starDatum bc heps)‖ * c₂ * R
      < sharpFloorConst (gammaSum 2) (4 * Real.sqrt 2 * frobSupBond V) (rawSigmaZero 2))
    (w : TildeFn witnessL 2) (hw : w ≠ 0) :
    0 < cdcFormTrue (starDatum bc heps) bc Qext J (centralFlipConfig ε V) 2
      (dinvC (centralFlipConfig ε V) 2) w := by
  have hκ0 : (0 : ℝ) ≤ 4 * Real.sqrt 2 * frobSupBond V :=
    mul_nonneg (by positivity) (frobSupBond_nonneg V)
  have hκγ : 4 * Real.sqrt 2 * frobSupBond V ≤ Real.sqrt (gammaSum 2) :=
    drift_le_sqrt_gammaSum (by norm_num) _ (frobSupBond_nonneg V) hdrift
  exact terminal_sum_posDef_from_printed (by norm_num : (2 : ℕ) ≤ 2)
    AdalyFormal.Balaban.CurvedContent.witnessL_strict
    AdalyFormal.Balaban.CurvedContent.witnessL_dvd
    (centralFlipConfig ε V) c M α₀ η Lj hη hηne hLj hc hM hα0 hthr 𝒞src hprinted hgeom
    (starDatum bc heps) bc (curlCovariantCLM_L2 (trivialU fineL))
    (feedPen eps : BondFnL2 fineL →L[ℝ] BondFnL2 fineL)
    (rawSigmaZero 2) (4 * Real.sqrt 2 * frobSupBond V) (rawSigmaZero_pos (by norm_num)) hκ0 hκγ
    (starDatum_hformR bc heps) (starDatum_hrawR_centerBlind bc heps ε V)
    Qext J S hS c₂ hc₂ hD2 R hJbound hRthr w hw

#print axioms starDatum_eq_feedDatumGen
#print axioms starDatum_norm_H1_le_sqrt65
#print axioms starDatum_norm_H1_le_nine
#print axioms eps_window_inhabited
#print axioms starDatum_hraw
#print axioms starDatum_hrawR
#print axioms starDatum_hformR
#print axioms sqrt_gammaSum_lower
#print axioms halfDrift_sum
#print axioms drift_le_sqrt_gammaSum
#print axioms curlValueCovariant_centralFlip
#print axioms curlCovariantCLM_L2_centralFlip
#print axioms hrawAt_centralFlip
#print axioms starDatum_hrawR_centerBlind
#print axioms drift_price_at_centerU
#print axioms centerU_eq_flip
#print axioms starDatum_hrawR_at_centerU
#print axioms centerU_drift_price_fails
#print axioms terminal_sum_at_star_datum

end AdalyFormal.HrawRDischarge
