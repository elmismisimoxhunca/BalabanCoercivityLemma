/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import CovPerCube
import HrawRDischarge
import AdalyFormal.Balaban.RegularUDomainWitness

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.style.longLine false

/-!
# `FloorMembership` — THE SCHUR-FLOOR BINDER, GAUGED THROUGH THE PER-CUBE SUMMATION FLOOR

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.

## §0 — ROW ZERO: THE ONE BINDER THIS FILE REMOVES, AND WHAT IT COSTS

`CovTerminal.terminal_covariant_bothGauged` (`compute/covariant_datum`) frees BOTH backgrounds onto
their joint gauge orbit, and its §6b records that ONE binder resisted:

    hthr : frobSupBond U ≤ 1/(186·ℓ₀³)

`frobSupBond` is measured against the FLAT reference and is manifestly gauge variant
(`CovWitness.two_le_frobSupBond_spikeU`), so `hthr` is a genuine ungauged smallness condition on the
coarse background.  §6b names the fix — route the floor through `SchurComposed`/`TerminalBrick`,
which are outside that lane's write scope — and stops there.  This file runs that route.

| binder of `terminal_covariant_bothGauged` | here |
|---|---|
| `hsmallUGauged : α₁(U^{γ̄}) ≤ 1/(13336·ℓ₀³)` | `≤ 1/(26672·ℓ₀³)` — **2× tighter**, DERIVED in §1 |
| `hsmallFineGauged : ‖H₁‖·rawErrorCoeff ≤ 1/(2356·ℓ₀³)` | `≤ 1/(4708·ℓ₀³)` — **2× tighter**, DERIVED in §1 |
| `hthr : α₁(U) ≤ 1/(186·ℓ₀³)` | **GONE.**  Replaced by the per-cube class (§2) / the printed class (3.35) + [GEOM] (§3) |
| `hδ : δ < 1/(1370001600·ℓ₀⁶·…)` | `δ < 1/(5480006400·ℓ₀⁶·…)` — **4×** tighter, `RecompTerminal`'s, CITED |
| everything else | unchanged |

**No number here is fitted.**  `26672 = 2·13336`, `4708 = 2·2354 = 4·1177`, and `5480006400 =
4·1370001600`; each factor is named to the counted multiplicity it comes from in §1 and §3.

## §0a — WHY THIS IS NOT `DriftNoGo` TERRITORY (the shape adjudication, in one paragraph)

`SCOPE.md` §1 traces `hthr` to its ONLY consumption site,
`TerminalBrick.cdc_floor_class_uniform`, whose conclusion is a QUADRATIC FORM inequality

    gammaBrick ℓ · ‖B̃‖²  ≤  ⟪C₀B̃, D_U^*D_U (C₀B̃)⟫

over the lattice.  `frobSupBond U` appears there ONLY in a hypothesis whose sole job is to bound the
coefficient `(1/360)ℓ⁻⁵ − 96·α₁²` from below (`TerminalBrick.gammaBrick_le_coefficient`); the
conclusion mentions no flat reference at all.  `DriftNoGo.percube_data_cannot_price_the_drift`
obstructs pricing a FLAT-REFERENCED quantity by per-cube data — it does not apply to a summable
quadratic form, and `compute/recompose_sum`'s `RecompFloor.hpoin_sum_at_cZero` is the constructive
proof that it does not: that theorem already floors the SAME form from per-cube gauged data alone.
This file's only new mathematics is §1 — the drift budget re-split so that the summation floor's
constant `gammaSum = gammaBrick/4` still absorbs BOTH halves of the gauged drift price.

**ISLAND.**  Nothing is installed in `formal/`; nothing enters `Spine.lean`'s import cone.
-/

namespace AdalyFormal.FloorMembership

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 witnessMElem)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg
  frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AlphaAnalyticity (SU2 GaugeFn gaugeInv spikeGauge)
open AdalyFormal.Balaban.RegularUDomainWitness (frobSupBond_trivialU)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (IsSourceOperator cdcFormTrue)
open AdalyFormal.Balaban.SourceWiredJ (JsuTwo)
open AdalyFormal.Balaban.SourceWired (LinkDev norm_source_le_of_linkDev)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.TerminalAssembly (sharpFloorConst)
open AdalyFormal.Balaban.DeltaAlpha0 (PrintedCubeClassI)
open AdalyFormal.Balaban.LocalizedEstimates (tilde bondsOn CSite singleton_family_ok)
open AdalyFormal.Balaban.RecomposeSum (gammaSum gammaSum_pos gammaSum_lower sumRadius
  CubesRefine terminal_sum_posDef_on_range terminal_sum_posDef_from_printed
  sharpFloorConstSum_lower_halfDrift delta_threshold_sum_suffices hpoin_sum_at_cZero)
open AdalyFormal.HrawRDischarge (sqrt_gammaSum_lower)
open AdalyFormal.HrawCarriers (ScaleQuotient ell_pos_of_scale sqrt_two_le feedPen)
open AdalyFormal.MechEdges.G16 (rawSigmaZero rawSigmaZero_pos rawErrorCoeff)
open AdalyFormal.TerminalBinder (PrintedG1FormAt HrawAt OnMinimizerRange feedDatumGen
  feedDatumGen_isPrintedG1Form)
open AdalyFormal.CovariantDatum (coarseGauge coarseGauge_surjective gaugedKappa gaugedKappa_nonneg
  hraw_on_range_gauged spikeU spikeU_gauged_flat spikeU_at two_le_frobSupBond_spikeU
  gluedGauge frobSupBond_glued_le liftCoarseGauge coarseGauge_liftCoarseGauge
  single_cube_mismatch_zero rawErrorCoeff_spikeU_gauged)

variable {Hs : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
variable {L L' : PeriodicLatticeExtent} {ell : ℕ}

/-! ## §1 — THE DRIFT BUDGET, RE-SPLIT FOR THE SUMMATION FLOOR

`terminal_covariant_bothGauged` needs `κ ≤ ½√(gammaBrick ℓ₀)`; the summation route needs
`κ ≤ ½√(gammaSum ℓ₀)` with `gammaSum = gammaBrick/4`, i.e. a target that is **`2×` tighter**.

`HrawRDischarge.halfDrift_sum` (CITED) already shows that `α₁ ≤ 1/(13336·ℓ³)` alone clears
`½√(gammaSum ℓ)` — but its own docstring measures the margin at **0.14%**, so the COARSE term
consumes essentially the whole budget and nothing is left for the FINE one.  `gaugedKappa` has both.

So the budget is split in two EQUAL halves and each half is priced separately.  Every constant:

* `√(gammaSum ℓ₀) ≥ 1/(1177·ℓ₀³)` — `HrawRDischarge.sqrt_gammaSum_lower`, CITED
  (`1177² = 1385329 ≥ 1383840 = 4·345960`);
* half of that is `1/(2354·ℓ₀³)`; **each of the two drift terms gets `1/(4708·ℓ₀³)`**, and
  `4708 = 2·2354 = 4·1177`;
* `√2 ≤ 1.4143` — `HrawCarriers.sqrt_two_le`, CITED;
* the coarse term `4√2·x ≤ 1/(4708·ℓ₀³)` needs `4·1.4143·4708 = 26634.0976 ≤ 26672`, which is why
  the coarse radius is `1/(26672·ℓ₀³)` and `26672 = 2·13336` — **exactly twice as tight as
  `TerminalBinder.halfDrift_split`'s**, the factor `2` being the half of the budget that halving
  the Poincaré constant (`gammaSum = gammaBrick/4`, so `√` halves) took away.  The margin is
  `37.9/26672 = 0.142%` and is exhibited by `nlinarith`, not asserted.

The fine radius `1/(4708·ℓ₀³)` is likewise exactly `2×` tighter than `halfDrift_split`'s
`1/(2356·ℓ₀³)` (`4708 = 2·2354`, and `2354 < 2356`, so it is very slightly tighter still — that
`2/2356 = 0.08%` is the difference between `√(gammaBrick)`'s `589` and `√(gammaSum)`'s `1177`,
`1178 = 2·589` vs `1177`). -/

/-- **THE SPLIT HALF-DRIFT ABSORPTION FOR THE SUMMATION FLOOR.**

    x ≤ 1/(26672·ℓ₀³)  ∧  y ≤ 1/(4708·ℓ₀³)   ⟹   4√2·x + y ≤ ½√(gammaSum ℓ₀).

This is `TerminalBinder.halfDrift_split`'s statement with `gammaBrick` replaced by `gammaSum` and
both radii doubled in tightness.  Nothing else in the chain changes. -/
theorem halfDrift_split_sum {ell₀ : ℕ} (hell : 0 < ell₀) (x y : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / (26672 * (ell₀ : ℝ) ^ 3))
    (hy : y ≤ 1 / (4708 * (ell₀ : ℝ) ^ 3)) :
    4 * Real.sqrt 2 * x + y ≤ Real.sqrt (gammaSum ell₀) / 2 := by
  have h1 : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell₀ : ℝ) := by linarith
  have hp3 : (0 : ℝ) < (ell₀ : ℝ) ^ 3 := by positivity
  have hs := sqrt_two_le
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hg := sqrt_gammaSum_lower hell
  -- the coarse term, priced at half the budget
  have hstep1 : 4 * Real.sqrt 2 * x ≤ 4 * 1.4143 * (1 / (26672 * (ell₀ : ℝ) ^ 3)) := by
    have hA : 4 * Real.sqrt 2 ≤ 4 * 1.4143 := by linarith
    have hB : (0 : ℝ) ≤ 4 * Real.sqrt 2 := by positivity
    nlinarith [hx, hx0, hA, hB]
  have hstep2 : 4 * 1.4143 * (1 / (26672 * (ell₀ : ℝ) ^ 3)) ≤ 1 / (4708 * (ell₀ : ℝ) ^ 3) := by
    have hL : 4 * 1.4143 * (1 / (26672 * (ell₀ : ℝ) ^ 3))
        = (4 * 1.4143) / (26672 * (ell₀ : ℝ) ^ 3) := by ring
    rw [hL, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hp3]
  -- the two halves sum to the lower bound on ½√(gammaSum ℓ₀)
  have hsum : 4 * Real.sqrt 2 * x + y ≤ 2 * (1 / (4708 * (ell₀ : ℝ) ^ 3)) := by linarith
  have hhalf : 2 * (1 / (4708 * (ell₀ : ℝ) ^ 3)) = (1 / (1177 * (ell₀ : ℝ) ^ 3)) / 2 := by
    field_simp
    ring
  rw [hhalf] at hsum
  linarith

/-- **THE WEAKER FORM THE HEADLINES LITERALLY ASK FOR**, `κ ≤ √(gammaSum ℓ₀)`. -/
theorem drift_split_le_sqrt_gammaSum {ell₀ : ℕ} (hell : 0 < ell₀) (x y : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / (26672 * (ell₀ : ℝ) ^ 3))
    (hy : y ≤ 1 / (4708 * (ell₀ : ℝ) ^ 3)) :
    4 * Real.sqrt 2 * x + y ≤ Real.sqrt (gammaSum ell₀) := by
  have h := halfDrift_split_sum hell x y hx0 hx hy
  have hg : (0 : ℝ) ≤ Real.sqrt (gammaSum ell₀) := Real.sqrt_nonneg _
  linarith

/-! ## §2 — THE TERMINAL THEOREM AT THE COVARIANT DATUM, WITH `hthr` GONE

The composition is: `CovTerminal`'s gauged drift price feeds `RecomposeSum`'s summation floor.
Neither lane could state this — `covariant_datum` cannot reach the floor (write scope), and
`recompose_sum` has no gauged drift. -/

/-- **§2 HEADLINE — THE PER-CUBE FORM.**

`CovTerminal.terminal_covariant_bothGauged` with `hthr` DELETED and the Schur floor taken from the
per-cube summation route instead: a pairwise-disjoint family of coarse cubes, ONE UNRELATED GAUGE
PER CUBE, holonomy deviations `≤ 1/(744·ℓ₀³)` on the doubly-enlarged bond sets.

**Every smallness hypothesis on a background is now measured at a gauge of the caller's choosing.**
`hsmallUGauged` and `hsmallFineGauged` at the joint orbit point `γ`; the floor at the per-cube
gauges `γcube`, which are unrelated to `γ` and to each other. -/
theorem terminal_covariant_sumFloor {ell₀ : ℕ} {ι : Type*} [DecidableEq ι]
    (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (γ : GaugeFn L)
    (hell2 : 2 ≤ ell₀) (hstrict : ∀ ν : Fin 3, ell₀ < L' ν + 1)
    (hdvd0 : ∀ ν : Fin 3, ell₀ ∣ (L' ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (hsmallUGauged : frobSupBond (periodicGaugeTransform (coarseGauge h γ) U)
      ≤ 1 / (26672 * (ell₀ : ℝ) ^ 3))
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (hsmallFineGauged : ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖
      * rawErrorCoeff ell (periodicGaugeTransform γ Ufine) ≤ 1 / (4708 * (ell₀ : ℝ) ^ 3))
    (α : ℝ) (hα0 : 0 ≤ α) (hα : α ≤ sumRadius ell₀)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L' ell₀)) (γcube : ι → GaugeFn L')
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite L' ell₀, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (tilde hdvd0 (tilde hdvd0 (Y i))),
      AdalyFormal.Balaban.RMapLipschitz.frobNorm
        (((periodicGaugeTransform (γcube i) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (Qext : BondFnL2 L' → BondFnL2 L') (T : BondFnL2 L' →L[ℝ] BondFnL2 L)
    (S : BondFnL2 L' →L[ℝ] BondFnL2 L')
    (hS : IsSourceOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) Qext (T (JsuTwo U)) S)
    (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hD2 : ∀ B : BondFnL2 L', ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hU : LinkDev δ U)
    (hH1 : 0 < ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖) (hT : 0 < ‖T‖)
    (hcard : 0 < Fintype.card (Bond L'))
    (hδ : δ < 1 / (5480006400 * (ell₀ : ℝ) ^ 6 * (rawSigmaZero ell) ^ 2
      * ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖ * c₂
      * (‖T‖ * Real.sqrt (2 * (Fintype.card (Bond L'))))))
    (w : TildeFn L' ell₀) (hw : w ≠ 0) :
    0 < cdcFormTrue (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) bc Qext (T (JsuTwo U)) U ell₀
      (dinvC U ell₀) w := by
  have hell : 0 < ell₀ := by omega
  set D := feedDatumGen h Ufine heps (le_of_lt bc.a_pos) with hD
  set κ := gaugedKappa h γ Ufine U heps (le_of_lt bc.a_pos) with hκdef
  set N : ℝ := Real.sqrt (2 * (Fintype.card (Bond L'))) with hN
  have hNpos : (0 : ℝ) < N := by
    rw [hN]
    refine Real.sqrt_pos.mpr ?_
    have : (0 : ℝ) < (Fintype.card (Bond L') : ℝ) := by exact_mod_cast hcard
    linarith
  have hTN : (0 : ℝ) < ‖T‖ * N := mul_pos hT hNpos
  have hκ0 : 0 ≤ κ := gaugedKappa_nonneg h γ Ufine U heps (le_of_lt bc.a_pos)
  -- §1: the re-split budget absorbs BOTH halves of the gauged price into ½√(gammaSum ℓ₀)
  have hhalf : κ ≤ Real.sqrt (gammaSum ell₀) / 2 := by
    rw [hκdef]
    unfold gaugedKappa
    exact halfDrift_split_sum hell _ _ (frobSupBond_nonneg _) hsmallUGauged hsmallFineGauged
  have hκγ : κ ≤ Real.sqrt (gammaSum ell₀) := by
    have hg : (0 : ℝ) ≤ Real.sqrt (gammaSum ell₀) := Real.sqrt_nonneg _
    linarith
  have hσ₀ := rawSigmaZero_pos (ell_pos_of_scale h)
  -- the source, from the link deviation
  have hJ : ‖T (JsuTwo U)‖ ≤ (‖T‖ * N) * (495 * δ) := by
    have := norm_source_le_of_linkDev T U hU
    rw [← hN] at this
    calc ‖T (JsuTwo U)‖ ≤ ‖T‖ * (N * (495 * δ)) := this
      _ = (‖T‖ * N) * (495 * δ) := by ring
  have harith := delta_threshold_sum_suffices hell (rawSigmaZero ell) ‖solutionOperator D‖ c₂
    (‖T‖ * N) δ hσ₀ hH1 hc₂ hTN hδ0 (by rw [hN] at hδ ⊢; exact hδ)
  have hlow := sharpFloorConstSum_lower_halfDrift hell (rawSigmaZero ell) κ hσ₀ hκ0 hhalf
  have hRthr : 2 * ‖solutionOperator D‖ * c₂ * ((‖T‖ * N) * (495 * δ))
      < sharpFloorConst (gammaSum ell₀) κ (rawSigmaZero ell) := by linarith
  exact terminal_sum_posDef_on_range hell2 hstrict hdvd0 U α hα0 hα 𝒞 Y γcube hdisj hcov hclass
    D bc (curlCovariantCLM_L2 Ufine) (feedPen eps : BondFnL2 L →L[ℝ] BondFnL2 L)
    (rawSigmaZero ell) κ hσ₀ hκ0 hκγ
    (fun B => feedDatumGen_isPrintedG1Form h Ufine heps (le_of_lt bc.a_pos) _)
    (hraw_on_range_gauged h γ Ufine U heps (le_of_lt bc.a_pos))
    Qext (T (JsuTwo U)) S hS c₂ (le_of_lt hc₂) hD2 ((‖T‖ * N) * (495 * δ)) hJ hRthr w hw

/-! ## §3 — THE SAME AT THE PRINTED CLASS

`RecompClass.terminal_sum_posDef_from_printed` (CITED, REUSED) discharges the per-cube family from
CMP99b (3.35) itself — `PrintedCubeClassI c M α₀ η Lj U 𝒞src` with `c·M·α₀ < 1/(1120·ℓ₀³)` — plus
the geometric guard [GEOM] `CubesRefine`.  Composing it with §1 gives the shape the dispatch asks
for: **printed per-cube class + guarded geometry + source threshold, and no ungauged smallness
binder anywhere.** -/

/-- **§3 HEADLINE — THE COVARIANT DATUM'S TERMINAL THEOREM WITH NO UNGAUGED SMALLNESS BINDER.**

    ℓ₀ ≥ 2 on a tiled torus,
    CMP99b (3.35) on a cube family 𝒞src with c·M·α₀ < 1/(1120·ℓ₀³),
    [GEOM] every doubly-enlarged block's bond set inside one cube of 𝒞src,
    α₁(U^{γ̄}) ≤ 1/(26672·ℓ₀³)  and  ‖H₁‖·rawErrorCoeff(U_fine^γ) ≤ 1/(4708·ℓ₀³)   [ONE γ, caller's choice]
    δ < 1/(5480006400·ℓ₀⁶·σ₀²·‖H₁‖·c₂·‖T‖√(2|Bond L'|))
  ⟹ ⟨B̃, C*Δ_k(U) C B̃⟩ > 0  for every B̃ ≠ 0.

**The gauge quantifier on the floor side is the printed `∀□ ∃u`; the gauge quantifier on the drift
side is `∃γ` at the caller's choice.  Neither is a global gauge, and `frobSupBond U` — the flat
reference — appears nowhere in this statement.** -/
theorem terminal_covariant_printed {ell₀ : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (γ : GaugeFn L)
    (hell2 : 2 ≤ ell₀) (hstrict : ∀ ν : Fin 3, ell₀ < L' ν + 1)
    (hdvd0 : ∀ ν : Fin 3, ell₀ ∣ (L' ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (hsmallUGauged : frobSupBond (periodicGaugeTransform (coarseGauge h γ) U)
      ≤ 1 / (26672 * (ell₀ : ℝ) ^ 3))
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (hsmallFineGauged : ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖
      * rawErrorCoeff ell (periodicGaugeTransform γ Ufine) ≤ 1 / (4708 * (ell₀ : ℝ) ^ 3))
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hα₀ : 0 ≤ α₀) (hprintedThr : c * M * α₀ < 1 / (1120 * (ell₀ : ℝ) ^ 3))
    (𝒞src : Set (Set (Bond L'))) (hprinted : PrintedCubeClassI c M α₀ η Lj U 𝒞src)
    (hgeom : CubesRefine hdvd0 (Finset.univ : Finset (CSite L' ell₀))
      (fun z => ({z} : Finset (CSite L' ell₀))) 𝒞src)
    (Qext : BondFnL2 L' → BondFnL2 L') (T : BondFnL2 L' →L[ℝ] BondFnL2 L)
    (S : BondFnL2 L' →L[ℝ] BondFnL2 L')
    (hS : IsSourceOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) Qext (T (JsuTwo U)) S)
    (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hD2 : ∀ B : BondFnL2 L', ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hU : LinkDev δ U)
    (hH1 : 0 < ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖) (hT : 0 < ‖T‖)
    (hcard : 0 < Fintype.card (Bond L'))
    (hδ : δ < 1 / (5480006400 * (ell₀ : ℝ) ^ 6 * (rawSigmaZero ell) ^ 2
      * ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖ * c₂
      * (‖T‖ * Real.sqrt (2 * (Fintype.card (Bond L'))))))
    (w : TildeFn L' ell₀) (hw : w ≠ 0) :
    0 < cdcFormTrue (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) bc Qext (T (JsuTwo U)) U ell₀
      (dinvC U ell₀) w := by
  have hell : 0 < ell₀ := by omega
  set D := feedDatumGen h Ufine heps (le_of_lt bc.a_pos) with hD
  set κ := gaugedKappa h γ Ufine U heps (le_of_lt bc.a_pos) with hκdef
  set N : ℝ := Real.sqrt (2 * (Fintype.card (Bond L'))) with hN
  have hNpos : (0 : ℝ) < N := by
    rw [hN]
    refine Real.sqrt_pos.mpr ?_
    have : (0 : ℝ) < (Fintype.card (Bond L') : ℝ) := by exact_mod_cast hcard
    linarith
  have hTN : (0 : ℝ) < ‖T‖ * N := mul_pos hT hNpos
  have hκ0 : 0 ≤ κ := gaugedKappa_nonneg h γ Ufine U heps (le_of_lt bc.a_pos)
  have hhalf : κ ≤ Real.sqrt (gammaSum ell₀) / 2 := by
    rw [hκdef]
    unfold gaugedKappa
    exact halfDrift_split_sum hell _ _ (frobSupBond_nonneg _) hsmallUGauged hsmallFineGauged
  have hκγ : κ ≤ Real.sqrt (gammaSum ell₀) := by
    have hg : (0 : ℝ) ≤ Real.sqrt (gammaSum ell₀) := Real.sqrt_nonneg _
    linarith
  have hσ₀ := rawSigmaZero_pos (ell_pos_of_scale h)
  have hJ : ‖T (JsuTwo U)‖ ≤ (‖T‖ * N) * (495 * δ) := by
    have := norm_source_le_of_linkDev T U hU
    rw [← hN] at this
    calc ‖T (JsuTwo U)‖ ≤ ‖T‖ * (N * (495 * δ)) := this
      _ = (‖T‖ * N) * (495 * δ) := by ring
  have harith := delta_threshold_sum_suffices hell (rawSigmaZero ell) ‖solutionOperator D‖ c₂
    (‖T‖ * N) δ hσ₀ hH1 hc₂ hTN hδ0 (by rw [hN] at hδ ⊢; exact hδ)
  have hlow := sharpFloorConstSum_lower_halfDrift hell (rawSigmaZero ell) κ hσ₀ hκ0 hhalf
  have hRthr : 2 * ‖solutionOperator D‖ * c₂ * ((‖T‖ * N) * (495 * δ))
      < sharpFloorConst (gammaSum ell₀) κ (rawSigmaZero ell) := by linarith
  exact terminal_sum_posDef_from_printed hell2 hstrict hdvd0 U c M α₀ η Lj hη hηne hLj hc hM hα₀
    hprintedThr 𝒞src hprinted hgeom D bc (curlCovariantCLM_L2 Ufine)
    (feedPen eps : BondFnL2 L →L[ℝ] BondFnL2 L) (rawSigmaZero ell) κ hσ₀ hκ0 hκγ
    (fun B => feedDatumGen_isPrintedG1Form h Ufine heps (le_of_lt bc.a_pos) _)
    (hraw_on_range_gauged h γ Ufine U heps (le_of_lt bc.a_pos))
    Qext (T (JsuTwo U)) S hS c₂ (le_of_lt hc₂) hD2 ((‖T‖ * N) * (495 * δ)) hJ hRthr w hw

/-! ## §3b — THE COARSE DRIFT BINDER IS ALSO FED BY PER-CUBE DATA

`CovPerCube.hsmallUGauged_of_perCube` does this at `TerminalBinder.halfDrift_split`'s radius
`1/(13336·ℓ₀³)`.  §1 tightened the radius to `1/(26672·ℓ₀³)`, so that theorem no longer applies as
stated; the SAME route re-run at the new radius does.  Written out rather than left as a residual,
because it is one `le_trans` away and a residual that could be closed in the pass that created it
is not a residual. -/

/-- **§3b — PER-CUBE DATA ON THE COARSE TORUS SUPPLIES `hsmallUGauged` AT THE TIGHTENED RADIUS.**
`CovPerCube.hsmallUGauged_of_perCube`'s statement and proof, with `13336` replaced by §1's `26672`.
The existential is `CovTerminal.coarseGauge_liftCoarseGauge`'s NAMED lift, not a choice principle. -/
theorem hsmallUGauged_of_perCube_sum {ell₀ : ℕ} {ι : Type*} (h : ScaleQuotient L ell L')
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (assign : PeriodicLatticeSite L' → ι) (γc : ι → GaugeFn L') (r m : ℝ)
    (hclass : ∀ b : Bond L', AdalyFormal.Balaban.RMapLipschitz.frobNorm
      (((periodicGaugeTransform (γc (assign b.1)) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r)
    (hmatch : ∀ b : Bond L', AdalyFormal.Balaban.RMapLipschitz.frobNorm
      (((γc (assign b.1) (periodicLatticeShift b.1 b.2)
          * (γc (assign (periodicLatticeShift b.1 b.2)) (periodicLatticeShift b.1 b.2))⁻¹ :
          Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ m)
    (hsum : r + m ≤ 1 / (26672 * (ell₀ : ℝ) ^ 3)) :
    coarseGauge h (liftCoarseGauge h (gluedGauge assign γc)) = gluedGauge assign γc
    ∧ frobSupBond (periodicGaugeTransform
        (coarseGauge h (liftCoarseGauge h (gluedGauge assign γc))) U)
      ≤ 1 / (26672 * (ell₀ : ℝ) ^ 3) := by
  refine ⟨coarseGauge_liftCoarseGauge h (gluedGauge assign γc), ?_⟩
  rw [coarseGauge_liftCoarseGauge h (gluedGauge assign γc)]
  exact le_trans (frobSupBond_glued_le assign γc U r m hclass hmatch) hsum

/-- **§3c — THE FULLY PER-CUBE FORM OF §3.**

§3 with `hsmallUGauged` DISCHARGED from per-cube data on the coarse torus by §3b, so the ONLY
smallness conditions left mentioning a background are

* the printed per-cube class (3.35) on the floor side,
* per-cube coarse data `(r, m)` on the drift side, and
* the FINE-side condition at the SAME `γ` — which is what couples the two, and is why `γ` is a
  binder here with `hγ` pinning it, rather than an existential: the fine condition must be checked
  at the gauge the coarse data produces.  Non-vacuity of that coupling is `hsmallUGauged_at_spike`
  and `CovTerminal.coarseGauge_surjective` (every coarse gauge IS induced by a fine one). -/
theorem terminal_covariant_printed_perCubeDrift {ell₀ : ℕ} {ι : Type*} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (γ : GaugeFn L)
    (hell2 : 2 ≤ ell₀) (hstrict : ∀ ν : Fin 3, ell₀ < L' ν + 1)
    (hdvd0 : ∀ ν : Fin 3, ell₀ ∣ (L' ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (assign : PeriodicLatticeSite L' → ι) (γc : ι → GaugeFn L') (r m : ℝ)
    (hγ : coarseGauge h γ = gluedGauge assign γc)
    (hclassD : ∀ b : Bond L', AdalyFormal.Balaban.RMapLipschitz.frobNorm
      (((periodicGaugeTransform (γc (assign b.1)) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r)
    (hmatch : ∀ b : Bond L', AdalyFormal.Balaban.RMapLipschitz.frobNorm
      (((γc (assign b.1) (periodicLatticeShift b.1 b.2)
          * (γc (assign (periodicLatticeShift b.1 b.2)) (periodicLatticeShift b.1 b.2))⁻¹ :
          Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ m)
    (hsum : r + m ≤ 1 / (26672 * (ell₀ : ℝ) ^ 3))
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (hsmallFineGauged : ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖
      * rawErrorCoeff ell (periodicGaugeTransform γ Ufine) ≤ 1 / (4708 * (ell₀ : ℝ) ^ 3))
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hα₀ : 0 ≤ α₀) (hprintedThr : c * M * α₀ < 1 / (1120 * (ell₀ : ℝ) ^ 3))
    (𝒞src : Set (Set (Bond L'))) (hprinted : PrintedCubeClassI c M α₀ η Lj U 𝒞src)
    (hgeom : CubesRefine hdvd0 (Finset.univ : Finset (CSite L' ell₀))
      (fun z => ({z} : Finset (CSite L' ell₀))) 𝒞src)
    (Qext : BondFnL2 L' → BondFnL2 L') (T : BondFnL2 L' →L[ℝ] BondFnL2 L)
    (S : BondFnL2 L' →L[ℝ] BondFnL2 L')
    (hS : IsSourceOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) Qext (T (JsuTwo U)) S)
    (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hD2 : ∀ B : BondFnL2 L', ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hU : LinkDev δ U)
    (hH1 : 0 < ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖) (hT : 0 < ‖T‖)
    (hcard : 0 < Fintype.card (Bond L'))
    (hδ : δ < 1 / (5480006400 * (ell₀ : ℝ) ^ 6 * (rawSigmaZero ell) ^ 2
      * ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖ * c₂
      * (‖T‖ * Real.sqrt (2 * (Fintype.card (Bond L'))))))
    (w : TildeFn L' ell₀) (hw : w ≠ 0) :
    0 < cdcFormTrue (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) bc Qext (T (JsuTwo U)) U ell₀
      (dinvC U ell₀) w := by
  have hsmallUGauged : frobSupBond (periodicGaugeTransform (coarseGauge h γ) U)
      ≤ 1 / (26672 * (ell₀ : ℝ) ^ 3) := by
    rw [hγ]
    exact le_trans (frobSupBond_glued_le assign γc U r m hclassD hmatch) hsum
  exact terminal_covariant_printed h Ufine γ hell2 hstrict hdvd0 U hsmallUGauged bc heps
    hsmallFineGauged c M α₀ η Lj hη hηne hLj hc hM hα₀ hprintedThr 𝒞src hprinted hgeom
    Qext T S hS c₂ hc₂ hD2 δ hδ0 hU hH1 hT hcard hδ w hw

/-- **§3d — THE COUPLING BINDER `hγ` IS INHABITED**, for EVERY per-cube gauge family: the lifted
glued gauge is a fine gauge inducing exactly `gluedGauge assign γc`.  So §3c is not conditioned on
an unsatisfiable relation between the fine gauge and the coarse cube data. -/
theorem coupling_gauge_exists {ι : Type*} (h : ScaleQuotient L ell L')
    (assign : PeriodicLatticeSite L' → ι) (γc : ι → GaugeFn L') :
    ∃ γ : GaugeFn L, coarseGauge h γ = gluedGauge assign γc :=
  ⟨liftCoarseGauge h (gluedGauge assign γc), coarseGauge_liftCoarseGauge h (gluedGauge assign γc)⟩

/-! ## §4 — THE WITNESS: A BACKGROUND THE OLD BINDER EXCLUDES AND THE NEW ONE ADMITS

Without this section §2 and §3 could be re-statements at a strictly smaller class.  The pure-gauge
spike (`CovWitness.spikeU`, itself built from the tree's `spikeGauge`) is a configuration at which

* `hthr : α₁(U) ≤ 1/(186·ℓ₀³)` is **FALSE** — `α₁ ≥ 2` and `1/(186·ℓ₀³) ≤ 1/186 < 2`; so
  `CovTerminal.terminal_covariant_bothGauged` **cannot be applied at it at all**; while
* the per-cube hypothesis of §2 holds at radius **exactly `0`**, with the SINGLE gauge that undoes
  the spike — and the Schur floor itself is then a theorem there.

This is `drift_percube`'s own pure-gauge witness (`DriftNoGo`) turned around: there it defeated a
flat-referenced bound; here it is admitted by the summable one. -/

/-- **§4a — THE OLD BINDER FAILS AT THE SPIKE.**  For every `ℓ₀ ≥ 1` and every spike site, on a
torus with `0 < L μ` in some direction. -/
theorem hthr_fails_at_spike {ell₀ : ℕ} (hell : 0 < ell₀)
    (x₀ : PeriodicLatticeSite L) (μ : Fin 3) (hL : 0 < L μ) :
    ¬ (frobSupBond (spikeU witnessMElem x₀) ≤ 1 / (186 * (ell₀ : ℝ) ^ 3)) := by
  intro hcon
  have h1 : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell
  have h2 := two_le_frobSupBond_spikeU (L := L) x₀ μ hL
  have hp3 : (1 : ℝ) ≤ (ell₀ : ℝ) ^ 3 := by nlinarith [h1, sq_nonneg ((ell₀ : ℝ) - 1), sq_nonneg ((ell₀ : ℝ) + 1)]
  have hsmall : 1 / (186 * (ell₀ : ℝ) ^ 3) ≤ 1 / 186 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hnum : (1 : ℝ) / 186 < 2 := by norm_num
  linarith

/-- **§4b — THE NEW BINDER HOLDS AT THE SPIKE, AT RADIUS EXACTLY ZERO.**  Every bond, not merely
those of the doubly-enlarged blocks: the gauged configuration IS the flat one. -/
theorem perCube_class_at_spike_zero (g : SU2) (x₀ : PeriodicLatticeSite L) (b : Bond L) :
    AdalyFormal.Balaban.RMapLipschitz.frobNorm
      (((periodicGaugeTransform (gaugeInv (spikeGauge g x₀)) (spikeU g x₀)) b :
        Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 0 := by
  rw [spikeU_gauged_flat g x₀]
  show AdalyFormal.Balaban.RMapLipschitz.frobNorm ((1 : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 0
  rw [sub_self]
  show Real.sqrt (AdalyFormal.Balaban.RMapLipschitz.frobSq 0) ≤ 0
  have hz : AdalyFormal.Balaban.RMapLipschitz.frobSq (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AdalyFormal.Balaban.RMapLipschitz.frobSq
    simp
  rw [hz, Real.sqrt_zero]

/-- **§4c — AND THE SCHUR FLOOR ITSELF IS A THEOREM AT THE SPIKE.**

`gammaSum ℓ₀ · ‖C₀B̃‖² ≤ ‖∂_U C₀B̃‖²` at `U = 1^{γ}`, via `RecompFloor.hpoin_sum_at_cZero` with the
one-cube-per-site family (`LocFeed.singleton_family_ok`, REUSED) and `α = 0`.

So the floor that `hthr` used to buy is available at a background `hthr` excludes.  This is the
NON-VACUITY of §2/§3 as an extension, not merely as a restatement. -/
theorem sum_floor_at_spike {ell₀ : ℕ} (hell2 : 2 ≤ ell₀)
    (hstrict : ∀ ν : Fin 3, ell₀ < L ν + 1) (hdvd : ∀ ν : Fin 3, ell₀ ∣ (L ν + 1))
    (g : SU2) (x₀ : PeriodicLatticeSite L) (w : TildeFn L ell₀) :
    gammaSum ell₀ * ‖cZero (spikeU g x₀) ell₀ (dinvC (spikeU g x₀) ell₀) w‖ ^ 2
      ≤ ‖curlCovariantCLM_L2 (spikeU g x₀)
          (cZero (spikeU g x₀) ell₀ (dinvC (spikeU g x₀) ell₀) w)‖ ^ 2 := by
  have hell : 0 < ell₀ := by omega
  have hrad : (0 : ℝ) ≤ sumRadius ell₀ := by
    unfold sumRadius
    have : (0 : ℝ) < (ell₀ : ℝ) := by exact_mod_cast hell
    positivity
  exact hpoin_sum_at_cZero hell2 hstrict hdvd (spikeU g x₀) 0 le_rfl hrad
    (Finset.univ : Finset (CSite L ell₀)) (fun z => ({z} : Finset (CSite L ell₀)))
    (fun _ => gaugeInv (spikeGauge g x₀))
    singleton_family_ok.1 singleton_family_ok.2
    (fun _ _ b _ => perCube_class_at_spike_zero g x₀ b) w

/-- **§4d — THE SPIKE ALSO CLEARS THE COARSE DRIFT BINDER, AT ITS OWN ZERO.**

There is a fine gauge `γ` whose induced coarse gauge sends the coarse spike to the flat
configuration, so `hsmallUGauged` of §2/§3 holds at radius `0 ≤ 1/(26672·ℓ₀³)`.  The existential is
`CovTerminal.coarseGauge_surjective`'s — a NAMED surjectivity theorem, not a choice principle
applied to free data. -/
theorem hsmallUGauged_at_spike {ell₀ : ℕ} (hell : 0 < ell₀) (h : ScaleQuotient L ell L')
    (g : SU2) (x₀ : PeriodicLatticeSite L') :
    ∃ γ : GaugeFn L,
      frobSupBond (periodicGaugeTransform (coarseGauge h γ) (spikeU g x₀))
        ≤ 1 / (26672 * (ell₀ : ℝ) ^ 3) := by
  obtain ⟨γ, hγ⟩ := coarseGauge_surjective h (gaugeInv (spikeGauge g x₀))
  refine ⟨γ, ?_⟩
  rw [hγ, spikeU_gauged_flat g x₀, frobSupBond_trivialU]
  have h1 : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell₀ : ℝ) := by linarith
  positivity

/-- **§4e — THE FINE-SIDE BINDER IS ALSO INHABITED AT THE TIGHTENED RADIUS.**

`CovWitness.hsmallFineGauged_at_spikeU` states this at `halfDrift_split`'s `1/(2356·ℓ₀³)`; §1
tightened it to `1/(4708·ℓ₀³)`, so that theorem no longer applies as written.  It holds for the
same reason and for EVERY `‖H₁‖`: the gauged fine background is flat, so `rawErrorCoeff` is `0`.

Closed here rather than filed, for the same reason as §3b. -/
theorem hsmallFineGauged_at_spike_sum {ell₀ : ℕ} (hell₀ : 0 < ell₀) (K : ℝ)
    (g : SU2) (x₀ : PeriodicLatticeSite L) :
    K * rawErrorCoeff ell (periodicGaugeTransform (gaugeInv (spikeGauge g x₀)) (spikeU g x₀))
      ≤ 1 / (4708 * (ell₀ : ℝ) ^ 3) := by
  have h1 : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell₀
  have h0 : (0 : ℝ) < (ell₀ : ℝ) := by linarith
  rw [rawErrorCoeff_spikeU_gauged, mul_zero]
  positivity

/-! ## §5 — CONTROLS

Three rows.  One says the re-split is not free, one says it is not gratuitous, one says the
witness of §4 is not a degenerate point. -/

/-- **MUST-NOT-FIRE — THE OLD RADII DO NOT SURVIVE THE SWAP, THROUGH THIS ROUTE.**

An EXACT rational fact: at `TerminalBinder.halfDrift_split`'s own radii `1/(13336·ℓ³)` and
`1/(2356·ℓ³)`, the budget that `sqrt_gammaSum_lower` makes available — `1/(2354·ℓ³)` — is
OVERSPENT by a factor `1.99773…`, i.e. very nearly exactly `2` (and the second conjunct pins it
above `1.99`, so the reading "nearly 2" is a theorem and not a remark).  It is NOT above `2`: the
old fine radius `2356` is very slightly LOOSER than `2·1177 = 2354`, which is where the missing
`0.0023` goes.  So §1's tightening is forced by the arithmetic and is not a margin taken for
comfort; and the third conjunct shows the NEW radii do fit, so the tightening is exactly enough.

**Stated precisely, and no more than that:** this is a statement about the LOWER BOUND
`√(gammaSum ℓ) ≥ 1/(1177·ℓ³)` that this route uses, i.e. it says the ROUTE is exhausted at the old
radii.  It does **not** assert that `4√2·x + y ≤ ½√(gammaSum ℓ)` is false there — the lower bound
`1/(1177·ℓ³)` is crude at small `ℓ` (at `ℓ = 3` the true `√(gammaSum 3)` exceeds it by a factor
`> 20`), and this lane proves nothing about the true value. -/
theorem old_radii_overspend_the_sum_budget :
    (4 * 1.4143 * (1 / 13336) + 1 / 2356 : ℝ) > 1 / 2354
    ∧ (4 * 1.4143 * (1 / 13336) + 1 / 2356 : ℝ) > (199 / 100) * (1 / 2354)
    ∧ (4 * 1.4143 * (1 / 26672) + 1 / 4708 : ℝ) ≤ 1 / 2354 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **THE FACTORISATIONS OF §1'S CONSTANTS**, so that no reader has to take "derived, not fitted"
on trust.  `26672 = 2·13336`, `4708 = 2·2354 = 4·1177`, `1177² = 1385329 ≥ 1383840 = 4·345960`, and
the coarse pricing inequality `4·1.4143·4708 ≤ 26672` with its exact slack. -/
theorem split_constant_factorisations :
    (26672 : ℕ) = 2 * 13336 ∧ (4708 : ℕ) = 2 * 2354 ∧ (4708 : ℕ) = 4 * 1177
    ∧ (1177 : ℕ) ^ 2 = 1385329 ∧ (1385329 : ℕ) ≥ 1383840 ∧ (1383840 : ℕ) = 4 * 345960
    ∧ (2354 : ℕ) = 2 * 1177
    ∧ (4 * 1.4143 * 4708 : ℝ) = 26634.0976 ∧ (26672 : ℝ) - 26634.0976 = 37.9024
    ∧ (5480006400 : ℕ) = 4 * 1370001600 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **JUNK SUBSTITUTION (S82) ON §4c.**  At `B̃ = 0` both sides of the spike floor vanish, so the
`w = 0` instance carries no information and must never be quoted as content.  Recorded so that the
non-degenerate reading of §4c is the one on `w ≠ 0`. -/
theorem sum_floor_at_spike_junk_at_zero {ell₀ : ℕ}
    (g : SU2) (x₀ : PeriodicLatticeSite L) :
    gammaSum ell₀ * ‖cZero (spikeU g x₀) ell₀ (dinvC (spikeU g x₀) ell₀)
        (0 : TildeFn L ell₀)‖ ^ 2 = 0 := by
  simp

/-- **THE FLOOR CONSTANT IS STRICTLY POSITIVE**, so §4c is not `0 ≤ ‖·‖²`. -/
theorem gammaSum_pos_at {ell₀ : ℕ} (hell : 0 < ell₀) : 0 < gammaSum ell₀ := gammaSum_pos hell

#print axioms halfDrift_split_sum
#print axioms drift_split_le_sqrt_gammaSum
#print axioms terminal_covariant_sumFloor
#print axioms terminal_covariant_printed
#print axioms hthr_fails_at_spike
#print axioms perCube_class_at_spike_zero
#print axioms sum_floor_at_spike
#print axioms hsmallUGauged_at_spike
#print axioms old_radii_overspend_the_sum_budget
#print axioms split_constant_factorisations
#print axioms sum_floor_at_spike_junk_at_zero
#print axioms gammaSum_pos_at

end AdalyFormal.FloorMembership
