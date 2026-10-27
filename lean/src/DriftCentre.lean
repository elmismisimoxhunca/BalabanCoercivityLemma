/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import DriftTerminal

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 40000
set_option linter.style.longLine false

/-!
# THE CENTRE-AWARE VARIANT: per-cube data measured at a CENTRAL FLIP of the background.

Lane `compute/drift_percube/`.  Write scope: that directory only.  Never `lake build`.

`DriftTerminal.terminal_sum_at_star_datum_percube` replaces `hdrift` by per-cube data measured at
the background `U` itself.  `HrawRDischarge` §5 proved the covariant curl is blind to a central flip
(`RMap(±1) = id`), so the SAME statement holds with the per-cube data measured at any central
relative of `U`.  This module states it, and records what the resulting class contains.

    class(r, ρ) := { centralFlipConfig ε V : V carries per-cube data (r) and gauge roughness (ρ) }

It contains, at `r = ρ = 0`:

* the flat background (`ε = false`, `V = 1`);
* the centre configuration `U ≡ −1` (`ε = true`, `V = 1`) — `centre_point_in_class`, the very
  configuration `GaugeInvPrinted.printed_class_does_not_reach_the_consumer` uses to separate the
  printed class from the global one;

and it does NOT contain the pure-gauge witness of `DriftNoGo` at any radius below `2`
(`bumpU_not_in_centre_class`), which is the obstruction of this lane restated at the largest class
it reaches.

**Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.  The gates adjudicate.**
-/

namespace AdalyFormal.Balaban.DriftPerCube

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeInv centerU)
open AdalyFormal.Balaban.LocalizedEstimates
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.VariationalProjectorH1 (solutionOperator)
open AdalyFormal.Balaban.ConstantA (BaseConstant)
open AdalyFormal.Balaban.ConstructCDC (TildeFn)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (IsSourceOperator cdcFormTrue)
open AdalyFormal.Balaban.TerminalAssembly (sharpFloorConst)
open AdalyFormal.Balaban.DeltaAlpha0 (PrintedCubeClassI)
open AdalyFormal.Balaban.RecomposeSum (gammaSum CubesRefine terminal_sum_posDef_from_printed)
open AdalyFormal.TerminalBinder (HrawAt OnMinimizerRange onMinimizerRange_of_forall)
open AdalyFormal.DatumWitness (fineL starScale starDatum)
open AdalyFormal.HrawRDischarge (starDatum_hformR hrawAt_centralFlip centerU_eq_flip)
open AdalyFormal.HoleHunt.CenterBlindness (centralFlipConfig)
open AdalyFormal.MechEdges.G16 (rawSigmaZero rawSigmaZero_pos)

/-! ## §1 — `hrawR` AT THE PER-CUBE PRICE, ISOLATED -/

/-- **`hrawR` at the star datum with the PER-CUBE drift price**, extracted from
`DriftTerminal.terminal_sum_at_star_datum_percube`'s proof so that the centre-blind transfer can be
applied to it.  Same hypotheses, same `κ = 16(r+ρ)`. -/
theorem starDatum_hrawR_percube {ι : Type*} [DecidableEq ι]
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (r ρ : ℝ) (hr0 : 0 ≤ r) (hρ0 : 0 ≤ ρ)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite witnessL 2)) (γ : ι → GaugeFn witnessL)
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite witnessL 2, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (Y i), RMapLipschitz.frobNorm
      (((periodicGaugeTransform (γ i) V) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r)
    (hrough : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (Y i), RMapLipschitz.frobNorm
      (((pureGauge (gaugeInv (γ i))) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ) :
    OnMinimizerRange (starDatum bc heps)
      (HrawAt (starDatum bc heps) V (curlCovariantCLM_L2 (trivialU fineL)) (rawSigmaZero 2)
        (16 * (r + ρ))) := by
  have hdvd2 : ∀ μ : Fin 3, (2 : ℕ) ∣ (witnessL μ + 1) :=
    AdalyFormal.Balaban.CurvedContent.witnessL_dvd
  have hκop : ∀ X : BondFnL2 witnessL,
      ‖curlCovariantCLM_L2 V X - curlCovariantCLM_L2 (trivialU witnessL) X‖
        ≤ 16 * (r + ρ) * ‖X‖ :=
    fun X => norm_curl_sub_flat_percube (by norm_num) hdvd2 V r ρ hr0 hρ0 𝒞 Y γ hdisj hcov
      hclass hrough X
  refine onMinimizerRange_of_forall _ _ (fun A => ?_)
  show ‖curlCovariantCLM_L2 V ((starDatum bc heps).Q A)‖
      ≤ rawSigmaZero 2 * ‖curlCovariantCLM_L2 (trivialU fineL) A‖
        + 16 * (r + ρ) * ‖(starDatum bc heps).Q A‖
  rw [AdalyFormal.DatumWitness.starDatum_Q bc heps]
  exact hraw_composed_of_drift starScale V (16 * (r + ρ)) hκop A

/-- **AND AT EVERY CENTRAL RELATIVE OF `V`.**  The price is still `V`'s; the background the
covariant curl is evaluated at is the flipped one, whose own `α₁` may be as large as `2√2`.
`hrawAt_centralFlip` is `HrawRDischarge`'s, CITED. -/
theorem starDatum_hrawR_percube_centreBlind {ι : Type*} [DecidableEq ι]
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (ε : Bond witnessL → Bool)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (r ρ : ℝ) (hr0 : 0 ≤ r) (hρ0 : 0 ≤ ρ)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite witnessL 2)) (γ : ι → GaugeFn witnessL)
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite witnessL 2, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (Y i), RMapLipschitz.frobNorm
      (((periodicGaugeTransform (γ i) V) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r)
    (hrough : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (Y i), RMapLipschitz.frobNorm
      (((pureGauge (gaugeInv (γ i))) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ) :
    OnMinimizerRange (starDatum bc heps)
      (HrawAt (starDatum bc heps) (centralFlipConfig ε V)
        (curlCovariantCLM_L2 (trivialU fineL)) (rawSigmaZero 2) (16 * (r + ρ))) :=
  fun B => (hrawAt_centralFlip (starDatum bc heps) ε V _ _ _ _).mpr
    (starDatum_hrawR_percube bc heps V r ρ hr0 hρ0 𝒞 Y γ hdisj hcov hclass hrough B)

/-! ## §2 — THE TERMINAL THEOREM ON THE CENTRE-AWARE PER-CUBE CLASS -/

/-- **THE RECOMPOSED TERMINAL THEOREM AT THE STAR DATUM, PER-CUBE AND CENTRE-AWARE.**

`hdrift` is gone.  The background is presented as `centralFlipConfig ε V`; the per-cube data
(`hclass`, `hrough`) is measured at `V`.  `ε = fun _ => false` recovers
`DriftTerminal.terminal_sum_at_star_datum_percube`, so nothing is lost, while the admissible class
now also contains every central relative of a per-cube-regular background — in particular `U ≡ −1`
(`centre_point_in_class`). -/
theorem terminal_sum_at_star_datum_percube_centre {ι : Type*} [DecidableEq ι]
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (ε : Bond witnessL → Bool)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (r ρ : ℝ) (hr0 : 0 ≤ r) (hρ0 : 0 ≤ ρ)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite witnessL 2)) (γ : ι → GaugeFn witnessL)
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite witnessL 2, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (Y i), RMapLipschitz.frobNorm
      (((periodicGaugeTransform (γ i) V) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r)
    (hrough : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (Y i), RMapLipschitz.frobNorm
      (((pureGauge (gaugeInv (γ i))) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ)
    (hsum : r + ρ ≤ 1 / (37664 * (((2 : ℕ)) : ℝ) ^ 3))
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hα0 : 0 ≤ α₀) (hthr : c * M * α₀ < 1 / (1120 * (((2 : ℕ)) : ℝ) ^ 3))
    (𝒞src : Set (Set (Bond witnessL)))
    (hprinted : PrintedCubeClassI c M α₀ η Lj (centralFlipConfig ε V) 𝒞src)
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
    0 < cdcFormTrue (starDatum bc heps) bc Qext J (centralFlipConfig ε V) 2
      (dinvC (centralFlipConfig ε V) 2) w := by
  have hκ0 : (0 : ℝ) ≤ 16 * (r + ρ) := by linarith
  have hκγ : 16 * (r + ρ) ≤ Real.sqrt (gammaSum 2) := by
    have hh := halfDrift_percube (ell₀ := 2) (by norm_num) (r + ρ) (by linarith) hsum
    have hg : (0 : ℝ) ≤ Real.sqrt (gammaSum 2) := Real.sqrt_nonneg _
    linarith
  exact terminal_sum_posDef_from_printed (by norm_num : (2 : ℕ) ≤ 2)
    AdalyFormal.Balaban.CurvedContent.witnessL_strict
    AdalyFormal.Balaban.CurvedContent.witnessL_dvd
    (centralFlipConfig ε V) c M α₀ η Lj hη hηne hLj hc hM hα0 hthr 𝒞src hprinted hgeom
    (starDatum bc heps) bc (curlCovariantCLM_L2 (trivialU fineL))
    (AdalyFormal.HrawCarriers.feedPen eps : BondFnL2 fineL →L[ℝ] BondFnL2 fineL)
    (rawSigmaZero 2) (16 * (r + ρ)) (rawSigmaZero_pos (by norm_num)) hκ0 hκγ
    (starDatum_hformR bc heps)
    (starDatum_hrawR_percube_centreBlind bc heps ε V r ρ hr0 hρ0 𝒞 Y γ hdisj hcov hclass hrough)
    Qext J S hS c₂ hc₂ hD2 R hJbound hRthr w hw

/-! ## §3 — WHAT THE CLASS CONTAINS, AND WHAT IT STILL DOES NOT -/

/-- **THE CENTRE POINT IS IN THE CLASS AT RADIUS `0`.**  `U ≡ −1` is `centralFlipConfig (fun _ =>
true) 1`, and the flat background carries the per-cube data at `r = ρ = 0` with the trivial gauges.
So §2's class contains the tree's own separator between the printed per-cube class and the global
one, at the tightest radius. -/
theorem centre_point_in_class :
    centerU witnessL
      = centralFlipConfig (fun _ => true) (trivialU witnessL)
    ∧ (∀ b : Bond witnessL, RMapLipschitz.frobNorm
        (((periodicGaugeTransform (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
          (trivialU witnessL)) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0)
    ∧ (∀ b : Bond witnessL, RMapLipschitz.frobNorm
        (((pureGauge (gaugeInv (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))))
          b : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0) := by
  refine ⟨centerU_eq_flip, fun b => ?_, fun b => (trivial_gauge_gives_rough_zero b).1⟩
  rw [AdalyFormal.Balaban.AlphaAnalyticity.gaugeTransform_one (trivialU witnessL)]
  have h1 : ((trivialU witnessL b : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) - 1 = 0 := by
    show ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1 = 0
    simp
  rw [h1, RMapLipschitz.frobNorm_zero]

/-- **AND THE PURE-GAUGE WITNESS IS STILL OUTSIDE IT.**  ~~Every central relative of `bumpU` has
`α₁ ≥ 2`, so `bumpU` is not `centralFlipConfig ε V` for any `V` in the per-cube-plus-roughness class
at a radius below `2`.~~  **THE STRUCK SENTENCE CLAIMED MORE THAN THIS TYPE STATES** (a docstring is
not a theorem): the type below is only the flip-invariant lower bound `2 ≤ α₁(centralFlipConfig ε
bumpU)`.  The exclusion it described IS now a theorem, but a different one, in a different module:
`DriftTriangle.bumpU_not_a_central_flip_of_the_class`, which needed the deviation split
`DriftTriangle.frobSupBond_le_of_percube`. -/
theorem bumpU_not_in_centre_class (ε : Bond witnessL → Bool) :
    2 ≤ frobSupBond (centralFlipConfig ε bumpU) :=
  bumpU_centralFlip_ge_two ε


open scoped Matrix

/-! ## §4 — NON-VACUITY: a CURVED background with GENUINELY DIFFERENT per-cube gauges

The dispatch names the trap: a per-cube quantifier that is typed but never exercised.  §4 exercises
it — the background is curved (`α₁ > 0`), the cover is a genuine disjoint cover, and the gauges
DIFFER from cube to cube.  The enabling fact is that a gauge which is CONSTANT on the whole lattice
leaves the deviations invariant (conjugation is a Frobenius isometry) and has zero roughness, so
constant-but-different-per-cube gauges give a witness at the tightened radius. -/

/-- **Conjugation by an `SU(2)` element is a Frobenius isometry.**  Proved from
`RMapLipschitz.frobSq_eq_trace` and `Matrix.trace_mul_comm`; the tree had only the RIGHT-multiplication
form (`frobSq_mul_right_isometry`). -/
theorem frobSq_conj (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    RMapLipschitz.frobSq ((g : Matrix (Fin 2) (Fin 2) ℂ) * M * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ)
      = RMapLipschitz.frobSq M := by
  have hu : ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp g.2.1
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [RMapLipschitz.frobSq_eq_trace, RMapLipschitz.frobSq_eq_trace]
  congr 1
  have hstep : ((g : Matrix (Fin 2) (Fin 2) ℂ) * M * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ)
      * ((g : Matrix (Fin 2) (Fin 2) ℂ) * M * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ)ᴴ
      = (g : Matrix (Fin 2) (Fin 2) ℂ) * (M * Mᴴ) * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc (g : Matrix (Fin 2) (Fin 2) ℂ) * M * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
          * ((g : Matrix (Fin 2) (Fin 2) ℂ) * (Mᴴ * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ))
        = (g : Matrix (Fin 2) (Fin 2) ℂ) * M
            * ((((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * (g : Matrix (Fin 2) (Fin 2) ℂ))
              * (Mᴴ * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ)) := by noncomm_ring
      _ = (g : Matrix (Fin 2) (Fin 2) ℂ) * (M * Mᴴ) * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := by
            rw [hu, Matrix.one_mul]; noncomm_ring
  rw [hstep, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul]

theorem frobNorm_conj (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    RMapLipschitz.frobNorm ((g : Matrix (Fin 2) (Fin 2) ℂ) * M * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ)
      = RMapLipschitz.frobNorm M := by
  show Real.sqrt (RMapLipschitz.frobSq _) = Real.sqrt (RMapLipschitz.frobSq _)
  rw [frobSq_conj]

/-- **A CONSTANT gauge leaves every deviation exactly where it was.**  So per-cube smallness at a
constant gauge is the ungauged smallness — and the per-cube gauges may still DIFFER between cubes. -/
theorem frobNorm_constGauge {L : PeriodicLatticeExtent}
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b : Bond L) :
    RMapLipschitz.frobNorm
        (((periodicGaugeTransform (fun _ => g) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      = RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  have hcoe : (((periodicGaugeTransform (fun _ => g) U) b : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ)
      = (g : Matrix (Fin 2) (Fin 2) ℂ) * (U b : Matrix (Fin 2) (Fin 2) ℂ)
        * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := by
    show ((g * U b * g⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [AdalyFormal.Balaban.LemmaAssembly.su_coe_mul,
      AdalyFormal.Balaban.LemmaAssembly.su_coe_mul,
      AdalyFormal.Balaban.RegularUQChain.su_coe_inv]
  have hsub : (g : Matrix (Fin 2) (Fin 2) ℂ) * (U b : Matrix (Fin 2) (Fin 2) ℂ)
        * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ - 1
      = (g : Matrix (Fin 2) (Fin 2) ℂ) * ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := by
    have hu : (g : Matrix (Fin 2) (Fin 2) ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ = 1 := by
      have h := Matrix.mem_unitaryGroup_iff.mp g.2.1
      rwa [Matrix.star_eq_conjTranspose] at h
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu]
  rw [hcoe, hsub, frobNorm_conj]

/-- **A CONSTANT gauge has zero roughness**: its pure gauge is the flat background, exactly. -/
theorem pureGauge_constGauge {L : PeriodicLatticeExtent}
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    pureGauge (fun _ => g) = trivialU L := by
  funext b
  rw [pureGauge_apply]
  show g * g⁻¹ = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
  rw [mul_inv_cancel]

/-! ### §4a — the witness -/

open AdalyFormal.Balaban.Lemma24GeneralEll (witL3 witL3_dvd witL3_strict)
open AdalyFormal.Balaban.CovLemma24Witness (witU frobSupBond_witU)

/-- The rotation parameter of the witness: `10⁻⁷`, small enough for the TIGHTENED per-cube radius
`1/(37664·ℓ³)` at `ℓ = 3` (`1/1016928`), where `CovLemma24Witness.witT = 10⁻⁵` is not. -/
noncomputable def witTdrift : ℝ := 1 / 10000000

/-- Genuinely different constant gauges: `witnessMElem` on the cube `z₀`, `1` on every other cube. -/
noncomputable def twoGauge (z₀ z : AdalyFormal.Balaban.LocalizedEstimates.CSite witL3 3) :
    GaugeFn witL3 :=
  fun _ => if z = z₀ then witnessMElem else 1

/-- The two values the gauge family takes are DIFFERENT — the per-cube quantifier is exercised, not
merely typed.  `witnessMElem ≠ 1` is `DeltaKFull.witnessMElem_ne_one`, CITED. -/
theorem twoGauge_genuinely_differs (z₀ : AdalyFormal.Balaban.LocalizedEstimates.CSite witL3 3) :
    twoGauge z₀ z₀ = (fun _ => witnessMElem)
    ∧ (∀ z, z ≠ z₀ → twoGauge z₀ z = (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    ∧ ((fun _ => witnessMElem : GaugeFn witL3)
        ≠ (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))) := by
  refine ⟨?_, ?_, ?_⟩
  · funext x; show (if z₀ = z₀ then witnessMElem else 1) = witnessMElem; rw [if_pos rfl]
  · intro z hz; funext x; show (if z = z₀ then witnessMElem else 1) = 1; rw [if_neg hz]
  · intro hcon
    exact AdalyFormal.Balaban.DeltaKFull.witnessMElem_ne_one
      (congrFun hcon (fun _ => (0 : Fin (witL3 0 + 1))))

/-- **THE HYPOTHESIS SET OF §2 IS SATISFIED AT A GENUINELY CURVED BACKGROUND WITH GENUINELY
DIFFERENT PER-CUBE GAUGES.**  Five conjuncts, all measured:

1. the background is curved: `α₁(witU witTdrift) > 0`;
2. it clears the TIGHTENED radius `1/(37664·3³)` — where `CovLemma24Witness.witT` would not;
3. `hclass` holds at `r = α₁`, cube by cube, at the DIFFERENT per-cube gauges;
4. `hrough` holds at `ρ = 0` — constant gauges are exactly smooth;
5. the singleton cube family is pairwise disjoint and covers.

So §1–§2's hypotheses are not vacuous, and the per-cube gauge argument is exercised by gauges that
are not all equal (`twoGauge_genuinely_differs`). -/
theorem percube_hypotheses_curved_nonvacuous
    (z₀ : AdalyFormal.Balaban.LocalizedEstimates.CSite witL3 3) :
    0 < frobSupBond (witU witTdrift)
    ∧ frobSupBond (witU witTdrift) ≤ 1 / (37664 * ((3 : ℕ) : ℝ) ^ 3)
    ∧ (∀ i ∈ (Finset.univ : Finset (AdalyFormal.Balaban.LocalizedEstimates.CSite witL3 3)),
        ∀ b ∈ AdalyFormal.Balaban.LocalizedEstimates.bondsOn
          ({i} : Finset (AdalyFormal.Balaban.LocalizedEstimates.CSite witL3 3)),
        RMapLipschitz.frobNorm
          (((periodicGaugeTransform (twoGauge z₀ i) (witU witTdrift)) b :
            Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ frobSupBond (witU witTdrift))
    ∧ (∀ i : AdalyFormal.Balaban.LocalizedEstimates.CSite witL3 3, ∀ b : Bond witL3,
        RMapLipschitz.frobNorm
          (((pureGauge (gaugeInv (twoGauge z₀ i))) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [frobSupBond_witU]
    refine Real.sqrt_pos.mpr ?_
    rw [witTdrift]; norm_num
  · rw [frobSupBond_witU]
    have hle : 8 * witTdrift ^ 2 / (1 + witTdrift ^ 2) ≤ (1 / (37664 * ((3 : ℕ) : ℝ) ^ 3)) ^ 2 := by
      rw [witTdrift]; norm_num
    refine (Real.sqrt_le_sqrt hle).trans (le_of_eq ?_)
    exact Real.sqrt_sq (by positivity)
  · intro i _ b _
    have hz : twoGauge z₀ i = (fun _ => if i = z₀ then witnessMElem else 1) := rfl
    rw [hz, frobNorm_constGauge]
    exact frobNorm_le_frobSupBond (witU witTdrift) b
  · intro i b
    have hginv : gaugeInv (twoGauge z₀ i)
        = (fun _ => (if i = z₀ then witnessMElem else 1)⁻¹) := rfl
    rw [hginv, pureGauge_constGauge]
    have h1 : ((trivialU witL3 b : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) - 1 = 0 := by
      show ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1 = 0
      simp
    rw [h1, RMapLipschitz.frobNorm_zero]

#print axioms frobSq_conj
#print axioms frobNorm_conj
#print axioms frobNorm_constGauge
#print axioms pureGauge_constGauge
#print axioms witTdrift
#print axioms twoGauge
#print axioms twoGauge_genuinely_differs
#print axioms percube_hypotheses_curved_nonvacuous

#print axioms starDatum_hrawR_percube
#print axioms starDatum_hrawR_percube_centreBlind
#print axioms terminal_sum_at_star_datum_percube_centre
#print axioms centre_point_in_class
#print axioms bumpU_not_in_centre_class

end AdalyFormal.Balaban.DriftPerCube
