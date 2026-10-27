/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import EBBridge
import PrintedToAlpha
import AdalyFormal.Balaban.BlockedGaugeGuardAlgebraExp
import AdalyFormal.Balaban.ClassPropagationUbar
import PerCubeSeparation

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.longLine false

/-!
# `DeltaAlpha0Conv.lean` — THE UNIT CONVERSION (part 1 of 2): the terminal threshold's `δ`, in the source's `O(1)Mα₀`

LANE `compute/delta_alpha0/`.  Write scope: that directory only.  Never `lake build`.

`TerminalAssembly.terminal_wired_posDef` states its smallness as a closed-form bound on the LINK
DEVIATION `δ` of `SourceWired.LinkDev δ U` — an ENTRYWISE bound `∀ b i j, ‖U(b)ᵢⱼ − 1ᵢⱼ‖ ≤ δ`.
CMP99b p.396 states ITS smallness as (3.35), a bound on the gauge-fixed POTENTIAL `A` in the paper's
own Hilbert–Schmidt norm at the paper's own NORMALIZED trace.  The two are not the same object and
not in the same units.  This module builds the conversion and composes it, end to end.

## THE PRINTED SOURCE, RE-VERIFIED AT THE PAGE IMAGE (LAW-11)

`corpus/renders/CMP99b_p396-08.png`, sha256
`d0f0d665232fc871e005f2e721ea338e96c1a52763e151c3966bf7fcb47568ec` (re-hashed in this lane and
equal to the value `corpus/pages/CMP99b_p396.md` records); the (3.35) block was re-read at 200% and
the exponent glyph at 700%.  VERBATIM, from the image:

> for an arbitrary cube □ of the described above class, and for a configuration `U` there exists a
> gauge transformation `u` on □ such that `U^u = e^{iηA}`, and if the index of □ is `j`, then
>
> `|A| < O(1) M α₀ (L^j η)^{-1}`, `|∇^η A| < O(1) M α₀ (L^j η)^{-2}` on □,
> where `O(1)M` is a size of □ in `T_{L^{-j}}`;   (3.35)

> The number `α₀` characterizes this class of configurations.  We will need `α₀` so small that
> `O(1)Mα₀` is still a sufficiently small number.

At 700% the character after `i` in the exponent carries a DESCENDER and is the same glyph as the
`η` of `(L^jη)^{-1}`: the exponent is `e^{iηA}`, not `e^{inA}`.  That mesh `η` is what cancels
against `(L^jη)^{-1}`, so the glyph is load-bearing and was checked, not inherited.

**The quantifier prefix, transcribed exactly:** `∀ □ ∀ U ∃ u`.  The gauge is existential INSIDE the
cube quantifier.  Nothing on the page ties the gauges of two cubes together.  §3 keeps that prefix;
§6 records the one place where it is not enough.

## WHAT THIS MODULE PROVES

§1  the entrywise bridge at CONSTANT `1`: `‖X‖_op ≤ a ⟹ EB a X`, and `1` is attained.
    §1b closes `EBBridge`'s explicitly disclaimed gap — its `printedNormSq` and
    `ThresholdVsPrinted`'s ARE the same function — and §1c re-derives the `√2` route through the
    `EBBridge` so the two constants can be compared as theorems: the `√2` is the price of entering
    from the printed HS norm, and is NOT paid when entering from the operator norm, which is the
    norm the rendering step actually delivers.
§2  (3.35) at one link ⟹ `EB (O(1)Mα₀) (U^u(b) − 1)`.  The mesh `η` and the level `L^j` cancel.
§3  (3.35) as printed — `∀□ ∃u` — ⟹ `GaugePatching.CubeGaugeData (O(1)Mα₀) U 𝒞`, hence
    `‖J(U)‖ ≤ √(2|Bond L|)·495·(O(1)Mα₀)` with no patching and no loss of constant.
§4  the closed-form threshold in the SOURCE's own parameter, every factor counted.
§5  the composed terminal statement, from the printed per-cube class (§5a) and from a global
    printed representation (§5b, where the covariance-class hypothesis is discharged too).
§6  what the per-cube quantifier does and does not reach, as theorems.
§7  non-vacuity and garbage-substitution guards.

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.
-/

namespace AdalyFormal.Balaban.DeltaAlpha0

open scoped Matrix.Norms.L2Operator
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.SourceWiredJ (EB JsuTwo)
open AdalyFormal.Balaban.SourceWired (LinkDev)
open AdalyFormal.Balaban.SourceWiredGauge (gaugeT)
open AdalyFormal.Balaban.GaugePatching (CubeGaugeData StencilCovered norm_JsuTwo_le_of_cubes
  norm_JsuTwo_le_of_linkDev')
open Carrier (M2)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE ENTRYWISE BRIDGE

`EB C X` is `∀ i j, ‖X i j‖ ≤ C` (`SourceWiredJ.EB`).  `LinkDev δ U` is `∀ b, EB δ (U(b) − 1)`.
So the terminal theorem's `δ` is an ENTRYWISE deviation, and the conversion has to land there. -/

/-- **THE ENTRYWISE BOUND FROM THE OPERATOR NORM, CONSTANT `1`.**  `|X_{ij}| = |⟨e_i, X e_j⟩| ≤ ‖X‖`.
Proved by reusing `ThresholdVsPrinted.col_normSq_le_opNorm_sq` (LAW-19: the column estimate is
already in the tree, tested on the two standard basis vectors) and picking one summand out of the
column. -/
theorem EB_of_opNorm_le (X : M2) {a : ℝ} (h : ‖X‖ ≤ a) : EB a X := by
  intro i j
  have hcol := ThresholdVsPrinted.col_normSq_le_opNorm_sq X j
  have hsingle : Complex.normSq (X i j) ≤ ∑ p : Fin 2, Complex.normSq (X p j) :=
    Finset.single_le_sum (f := fun p => Complex.normSq (X p j))
      (fun p _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have hsq : ‖X i j‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    linarith
  have h0 : (0 : ℝ) ≤ ‖X‖ := norm_nonneg X
  nlinarith [hsq, h, h0, norm_nonneg (X i j)]

/-- **AND `1` CANNOT BE LOWERED.**  Any `K` valid for every `X` and every `a` obeys `1 ≤ K`, by
testing at `X = 1`, `a = 1`: `‖1‖_op = 1` and the entry `1₀₀` has modulus `1`.  So §1's conversion
is EXACT, not merely available. -/
theorem EB_opNorm_constant_sharp {K : ℝ}
    (hall : ∀ (X : M2) (a : ℝ), 0 ≤ a → ‖X‖ ≤ a → EB (K * a) X) : 1 ≤ K := by
  have h := hall 1 1 (by norm_num) (by rw [norm_one]) 0 0
  simpa [Matrix.one_apply] using h

/-! ### §1b — THE TWO `printedNormSq`s ARE THE SAME FUNCTION

`compute/gauge_patching/stage/EBBridge.lean`'s header says, verbatim: *"`compute/rendering_step_v2/
stage/TwoByTwo.lean` has its own `printedNormSq` on its own abstract carrier.  This file does not
pin or import it; … Agreement of the two is not asserted."*  It is asserted here, and proved.  The
two definitions are `½·Σ_{ij}‖X_{ij}‖²` (EBBridge) and `½·frobSq X` with
`frobSq = Σ Complex.normSq` (`RMapLipschitz`, through `ThresholdVsPrinted.printedNormSq`); they
agree because `Complex.normSq z = ‖z‖²`. -/
theorem printedNormSq_agree (X : M2) :
    GaugePatching.EBBridge.printedNormSq X = ThresholdVsPrinted.printedNormSq X := by
  unfold GaugePatching.EBBridge.printedNormSq ThresholdVsPrinted.printedNormSq
    RMapLipschitz.frobSq
  simp only [Fin.sum_univ_two, Complex.normSq_eq_norm_sq]
  ring

/-! ### §1c — THE `√2` ROUTE, AND WHAT THE `√2` IS THE PRICE OF -/

/-- **THE `EBBridge` ROUTE, RE-ENTERED FROM THE OPERATOR NORM.**  `EBBridge.EB_of_printedNormSq_le`
is exact for its own hypothesis (its `√2` is proved SHARP there, at `X = e₀₀`).  Fed from an
operator-norm bound it yields `√2·a`, because `|X| ≤ ‖X‖_op` loses nothing but the bridge's own
constant is then applied to a quantity that is already the larger one. -/
theorem EB_sqrtTwo_of_opNorm_le (X : M2) {a : ℝ} (ha : 0 ≤ a) (h : ‖X‖ ≤ a) :
    EB (Real.sqrt 2 * a) X := by
  refine GaugePatching.EBBridge.EB_of_printedNormSq_le X ha ?_
  rw [printedNormSq_agree]
  refine le_trans (ThresholdVsPrinted.printedNormSq_le_opNorm_sq X) ?_
  nlinarith [norm_nonneg X, h, ha]

/-- **THE COMPARISON, AS A THEOREM.**  At every strictly positive `a` the direct route's constant is
strictly smaller.  Recorded because a lane holding only the printed HS norm MUST pay the `√2` (and
`EBBridge.EB_constant_sharp` proves it cannot do better), while a lane holding the operator norm —
which is what `RenderStep.rendering_step_group_from_source` delivers — must not. -/
theorem direct_route_strictly_sharper {a : ℝ} (ha : 0 < a) : a < Real.sqrt 2 * a := by
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    have hs : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa [Real.sqrt_one] using hs
  nlinarith [h1, ha]

/-! ## §2 — (3.35) AT ONE LINK

`RenderStep.rendering_step_group_from_source` (kernel-checked in `compute/rendering_step_v2/`,
recompiled here from a plain copy) takes the printed premise
`a ≤ printedABound c M α₀ Lj η = c·M·α₀/(L^j·η)` with `a = |A|` fixed by Cayley–Hamilton
`A² = |A|²·1`, and delivers `‖e^{iηA} − 1‖_op ≤ linkEps c M α₀ Lj = c·M·α₀/L^j`.
`ThresholdVsPrinted.linkEps_le_smallness` drops `L^{-j} ≤ 1`.  §1 lands it entrywise. -/

/-- **THE LINK DEVIATION FROM (3.35), AT THE PRINTED CONSTANT.**  Hypotheses are exactly the printed
ones plus the two structural facts about the printed object (`A` Hermitian, Cayley–Hamilton).

**The mesh `η` and the level `L^j` do not appear in the conclusion**: `η` cancels against
`(L^jη)^{-1}` inside `rendering_step_group_from_source`, and `L^{-j} ≤ 1` for every `L ≥ 1`, `j ≥ 0`.
The surviving constant is `1`: the entrywise deviation is bounded by `O(1)Mα₀` itself. -/
theorem EB_link_of_printed (Jm A : M2) (hJ : RenderStep.IsImaginaryUnit Jm) (hA : star A = A)
    (η a c M α₀ Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (ha : 0 ≤ a) (hLj : 1 ≤ Lj)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (hsq : A * A = (a ^ 2) • (1 : M2))
    (hprint : a ≤ RenderStep.printedABound c M α₀ Lj η) :
    EB (c * M * α₀) (NormedSpace.exp (η • (Jm * A)) - 1) := by
  refine EB_of_opNorm_le _ ?_
  refine le_trans (RenderStep.rendering_step_group_from_source Jm A hJ hA η a c M α₀ Lj hη hηne ha
    (lt_of_lt_of_le zero_lt_one hLj) hsq hprint) ?_
  exact ThresholdVsPrinted.linkEps_le_smallness c M α₀ Lj hc hM hα hLj

/-- The same through the `EBBridge`, for a consumer that holds only the printed HS norm.  The
constant is `√2·O(1)Mα₀`; `direct_route_strictly_sharper` says what that costs. -/
theorem EB_link_of_printed_via_bridge (Jm A : M2) (hJ : RenderStep.IsImaginaryUnit Jm)
    (hA : star A = A) (η a c M α₀ Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (ha : 0 ≤ a) (hLj : 1 ≤ Lj)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (hsq : A * A = (a ^ 2) • (1 : M2))
    (hprint : a ≤ RenderStep.printedABound c M α₀ Lj η) :
    EB (Real.sqrt 2 * (c * M * α₀)) (NormedSpace.exp (η • (Jm * A)) - 1) := by
  refine EB_sqrtTwo_of_opNorm_le _ (by positivity) ?_
  refine le_trans (RenderStep.rendering_step_group_from_source Jm A hJ hA η a c M α₀ Lj hη hηne ha
    (lt_of_lt_of_le zero_lt_one hLj) hsq hprint) ?_
  exact ThresholdVsPrinted.linkEps_le_smallness c M α₀ Lj hc hM hα hLj

/-! ## §3 — (3.35) AS PRINTED: THE PER-CUBE CLASS

The quantifier prefix of p.396 is `∀□ ∃u`.  `PrintedCubeClass` transcribes it: the gauge is chosen
per cube, and the printed exponential representation with the printed size bound is asserted at each
link OF THAT CUBE.  Nothing relates two cubes' gauges — because the page relates nothing. -/

/-- **(3.35) AT ONE CUBE.**  `∃u` on `□` with `U^u = e^{iηA}` and `|A| < O(1)Mα₀(L^jη)^{-1}` on `□`.
`a` is the printed size of `A` at that link, pinned by Cayley–Hamilton (`A² = a²·1`, which for a
traceless Hermitian `2×2` holds with `a = |A|`, `TwoByTwo.herm2_sq`). -/
def PrintedGaugeCube (Jm : M2) (c M α₀ η Lj : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (C : Set (Bond L)) : Prop :=
  ∃ g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ,
    ∀ e ∈ C, ∃ A : M2, ∃ a : ℝ,
      star A = A ∧ 0 ≤ a ∧ A * A = (a ^ 2) • (1 : M2) ∧
        a ≤ RenderStep.printedABound c M α₀ Lj η ∧
        ((gaugeT g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : M2)
          = NormedSpace.exp (η • (Jm * A))

/-- **(3.35) OVER A FAMILY OF CUBES**, with the printed quantifier prefix `∀□ ∃u` intact. -/
def PrintedCubeClass (Jm : M2) (c M α₀ η Lj : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (𝒞 : Set (Set (Bond L))) : Prop :=
  ∀ C ∈ 𝒞, PrintedGaugeCube Jm c M α₀ η Lj U C

/-- **THE CONVERSION, PER CUBE.**  (3.35) as printed gives exactly `GaugePatching.CubeGaugeData` at
`δ = O(1)Mα₀` — the hypothesis shape `norm_JsuTwo_le_of_cubes` consumes.  The gauge is passed
through unchanged; no compatibility between cubes is introduced, because none is used. -/
theorem cubeGaugeData_of_printedCubeClass (Jm : M2) (hJ : RenderStep.IsImaginaryUnit Jm)
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (𝒞 : Set (Set (Bond L))) (h : PrintedCubeClass Jm c M α₀ η Lj U 𝒞) :
    CubeGaugeData (c * M * α₀) U 𝒞 := by
  intro C hC
  obtain ⟨g, hg⟩ := h C hC
  refine ⟨g, fun e he => ?_⟩
  obtain ⟨A, a, hA, ha, hsq, hprint, hexp⟩ := hg e he
  rw [hexp]
  exact EB_link_of_printed Jm A hJ hA η a c M α₀ Lj hη hηne ha hLj hc hM hα hsq hprint

/-- **THE SOURCE BOUND FROM (3.35) ALONE.**  `‖J(U)‖ ≤ √(2|Bond L|)·495·(O(1)Mα₀)`, from the printed
per-cube data plus the ONE piece of cube geometry `norm_JsuTwo_le_of_cubes` needs
(`StencilCovered 𝒞`: every bond's `J`-stencil, of radius one lattice spacing, sits inside a single
cube — and p.396's cubes have size `O(1)ML^jη` with `O(1) ≥ 10`).  `495` is `SourceWiredJ`'s
per-bond constant, unchanged. -/
theorem norm_JsuTwo_le_of_printedCubes (Jm : M2) (hJ : RenderStep.IsImaginaryUnit Jm)
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (𝒞 : Set (Set (Bond L))) (hcov : StencilCovered 𝒞)
    (h : PrintedCubeClass Jm c M α₀ η Lj U 𝒞) :
    ‖JsuTwo U‖ ≤ Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * (c * M * α₀)) :=
  norm_JsuTwo_le_of_cubes (by positivity) U 𝒞 hcov
    (cubeGaugeData_of_printedCubeClass Jm hJ c M α₀ η Lj hη hηne hLj hc hM hα U 𝒞 h)

/-! ## §4 — THE THRESHOLD IN THE SOURCE'S OWN PARAMETER

`TerminalAssembly.delta_threshold_suffices` says: with `R = N·495·δ` and
`N = ‖T‖·√(2|Bond L|)`, the hypothesis `2‖H₁‖c₂R < γ` of the terminal theorem holds as soon as

    δ < 1 / (1370001600 · ℓ⁶ · σ₀² · ‖H₁‖ · c₂ · N) .

§2 says the printed data delivers `δ = O(1)Mα₀`.  Substituting is the whole conversion.  Every
factor of `1370001600` is counted upstream: `1370001600 = 990 · 1383840`, `990 = 2·495` (`2` from
the printed `−2⟨H₁D̃⁽²⁾(B),J⟩` of (3.156), `495` from `SourceWiredJ`), `1383840 = 4·345960` (the `4`
from the drift regime `κ ≤ ½√γ`), `345960 = 12454560/36` from `TerminalCompose.gammaBrick_lower`. -/

/-- The source-term half of the admissible region for the printed `O(1)Mα₀`. -/
noncomputable def sourceThreshold (ell : ℕ) (σ₀ H1 c₂ N : ℝ) : ℝ :=
  1 / (1370001600 * (ell : ℝ) ^ 6 * σ₀ ^ 2 * H1 * c₂ * N)

/-- The covariance-class half, in a RATIONAL constant.  `280` is derived in
`covThreshold_constant_derivation`: `186·(3/2) = 279 ≤ 280` and `√2 ≤ 3/2`.  The EXACT requirement
is `186·√2 = 263.04…`, so `280` is sufficient and not least; `covariance_class_of_alpha0_exact`
gives the exact form. -/
noncomputable def covThreshold (ell : ℕ) : ℝ := 1 / (280 * (ell : ℝ) ^ 3)

/-- **THE ADMISSIBLE REGION FOR THE SOURCE'S OWN SMALLNESS PARAMETER**, in closed form.  One number:
the printed `O(1)Mα₀` must lie below it, and both hypotheses of the terminal theorem follow. -/
noncomputable def alphaThreshold (ell : ℕ) (σ₀ H1 c₂ N : ℝ) : ℝ :=
  min (sourceThreshold ell σ₀ H1 c₂ N) (covThreshold ell)

theorem alphaThreshold_le_source (ell : ℕ) (σ₀ H1 c₂ N : ℝ) :
    alphaThreshold ell σ₀ H1 c₂ N ≤ sourceThreshold ell σ₀ H1 c₂ N := min_le_left _ _

theorem alphaThreshold_le_cov (ell : ℕ) (σ₀ H1 c₂ N : ℝ) :
    alphaThreshold ell σ₀ H1 c₂ N ≤ covThreshold ell := min_le_right _ _

/-- `√2 ≤ 3/2`, by squaring — the only place a `√2` is estimated rather than carried exactly. -/
theorem sqrt_two_le_three_halves : Real.sqrt 2 ≤ 3 / 2 := by
  rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- **THE `280` IS COUNTED, NOT CHOSEN.**  `186 · (3/2) = 279 ≤ 280`. -/
theorem covThreshold_constant_derivation : (186 : ℝ) * (3 / 2) = 279 ∧ (279 : ℝ) ≤ 280 := by
  constructor <;> norm_num

/-- **THE COVARIANCE CLASS FROM THE PRINTED PARAMETER, EXACT FORM.**  `√2·s ≤ 1/(186ℓ³)` exactly
when `s ≤ 1/(186√2·ℓ³)`; this is the direction needed. -/
theorem covariance_class_of_alpha0_exact {ell : ℕ} (hell : 0 < ell) (s : ℝ) (hs : 0 ≤ s)
    (h : s ≤ 1 / (186 * Real.sqrt 2 * (ell : ℝ) ^ 3)) :
    Real.sqrt 2 * s ≤ 1 / (186 * (ell : ℝ) ^ 3) := by
  have hL : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hL3 : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hden : (0 : ℝ) < 186 * Real.sqrt 2 * (ell : ℝ) ^ 3 := by positivity
  have hden' : (0 : ℝ) < 186 * (ell : ℝ) ^ 3 := by positivity
  rw [le_div_iff₀ hden] at h
  rw [le_div_iff₀ hden']
  nlinarith [h, h2, hL3, hsq, hs]

/-- **THE COVARIANCE CLASS FROM THE PRINTED PARAMETER, RATIONAL FORM.**  `s < covThreshold ℓ`
suffices for `√2·s ≤ 1/(186ℓ³)` — the class hypothesis `terminal_posDef_of_source_bound` takes. -/
theorem covariance_class_of_alpha0 {ell : ℕ} (hell : 0 < ell) (s : ℝ) (hs : 0 ≤ s)
    (h : s < covThreshold ell) : Real.sqrt 2 * s ≤ 1 / (186 * (ell : ℝ) ^ 3) := by
  have hL : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hL3 : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  have hden : (0 : ℝ) < 280 * (ell : ℝ) ^ 3 := by positivity
  have hden' : (0 : ℝ) < 186 * (ell : ℝ) ^ 3 := by positivity
  have h' : s * (280 * (ell : ℝ) ^ 3) < 1 := by
    unfold covThreshold at h
    rw [lt_div_iff₀ hden] at h
    exact h
  have h32 := sqrt_two_le_three_halves
  have h2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [le_div_iff₀ hden']
  nlinarith [h', h32, h2nn, hs, hL3]

/-! ### §5b — A GLOBAL PRINTED REPRESENTATION DISCHARGES BOTH HYPOTHESES

If the configuration is in the printed exponential form at EVERY bond with ONE `A`-field — i.e. the
gauge has already been applied globally, which is what CMP99b's own `U' = e^{iηA'}` shape assumes on
`Ω_j` in (3.37) — then the covariance-class hypothesis is a consequence of the SAME parameter, and
the terminal statement has no carried smallness hypothesis at all. -/

/-- **THE GLOBAL PRINTED REPRESENTATION.**  (3.35)'s conclusion at every bond, with the gauge already
applied.  This is STRICTLY STRONGER than `PrintedCubeClass` (§6b proves the implication and §6c
proves the converse fails). -/
def PrintedGlobalRep (Jm : M2) (c M α₀ η Lj : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : Prop :=
  ∀ b : Bond L, ∃ A : M2, ∃ a : ℝ,
    star A = A ∧ 0 ≤ a ∧ A * A = (a ^ 2) • (1 : M2) ∧
      a ≤ RenderStep.printedABound c M α₀ Lj η ∧
      ((U b : Matrix.specialUnitaryGroup (Fin 2) ℂ) : M2) = NormedSpace.exp (η • (Jm * A))

/-- **THE LINK-DEVIATION CLASS FROM A GLOBAL PRINTED REPRESENTATION**, at constant `1`.  This is the
exact `LinkDev δ U` the terminal theorem's §8c form consumes, with `δ = O(1)Mα₀`. -/
theorem linkDev_of_printedGlobal (Jm : M2) (hJm : RenderStep.IsImaginaryUnit Jm)
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (h : PrintedGlobalRep Jm c M α₀ η Lj U) : LinkDev (c * M * α₀) U := by
  intro b
  obtain ⟨A, a, hA, ha, hsq, hprint, hexp⟩ := h b
  rw [hexp]
  exact EB_link_of_printed Jm A hJm hA η a c M α₀ Lj hη hηne ha hLj hc hM hα hsq hprint

/-- **THE COVARIANCE CLASS FROM A GLOBAL PRINTED REPRESENTATION.**  `frobSupBond U ≤ √2·O(1)Mα₀`,
reusing `ThresholdVsPrinted.printed_to_smallness` (the per-link Frobenius conversion) and
`frobSupBond_le_of_links` (the `sup'`).  The `√2` here is EXACT and unavoidable: it is
`‖X‖_F = √2·|X|`, an equality (`ThresholdVsPrinted.frobNorm_eq_sqrt_two_mul_printed`), and
`frobSupBond` is built from `‖·‖_F`. -/
theorem frobSupBond_le_of_printedGlobal (Jm : M2) (hJm : RenderStep.IsImaginaryUnit Jm)
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (h : PrintedGlobalRep Jm c M α₀ η Lj U) :
    frobSupBond U ≤ Real.sqrt 2 * (c * M * α₀) := by
  refine ThresholdVsPrinted.frobSupBond_le_of_links U (c * M * α₀) (fun b => ?_)
  obtain ⟨A, a, hA, ha, hsq, hprint, hexp⟩ := h b
  rw [hexp]
  exact ThresholdVsPrinted.printed_to_smallness Jm A hJm hA η a c M α₀ Lj hη hηne ha hLj hc hM hα
    hsq hprint

/-! ## §6 — WHAT THE PER-CUBE QUANTIFIER REACHES, AND WHAT IT DOES NOT -/

/-- **§6b — THE GLOBAL REPRESENTATION IMPLIES THE PRINTED PER-CUBE CLASS**, for EVERY cube family:
take the constant gauge `g ≡ 1`.  So §5b's hypothesis set contains §5a's. -/
theorem printedCubeClass_of_printedGlobal (Jm : M2) (c M α₀ η Lj : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (𝒞 : Set (Set (Bond L))) (h : PrintedGlobalRep Jm c M α₀ η Lj U) :
    PrintedCubeClass Jm c M α₀ η Lj U 𝒞 := by
  intro C _
  refine ⟨fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ), fun e _ => ?_⟩
  obtain ⟨A, a, hA, ha, hsq, hprint, hexp⟩ := h e
  refine ⟨A, a, hA, ha, hsq, hprint, ?_⟩
  have hone : gaugeT (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) U e = U e := by
    simp [gaugeT]
  rw [hone]
  exact hexp

/-- **§6c — THE ONE THING THE PER-CUBE CLASS CANNOT REACH, AS A THEOREM: `frobSupBond`.**

`frobSupBond` is a `sup'` of `‖U(b) − 1‖_F` over the UNGAUGED configuration, and it is not a
function of the gauge orbit: `ThresholdVsPrinted.frobNorm_negOne_sub_one` computes `2√2` for the
link `−1`, which is gauge-equivalent to the flat link `1` (`frobSupBond = 0`).  This theorem states
the consequence in the form that matters here: `frobSupBond` SEPARATES two configurations that the
printed per-cube class cannot distinguish, so no per-cube-gauge hypothesis can bound it.

Concretely, the gap between `0` and `2√2` is the whole admissible range: `1/(186ℓ³) < 2√2` for every
`ℓ ≥ 1`, so a configuration whose gauged form is EXACTLY flat can still fail the covariance class. -/
theorem frobSupBond_gauge_gap {ell : ℕ} (hell : 0 < ell) :
    RMapLipschitz.frobNorm ((-1 : M2) - 1) = 2 * Real.sqrt 2 ∧
      1 / (186 * (ell : ℝ) ^ 3) < 2 * Real.sqrt 2 := by
  refine ⟨ThresholdVsPrinted.frobNorm_negOne_sub_one, ?_⟩
  have hL : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hL3 : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ hL
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    have hs : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa [Real.sqrt_one] using hs
  have hden : (0 : ℝ) < 186 * (ell : ℝ) ^ 3 := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith [h1, hL3]

/-! ## §7 — NON-VACUITY AND GARBAGE SUBSTITUTION -/

/-- **THE PRINTED CLASS IS INHABITED** — at the flat configuration, the identity gauge, `A = 0`,
`a = 0`, for EVERY cube family and every printed parameter.  **DISCLOSED, and it is the point of
stating it as a theorem rather than a remark:** this witness is DEGENERATE — at `A = 0` the link is
`1` and `J(U) = 0`, so the source term contributes nothing.  It shows the hypothesis set of §5a is
not empty; it does not show the conclusion has content there.  §7b and §7c supply the content. -/
theorem printedCubeClass_inhabited (Jm : M2) (c M α₀ η Lj : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hα : 0 ≤ α₀) (hLj : 0 < Lj) (hη : 0 < η)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hflat : ∀ b : Bond L, ((U b : Matrix.specialUnitaryGroup (Fin 2) ℂ) : M2) = 1)
    (𝒞 : Set (Set (Bond L))) : PrintedCubeClass Jm c M α₀ η Lj U 𝒞 := by
  intro C _
  refine ⟨fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ), fun e _ => ?_⟩
  refine ⟨0, 0, by simp, le_refl 0, by simp, ?_, ?_⟩
  · unfold RenderStep.printedABound
    positivity
  · have hone : gaugeT (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) U e = U e := by
      simp [gaugeT]
    rw [hone, hflat e]
    simp

/-- **§7b — GARBAGE SUBSTITUTION (S82): THE CONCLUSION IS NOT ALGEBRAICALLY FORCED.**  Substitute a
structurally admissible but non-small group element — `−1 ∈ SU(2)` — for the link.  Every entry of
`(−1) − 1` has modulus `2` on the diagonal, so `EB δ ((−1) − 1)` is FALSE for every `δ < 2`.  Hence
`EB δ` at a small `δ` is a real restriction on `SU(2)` links, not a tautology, and a certificate
that "passes" for every link would be measuring nothing. -/
theorem EB_not_forced {δ : ℝ} (hδ : δ < 2) : ¬ EB δ ((-1 : M2) - 1) := by
  intro h
  have h00 := h 0 0
  have hval : ((-1 : M2) - 1) 0 0 = (-2 : ℂ) := by
    simp [Matrix.one_apply]
    ring
  rw [hval] at h00
  have : ‖(-2 : ℂ)‖ = 2 := by
    rw [show (-2 : ℂ) = ((-2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
    norm_num
  rw [this] at h00
  linarith

/-- **§7c — THE PRINTED PREMISE ADMITS A NONZERO POTENTIAL.**  At strictly positive printed data the
bound `|A| < O(1)Mα₀(L^jη)^{-1}` is a bound by a STRICTLY POSITIVE number, so (3.35) does not force
`A = 0` and the class is not secretly the flat one.  (Together with §7b: the hypothesis admits
non-flat data and the conclusion excludes far-from-flat data — the conversion sits strictly between
the two.) -/
theorem printedABound_pos (c M α₀ Lj η : ℝ) (hc : 0 < c) (hM : 0 < M) (hα : 0 < α₀) (hLj : 0 < Lj)
    (hη : 0 < η) : 0 < RenderStep.printedABound c M α₀ Lj η := by
  unfold RenderStep.printedABound
  positivity

/-- **§7d — THE THRESHOLD IS NOT VACUOUS**: at strictly positive derived constants the admissible
region for `O(1)Mα₀` is a nonempty interval `(0, alphaThreshold)`. -/
theorem alphaThreshold_pos {ell : ℕ} (hell : 0 < ell) (σ₀ H1 c₂ N : ℝ) (hσ₀ : 0 < σ₀)
    (hH1 : 0 < H1) (hc₂ : 0 < c₂) (hN : 0 < N) : 0 < alphaThreshold ell σ₀ H1 c₂ N := by
  have hL : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  unfold alphaThreshold sourceThreshold covThreshold
  refine lt_min ?_ ?_ <;> positivity

/-- **§7e — THE UNIFORM-RESCALE TEST ON THE LOAD-BEARING NORMALIZATION.**  The whole conversion is
anchored on the source's NORMALIZED trace (`tr 1 = 1`, p.392), which is what makes `|A| = ‖A‖_op`
for the printed potential and `printedNormSq 1 = 1`.  If the normalization were doubled — the
unnormalized trace — `printedNormSq 1` would be `2`, and this equation would be false.  Recorded at
BOTH definitions, so a rescaling of either is caught. -/
theorem normalization_pinned :
    GaugePatching.EBBridge.printedNormSq (1 : M2) = 1 ∧
      ThresholdVsPrinted.printedNormSq (1 : M2) = 1 ∧
        RMapLipschitz.frobSq (1 : M2) = 2 :=
  ⟨GaugePatching.EBBridge.printedNormSq_one, ThresholdVsPrinted.printedNormSq_one,
    ThresholdVsPrinted.frobSq_one⟩



/-! ## §8 — THE PRINTED CLASS AT THE SOURCE'S OWN `i`

p.396 writes `U^u = e^{iηA}` with `i` THE imaginary unit, not an arbitrary square root of `−1`.
Fixing the algebra element to `Carrier.imagUnit` (`i·1` in `M2`, whose three `IsImaginaryUnit`
clauses are proved by `Carrier.isImaginaryUnit_imagUnit`) removes both the `Jm` binder and its
hypothesis from every downstream statement.

**This is not a convenience.**  Measured in this lane: keeping `M2` and the scoped matrix-norm
instances out of the composed theorems is what makes them elaborate at all.  With
`open scoped Matrix.Norms.L2Operator` in the composed module, `BondFnL2 L` acquires TWO
syntactically distinct `Norm` instances — `PiLp.instNorm 2 (fun _ => SuTwo)` and
`(PiLp.seminormedAddCommGroup 2 (fun _ => SuTwo)).toNorm` — and every `‖·‖` on that carrier then
costs a deep defeq check.  §8 is the interface that keeps the two worlds apart. -/

/-- **(3.35) OVER A FAMILY OF CUBES, AT THE PRINTED `i`.** -/
def PrintedCubeClassI (c M α₀ η Lj : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (𝒞 : Set (Set (Bond L))) : Prop :=
  PrintedCubeClass Carrier.imagUnit c M α₀ η Lj U 𝒞

/-- **THE GLOBAL PRINTED REPRESENTATION, AT THE PRINTED `i`.** -/
def PrintedGlobalRepI (c M α₀ η Lj : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : Prop :=
  PrintedGlobalRep Carrier.imagUnit c M α₀ η Lj U

/-- §3's source bound, with the `Jm` binder and `IsImaginaryUnit` discharged at the printed `i`. -/
theorem norm_JsuTwo_le_of_printedCubesI (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0)
    (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (𝒞 : Set (Set (Bond L))) (hcov : StencilCovered 𝒞)
    (h : PrintedCubeClassI c M α₀ η Lj U 𝒞) :
    ‖JsuTwo U‖ ≤ Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * (c * M * α₀)) :=
  norm_JsuTwo_le_of_printedCubes Carrier.imagUnit Carrier.isImaginaryUnit_imagUnit c M α₀ η Lj
    hη hηne hLj hc hM hα U 𝒞 hcov h

/-- §5b's link-deviation class, at the printed `i`. -/
theorem linkDev_of_printedGlobalI (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (h : PrintedGlobalRepI c M α₀ η Lj U) : LinkDev (c * M * α₀) U :=
  linkDev_of_printedGlobal Carrier.imagUnit Carrier.isImaginaryUnit_imagUnit c M α₀ η Lj
    hη hηne hLj hc hM hα U h

/-- §5b's covariance-class bound, at the printed `i`. -/
theorem frobSupBond_le_of_printedGlobalI (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0)
    (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (h : PrintedGlobalRepI c M α₀ η Lj U) :
    frobSupBond U ≤ Real.sqrt 2 * (c * M * α₀) :=
  frobSupBond_le_of_printedGlobal Carrier.imagUnit Carrier.isImaginaryUnit_imagUnit c M α₀ η Lj
    hη hηne hLj hc hM hα U h

/-- §6b at the printed `i`: the global representation implies the per-cube class. -/
theorem printedCubeClassI_of_printedGlobalI (c M α₀ η Lj : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (𝒞 : Set (Set (Bond L))) (h : PrintedGlobalRepI c M α₀ η Lj U) :
    PrintedCubeClassI c M α₀ η Lj U 𝒞 :=
  printedCubeClass_of_printedGlobal Carrier.imagUnit c M α₀ η Lj U 𝒞 h

/-- §7a at the printed `i`: the class is inhabited (degenerately — see §7a's disclosure). -/
theorem printedCubeClassI_inhabited (c M α₀ η Lj : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hα : 0 ≤ α₀) (hLj : 0 < Lj) (hη : 0 < η)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hflat : ∀ b : Bond L, ((U b : Matrix.specialUnitaryGroup (Fin 2) ℂ) : M2) = 1)
    (𝒞 : Set (Set (Bond L))) : PrintedCubeClassI c M α₀ η Lj U 𝒞 :=
  printedCubeClass_inhabited Carrier.imagUnit c M α₀ η Lj hc hM hα hLj hη U hflat 𝒞



/-! ## §9 — A NON-DEGENERATE INHABITANT: EVERY ADMISSIBLE PRINTED POTENTIAL FIELD

§7a's witness is the FLAT configuration, and is disclosed there as degenerate.  §9 replaces it by
the full family the printed data allows: for an ARBITRARY field of traceless Hermitian potentials
`A(b) = herm2 (x b) (y b)` whose printed size obeys (3.35), the configuration `b ↦ e^{iηA(b)}` is a
genuine `SU(2)` link configuration and lies in the printed class.  Nothing is assumed about `x`,
`y` beyond the printed bound — in particular they need not vanish, so the class is not the flat one
in disguise.

`SU(2)` membership is NOT re-derived here: it is `SuTwoLogExp.exp_antiHerm_traceless_mem_special`
(LAW-19), whose two hypotheses — anti-Hermiticity and tracelessness of the exponent — are supplied
from `RenderStep.star_eta_smul_mul` and `TwoByTwo.herm2_trace`.  That this composes at all is a
FACT worth recording: that theorem is stated at the tree's default matrix instances and this lane
works under `Matrix.Norms.L2Operator`, and the two elaborations agree. -/

/-- The printed exponent `iηA` is anti-Hermitian, for `A = herm2 x y`. -/
theorem printedExponent_antiHerm (x : ℝ) (y : ℂ) (η : ℝ) :
    Matrix.conjTranspose (η • (Carrier.imagUnit * TwoByTwo.herm2 x y))
      = -(η • (Carrier.imagUnit * TwoByTwo.herm2 x y)) := by
  have h := RenderStep.star_eta_smul_mul Carrier.imagUnit (TwoByTwo.herm2 x y)
    Carrier.isImaginaryUnit_imagUnit (Carrier.star_herm2 x y) η
  simpa [Matrix.star_eq_conjTranspose] using h

/-- The printed exponent is traceless — `herm2` is, and `i` and `η` are scalars. -/
theorem printedExponent_trace (x : ℝ) (y : ℂ) (η : ℝ) :
    Matrix.trace (η • (Carrier.imagUnit * TwoByTwo.herm2 x y)) = 0 := by
  have hmul : Carrier.imagUnit * TwoByTwo.herm2 x y = Complex.I • TwoByTwo.herm2 x y := by
    rw [Carrier.imagUnit, smul_mul_assoc, one_mul]
  rw [hmul, Matrix.trace_smul, Matrix.trace_smul, TwoByTwo.herm2_trace, smul_zero, smul_zero]

/-- **`e^{iηA} ∈ SU(2)`** for every real `η` and every traceless Hermitian `A = herm2 x y`. -/
theorem printedExp_mem_su2 (x : ℝ) (y : ℂ) (η : ℝ) :
    NormedSpace.exp (η • (Carrier.imagUnit * TwoByTwo.herm2 x y))
      ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  AdalyFormal.Balaban.SuTwoLogExp.exp_antiHerm_traceless_mem_special
    (printedExponent_antiHerm x y η) (printedExponent_trace x y η)

/-- **THE CONFIGURATION `U(b) = e^{iηA(b)}`**, for an arbitrary field of printed potentials. -/
noncomputable def hermExpConfig (η : ℝ) (x : Bond L → ℝ) (y : Bond L → ℂ) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L :=
  fun b => ⟨NormedSpace.exp (η • (Carrier.imagUnit * TwoByTwo.herm2 (x b) (y b))),
    printedExp_mem_su2 (x b) (y b) η⟩

theorem hermExpConfig_apply (η : ℝ) (x : Bond L → ℝ) (y : Bond L → ℂ) (b : Bond L) :
    ((hermExpConfig η x y b : Matrix.specialUnitaryGroup (Fin 2) ℂ) : M2)
      = NormedSpace.exp (η • (Carrier.imagUnit * TwoByTwo.herm2 (x b) (y b))) := rfl

/-- **THE PRINTED CLASS CONTAINS THE WHOLE ADMISSIBLE FAMILY.**  The only hypothesis is (3.35)
itself, at the printed size `|A| = √(x² + |y|²)` (`TwoByTwo.printedNormSq`).  Contrast §7a, whose
inhabitant is the flat configuration and therefore says nothing about the class's size. -/
theorem hermExpConfig_printedGlobalRepI (η c M α₀ Lj : ℝ) (x : Bond L → ℝ) (y : Bond L → ℂ)
    (hsize : ∀ b : Bond L,
      Real.sqrt (TwoByTwo.printedNormSq (x b) (y b)) ≤ RenderStep.printedABound c M α₀ Lj η) :
    PrintedGlobalRepI c M α₀ η Lj (hermExpConfig η x y) := by
  intro b
  refine ⟨TwoByTwo.herm2 (x b) (y b), Real.sqrt (TwoByTwo.printedNormSq (x b) (y b)),
    Carrier.star_herm2 (x b) (y b), Real.sqrt_nonneg _, ?_, hsize b, hermExpConfig_apply η x y b⟩
  refine TwoByTwo.herm2_sq (x b) (y b) _ ?_
  refine Real.sq_sqrt ?_
  unfold TwoByTwo.printedNormSq
  have hn : (0 : ℝ) ≤ Complex.normSq (y b) := Complex.normSq_nonneg _
  nlinarith [sq_nonneg (x b), hn]

/-- **AND THE ADMISSIBLE FAMILY IS NOT THE FLAT ONE IN DISGUISE — the printed bound admits a
STRICTLY POSITIVE potential at every bond.**  At strictly positive printed data, `x ≡ ε` with
`ε = c·M·α₀/(2·Lj·η) > 0` satisfies (3.35) strictly, so the family of §9 is parametrised by a
nonempty open set of potential fields rather than by `A = 0` alone.

**Stated as what it is:** this is a fact about the POTENTIAL, not about the link.  Whether
`e^{iηA} ≠ 1` at such an `A` is not proved here; it would need a LOWER bound on `‖e^{iηA} − 1‖`,
i.e. the converse of `RenderStep.rendering_step_group_from_source`, which this lane does not
build. -/
theorem printed_family_admits_positive_potential (c M α₀ Lj η : ℝ) (hc : 0 < c) (hM : 0 < M)
    (hα : 0 < α₀) (hLj : 0 < Lj) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧
      Real.sqrt (TwoByTwo.printedNormSq ε 0) < RenderStep.printedABound c M α₀ Lj η := by
  refine ⟨RenderStep.printedABound c M α₀ Lj η / 2, by unfold RenderStep.printedABound; positivity, ?_⟩
  have hb : 0 < RenderStep.printedABound c M α₀ Lj η := by
    unfold RenderStep.printedABound; positivity
  have hval : TwoByTwo.printedNormSq (RenderStep.printedABound c M α₀ Lj η / 2) 0
      = (RenderStep.printedABound c M α₀ Lj η / 2) ^ 2 := by
    unfold TwoByTwo.printedNormSq; simp
  rw [hval, Real.sqrt_sq (by linarith)]
  linarith



/-! ## §10 — THE OBSTRUCTION OF §6c, AS A THEOREM RATHER THAN AN INFERENCE

§6c computes two numbers (`‖(−1) − 1‖_F = 2√2` and `1/(186ℓ³) < 2√2`) and then DEDUCES in prose
that no per-cube-gauge hypothesis can bound `frobSupBond`.  §10 replaces the deduction by a
theorem: it exhibits a configuration that satisfies the per-cube hypotheses **at `δ = 0`** — the
strongest per-cube smallness there is — and FAILS the covariance class at every `ℓ`.

The configuration is `compute/gauge_patching/stage/PerCubeSeparation.lean`'s `U₀` (REUSED, LAW-19):
`−1` on one layer of direction-`0` links of the `4³` torus, `1` elsewhere.  `U0_locGaugeDev_zero`
proves every stencil is EXACTLY flattened by some gauge; `U0_no_global_flat` proves no single gauge
flattens it. -/

/-- The per-bond stencils form a cube family that is `StencilCovered` by construction, and
`LocGaugeDev` is exactly `CubeGaugeData` on it.  So the per-cube hypothesis pair of
`terminal_posDef_from_printed_cubes` is met by any `LocGaugeDev` configuration. -/
theorem cubeGaugeData_stencils {δ : ℝ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (h : GaugePatching.LocGaugeDev δ U) :
    StencilCovered {C : Set (Bond L) | ∃ b : Bond L, C = GaugePatching.Jstencil b} ∧
      CubeGaugeData δ U {C : Set (Bond L) | ∃ b : Bond L, C = GaugePatching.Jstencil b} := by
  constructor
  · intro b
    exact ⟨GaugePatching.Jstencil b, ⟨b, rfl⟩, le_refl _⟩
  · rintro C ⟨b, rfl⟩
    exact h b

/-- `frobSupBond U₀ ≥ 2√2` — the sup is at least the value at the defect link, which is `−1`. -/
theorem frobSupBond_U0_ge : 2 * Real.sqrt 2 ≤ frobSupBond GaugePatching.Sep.U0 := by
  have hle := Finset.le_sup' (f := fun b : Bond GaugePatching.Sep.L4 =>
      RMapLipschitz.frobNorm ((GaugePatching.Sep.U0 b : M2) - 1))
    (Finset.mem_univ ((GaugePatching.Sep.site 3, (0 : Fin 3)) : Bond GaugePatching.Sep.L4))
  simp only [GaugePatching.Sep.U0_axis_three] at hle
  have hz : ((GaugePatching.Sep.zEl : Matrix.specialUnitaryGroup (Fin 2) ℂ) : M2) = -1 := rfl
  rw [hz, ThresholdVsPrinted.frobNorm_negOne_sub_one] at hle
  exact hle

/-- **THE OBSTRUCTION, PROVED.**  There is a cube family and a configuration meeting BOTH per-cube
hypotheses of `terminal_posDef_from_printed_cubes` at `δ = 0`, whose `frobSupBond` exceeds the
covariance-class threshold at EVERY `ℓ ≥ 1`.  Hence the per-cube data — however small `α₀` is made,
since `δ = 0` is already attained — does not imply `frobSupBond U ≤ 1/(186ℓ³)`, and `hthr` is
carried in §5a of `DeltaAlpha0.lean` for a reason that is now a theorem and not a remark. -/
theorem percube_hypotheses_cannot_bound_frobSupBond {ell : ℕ} (hell : 0 < ell) :
    ∃ 𝒞 : Set (Set (Bond GaugePatching.Sep.L4)),
      StencilCovered 𝒞 ∧ CubeGaugeData 0 GaugePatching.Sep.U0 𝒞 ∧
        ¬ (frobSupBond GaugePatching.Sep.U0 ≤ 1 / (186 * (ell : ℝ) ^ 3)) := by
  obtain ⟨hcov, hdata⟩ := cubeGaugeData_stencils GaugePatching.Sep.U0
    GaugePatching.Sep.U0_locGaugeDev_zero
  refine ⟨_, hcov, hdata, ?_⟩
  intro hcon
  have h1 := (frobSupBond_gauge_gap hell).2
  have h2 := frobSupBond_U0_ge
  linarith

/-! ## §11 — THE §9 WITNESS'S LINKS ARE NOT THE IDENTITY

§9 exhibits the admissible family; §11 proves its links are genuinely non-flat, closing the residual
§9's docstring named.  The tool is `ClassPropagationUbar.exp_closed` (REUSED, LAW-19):
`exp H = cos r · 1 + (sin r / r) · H` with `r = √(frobSq H / 2)`.  **That it applies here is a fact
worth recording**: `exp_closed` is stated under `attribute [local instance]
Matrix.linftyOpNormedRing`, this lane works under `Matrix.Norms.L2Operator`, and the two
elaborations agree. -/

/-- The exponent's Frobenius square, at `y = 0`: `frobSq (iη·herm2 x 0) = 2(ηx)²`, so `r = |ηx|`. -/
theorem frobSq_printedExponent (x η : ℝ) :
    RMapLipschitz.frobSq (η • (Carrier.imagUnit * TwoByTwo.herm2 x 0)) = 2 * (η * x) ^ 2 := by
  unfold RMapLipschitz.frobSq
  simp [Carrier.imagUnit, TwoByTwo.herm2, Complex.normSq_apply]
  ring

/-- The exponent's `(0,0)` entry is `i·(ηx)`. -/
theorem entry_printedExponent (x η : ℝ) :
    (η • (Carrier.imagUnit * TwoByTwo.herm2 x 0)) 0 0 = Complex.I * ((η * x : ℝ) : ℂ) := by
  simp [Carrier.imagUnit, TwoByTwo.herm2]
  ring

/-- **`e^{iηA} ≠ 1`** for `A = herm2 x 0` whenever `0 < ηx < 2π`.  Proved from the closed form by
reading the `(0,0)` entry: it is `cos r + i sin r`, and `cos r = 1` forces `r = 0`. -/
theorem printedExp_ne_one (x η : ℝ) (hpos : 0 < η * x) (hlt : η * x < 2 * Real.pi) :
    NormedSpace.exp (η • (Carrier.imagUnit * TwoByTwo.herm2 x 0)) ≠ (1 : M2) := by
  set H : M2 := η • (Carrier.imagUnit * TwoByTwo.herm2 x 0) with hH
  set r : ℝ := η * x with hr
  have hah : Matrix.conjTranspose H = -H := printedExponent_antiHerm x 0 η
  have htr : Matrix.trace H = 0 := printedExponent_trace x 0 η
  have hr2 : r ^ 2 = RMapLipschitz.frobSq H / 2 := by
    rw [hH, frobSq_printedExponent, hr]; ring
  have hclosed := AdalyFormal.Balaban.ClassPropagationUbar.exp_closed hah htr hpos hr2
  intro hone
  rw [hone] at hclosed
  have hHval : H 0 0 = Complex.I * ((r : ℝ) : ℂ) := by rw [hH, hr]; exact entry_printedExponent x η
  have hrne : r ≠ 0 := ne_of_gt hpos
  have hrC : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hrne
  have h0 := congrArg (fun MM : M2 => MM 0 0) hclosed
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, hHval,
    Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv, mul_one] at h0
  have hkey : (1 : ℂ) = ((Real.cos r : ℝ) : ℂ) + ((Real.sin r : ℝ) : ℂ) * Complex.I := by
    rw [h0]; field_simp
  have hre : Real.cos r = 1 := by
    have h2 : ((Real.cos r : ℝ) : ℂ).re + (((Real.sin r : ℝ) : ℂ) * Complex.I).re = (1 : ℂ).re := by
      rw [← Complex.add_re, ← hkey]
    simpa [-Complex.ofReal_cos, -Complex.ofReal_sin] using h2
  exact hrne ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hlt).mp hre)

/-- **THE §9 FAMILY CONTAINS A NON-FLAT ADMISSIBLE CONFIGURATION, AT EVERY POSITIVE PRINTED DATA.**
Choose `x = min (O(1)Mα₀/(L^jη)) (π/η)`: it satisfies (3.35) and `0 < ηx ≤ π < 2π`, so the link is
in the printed class AND is not the identity.  This is the statement §9's docstring said was not
proved; it is proved here. -/
theorem printed_class_has_nonflat_link (c M α₀ Lj η : ℝ) (hc : 0 < c) (hM : 0 < M) (hα : 0 < α₀)
    (hLj : 0 < Lj) (hη : 0 < η) :
    ∃ x : ℝ, 0 < x ∧
      Real.sqrt (TwoByTwo.printedNormSq x 0) ≤ RenderStep.printedABound c M α₀ Lj η ∧
      NormedSpace.exp (η • (Carrier.imagUnit * TwoByTwo.herm2 x 0)) ≠ (1 : M2) := by
  have hb : 0 < RenderStep.printedABound c M α₀ Lj η := by
    unfold RenderStep.printedABound; positivity
  have hpi : 0 < Real.pi / η := by positivity
  refine ⟨min (RenderStep.printedABound c M α₀ Lj η) (Real.pi / η), lt_min hb hpi, ?_, ?_⟩
  · have hxpos : 0 < min (RenderStep.printedABound c M α₀ Lj η) (Real.pi / η) := lt_min hb hpi
    have hval : TwoByTwo.printedNormSq (min (RenderStep.printedABound c M α₀ Lj η) (Real.pi / η)) 0
        = (min (RenderStep.printedABound c M α₀ Lj η) (Real.pi / η)) ^ 2 := by
      unfold TwoByTwo.printedNormSq; simp
    rw [hval, Real.sqrt_sq (le_of_lt hxpos)]
    exact min_le_left _ _
  · refine printedExp_ne_one _ η ?_ ?_
    · have hxpos : 0 < min (RenderStep.printedABound c M α₀ Lj η) (Real.pi / η) := lt_min hb hpi
      positivity
    · have hle : min (RenderStep.printedABound c M α₀ Lj η) (Real.pi / η) ≤ Real.pi / η :=
        min_le_right _ _
      have : η * min (RenderStep.printedABound c M α₀ Lj η) (Real.pi / η) ≤ η * (Real.pi / η) :=
        mul_le_mul_of_nonneg_left hle (le_of_lt hη)
      have heq : η * (Real.pi / η) = Real.pi := by field_simp
      rw [heq] at this
      linarith [Real.pi_pos]


#print axioms cubeGaugeData_stencils
#print axioms frobSupBond_U0_ge
#print axioms percube_hypotheses_cannot_bound_frobSupBond
#print axioms frobSq_printedExponent
#print axioms entry_printedExponent
#print axioms printedExp_ne_one
#print axioms printed_class_has_nonflat_link
#print axioms printedExponent_antiHerm
#print axioms printedExponent_trace
#print axioms printedExp_mem_su2
#print axioms hermExpConfig
#print axioms hermExpConfig_apply
#print axioms hermExpConfig_printedGlobalRepI
#print axioms printed_family_admits_positive_potential
#print axioms PrintedGaugeCube
#print axioms PrintedCubeClass
#print axioms sourceThreshold
#print axioms covThreshold
#print axioms alphaThreshold
#print axioms PrintedGlobalRep
#print axioms PrintedCubeClassI
#print axioms PrintedGlobalRepI
#print axioms norm_JsuTwo_le_of_printedCubesI
#print axioms linkDev_of_printedGlobalI
#print axioms frobSupBond_le_of_printedGlobalI
#print axioms printedCubeClassI_of_printedGlobalI
#print axioms printedCubeClassI_inhabited
#print axioms EB_of_opNorm_le
#print axioms EB_opNorm_constant_sharp
#print axioms printedNormSq_agree
#print axioms EB_sqrtTwo_of_opNorm_le
#print axioms direct_route_strictly_sharper
#print axioms EB_link_of_printed
#print axioms EB_link_of_printed_via_bridge
#print axioms cubeGaugeData_of_printedCubeClass
#print axioms norm_JsuTwo_le_of_printedCubes
#print axioms alphaThreshold_le_source
#print axioms alphaThreshold_le_cov
#print axioms sqrt_two_le_three_halves
#print axioms covThreshold_constant_derivation
#print axioms covariance_class_of_alpha0_exact
#print axioms covariance_class_of_alpha0
#print axioms linkDev_of_printedGlobal
#print axioms frobSupBond_le_of_printedGlobal
#print axioms printedCubeClass_of_printedGlobal
#print axioms frobSupBond_gauge_gap
#print axioms printedCubeClass_inhabited
#print axioms EB_not_forced
#print axioms printedABound_pos
#print axioms alphaThreshold_pos
#print axioms normalization_pinned

end AdalyFormal.Balaban.DeltaAlpha0
