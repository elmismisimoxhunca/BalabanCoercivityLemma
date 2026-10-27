/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import RecompFloor
import TerminalBinder

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.longLine false

/-!
# `RecompTerminal.lean` — THE TERMINAL CHAIN ON THE SUMMATION FLOOR

`RecompFloor` replaced the chain's Poincaré input.  This module runs the rest of the chain on it,
and recomputes every constant the swap moves.

## WHAT CHANGES, AND WHAT DOES NOT

Unchanged, reused verbatim (LAW-19): `floor_of_hraw_sharp` (the absorption), `hKcurl_at`
(CMP99b (3.128) at one vector), `canonical_isAQuadSplit`, `deltaKQuadForm_eq`,
`cdcFormTrue_posDef_at_cZero` (the source-term accounting), `deltaKQuadForm_eq_inner_deltaKQuadOp`.
Every one of them is generic in the Poincaré constant `γP`, which is exactly why the swap is
possible at all.

Changed: `γP = gammaBrick ℓ` becomes `γP = gammaSum ℓ = gammaBrick ℓ/4`, and the covariance-side
hypothesis `hthr : frobSupBond U ≤ 1/(186ℓ³)` — a GLOBAL statement about the original links —
becomes the per-cube gauged class of `RecompFloor.sum_brick_at_cZero`.  **No `frobSupBond` appears
in any statement of this module, and no gauge-orbit hypothesis.**

## THE CONSTANTS, RE-DERIVED

| slot | old | new | factor | why |
|---|---|---|---|---|
| floor | `gammaBrick ℓ ≥ 1/(345960ℓ⁶)` | `gammaSum ℓ ≥ 1/(1383840ℓ⁶)` | `4` | plaquette multiplicity `Mp = 4` |
| radius | `1/(186ℓ³)` | `1/(744ℓ³)` | `4` | `√16`, `16` = doubly-enlarged bond multiplicity |
| Schur, half drift | `1/(1383840ℓ⁶σ₀²)` | `1/(5535360ℓ⁶σ₀²)` | `4` | the floor's `4` |
| link deviation `δ` | `1/(1370001600·ℓ⁶σ₀²‖H₁‖c₂N)` | `1/(5480006400·…)` | `4` | the floor's `4` |

`5535360 = 4·1383840` and `5480006400 = 990·5535360 = 4·1370001600`; `990 = 2·495` with `495` the
source lane's per-bond constant and `2` the printed `−2⟨H₁D̃⁽²⁾,J⟩`.

**The binders are `TerminalBinder`'s minimiser-range ones**, not the universal forms: `hform` and
`hraw` are consumed at the single point `H₁(C₀B̃)` and nowhere else, and this module keeps them
there.

**ISLAND.**  Nothing is installed in `formal/`; nothing enters `Spine.lean`'s import cone;
this module contributes nothing to `FULL3D.main`'s axiom set.  `RecompClass.lean`'s header
carries the measured island/merge status of the WHOLE chain composed here.

**Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.**
-/

namespace AdalyFormal.Balaban.RecomposeSum

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator
  interpolates)
open AdalyFormal.Balaban.Gamma1Positive (deltaKQuadForm deltaKQuadForm_eq)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (IsSourceOperator cdcFormTrue)
open AdalyFormal.Balaban.TerminalAssembly (IsPrintedG1Form canonicalKop canonical_isAQuadSplit
  sharpFloorConst floor_of_hraw_sharp cdcFormTrue_posDef_at_cZero
  deltaKQuadForm_eq_inner_deltaKQuadOp)
open AdalyFormal.TerminalBinder (PrintedG1FormAt HrawAt OnMinimizerRange hKcurl_at)
open AdalyFormal.Balaban.LocalizedEstimates (tilde bondsOn CSite)

variable {Hs : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE SCHUR FLOOR ON THE SUMMATION BRICK -/

/-- **THE SCHUR FLOOR AT THE SINGLE CONSUMED POINT, ON THE SUMMATION FLOOR.**

Statement and proof are `TerminalBinder.schur_floor_at_point`'s, with two substitutions and nothing
else: `hthr` is replaced by the per-cube gauged class, and `gammaBrick ℓ` by `gammaSum ℓ`. -/
theorem schur_floor_sum_at_point {ell : ℕ} {ι : Type*} [DecidableEq ι] (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (α : ℝ) (hα0 : 0 ≤ α) (hα : α ≤ sumRadius ell)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell)) (γ : ι → GaugeFn L)
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite L ell, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (tilde hdvd (tilde hdvd (Y i))),
      RMapLipschitz.frobNorm
        (((periodicGaugeTransform (γ i) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (a : ℝ) (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ) (hκγ : κ ≤ Real.sqrt (gammaSum ell))
    (w : TildeFn L ell)
    (hformAt : PrintedG1FormAt D a d pen (solutionOperator D (cZero U ell (dinvC U ell) w)))
    (hrawAt : HrawAt D U d σ₀ κ (solutionOperator D (cZero U ell (dinvC U ell) w))) :
    sharpFloorConst (gammaSum ell) κ σ₀ * ‖cZero U ell (dinvC U ell) w‖ ^ 2
      ≤ deltaKQuadForm D a (cZero U ell (dinvC U ell) w) := by
  set B : BondFnL2 L := cZero U ell (dinvC U ell) w with hB
  set A : Hs := solutionOperator D B with hA
  have hQA : D.Q A = B := interpolates D B
  have hfl := floor_of_hraw_sharp D.Q d (curlCovariantCLM_L2 U) (canonicalKop D a) σ₀ κ
    (gammaSum ell) hσ₀ hκ hκγ A hrawAt
    (by rw [hQA]; exact hpoin_sum_at_cZero hell2 hstrict hdvd U α hα0 hα 𝒞 Y γ hdisj hcov hclass w)
    (hKcurl_at hformAt)
  rw [hQA] at hfl
  rw [deltaKQuadForm_eq D a (canonicalKop D a) (canonical_isAQuadSplit D a) B]
  exact hfl

/-- **THE SCHUR FLOOR ON THE MINIMISER RANGE, ON THE SUMMATION FLOOR.** -/
theorem schur_floor_sum_on_range {ell : ℕ} {ι : Type*} [DecidableEq ι] (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (α : ℝ) (hα0 : 0 ≤ α) (hα : α ≤ sumRadius ell)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell)) (γ : ι → GaugeFn L)
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite L ell, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (tilde hdvd (tilde hdvd (Y i))),
      RMapLipschitz.frobNorm
        (((periodicGaugeTransform (γ i) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (a : ℝ) (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ) (hκγ : κ ≤ Real.sqrt (gammaSum ell))
    (hformR : OnMinimizerRange D (PrintedG1FormAt D a d pen))
    (hrawR : OnMinimizerRange D (HrawAt D U d σ₀ κ))
    (w : TildeFn L ell) :
    sharpFloorConst (gammaSum ell) κ σ₀ * ‖cZero U ell (dinvC U ell) w‖ ^ 2
      ≤ deltaKQuadForm D a (cZero U ell (dinvC U ell) w) :=
  schur_floor_sum_at_point hell2 hstrict hdvd U α hα0 hα 𝒞 Y γ hdisj hcov hclass D a d pen σ₀ κ
    hσ₀ hκ hκγ w (hformR _) (hrawR _)

/-! ## §2 — THE COMPOSED THEOREM: THE PRINTED FORM IS POSITIVE ON THE PRINTED SUBSPACE -/

/-- **THE RECOMPOSED TERMINAL THEOREM.**

For every `ℓ ≥ 2` on a tiled torus, every background `U` admitting a pairwise-disjoint covering
family of cubes with ONE UNRELATED GAUGE PER CUBE putting the locally gauged holonomy deviations
below `1/(744ℓ³)` on the doubly-enlarged bond sets, every datum `D` whose `G₁⁻¹` satisfies CMP99b
(3.128) on the minimiser range and whose drift-priced chain bound holds there, and every source
below the threshold: the printed `C*Δ_kC` is positive definite on `ℓ²(Λ̃)`.

**Hypothesis inventory, tagged.**
* `hell2`, `hstrict`, `hdvd` — [OURS] the tiling conditions the corrected `ℓ⁻⁵` Lemma 2.4 needs.
* `hα`, `hclass`, `hdisj`, `hcov` — the covariance input.  `hclass` is [SOURCE] once discharged from
  CMP99b (3.35) (`RecompClass`); `hdisj`/`hcov` are [OURS] and are inhabited by the single-block
  family (`RecompFloor.sum_brick_family_inhabited`).
* `hformR` — [SOURCE] CMP99b (3.128), `J`-free part, on the minimiser range.
* `hrawR` — [OURS] the drift-priced chain bound on the minimiser range.
* `hS`, `hD2` — [SOURCE] p.427's quadratic `D̃⁽²⁾` and the source term as an operator.
* `hRthr` — the source below the recomposed threshold; §3 puts it in closed form.

**No `frobSupBond` hypothesis, no gauge-orbit hypothesis, no global gauge.** -/
theorem terminal_sum_posDef_on_range {ell : ℕ} {ι : Type*} [DecidableEq ι] (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (α : ℝ) (hα0 : 0 ≤ α) (hα : α ≤ sumRadius ell)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell)) (γ : ι → GaugeFn L)
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite L ell, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (tilde hdvd (tilde hdvd (Y i))),
      RMapLipschitz.frobNorm
        (((periodicGaugeTransform (γ i) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (bc : BaseConstant)
    (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ) (hκγ : κ ≤ Real.sqrt (gammaSum ell))
    (hformR : OnMinimizerRange D (PrintedG1FormAt D (usedAt bc 0) d pen))
    (hrawR : OnMinimizerRange D (HrawAt D U d σ₀ κ))
    (Qext : BondFnL2 L → BondFnL2 L) (J : Hs) (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hS : IsSourceOperator D Qext J S) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (R : ℝ) (hJbound : ‖J‖ ≤ R)
    (hRthr : 2 * ‖solutionOperator D‖ * c₂ * R < sharpFloorConst (gammaSum ell) κ σ₀)
    (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < cdcFormTrue D bc Qext J U ell (dinvC U ell) w := by
  have hcoef : (0 : ℝ) ≤ 2 * ‖solutionOperator D‖ * c₂ := by positivity
  have hsmall : 2 * ‖solutionOperator D‖ * c₂ * ‖J‖
      < sharpFloorConst (gammaSum ell) κ σ₀ := by
    have := mul_le_mul_of_nonneg_left hJbound hcoef
    linarith
  have hfl := schur_floor_sum_on_range hell2 hstrict hdvd U α hα0 hα 𝒞 Y γ hdisj hcov hclass
    D (usedAt bc 0) d pen σ₀ κ hσ₀ hκ hκγ hformR hrawR w
  rw [deltaKQuadForm_eq_inner_deltaKQuadOp D bc] at hfl
  exact cdcFormTrue_posDef_at_cZero D bc Qext J S hS _ c₂ hc₂ hD2 U (dinvC U ell) w hw hfl hsmall

/-! ## §3 — THE THRESHOLD, IN EXACT RATIONALS

Three rows: a `γ`-generic half-drift absorption (which the upstream lane states only at
`gammaBrick`), its instance at `gammaSum`, and the link-deviation threshold in closed form. -/

/-- **THE HALF-DRIFT ABSORPTION, GENERIC IN THE POINCARÉ CONSTANT.**  `κ ≤ ½√γ` gives
`sharpFloorConst γ κ σ₀ ≥ γ/(4σ₀²)`.  `TerminalAssembly.sharpFloorConst_lower_halfDrift` proves the
same statement only at `γ = gammaBrick ℓ`; this is that proof with the constant abstracted, which
is what lets the summation floor reuse it. -/
theorem sharpFloorConst_lower_halfDrift_gen (γ κ σ₀ : ℝ) (hγ : 0 < γ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ)
    (hhalf : κ ≤ Real.sqrt γ / 2) :
    γ / (4 * σ₀ ^ 2) ≤ sharpFloorConst γ κ σ₀ := by
  have hs : Real.sqrt γ ^ 2 = γ := Real.sq_sqrt (le_of_lt hγ)
  have hs0 : 0 ≤ Real.sqrt γ := Real.sqrt_nonneg _
  have hgap : Real.sqrt γ / 2 ≤ Real.sqrt γ - κ := by linarith
  have hgap0 : (0 : ℝ) ≤ Real.sqrt γ / 2 := by linarith
  have hquart : γ / 4 ≤ (Real.sqrt γ - κ) ^ 2 := by nlinarith [hgap, hgap0, hs]
  have hd : (0 : ℝ) < σ₀ ^ 2 := by positivity
  unfold sharpFloorConst
  rw [div_pow, div_le_div_iff₀ (by positivity) hd]
  nlinarith [hquart, hd]

/-- **THE SCHUR CONSTANT UNDER THE HALF-DRIFT HYPOTHESIS, ON THE SUMMATION FLOOR.**
`5535360 = 4·1383840 = 16·345960`: one `4` from the plaquette multiplicity, one from the drift
absorption. -/
theorem sharpFloorConstSum_lower_halfDrift {ell : ℕ} (hell : 0 < ell) (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀)
    (hκ : 0 ≤ κ) (hhalf : κ ≤ Real.sqrt (gammaSum ell) / 2) :
    1 / (5535360 * (ell : ℝ) ^ 6 * σ₀ ^ 2) ≤ sharpFloorConst (gammaSum ell) κ σ₀ := by
  have hγ : 0 < gammaSum ell := gammaSum_pos hell
  have hlow := gammaSum_lower hell
  have h0 : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hd : (0 : ℝ) < σ₀ ^ 2 := by positivity
  have he : (0 : ℝ) < 1383840 * (ell : ℝ) ^ 6 := by positivity
  have hgen := sharpFloorConst_lower_halfDrift_gen (gammaSum ell) κ σ₀ hγ hσ₀ hκ hhalf
  have hstep : 1 / (5535360 * (ell : ℝ) ^ 6 * σ₀ ^ 2) ≤ gammaSum ell / (4 * σ₀ ^ 2) := by
    have hrw : 1 / (5535360 * (ell : ℝ) ^ 6 * σ₀ ^ 2)
        = (1 / (1383840 * (ell : ℝ) ^ 6)) / (4 * σ₀ ^ 2) := by
      have hne : ((ell : ℝ)) ≠ 0 := ne_of_gt h0
      have hσne : σ₀ ≠ 0 := ne_of_gt hσ₀
      field_simp
      ring
    rw [hrw]
    have h4 : (0 : ℝ) < 4 * σ₀ ^ 2 := by positivity
    exact div_le_div_of_nonneg_right hlow (le_of_lt h4)
  linarith [hgen, hstep]

/-- **THE LINK-DEVIATION THRESHOLD, SOLVED IN CLOSED FORM.**

    δ  <  1 / (5480006400 · ℓ⁶ · σ₀² · ‖H₁‖ · c₂ · N)   ⟹   2‖H₁‖c₂·(N·495·δ)  <  1/(5535360·ℓ⁶σ₀²)

Every factor is counted: `495` and `N = ‖T‖√(2|Bond L|)` are `SourceWiredJ`'s (GRADE 3), `2` is the
printed `−2⟨H₁D̃⁽²⁾,J⟩`, `5535360 = 4·1383840` is §3's, and `5480006400 = 990·5535360`.  It is
exactly `4×` `TerminalAssembly.delta_threshold_suffices`'s `1370001600`, the factor being the
plaquette multiplicity and nothing else.

**`hδ0` IS RETAINED DELIBERATELY AND IS NOT USED BY THE PROOF**, for the reason
`TerminalAssembly.delta_threshold_suffices` retains its own: at `δ < 0` the left-hand side is
negative and the statement holds by a sign accident rather than in the intended regime. -/
theorem delta_threshold_sum_suffices {ell : ℕ} (hell : 0 < ell) (σ₀ H1 c₂ N δ : ℝ)
    (hσ₀ : 0 < σ₀) (hH1 : 0 < H1) (hc₂ : 0 < c₂) (hN : 0 < N) (hδ0 : 0 ≤ δ)
    (hδ : δ < 1 / (5480006400 * (ell : ℝ) ^ 6 * σ₀ ^ 2 * H1 * c₂ * N)) :
    2 * H1 * c₂ * (N * (495 * δ)) < 1 / (5535360 * (ell : ℝ) ^ 6 * σ₀ ^ 2) := by
  have h0 : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have he : (0 : ℝ) < (ell : ℝ) ^ 6 := by positivity
  have hden : (0 : ℝ) < 5480006400 * (ell : ℝ) ^ 6 * σ₀ ^ 2 * H1 * c₂ * N := by positivity
  have hden2 : (0 : ℝ) < 5535360 * (ell : ℝ) ^ 6 * σ₀ ^ 2 := by positivity
  rw [lt_div_iff₀ hden] at hδ
  rw [lt_div_iff₀ hden2]
  nlinarith [hδ, he, hσ₀, hH1, hc₂, hN, mul_pos hH1 hc₂, sq_nonneg σ₀]

/-! ## §4 — THE HEADLINE WITH THE THRESHOLD IN CLOSED FORM -/

/-- **THE RECOMPOSED HEADLINE.**  §2 with the two constants of §3 substituted, so the source
hypothesis is a single closed-form inequality on the link deviation `δ` and the covariance
hypothesis is the per-cube gauged class.  Nothing else changes. -/
theorem terminal_sum_posDef_closedForm {ell : ℕ} {ι : Type*} [DecidableEq ι] (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (α : ℝ) (hα0 : 0 ≤ α) (hα : α ≤ sumRadius ell)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell)) (γ : ι → GaugeFn L)
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite L ell, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (tilde hdvd (tilde hdvd (Y i))),
      RMapLipschitz.frobNorm
        (((periodicGaugeTransform (γ i) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (bc : BaseConstant)
    (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ) (hhalf : κ ≤ Real.sqrt (gammaSum ell) / 2)
    (hformR : OnMinimizerRange D (PrintedG1FormAt D (usedAt bc 0) d pen))
    (hrawR : OnMinimizerRange D (HrawAt D U d σ₀ κ))
    (Qext : BondFnL2 L → BondFnL2 L) (J : Hs) (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hS : IsSourceOperator D Qext J S) (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (N δ : ℝ) (hN : 0 < N) (hδ0 : 0 ≤ δ) (hH1 : 0 < ‖solutionOperator D‖)
    (hJbound : ‖J‖ ≤ N * (495 * δ))
    (hδ : δ < 1 / (5480006400 * (ell : ℝ) ^ 6 * σ₀ ^ 2 * ‖solutionOperator D‖ * c₂ * N))
    (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < cdcFormTrue D bc Qext J U ell (dinvC U ell) w := by
  have hell : 0 < ell := by omega
  have hs0 : (0 : ℝ) ≤ Real.sqrt (gammaSum ell) := Real.sqrt_nonneg _
  have hκγ : κ ≤ Real.sqrt (gammaSum ell) := by linarith
  have harith := delta_threshold_sum_suffices hell σ₀ ‖solutionOperator D‖ c₂ N δ hσ₀ hH1 hc₂ hN
    hδ0 hδ
  have hlow := sharpFloorConstSum_lower_halfDrift hell σ₀ κ hσ₀ hκ hhalf
  refine terminal_sum_posDef_on_range hell2 hstrict hdvd U α hα0 hα 𝒞 Y γ hdisj hcov hclass
    D bc d pen σ₀ κ hσ₀ hκ hκγ hformR hrawR Qext J S hS c₂ (le_of_lt hc₂) hD2
    (N * (495 * δ)) hJbound ?_ w hw
  have hre : 2 * ‖solutionOperator D‖ * c₂ * (N * (495 * δ))
      = 2 * ‖solutionOperator D‖ * c₂ * (N * (495 * δ)) := rfl
  linarith [harith, hlow]

#print axioms schur_floor_sum_at_point
#print axioms schur_floor_sum_on_range
#print axioms terminal_sum_posDef_on_range
#print axioms sharpFloorConst_lower_halfDrift_gen
#print axioms sharpFloorConstSum_lower_halfDrift
#print axioms delta_threshold_sum_suffices
#print axioms terminal_sum_posDef_closedForm

end AdalyFormal.Balaban.RecomposeSum
