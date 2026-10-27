/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import LocFeed
import TerminalAssembly

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.style.longLine false

/-!
# `RecompFloor.lean` — THE TERMINAL CHAIN'S POINCARÉ INPUT, REBUILT ON THE SUMMATION FLOOR

The terminal chain takes its Poincaré constant from `TerminalCompose.gammaBrick`, which is
`covariant_lemma24`'s coefficient evaluated at the GLOBAL smallness class
`frobSupBond U ≤ 1/(186·ℓ³)` — a bound on the deviations of the ORIGINAL links, uniformly over the
whole torus.  `compute/localized_estimates/stage/LocFeed.lean`'s
`global_floor_from_percube_gauges` proves the same kind of floor from PER-CUBE gauged smallness
with **one unrelated gauge per cube and no global gauge**, at the price of two counted
multiplicities: the doubly-enlarged bond multiplicity `16` on the drift term and the enlarged
plaquette multiplicity `4` on the curl term.

This module swaps the input and re-derives every downstream constant.  §1 is the whole arithmetic
of the swap; §2 puts the new floor at `C₀B̃`; §3 delivers it in the exact shape
`floor_of_hraw_sharp` consumes.

## THE SWAP, IN ONE LINE

>  `gammaSum ℓ = gammaBrick ℓ / 4`, at the smallness radius `1/(744·ℓ³) = (1/4)·(1/(186·ℓ³))`.

Both `4`s are DERIVED, and they are different `4`s:

* the radius shrinks by `4` because the drift constant is multiplied by the doubly-enlarged
  multiplicity `16` and the radius enters SQUARED — `√16 = 4`.  `1536 = 96·16` and
  `744 = 4·186`, and `1536/744² = 96/186²` EXACTLY (`sum_coefficient_eq_gammaBrick`), so the
  bracket is *the same number* `gammaBrick ℓ`, not merely a bound on it;
* the floor shrinks by `4` because the curl side carries the enlarged plaquette multiplicity
  `Mp = 4`, and the chain divides by it.

Consequently **every downstream constant is the old one times four**, in the direction that costs:
`1/(345960·ℓ⁶) → 1/(1383840·ℓ⁶)` for the floor, `1/(1383840·ℓ⁶σ₀²) → 1/(5535360·ℓ⁶σ₀²)` for the
half-drift Schur constant, and `1/(1370001600·…) → 1/(5480006400·…)` for the link deviation
(`RecompTerminal`).  No constant is fitted; each is `4×` a named upstream one.

**ISLAND.**  Nothing is installed in `formal/`; nothing enters `Spine.lean`'s import cone;
this module contributes nothing to `FULL3D.main`'s axiom set.  `RecompClass.lean`'s header
carries the measured island/merge status of the WHOLE chain composed here.

**Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.**
-/

namespace AdalyFormal.Balaban.RecomposeSum

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CStarDeltaKCOperator (dstarDCLM)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.TerminalCompose (gammaBrick gammaBrick_pos gammaBrick_lower
  gammaBrick_le_coefficient cZeroFn cZeroFn_admissible coarseQEnergyCov_cZero_eq_zero
  bondEnergy_eq_normSq curlEnergyCov_eq_inner_dstarDCLM)
open AdalyFormal.Balaban.TerminalAssembly (normSq_curlCLM_eq_dstarDCLM_form)
open AdalyFormal.Balaban.LocalizedEstimates (tilde bondsOn CSite global_floor_from_percube_gauges
  singleton_family_ok)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE CONSTANTS OF THE SWAP, IN EXACT RATIONALS -/

/-- **THE SUMMATION ROUTE'S SMALLNESS RADIUS**, `1/(744·ℓ³)`.  `744 = 4·186`, and the `4` is
`√16` with `16` the doubly-enlarged bond multiplicity `LocSum.tilde2_mult_le_sixteen`. -/
noncomputable def sumRadius (ell : ℕ) : ℝ := 1 / (744 * (ell : ℝ) ^ 3)

/-- **THE SUMMATION ROUTE'S FLOOR CONSTANT**, `gammaBrick ℓ / 4`.  The `4` is the enlarged
plaquette multiplicity `LocFeed.plaqsOn_tilde_mult_le_four`, and nothing else. -/
noncomputable def gammaSum (ell : ℕ) : ℝ := gammaBrick ell / 4

/-- **THE EXACT IDENTITY THE WHOLE SWAP RESTS ON.**  At the radius `1/(744ℓ³)` the summation
floor's bracket is EQUAL to `gammaBrick ℓ` — not bounded by it, equal to it.  `1536 = 96·16` is
`LocFeed`'s own composed drift constant and `744² = 16·186²`, so the two `16`s cancel exactly.

This is what makes the swap cost a factor `4` and not an unknown amount. -/
theorem sum_coefficient_eq_gammaBrick {ell : ℕ} (hell : 0 < ell) :
    (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * (1 / (744 * (ell : ℝ) ^ 3)) ^ 2 * ((16 : ℕ) : ℝ)
      = gammaBrick ell := by
  have h0 : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hne : ((ell : ℝ)) ≠ 0 := ne_of_gt h0
  unfold gammaBrick
  push_cast
  field_simp
  ring

/-- **THE COEFFICIENT AT ANY ADMISSIBLE `α`.**  For `0 ≤ α ≤ 1/(744ℓ³)`, the summation floor's
bracket is at least `gammaBrick ℓ`, i.e. at least `4·gammaSum ℓ`.  Stated in MULTIPLIED form so no
division appears; this is the exact analogue of `TerminalCompose.gammaBrick_le_coefficient`, with
`96·α²` replaced by `LocFeed`'s `96·α²·16`. -/
theorem four_gammaSum_le_coefficient {ell : ℕ} (hell : 0 < ell) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : α ≤ sumRadius ell) :
    4 * gammaSum ell
      ≤ (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * α ^ 2 * ((16 : ℕ) : ℝ) := by
  have hid := sum_coefficient_eq_gammaBrick hell
  have hsq : α ^ 2 ≤ (1 / (744 * (ell : ℝ) ^ 3)) ^ 2 := by
    have : α ≤ 1 / (744 * (ell : ℝ) ^ 3) := hα
    exact pow_le_pow_left₀ hα0 this 2
  have hg : 4 * gammaSum ell = gammaBrick ell := by
    unfold gammaSum; ring
  rw [hg, ← hid]
  push_cast
  nlinarith [hsq]

theorem gammaSum_pos {ell : ℕ} (hell : 0 < ell) : 0 < gammaSum ell := by
  unfold gammaSum
  have := gammaBrick_pos hell
  linarith

/-- **THE FLOOR CONSTANT, BOUNDED BELOW BY AN EXPLICIT RATIONAL.**  `1383840 = 4·345960`, and
`345960` is `TerminalCompose.gammaBrick_lower`'s (whose own factorisation is
`12454560/36 = 345960` with margin exactly `36`).  The `4` is the plaquette multiplicity. -/
theorem gammaSum_lower {ell : ℕ} (hell : 0 < ell) :
    1 / (1383840 * (ell : ℝ) ^ 6) ≤ gammaSum ell := by
  have hlow := gammaBrick_lower hell
  have h0 : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hd : (0 : ℝ) < 345960 * (ell : ℝ) ^ 6 := by positivity
  unfold gammaSum
  have hrw : 1 / (1383840 * (ell : ℝ) ^ 6) = (1 / (345960 * (ell : ℝ) ^ 6)) / 4 := by
    field_simp
    ring
  rw [hrw]
  linarith

/-- **AND THE FACTOR IS EXACTLY FOUR, IN BOTH DIRECTIONS** — so the swap's price cannot be quoted
as "some constant".  Both conjuncts are equalities. -/
theorem swap_price_is_exactly_four {ell : ℕ} (hell : 0 < ell) :
    4 * gammaSum ell = gammaBrick ell ∧ 4 * sumRadius ell = 1 / (186 * (ell : ℝ) ^ 3) := by
  have h0 : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  refine ⟨by unfold gammaSum; ring, ?_⟩
  unfold sumRadius
  field_simp
  ring

/-- **EVERY PROVENANCE NUMBER OF THE SWAP, ASSERTED RATHER THAN NARRATED.**  A nested validator
found five constants (`280`, `990`, `1536`, `552960`, `12454560`) living only in docstring
arithmetic; this row puts each of them into a compiled type, so no number in this lane's prose is
uncertified.  Each factorisation is the one the SCOPE table cites. -/
theorem constant_factorisations :
    (1536 : ℕ) = 96 * 16 ∧ (744 : ℕ) = 4 * 186 ∧ (1120 : ℕ) = 4 * 280
    ∧ (1383840 : ℕ) = 4 * 345960 ∧ (5535360 : ℕ) = 4 * 1383840
    ∧ (5480006400 : ℕ) = 990 * 5535360 ∧ (5480006400 : ℕ) = 4 * 1370001600
    ∧ (990 : ℕ) = 2 * 495 ∧ (552960 : ℕ) = 360 * 1536
    ∧ (12454560 : ℕ) = 360 * 34596 ∧ (34596 : ℕ) = 186 ^ 2
    ∧ (744 : ℕ) ^ 2 = 16 * 186 ^ 2 ∧ (345960 : ℕ) * 36 = 12454560 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## §2 — THE BRICK AT `C₀B̃`, FROM PER-CUBE GAUGES ALONE

`TerminalAssembly.cdc_floor_class_uniform_at_cZero_norm` derives the same inequality from
`covariant_lemma24` at the GLOBAL class.  This is that derivation with `LocFeed`'s summation floor
in its place: the hypothesis is per-cube, the conclusion is at the ORIGINAL `U`, and the constant
is `gammaSum ℓ` rather than `gammaBrick ℓ`. -/

/-- **THE BRICK FROM THE SUMMATION FLOOR.**

    gammaSum ℓ · ‖C₀B̃‖²  ≤  ⟪C₀B̃, D_U^*D_U (C₀B̃)⟫

for a pairwise-disjoint family of cubes covering the coarse lattice, each with its OWN gauge `γ i`,
with the LOCALLY GAUGED holonomy deviations bounded by `α ≤ 1/(744ℓ³)` on the doubly-enlarged bond
set.  **No global gauge, no `frobSupBond`, no gauge-orbit hypothesis.** -/
theorem sum_brick_at_cZero {ell : ℕ} {ι : Type*} [DecidableEq ι] (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (α : ℝ) (hα0 : 0 ≤ α) (hα : α ≤ sumRadius ell)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell)) (γ : ι → GaugeFn L)
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite L ell, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (tilde hdvd (tilde hdvd (Y i))),
      RMapLipschitz.frobNorm
        (((periodicGaugeTransform (γ i) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (w : TildeFn L ell) :
    gammaSum ell * ‖cZero U ell (dinvC U ell) w‖ ^ 2
      ≤ (inner ℝ (cZero U ell (dinvC U ell) w)
          (dstarDCLM U (cZero U ell (dinvC U ell) w)) : ℝ) := by
  have hell : 0 < ell := by omega
  have hmain := global_floor_from_percube_gauges hell2 hstrict hdvd U (cZeroFn U ell w)
    (cZeroFn_admissible hell hdvd U w) α hα0 𝒞 Y γ hdisj hcov hclass
  rw [coarseQEnergyCov_cZero_eq_zero hell hdvd U w, mul_zero, mul_zero, zero_add] at hmain
  have hfn : cZeroFn U ell w = fun b => (cZero U ell (dinvC U ell) w : BondFnL2 L) b := rfl
  rw [hfn, bondEnergy_eq_normSq, curlEnergyCov_eq_inner_dstarDCLM] at hmain
  have hcoef := four_gammaSum_le_coefficient hell α hα0 hα
  have hn : (0 : ℝ) ≤ ‖cZero U ell (dinvC U ell) w‖ ^ 2 := sq_nonneg _
  have hstep := mul_le_mul_of_nonneg_right hcoef hn
  push_cast at hmain hstep ⊢
  linarith [hmain, hstep]

/-! ## §3 — THE POINCARÉ INPUT IN THE SHAPE `floor_of_hraw_sharp` CONSUMES

`TerminalAssembly.normSq_curlCLM_eq_dstarDCLM_form` (REUSED, LAW-19) turns the `D_U^*D_U` form into
`‖∂_U ·‖²`, which is `hpoin`'s left-hand side. -/

/-- **`γP‖B‖² ≤ ‖∂_U B‖²` at `B = C₀B̃`, with `γP = gammaSum ℓ`** — the summation route's exact
analogue of `TerminalAssembly.hpoin_at_cZero`, with the per-cube hypothesis in place of `hthr`. -/
theorem hpoin_sum_at_cZero {ell : ℕ} {ι : Type*} [DecidableEq ι] (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (α : ℝ) (hα0 : 0 ≤ α) (hα : α ≤ sumRadius ell)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell)) (γ : ι → GaugeFn L)
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite L ell, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (tilde hdvd (tilde hdvd (Y i))),
      RMapLipschitz.frobNorm
        (((periodicGaugeTransform (γ i) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (w : TildeFn L ell) :
    gammaSum ell * ‖cZero U ell (dinvC U ell) w‖ ^ 2
      ≤ ‖curlCovariantCLM_L2 U (cZero U ell (dinvC U ell) w)‖ ^ 2 := by
  rw [normSq_curlCLM_eq_dstarDCLM_form]
  exact sum_brick_at_cZero hell2 hstrict hdvd U α hα0 hα 𝒞 Y γ hdisj hcov hclass w

/-! ## §4 — CONTROLS

Four rows.  Two say the swap is not vacuous; two say it is not free. -/

/-- **MUST-NOT-FIRE — THE OLD RADIUS DOES NOT SURVIVE THE SWAP.**  Two conjuncts, both equalities
or strict inequalities, so neither can be softened:

1. at the OLD radius `1/(186ℓ³)` the summation floor's bracket is STRICTLY SMALLER than
   `gammaBrick ℓ`, by exactly `1440/(34596·ℓ⁶)` — so the recomposition cannot be obtained by
   quoting the old class at the old constant;
2. at the campaign's own witness `ℓ = 3` the bracket at the old radius is NEGATIVE, i.e. the
   summation floor is vacuous there.  `552960/34596 = 15.98…`, so this holds at every `ℓ ≤ 15`.

The exact numerator is `34596·ℓ − 552960` over `12454560·ℓ⁶`, both counted:
`34596 = 186²`, `552960 = 360·1536`, `12454560 = 360·34596`. -/
theorem old_radius_fails_after_swap {ell : ℕ} (hell : 0 < ell) :
    (1 / 360) * (1 / (ell : ℝ) ^ 5)
        - 96 * (1 / (186 * (ell : ℝ) ^ 3)) ^ 2 * ((16 : ℕ) : ℝ)
      = gammaBrick ell - 1440 / (34596 * (ell : ℝ) ^ 6)
    ∧ (1 / 360) * (1 / (ell : ℝ) ^ 5)
        - 96 * (1 / (186 * (ell : ℝ) ^ 3)) ^ 2 * ((16 : ℕ) : ℝ)
      = (34596 * (ell : ℝ) - 552960) / (12454560 * (ell : ℝ) ^ 6)
    ∧ (1 / 360) * (1 / ((3 : ℕ) : ℝ) ^ 5)
        - 96 * (1 / (186 * ((3 : ℕ) : ℝ) ^ 3)) ^ 2 * ((16 : ℕ) : ℝ) < 0 := by
  have h0 : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  refine ⟨?_, ?_, ?_⟩
  · unfold gammaBrick
    push_cast
    field_simp
    ring
  · push_cast
    field_simp
    ring
  · norm_num

/-- **NON-VACUITY — THE CUBE FAMILY BINDERS ARE INHABITED.**  `LocFeed.singleton_family_ok`
(REUSED): one cube per coarse site is pairwise disjoint and covers, so `sum_brick_at_cZero` is not
conditioned on an unsatisfiable covering. -/
theorem sum_brick_family_inhabited {ell : ℕ} :
    (∀ i ∈ (Finset.univ : Finset (CSite L ell)), ∀ j ∈ (Finset.univ : Finset (CSite L ell)),
      i ≠ j → Disjoint ({i} : Finset (CSite L ell)) ({j} : Finset (CSite L ell)))
    ∧ (∀ z : CSite L ell, ∃ i ∈ (Finset.univ : Finset (CSite L ell)),
        z ∈ ({i} : Finset (CSite L ell))) := singleton_family_ok

#print axioms sumRadius
#print axioms gammaSum
#print axioms sum_coefficient_eq_gammaBrick
#print axioms four_gammaSum_le_coefficient
#print axioms gammaSum_pos
#print axioms gammaSum_lower
#print axioms swap_price_is_exactly_four
#print axioms old_radius_fails_after_swap
#print axioms constant_factorisations
#print axioms sum_brick_at_cZero
#print axioms hpoin_sum_at_cZero
#print axioms sum_brick_family_inhabited

end AdalyFormal.Balaban.RecomposeSum
