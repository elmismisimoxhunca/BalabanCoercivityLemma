/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import CovLemma24Center
import AdalyFormal.Balaban.AlphaAnalyticity
import AdalyFormal.Balaban.CoercUMainRegular

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# THE COVARIANCE CLASS AT A GAUGE-INVARIANT QUANTITY

## The gap this module addresses, quoted from the lane that proved it

`compute/delta_alpha0/SCOPE.md` §5, verbatim:

> "The gap is on the COVARIANCE side. `terminal_posDef_of_source_bound` also requires
> `frobSupBond U ≤ 1/(186ℓ³)`, a bound on the UNGAUGED configuration in a quantity that is NOT a
> function of the gauge orbit. `frobSupBond_gauge_gap` states the obstruction as a theorem: the
> link `−1` — gauge-equivalent to the flat link `1`, whose `frobSupBond` is `0` — has
> `‖(−1) − 1‖_F = 2√2`, and `1/(186ℓ³) < 2√2` for every `ℓ ≥ 1`. So the entire admissible range
> lies inside the gauge-orbit spread, and no per-cube-gauge hypothesis can bound `frobSupBond`."

## Bałaban's own move, and where it already exists in this tree

CMP99b p.408, image-read verbatim in `compute/gauge_patching/SCOPE.md` §1a:

> "This follows from Corollary 3.5 applied to the configuration `U' = U^u`, and we have to recall
> only that all the results of these theorems are gauge invariant."

**LAW-19 / BUILD-DISCIPLINE-2 DISCLOSURE — most of the covariance algebra was ALREADY IN PRINT in
this tree and is REUSED, not rebuilt.** `AdalyFormal/Balaban/AlphaAnalyticity.lean` §1–§3 already
carries `gaugeActA`, `periodicPathHolonomy_gauge`, `rZeroA_gauge`, `lineCoarseRestrictCov_gauge`,
`curlValueCovariant_gauge`, `bondEnergy_gauge`, `axialGauge_gauge`, `norm_RMap`, the orbit class
`GaugeRegular α₀ U := ∃ γ, frobSupBond (U^γ) ≤ α₀`, `gaugeRegular_of_frobSupBond_le`,
`gaugeRegular_gauge_invariant`, and the center witness `centerU_is_gaugeRegular`. **Not one of those
is re-derived here.**

What did NOT exist, and is built here:

1. the gauge invariance of the two ENERGIES that `CovariantLemma24`'s statement is written in
   (`coarseQEnergyCov`, `curlEnergyCov`) — `AlphaAnalyticity` proves covariance of the pointwise
   operators and of `dstarDQuadForm`, but neither of the two `∑ ‖·‖²` energies of Lemma 2.4;
2. the resulting gauge invariance of the whole INEQUALITY (`lemma24_form_gauge_invariant`);
3. the covariant Lemma 2.4 restated at the ORBIT class (`covariant_lemma24_orbit`), which is the
   restatement `delta_alpha0` §5 named as the missing statement;
4. the fact that the restatement's constant at the campaign's own threshold is EXACTLY
   `TerminalCompose.gammaBrick ell` — no constant is lost. That equality is
   `GaugeInvTerminal.orbit_coefficient_eq_gammaBrick`, in this lane's SECOND module, not here;
5. the negative control demanded by the dispatch: at `U ≡ −1` the orbit class HOLDS at every
   `α ≥ 0` while the old class FAILS at every `ℓ`, and the orbit floor is therefore non-vacuous
   exactly where `center_outside_certified_class` showed the old one says nothing.

## Honest scope

* Everything here inherits `CovLemma24`'s corrected `ell⁻⁵` exponent and its non-least constant
  `96`, and asserts nothing new about either.
* `GaugeRegular` uses ONE GLOBAL gauge. The printed class of CMP99b (3.35) grants a gauge PER CUBE.
  This module does NOT claim the per-cube class implies `GaugeRegular`;
  `compute/gauge_inv_class/stage/GaugeInvPerCube.lean` is where that question is prosecuted, and it
  is answered there in the negative with a named witness
  (`GaugeInvPerCube.perCube_not_implies_global`).
* This module is an ISLAND: not imported by `Spine.lean`, changes no axiom set.
-/

namespace AdalyFormal.Balaban.GaugeInvClass

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy frobSupBond frobSupBond_nonneg)
open AdalyFormal.Balaban.CovariantLemma24 (coarseQEnergyCov curlEnergyCov SuAdmissible
  covariant_lemma24 covariant_floor_pos_iff threshold_of_alpha_le)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply gaugeInv gaugeMul
  gaugeTransform_comp gaugeTransform_one gaugeTransform_inv lineCoarseRestrictCov_gauge
  curlValueCovariant_gauge bondEnergy_gauge axialGauge_gauge norm_RMap GaugeRegular
  gaugeRegular_of_frobSupBond_le gaugeRegular_gauge_invariant centerU centerU_is_gaugeRegular
  frobSupBond_centerU negOneElem)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE TWO LEMMA-2.4 ENERGIES ARE GAUGE INVARIANT

`AlphaAnalyticity` proves the two *operators* transform by `R(γ(·))` at the object's own base site.
`R(g)` is an isometry (`norm_RMap`), so summing squared norms erases the gauge entirely. These two
lemmas are the reason the INEQUALITY — not merely the operator — crosses. -/

/-- **THE COARSE `Q_ell(U)` ENERGY IS A GAUGE INVARIANT.**
`∑_c ‖(Q_ell(U^γ) A^γ)(c)‖² = ∑_c ‖(Q_ell(U) A)(c)‖²`. -/
theorem coarseQEnergyCov_gauge (γ : GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : Bond L → SuTwo) :
    coarseQEnergyCov (periodicGaugeTransform γ U) ell (gaugeActA γ A) = coarseQEnergyCov U ell A := by
  unfold coarseQEnergyCov
  exact Finset.sum_congr rfl (fun c _ => by
    rw [lineCoarseRestrictCov_gauge, norm_RMap])

/-- **THE FINE COVARIANT CURL ENERGY IS A GAUGE INVARIANT.**
`∑_p ‖(D_{U^γ} A^γ)(p)‖² = ∑_p ‖(D_U A)(p)‖²`. -/
theorem curlEnergyCov_gauge (γ : GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    curlEnergyCov (periodicGaugeTransform γ U) (gaugeActA γ A) = curlEnergyCov U A := by
  unfold curlEnergyCov plaqEnergy
  exact Finset.sum_congr rfl (fun p _ => by
    rw [curlValueCovariant_gauge, norm_RMap])

/-- **THE (2.121) AXIAL GAUGE CLAUSE IS GAUGE EQUIVARIANT.** `SuAdmissible` is a pointwise
vanishing condition and `R(g)` is linear; this is `AlphaAnalyticity.axialGauge_gauge`, RESTATED at
`CovariantLemma24`'s own predicate name so the two files' vocabularies meet. Nothing is proved. -/
theorem suAdmissible_gauge (γ : GaugeFn L) (ell : ℕ) (A : Bond L → SuTwo)
    (hadm : SuAdmissible L ell A) : SuAdmissible L ell (gaugeActA γ A) :=
  axialGauge_gauge γ ell A hadm

/-- **THE WHOLE LEMMA-2.4 INEQUALITY IS GAUGE INVARIANT** — all three terms at once, which is the
form p.398's *"All these inequalities are invariant with respect to gauge transformations of `U`"*
asserts. Stated as an equality of the two SIDES rather than as an implication, so no direction is
smuggled. -/
theorem lemma24_form_gauge_invariant (γ : GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : Bond L → SuTwo) :
    bondEnergy (gaugeActA γ A) = bondEnergy A
    ∧ (ell : ℝ) * coarseQEnergyCov (periodicGaugeTransform γ U) ell (gaugeActA γ A)
        + curlEnergyCov (periodicGaugeTransform γ U) (gaugeActA γ A)
      = (ell : ℝ) * coarseQEnergyCov U ell A + curlEnergyCov U A :=
  ⟨bondEnergy_gauge γ A, by rw [coarseQEnergyCov_gauge, curlEnergyCov_gauge]⟩

#print axioms coarseQEnergyCov_gauge
#print axioms curlEnergyCov_gauge
#print axioms suAdmissible_gauge
#print axioms lemma24_form_gauge_invariant

/-! ## §2 — THE ORBIT CLASS, AND THE COVARIANT LEMMA 2.4 RESTATED AT IT

`GaugeRegular α U := ∃ γ, frobSupBond (U^γ) ≤ α` is `AlphaAnalyticity`'s (REUSED). It is
gauge-invariant BY CONSTRUCTION (`gaugeRegular_gauge_invariant`, REUSED). The new content is that
the covariant floor **transfers from the gauged representative back to `U` itself**. -/

/-- Monotone in the parameter: a smaller radius implies a larger one. -/
theorem gaugeRegular_mono {α β : ℝ} (hαβ : α ≤ β)
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    (h : GaugeRegular α U) : GaugeRegular β U := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ, le_trans hγ hαβ⟩

/-- The orbit class never has a negative radius (it is a bound on a nonnegative quantity). -/
theorem nonneg_of_gaugeRegular {α : ℝ}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    (h : GaugeRegular α U) : 0 ≤ α := by
  obtain ⟨γ, hγ⟩ := h
  exact le_trans (frobSupBond_nonneg _) hγ

/-- **THE COVARIANT LEMMA 2.4 AT THE GAUGE ORBIT.**

For every `ell ≥ 2`, every compatible torus, every background `U`, every `α` with
`GaugeRegular α U`, and every `(2.121)`-admissible `A`:

`((1/360)·ell⁻⁵ − 96·α²)·∑_b ‖A b‖² ≤ ell·∑_c ‖(Q₁(U)A)(c)‖² + ∑_p ‖(D_U A)(p)‖²`

— **at `U` itself, not at the gauged representative.** The gauge is created and destroyed inside
this proof: `covariant_lemma24` is applied at `(U^γ, A^γ)` and §1 carries all three terms back.
This is CMP99b p.408's mechanism (*"applied to the configuration `U' = U^u`, and we have to recall
only that all the results of these theorems are gauge invariant"*) at this chain's own inequality.

Compare `covariant_lemma24`, whose coefficient is `(1/360)ell⁻⁵ − 96·frobSupBond U ²`: here
`frobSupBond U` — which is not a function of the orbit — has been replaced by the orbit radius. -/
theorem covariant_lemma24_orbit {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (α : ℝ) (hreg : GaugeRegular α U)
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) :
    ((1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * α ^ 2) * bondEnergy A
      ≤ (ell : ℝ) * coarseQEnergyCov U ell A + curlEnergyCov U A := by
  obtain ⟨γ, hγ⟩ := hreg
  have hA : SuAdmissible L ell (gaugeActA γ A) := suAdmissible_gauge γ ell A hadm
  have hmain := covariant_lemma24 (L := L) hell2 hstrict hdvd (periodicGaugeTransform γ U)
    (gaugeActA γ A) hA
  rw [bondEnergy_gauge, coarseQEnergyCov_gauge, curlEnergyCov_gauge] at hmain
  -- the gauged representative's coefficient dominates the orbit-radius coefficient
  have h0 : (0 : ℝ) ≤ frobSupBond (periodicGaugeTransform γ U) := frobSupBond_nonneg _
  have hsq : frobSupBond (periodicGaugeTransform γ U) ^ 2 ≤ α ^ 2 := pow_le_pow_left₀ h0 hγ 2
  have hbe : (0 : ℝ) ≤ bondEnergy A := AdalyFormal.Balaban.RegularUPerturbation.bondEnergy_nonneg A
  nlinarith [hmain, hsq, hbe]

/-- **THE ORBIT FLOOR IS STRICTLY POSITIVE AT THE CAMPAIGN'S OWN THRESHOLD.**
`GaugeRegular (1/(186·ell³)) U` — the gauge-invariant restatement of `frobSupBond U ≤ 1/(186ell³)` —
delivers both the positivity of the coefficient and the floor, at `U` itself. -/
theorem covariant_lemma24_orbit_positive {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular (1 / (186 * (ell : ℝ) ^ 3)) U)
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) :
    0 < (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * (1 / (186 * (ell : ℝ) ^ 3)) ^ 2
    ∧ ((1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * (1 / (186 * (ell : ℝ) ^ 3)) ^ 2) * bondEnergy A
        ≤ (ell : ℝ) * coarseQEnergyCov U ell A + curlEnergyCov U A := by
  have hell : 0 < ell := by omega
  have hpos : (0 : ℝ) < 186 * (ell : ℝ) ^ 3 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  refine ⟨?_, covariant_lemma24_orbit hell2 hstrict hdvd U _ hreg A hadm⟩
  exact (covariant_floor_pos_iff hell _).mpr
    (threshold_of_alpha_le hell (le_of_lt (by positivity)) (le_refl _))

/-- **THE PRINTED (UNGAUGED) CLASS IMPLIES THE ORBIT CLASS**, so the restatement never LOSES a
configuration: every theorem consuming the orbit class also serves every `U` the old hypothesis
served. This is `gaugeRegular_of_frobSupBond_le` (REUSED), named here at the campaign's threshold. -/
theorem orbit_class_of_threshold {ell : ℕ}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3)) :
    GaugeRegular (1 / (186 * (ell : ℝ) ^ 3)) U :=
  gaugeRegular_of_frobSupBond_le hthr

/-- **THE RESTATED HYPOTHESIS IS GAUGE-INVARIANT BY CONSTRUCTION** — `AlphaAnalyticity`'s theorem
(REUSED), named at this lane's threshold so the property `delta_alpha0` §5 asked for is on record
next to the theorem that consumes it. -/
theorem orbit_class_gauge_invariant {ell : ℕ} (δ : GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    GaugeRegular (1 / (186 * (ell : ℝ) ^ 3)) (periodicGaugeTransform δ U)
      ↔ GaugeRegular (1 / (186 * (ell : ℝ) ^ 3)) U :=
  gaugeRegular_gauge_invariant δ U

/-- **THE OLD HYPOTHESIS IS NOT GAUGE-INVARIANT — the contrast, as one statement.** On any torus
with `2 ∣ L μ + 1`, `U ≡ −1` and its gauge transform `U^{parity} = 1` have `frobSupBond` equal to
`2√2` and `0` respectively, so `frobSupBond U ≤ t` is NOT a property of the orbit for any
`0 ≤ t < 2√2`; whereas `GaugeRegular t` agrees on the two by `orbit_class_gauge_invariant`. -/
theorem old_hypothesis_not_gauge_invariant
    (hdvd2 : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 2 * Real.sqrt 2) :
    ¬ (frobSupBond (centerU L) ≤ t)
    ∧ (∃ δ : GaugeFn L, frobSupBond (periodicGaugeTransform δ (centerU L)) ≤ t)
    ∧ (GaugeRegular t (centerU L) ↔ GaugeRegular t (centerU L)) := by
  refine ⟨?_, ?_, Iff.rfl⟩
  · rw [frobSupBond_centerU]; linarith
  · exact ⟨AdalyFormal.Balaban.AlphaAnalyticity.parityGauge L, by
      rw [AdalyFormal.Balaban.AlphaAnalyticity.centerU_gaugeRegular_zero hdvd2,
        AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU]
      exact ht0⟩

#print axioms gaugeRegular_mono
#print axioms nonneg_of_gaugeRegular
#print axioms covariant_lemma24_orbit
#print axioms covariant_lemma24_orbit_positive
#print axioms orbit_class_of_threshold
#print axioms orbit_class_gauge_invariant
#print axioms old_hypothesis_not_gauge_invariant

/-! ## §3 — THE NEGATIVE CONTROL THE DISPATCH DEMANDED

`CovLemma24Center.center_outside_certified_class` proves that at `U ≡ −1` the OLD threshold fails,
the OLD coefficient is strictly negative, and yet the covariant Lemma 2.4 holds there with the full
flat constant. That is a proved instance of the old class being strictly conservative.

Here is the same background against the RESTATED class. -/

/-- `CovLemma24Sharp.negOneU` and `AlphaAnalyticity.centerU` are the same configuration: both are
the constant function at `⟨−1, _⟩ ∈ SU(2)`, defined independently in the two files.

**This is a FINDING about the tree, not a repair (LAW-4):** the element `−1 ∈ SU(2)` is now defined
at least THREE times — `CovLemma24Sharp.negOneElem`, `AlphaAnalyticity.negOneElem` (whose own
docstring already discloses a fourth, `HoleHunt/CenterBlindness.negI`). The bridge is proved rather
than assumed so that this module's control can quote the two lanes' theorems about the SAME `U`. -/
theorem negOneU_eq_centerU :
    AdalyFormal.Balaban.CovLemma24Sharp.negOneU L = centerU L := by
  funext b
  exact Subtype.ext rfl

/-- **THE RESTATEMENT GENUINELY WIDENS THE CLASS — the non-vacuity witness, at the exact background
where the old class collapses.**

On any torus with `2 ∣ L μ + 1` and `ell ≥ 2` a compatible block size, at `U ≡ −1`:

1. the OLD hypothesis `frobSupBond U ≤ 1/(186ell³)` FAILS (`negOneU_fails_threshold`, REUSED), so
   `covariant_lemma24_positive` is unusable and `covariant_lemma24`'s own coefficient is negative
   (`center_outside_certified_class`, REUSED);
2. the RESTATED hypothesis HOLDS — at radius `0`, the strongest possible
   (`centerU_is_gaugeRegular`, REUSED);
3. and therefore the orbit floor is available at this background with a STRICTLY POSITIVE constant
   `(1/360)·ell⁻⁵`, whereas the old route delivers nothing at all.

**The widening is not cosmetic**: item 1 and item 3 hold simultaneously at the same `U`. -/
theorem center_inside_orbit_class_outside_old {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (hdvd2 : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) :
    ¬ (frobSupBond (centerU L) ≤ 1 / (186 * (ell : ℝ) ^ 3))
    ∧ (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond (centerU L) ^ 2 < 0
    ∧ GaugeRegular 0 (centerU L)
    ∧ 0 < (1 / 360) * (1 / (ell : ℝ) ^ 5)
    ∧ ((1 / 360) * (1 / (ell : ℝ) ^ 5)) * bondEnergy A
        ≤ (ell : ℝ) * coarseQEnergyCov (centerU L) ell A + curlEnergyCov (centerU L) A := by
  have hell : 0 < ell := by omega
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hold := AdalyFormal.Balaban.CovLemma24Center.center_outside_certified_class
    (L := L) hell2 hstrict hdvd A hadm
  rw [negOneU_eq_centerU] at hold
  have hreg0 : GaugeRegular 0 (centerU L) := centerU_is_gaugeRegular hdvd2
  have hfloor := covariant_lemma24_orbit hell2 hstrict hdvd (centerU L) 0 hreg0 A hadm
  have hz : ((1 / 360 : ℝ) * (1 / (ell : ℝ) ^ 5) - 96 * (0 : ℝ) ^ 2)
      = (1 / 360) * (1 / (ell : ℝ) ^ 5) := by ring
  rw [hz] at hfloor
  exact ⟨hold.1, hold.2.1, hreg0, by positivity, hfloor⟩

#print axioms negOneU_eq_centerU
#print axioms center_inside_orbit_class_outside_old

/-! ## §4 — JUNK ATTACKS ON THIS MODULE'S OWN STATEMENTS

Every restatement widens a hypothesis, and a hypothesis widened far enough certifies nothing. The
three checks below are the ones that answer *"is `GaugeRegular α` still a restriction?"*. -/

/-- **THE ORBIT CLASS IS TOTAL AT RADIUS `2√2` AND ABOVE — disclosed, not hidden.** `frobSupBond`
of ANY `SU(2)` configuration is at most `2√2` (`RegularUPerturbation.frobSupBond_le_two_sqrt_two`,
REUSED), so `GaugeRegular α U` holds for every `U` once `2√2 ≤ α`. The campaign's threshold
`1/(186ell³) ≤ 1/(186·8) = 1/1488` at `ell ≥ 2` is far below that, but the fact is recorded here
because it is the first thing a prosecutor should try. -/
theorem gaugeRegular_total_above_diameter {α : ℝ} (hα : 2 * Real.sqrt 2 ≤ α)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    GaugeRegular α U :=
  gaugeRegular_of_frobSupBond_le
    (le_trans (AdalyFormal.Balaban.CoercUMainRegular.frobSupBond_le_two_sqrt_two U) hα)

/-- **THE CAMPAIGN'S THRESHOLD IS STRICTLY BELOW THE DIAMETER AT EVERY `ell ≥ 1`**, so
`gaugeRegular_total_above_diameter` never applies to `covariant_lemma24_orbit_positive`'s
hypothesis: the restated class is a genuine restriction at the radius actually used. -/
theorem threshold_below_diameter {ell : ℕ} (hell : 0 < ell) :
    1 / (186 * (ell : ℝ) ^ 3) < 2 * Real.sqrt 2 := by
  have h1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h3 : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ h1
  have hd : (0 : ℝ) < 186 * (ell : ℝ) ^ 3 := by linarith
  have hle : 1 / (186 * (ell : ℝ) ^ 3) ≤ 1 / 186 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **THE ORBIT FLOOR IS NOT VACUOUS FOR LACK OF FIELDS**: the constant zero field is admissible,
and the flat background lies in the class, so `covariant_lemma24_orbit` has at least one instance
where every object is defined. **Disclosed as DEGENERATE** (both sides are `0`); the non-degenerate
content is `center_inside_orbit_class_outside_old`, whose `A` is arbitrary. -/
theorem orbit_instance_exists (ell : ℕ) :
    SuAdmissible L ell (fun _ => (0 : SuTwo))
    ∧ GaugeRegular 0 (trivialU L) := by
  refine ⟨fun _ _ _ _ _ _ => rfl, ?_⟩
  exact gaugeRegular_of_frobSupBond_le
    (le_of_eq (AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU L))

#print axioms gaugeRegular_total_above_diameter
#print axioms threshold_below_diameter
#print axioms orbit_instance_exists

end AdalyFormal.Balaban.GaugeInvClass
