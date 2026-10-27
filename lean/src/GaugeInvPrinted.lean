/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import GaugeInvPerCube
import DeltaAlpha0Conv

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.longLine false

/-!
# CMP99b (3.35) AS PRINTED ⟹ THE ORBIT CLASS, PER CUBE — AND EXACTLY WHERE THAT STOPS.

`compute/delta_alpha0/` converts the printed (3.35) data into `GaugePatching.CubeGaugeData` (an
ENTRYWISE bound) and, from a GLOBAL printed representation, into `frobSupBond U ≤ √2·O(1)Mα₀`. What
it does NOT have is the printed PER-CUBE data landed in `GaugeRegular`'s own Frobenius norm at the
per-cube quantifier. That is the one step this module adds, and it is a five-line reuse:
`ThresholdVsPrinted.printed_to_smallness` is exactly the per-link Frobenius conversion, and
`gaugeT` and `periodicGaugeTransform` are the SAME function (`gaugeT_eq_periodicGaugeTransform`,
proved here rather than assumed — two lanes had defined it independently).

## THE CHAIN, AND ITS EXACT STOPPING POINT

| step | statement | where |
|---|---|---|
| (3.35) per cube ⟹ per-cube orbit class at `√2·O(1)Mα₀` | `perCubeRegular_of_printedCubeClass` | **here** |
| that class at the campaign threshold `1/(186ℓ³)` | `perCubeRegular_at_threshold_of_printed` | **here** |
| per-cube orbit class ⟹ GLOBAL orbit class | **FALSE** | `GaugeInvPerCube.perCube_not_implies_global` |
| GLOBAL orbit class ⟹ the terminal composition | `GaugeInvTerminal.terminal_wired_posDef_orbit` | this lane |
| one cube covering every bond ⟹ per-cube IS global | `gaugeRegular_of_perCubeRegular_univ` | **here** |

So (3.35) as printed reaches the orbit class **cube by cube and no further**, and the last row says
precisely what extra geometry would close the gap: a single cube containing every bond. p.409 fixes
the cube side at `12·M·L^jη`, which is not the torus, so that row is a boundary case and not a
route — it is included so the failure is located at the GEOMETRY rather than left as an atmosphere.

**Nothing here is graded (BUILD DISCIPLINE 8): it reports facts.**
-/

namespace AdalyFormal.Balaban.GaugeInvPrinted

open scoped Matrix.Norms.L2Operator

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.SourceWiredGauge (gaugeT)
open AdalyFormal.Balaban.DeltaAlpha0 (PrintedCubeClass PrintedCubeClassI covThreshold
  covariance_class_of_alpha0_exact covariance_class_of_alpha0)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn GaugeRegular)
open AdalyFormal.Balaban.GaugeInvPerCube (PerCubeRegular perCubeRegular_of_gaugeRegular
  perCubeRegular_mono)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE TWO LANES' GAUGE ACTIONS ARE THE SAME FUNCTION

`compute/source_wired/`'s `gaugeT` and `Target.ClayStatement.periodicGaugeTransform` were written
independently. **This is a FINDING about the tree, not a repair (LAW-4):** the gauge action on link
configurations now exists under at least two names. The bridge is PROVED so that this module's
statements can quote both lanes. -/

theorem gaugeT_eq_periodicGaugeTransform
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    gaugeT g U = periodicGaugeTransform g U := rfl

#print axioms gaugeT_eq_periodicGaugeTransform

/-! ## §2 — (3.35) AS PRINTED LANDS THE ORBIT CLASS, CUBE BY CUBE -/

/-- **THE PRINTED PER-CUBE CLASS ⟹ THE PER-CUBE ORBIT CLASS, at `√2·O(1)Mα₀`.**

The `√2` is EXACT and unavoidable: it is `‖X‖_F = √2·|X|` at the source's NORMALIZED trace
(`ThresholdVsPrinted.frobNorm_eq_sqrt_two_mul_printed`), an equality, and `frobSupBond` — hence
`PerCubeRegular` — is built from `‖·‖_F`. No constant is introduced here.

The gauge is passed through UNCHANGED and no relation between two cubes' gauges is introduced,
because none is used. -/
theorem perCubeRegular_of_printedCubeClass (Jm : ThresholdVsPrinted.M2)
    (hJ : RenderStep.IsImaginaryUnit Jm) (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0)
    (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (𝒞 : Set (Set (Bond L))) (h : PrintedCubeClass Jm c M α₀ η Lj U 𝒞) :
    PerCubeRegular (Real.sqrt 2 * (c * M * α₀)) U 𝒞 := by
  intro C hC
  obtain ⟨g, hg⟩ := h C hC
  refine ⟨g, fun e he => ?_⟩
  obtain ⟨A, a, hA, ha, hsq, hprint, hexp⟩ := hg e he
  show frobNorm (((periodicGaugeTransform g U e :
    Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ _
  rw [← gaugeT_eq_periodicGaugeTransform g U, hexp]
  exact ThresholdVsPrinted.printed_to_smallness Jm A hJ hA η a c M α₀ Lj hη hηne ha hLj hc hM hα
    hsq hprint

/-- The same at the source's own imaginary unit `i` (`Carrier.imagUnit`), so no `Jm` binder is
carried — the form a consumer sees. -/
theorem perCubeRegular_of_printedCubeClassI (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0)
    (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (𝒞 : Set (Set (Bond L))) (h : PrintedCubeClassI c M α₀ η Lj U 𝒞) :
    PerCubeRegular (Real.sqrt 2 * (c * M * α₀)) U 𝒞 :=
  perCubeRegular_of_printedCubeClass Carrier.imagUnit Carrier.isImaginaryUnit_imagUnit
    c M α₀ η Lj hη hηne hLj hc hM hα U 𝒞 h

/-- **THE PER-CUBE ORBIT CLASS AT THE CAMPAIGN'S OWN THRESHOLD**, from the printed parameter alone:
`O(1)Mα₀ ≤ 1/(186·√2·ℓ³)` — `delta_alpha0`'s EXACT-constant form, reused — gives
`PerCubeRegular (1/(186·ℓ³))`, which is the radius `GaugeInvClass.covariant_lemma24_orbit_positive`
consumes, **but at the per-cube quantifier, which `GaugeInvPerCube.perCube_not_implies_global`
proves does not deliver the global one.** -/
theorem perCubeRegular_at_threshold_of_printed {ell : ℕ} (hell : 0 < ell)
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0)
    (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (hthr : c * M * α₀ ≤ 1 / (186 * Real.sqrt 2 * (ell : ℝ) ^ 3))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (𝒞 : Set (Set (Bond L))) (h : PrintedCubeClassI c M α₀ η Lj U 𝒞) :
    PerCubeRegular (1 / (186 * (ell : ℝ) ^ 3)) U 𝒞 := by
  have hs : (0 : ℝ) ≤ c * M * α₀ := by positivity
  refine fun C hC => ?_
  obtain ⟨g, hg⟩ := perCubeRegular_of_printedCubeClassI c M α₀ η Lj hη hηne hLj hc hM hα U 𝒞 h C hC
  exact ⟨g, fun b hb => le_trans (hg b hb)
    (covariance_class_of_alpha0_exact hell (c * M * α₀) hs hthr)⟩

/-- The same with `delta_alpha0`'s RATIONAL threshold `covThreshold ℓ = 1/(280ℓ³)`, so no `√2`
appears in the hypothesis a consumer must check. -/
theorem perCubeRegular_at_threshold_of_printed_rational {ell : ℕ} (hell : 0 < ell)
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0)
    (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (hthr : c * M * α₀ < covThreshold ell)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (𝒞 : Set (Set (Bond L))) (h : PrintedCubeClassI c M α₀ η Lj U 𝒞) :
    PerCubeRegular (1 / (186 * (ell : ℝ) ^ 3)) U 𝒞 := by
  have hs : (0 : ℝ) ≤ c * M * α₀ := by positivity
  refine fun C hC => ?_
  obtain ⟨g, hg⟩ := perCubeRegular_of_printedCubeClassI c M α₀ η Lj hη hηne hLj hc hM hα U 𝒞 h C hC
  exact ⟨g, fun b hb => le_trans (hg b hb)
    (covariance_class_of_alpha0 hell (c * M * α₀) hs hthr)⟩

#print axioms perCubeRegular_of_printedCubeClass
#print axioms perCubeRegular_of_printedCubeClassI
#print axioms perCubeRegular_at_threshold_of_printed
#print axioms perCubeRegular_at_threshold_of_printed_rational

/-! ## §3 — THE EXACT GEOMETRIC BOUNDARY BETWEEN PER-CUBE AND GLOBAL -/

/-- **A CUBE CONTAINING EVERY BOND TURNS THE PER-CUBE CLASS INTO THE GLOBAL ONE.** Stated so the
failure in `GaugeInvPerCube.perCube_not_implies_global` is located precisely: it is not that the
per-cube quantifier is weaker in some diffuse way, it is that no cube of side `12ML^jη` contains
every bond of the torus. -/
theorem gaugeRegular_of_perCubeRegular_univ {α : ℝ}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    {𝒞 : Set (Set (Bond L))} (huniv : (Set.univ : Set (Bond L)) ∈ 𝒞)
    (h : PerCubeRegular α U 𝒞) : GaugeRegular α U := by
  obtain ⟨γ, hγ⟩ := h Set.univ huniv
  refine ⟨γ, ?_⟩
  refine Finset.sup'_le _ _ (fun b _ => hγ b (Set.mem_univ b))

/-- **AND THE CONVERSE**, so the two classes are pinned against each other at the boundary and the
`univ` case is an equivalence rather than a one-way convenience. -/
theorem perCubeRegular_univ_iff_gaugeRegular {α : ℝ}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} :
    PerCubeRegular α U {(Set.univ : Set (Bond L))} ↔ GaugeRegular α U := by
  constructor
  · exact fun h => gaugeRegular_of_perCubeRegular_univ (Set.mem_singleton _) h
  · exact fun h => perCubeRegular_of_gaugeRegular h _

#print axioms gaugeRegular_of_perCubeRegular_univ
#print axioms perCubeRegular_univ_iff_gaugeRegular

/-! ## §4 — WHAT THIS MODULE DOES NOT CLOSE, STATED AS A THEOREM RATHER THAN AS PROSE

The printed per-cube class delivers `PerCubeRegular (1/(186ℓ³))` (§2). The terminal composition
consumes `GaugeRegular (1/(186ℓ³))` (`GaugeInvTerminal.terminal_wired_posDef_orbit`). The two are
NOT the same hypothesis, and the separation is not a technicality of this encoding: it is the
wrapping holonomy. -/

/-- **THE GAP, ASSEMBLED AT ONE CONFIGURATION.** On an odd torus with every extent `≥ 3`, the
constant center configuration `U ≡ −1` is in the per-cube class at the STRONGEST radius `0` for the
family of non-wrapping cubes, and outside the global class at every radius the campaign uses.
So `perCubeRegular_at_threshold_of_printed`'s conclusion cannot be upgraded to
`terminal_wired_posDef_orbit`'s hypothesis by any argument at all. -/
theorem printed_class_does_not_reach_the_consumer {ell : ℕ} (hell : 0 < ell)
    (hbig : ∀ μ : Fin 3, 2 ≤ L μ) (hodd : ∀ μ : Fin 3, (L μ + 1) % 2 = 1)
    (hsize : ((L 0 + 1 : ℕ) : ℝ) * (1 / (186 * (ell : ℝ) ^ 3)) < 2 * Real.sqrt 2) :
    PerCubeRegular (0 : ℝ) (AdalyFormal.Balaban.AlphaAnalyticity.centerU L)
        {{b : Bond L | ¬ AdalyFormal.Balaban.GaugeInvPerCube.Wraps b}}
    ∧ ¬ GaugeRegular (1 / (186 * (ell : ℝ) ^ 3))
        (AdalyFormal.Balaban.AlphaAnalyticity.centerU L) :=
  AdalyFormal.Balaban.GaugeInvPerCube.perCube_not_implies_global hbig hodd hsize

#print axioms printed_class_does_not_reach_the_consumer

end AdalyFormal.Balaban.GaugeInvPrinted
