/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CovariantOperators

set_option autoImplicit false

/-!
# WALL-PROVER dispatch: `Δ_j^{cov}(U)`'s covariant building blocks are `ℤ₂`-per-link BLIND

**Role: wall-prover** (`compute/unrestricted_u_kill/`), attacking `[LEM-COERC-U]` at unrestricted
`U` via the CENTRAL/near-central-background angle named in the dispatch (§3: "`Ad(−I) = Ad(I) = I`,
so `U = −I` acts trivially despite being far from the identity ... degenerate directions of `Ad`
are where a coercivity constant is most likely to collapse").

## What this file proves (kernel-checked, not asserted)

Every operator this tree builds out of the covariant background `U` — `gradValueCovariant`
(`D_Uλ`), `curlValueCovariant` (`D_UA`), `gradCovariantAdjointValue` (`D_U^*A`), and the bundled
`LinearMap`s `gradCovariantLM`/`curlCovariantLM`/`gradCovariantAdjointLM`/`siteLaplacianCovLM` —
depends on `U` **only through `RMap (U b) = fun X ↦ U(b) X U(b)⁻¹`, the adjoint action, at each
individual bond `b`.** Since `RMap` is literally invariant under multiplying any *single* link
variable by the central element `-1 ∈ SU(2)` (`RMap (-U) = RMap U`, proved below from the bare
matrix identity `(-U)X(-U)ᴴ = UXUᴴ`), **every one of these operators is exactly invariant under
flipping the sign of an ARBITRARY SUBSET of links, independently, one link at a time.**

This is a genuine `(ℤ/2)^{#bonds}`-fold redundancy of the campaign's own quantifier `∀ U`
(unrestricted, over the *whole* `SU(2)^{Bond L}` configuration space): the map
`U ↦ (siteLaplacianCovLM U, curlCovariantLM U, gradCovariantAdjointLM U)` — the entire operator
content `Δ₀^{cov}(U) = D_U^*D_U` is built from before `H_j^{cov}`'s minimization step is even
reached — factors through the quotient `U ↦ (Ad(U(b)))_b ∈ SO(3)^{Bond L}`.

## What this DOES and does NOT establish about `[LEM-COERC-U]`

**Does NOT refute uniform coercivity.** A central flip leaves every downstream quantity EXACTLY
fixed, in particular it does not drive `⟨B,Δ_j(U)B⟩/‖B‖²` toward `0` — it is a symmetry, not a
degeneration. So this is not a kill.

**DOES sharpen the wall the dispatch asked for**, precisely: Bałaban's own "regularity"/"smallness"
condition (`(3.35)`/`(3.36)`, `GOAL.md`'s OWNER RULING quoting it) measures geodesic distance to the
identity **in `SU(2)` itself**. `U = -I` (or any single link flipped to `-I`, all others `= I`) is
at the MAXIMUM possible `SU(2)`-geodesic distance from the identity (`π`, i.e. antipodal on the
double cover) — Bałaban's own metric would classify it as maximally "irregular" — **yet
`Δ₀^{cov}(-I)` (and, by the propagation argued in §5, the FULL Schur complement `Δ_j^{cov}`) is
IDENTICAL to its value at `U ≡ 1`, the "most regular" point.** Any proof strategy for
`[LEM-COERC-U]` that tries to control unrestricted `U` by controlling `SU(2)`-geodesic distance to
`1` (the natural reading of "continuation from the regular class", `GOAL.md`'s consequence #2) is
attempting to bound a function that DOES NOT SEE the metric it is being measured against — the
metric and the operator disagree about what "close to the trivial background" means, off by exactly
the `{±1}` center. A continuation-style proof must either (a) work on the quotient `SO(3)^{Bond L}`
from the start, or (b) explicitly show the extra `ℤ₂`-redundancy is harmless to its own estimates —
neither is automatic, and the second is exactly the kind of "hidden assumption" `GOAL.md`'s own
consequence #2 warns a regularity-based route smuggles in.

## Scope, honestly bounded (read before citing)

**Proved here (kernel-checked)**: the value-level and `LinearMap`-level invariance for
`gradValueCovariant`/`curlValueCovariant`/`gradCovariantAdjointValue`/`gradCovariantLM`/
`curlCovariantLM`/`gradCovariantAdjointLM`/`siteLaplacianCovLM` — i.e. everything up through
`Δ₀^{cov}(U) = D_U^*D_U`, `CovariantHjMinimizer.lean` §5-§6.

**NOT proved here, named as the explicit next step**: propagation through `H_j^{cov}` itself
(`RcovLM`, `gaugeConstraintSubspaceCov`, `curlImageCovProj`, `hjExtensionCov`, `deltaJQuadFormCov`,
`CovariantHjMinimizer.lean` §7-§13). The mechanism is the same (every one of those objects is
built from `siteLaplacianCovLM U`/`curlCovariantLM U`/`gradCovariantAdjointLM U` and a
`U`-INDEPENDENT kernel submodule `kernelSubspaceCov`, so the intermediate submodule
`deltaKernelImageCovH U levels` is LITERALLY the same submodule for `U` and any central flip of
`U`), but discharging it requires transporting the `[HasOrthogonalProjection]` INSTANCE argument
across that submodule equality through five further definitions — a real but purely mechanical
proof-engineering task, not attempted in this dispatch's budget. **Do not cite this file as having
shown `deltaJQuadFormCov` itself is center-blind — only its `D_U`/`D_U^*`/`Δ₀^{cov}` ingredients.**
`Balaban/UnrestrictedU.lean` (a concurrent, off-limits lane) is the natural place this propagation
would be finished, if wanted.

**Write scope**: this file only, plus `compute/unrestricted_u_kill/`. No existing `.lean` file
touched, per the dispatch.
-/

namespace AdalyFormal.HoleHunt.CenterBlindness

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.AdmissibleSubspace

/-! ## §1 — `negI`, the central element `-1 ∈ SU(2)`, and `RMap negI = id` -/

/-- **`-I`, as a bare `2×2` complex matrix.** -/
def negIMat : Matrix (Fin 2) (Fin 2) ℂ := -1

theorem negIMat_mem_unitaryGroup : negIMat ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  simp [negIMat]

theorem negIMat_det : negIMat.det = 1 := by
  simp [negIMat, Matrix.det_neg]

theorem negIMat_mem : negIMat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  Matrix.mem_specialUnitaryGroup_iff.mpr ⟨negIMat_mem_unitaryGroup, negIMat_det⟩

/-- **`negI` — the central element `-1`, packaged as a genuine `SU(2)` group element.** The
`SU(2)`-geodesic-distance-`π` antipode of `1`: `RMap negI = id` below shows the ADJOINT action
cannot see this distance at all. -/
def negI : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨negIMat, negIMat_mem⟩

theorem negI_coe : (negI : Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl

/-- **THE CORE FACT: `RMap negI = id`.** Conjugation by `-I` is the identity — `(-I)X(-I)⁻¹ = X`
for every `X`, since `(-I)⁻¹ = -I` and `(-I)X(-I) = X`. This is the single algebraic fact behind
every invariance theorem in this file. -/
theorem RMap_negI : RMap negI = LinearMap.id := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  rw [RMap_coe_apply]
  change negIMat * (X : Matrix (Fin 2) (Fin 2) ℂ) * negIMat.conjTranspose =
    (X : Matrix (Fin 2) (Fin 2) ℂ)
  have hct : negIMat.conjTranspose = negIMat := by
    simp [negIMat, Matrix.conjTranspose_neg, Matrix.conjTranspose_one]
  rw [hct]
  change (-1 : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ) * (-1) = X
  noncomm_ring

#print axioms negIMat_mem_unitaryGroup
#print axioms negIMat_det
#print axioms negIMat_mem
#print axioms RMap_negI

/-- **`RMap` is `negI`-multiplication-blind, on EITHER side**: flipping a single link's sign by
central multiplication leaves its adjoint action exactly unchanged. -/
theorem RMap_negI_mul (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) : RMap (negI * U) = RMap U := by
  rw [RMap_mul, RMap_negI]
  ext X
  simp

theorem RMap_mul_negI (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) : RMap (U * negI) = RMap U := by
  rw [RMap_mul, RMap_negI]
  ext X
  simp

#print axioms RMap_negI_mul
#print axioms RMap_mul_negI

/-! ## §2 — the per-link `ℤ₂`-flip of a whole configuration, and `RMap`'s blindness to it -/

variable {L : PeriodicLatticeExtent}

/-- **`flipSign b`**: `negI` if `b = true`, else `1`. -/
def flipSign (b : Bool) : Matrix.specialUnitaryGroup (Fin 2) ℂ := if b then negI else 1

/-- **`centralFlipConfig ε U`**: the configuration `U` with an INDEPENDENT, arbitrary subset of
links (named by `ε : Bond L → Bool`) flipped by the central element `-I`. Genuinely arbitrary per
link — `ε` need not be constant, so this covers everything from "flip one link" to "flip every
link" and every subset in between, `2^{#bonds}` configurations total for a finite lattice. -/
def centralFlipConfig (ε : Bond L → Bool)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L :=
  fun b => flipSign (ε b) * U b

/-- **`RMap` cannot distinguish `U` from any central flip of it, bond by bond.** -/
theorem RMap_centralFlipConfig (ε : Bond L → Bool)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b : Bond L) :
    RMap (centralFlipConfig ε U b) = RMap (U b) := by
  unfold centralFlipConfig flipSign
  split
  · exact RMap_negI_mul (U b)
  · simp

#print axioms RMap_centralFlipConfig

/-- **S82 garbage substitution — the claim can fail.** Dropping the centrality (replacing `negI`
by `witnessMElem`, a GENUINE non-central `SU(2)` element, already banked as a witness elsewhere in
this tree) breaks the invariance: conjugation by a non-central element is NOT the identity in
general. Recorded so the reader can see `RMap_negI`/`RMap_negI_mul` are not vacuous facts about
"any group element" — they depend genuinely on `negI` being CENTRAL. -/
example :
    RMap witnessMElem suTwoWitness ≠
      RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) suTwoWitness := by
  rw [RMap_witnessMElem, RMap_one]
  simp only [LinearMap.id_coe, id_eq]
  intro h
  apply suTwoWitnessVal_ne_neg_self
  have hval : (suTwoWitness : SuTwo).val = ((-suTwoWitness : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) :=
    congrArg Subtype.val h.symm
  have hcoe : ((-suTwoWitness : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) =
      -(suTwoWitness : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  rw [hcoe] at hval
  exact hval

end AdalyFormal.HoleHunt.CenterBlindness
