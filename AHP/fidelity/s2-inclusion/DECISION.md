# DECISION — s2-inclusion

**Decision: `lean-comparison`, with a non-vacuity hold on substantive class-variant acceptance.**

Send the repaired conditional inclusion chain to Stage B. Do **not** classify either touching headline as `lean-proof`: no proper nonempty admissible-domain member of either touching class has been supplied. Do not classify this as `reading-only`: the precisely defined inclusions are formal, testable statements. No result is certified by this decision; S-2 remains unclosed.

## What is accepted for comparison

Use `AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean`, namespace `AdalyFormal.AHP.FidelS2Inclusion`, with its current definitions and direct imports `ZT5A`, `ZR2Ops2`, `ZR8Class`.

- `ClassCoupledFour`: frozen site coverage, four-touch-bond plaquette coverage, touching per-cube regularity.
- `ClassCoupledCorner`: frozen site coverage, one-corner plaquette coverage with all four bonds touching one witness box, touching per-cube regularity. This matches the **old** S-1 class, not a newly designed shell class.
- Both retain frozen `IsClassCube`, factor 12 in the headlines, the per-cube existential gauge and field, all regularity bounds, quantifier order and smallness condition. Their conclusion remains frozen `InstIneq`, with `Delta` and `J` on `plaqIn`. Lambda is unchanged.

These are faithful descriptions of the proposed formal variants, **not** certification that either variant expresses the printed convention. In particular, four-touch is not one-corner, and the corner coverage requirement is an additional hypothesis, not supplied by the source convention.

The mathematical comparison survives attack. Coverage is not plain predicate monotonicity: replacing both occurrences of `CubeBond` enlarges the antecedent and weakens the witness. The witness is nevertheless a product `siteBox` (`ZStatementP428.lean:122,131,140`). Touching every edge of a square supplies an opposite pair of corners, and product membership supplies the other pair. Thus the same box supports the frozen coverage conclusion (`ZR6A.lean:27`). Regularity restricts to the frozen bond and curl-read predicates (`ZR2A.lean:35,47`); site coverage stays fixed (`:107`). The class conjunction (`ZR6A.lean:124`) and headline binder order (`ZT5A.lean:89,291`) then give the indicated directions. No reverse or strict inclusion is selected.

## Vacuity and the attack findings

**F1 accepted.** The SPEC sentence saying Sol rejected the saturation argument is misleading. Sol upheld that argument as a necessary-condition concern and rejected the previous S-1 proposal as a resolution of S-1. This decision supersedes that wording; the saturation assertion itself is still uncompiled.

**F2 accepted with a qualification.** Odd and degenerate *torus extents* were checked. That is not an in-regime test of odd *blocking factor* ell > 11. The two parameters must not be conflated.

**F3 is an acceptance blocker, not cosmetic disclosure.** At set/box level every tested proper nonempty domain fails corner coverage. The general empty/whole-torus conclusion is only conditional on the separate saturation argument passing its formal check with all its hypotheses. Do not infer it universally from these finite scans. Even if the corner headline implications compile, they provide no proper-domain analytic application. The four-bond class avoids this particular tested obstruction on product domains, but its full admissible-class inhabitation remains unshown.

**F4 remains for Stage B.** Elaborator risks include boundary-finset unfolding, `mem_siteBox_iff`, dependent equality transport and coordinate rewrites. Repairs may change tactics, not definitions or statement strength. The unused `cubeAnte_iff_plaqIn` is not an acceptance target.

**F5 retained.** No elaboration or axiom output was obtained here. A successful comparison does not itself provide non-vacuity, strictness, touching-operator equality, a shell-class inclusion, or a paper sentence.

To promote the four-bond variant beyond comparison, first supply a checked witness satisfying the actual `TorusOK`, `Admissible`, factor-12 class, positive parameters and proper nonempty Omega_0 requirements. A headline-level non-vacuity claim must also address Lambda and the nontrivial test-field regime, rather than taking empty Lambda. Product-box frozen witnesses with U = 1 are a possible route, not an established witness. That missing witness is not silently added as a hypothesis to an approved headline. The corner class is not recommended as a route to a proper-domain touching result.

## Independent numerical recheck in this decision

Reran the two existing scripts unchanged, sequentially, with `ulimit -v 3906250` (4,000,000,000 bytes of virtual address space), one BLAS/OMP thread, and no bytecode writes. Both completed successfully; no run exceeded side 8. Results are saved separately:

- `numerics/decision_geometry.json`: 0.734 seconds. All box/square scans on sides 2,4,6,8 had zero touch-without-cube and cube-without-touch counts. Side 8 had 1,603,584 touch-cover instances. The proper side-4 box on side 8 had 108 inside/four-touch plaquettes and 300 corner plaquettes; its exit plaquette had zero containing-box touch covers. The two-block L had 14 four-touch versus 12 inside plaquettes, with zero box covers of the exhibited diagonal square.
- `numerics/decision_attack.json`: 1.829 seconds. Sides 1,3,5,7 also had zero comparison failures. All 254 proper nonempty side-2 subsets and all 462 side-3 sampled entries failed corner coverage. The side-3 collection includes repeated masks; it is not 462 distinct domains or an exhaustive scan. Product-box antecedent comparisons on sides 2,3,4,5 had zero mismatches.

These are exact Boolean/integer tests of geometry, not gauge-field operator calculations, admissible-class witnesses or proofs. Small tori do not instantiate the proper-domain factor-12 headline geometry. The frozen transcription anchors are `ClayStatement.lean:1281,1295`, `ZStatementP428.lean:122,145`, and `ZR2Ops2.lean:74`. Touching/corner predicates are the local definitions in `ClassInclusion.lean`. The L example also warns against extending the product-box argument to arbitrary unions.

## Exact Stage B declaration targets

All names below are in `AdalyFormal.AHP.FidelS2Inclusion`; use the same opened namespaces as `ClassInclusion.lean`. The signatures below explicitly include the ambient extent binder. They are requested signatures, not checked declarations. The first seven compare predicates; the last three are conditional transports, **not** endorsements of non-vacuous touching headlines.

```lean
touchCover_cubeBond {L : PeriodicLatticeExtent}
    {z : PeriodicLatticeSite L} {s : ℕ} {p : PeriodicLatticePlaquette L}
    (ht : ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond (siteBox z s) e)
    {e : Bond L} (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    CubeBond (siteBox z s) e

CoversPlaqFour.toFrozen {L : PeriodicLatticeExtent}
    {ell M c k : ℕ} {S : Tower L}
    (h : CoversPlaqFour ell M c k S) : CoversPlaqOm0c ell M c k S

CoversPlaqCorner.toFour {L : PeriodicLatticeExtent}
    {ell M c k : ℕ} {S : Tower L}
    (h : CoversPlaqCorner ell M c k S) : CoversPlaqFour ell M c k S

PerCubeRegularTouch.toFrozen {L : PeriodicLatticeExtent}
    {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : PerCubeRegularTouch ell M f k S α₀ η U) :
    PerCubeRegular2 ell M f k S α₀ η U

ClassCoupledFour.toFrozen {L : PeriodicLatticeExtent}
    {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupledFour ell M c k S α₀ η U) :
    ClassCoupled ell M c k S α₀ η U

ClassCoupledCorner.toFour {L : PeriodicLatticeExtent}
    {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupledCorner ell M c k S α₀ η U) :
    ClassCoupledFour ell M c k S α₀ η U

ClassCoupledCorner.toFrozen {L : PeriodicLatticeExtent}
    {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupledCorner ell M c k S α₀ η U) :
    ClassCoupled ell M c k S α₀ η U

targetFour_of_frozen (h : P428Target8) : P428Target8Four

targetCorner_of_four (h : P428Target8Four) : P428Target8Corner

targetCorner_of_frozen (h : P428Target8) : P428Target8Corner
```

## Stage B gate and stopping boundary

Only after the coordinator verifies that `REPRODUCE.sh` has passed and oleans are ready, compile the local file from `lean/` using `lake env lean ../AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean`, through the required heavy-run wrapper. Append `#print axioms` for each of the ten fully qualified names above to the local file, or an equivalent local checking file. Accept only subsets of `propext`, `Classical.choice`, `Quot.sound`, with no placeholders or extra axioms. Do not import the old S-1/S-2 drafts or edit the lakefile.

If these checks pass, report **checked conditional class/headline comparisons only**. Do not mark the proper-domain touching-class fidelity question closed until its independent non-vacuity and class-identification obligations have been met. S-1's new class must be compared from its actual definition; no inclusion for it is authorized by matching a name.

This decision wrote only this file and the two recheck JSON files under `AHP/fidelity/s2-inclusion/`. No Lean, Lake or reproduction command was run; no frozen, paper, sheet, expected-output or Lake-configuration file was edited.
