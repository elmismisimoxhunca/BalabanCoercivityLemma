# Nonvanishing R3 hand-off — final

Published `R3_DilatedFlux.lean` (824 lines, 82 individually audited declarations: 66 new and 16 reused verbatim), independently compiled at original and shared paths: exit 0, no diagnostics, standard axioms only. It imports frozen `DrEquiv` and `ZXR2Flat6`.

**No GoalNeg2 or cofinal coupling premise is proved.**

Main namespace: `AdalyFormal.Round10.Nonvanishing.DilatedFlux`.

Main theorem `localized_curl_of_jetAggregate`: for the actual dilated geometry, q>0, R>=1, j<4q(R+1), arbitrary scalar functional phi, and genuine fine fields A,v, if

```
QfullOf (G q R) flatCfg A = C2fullOf (G q R) flatCfg v
jetAggregate hq hj phi v != 0
```

then an actual plaquette inside Omega_0 has nonzero scalar curl of `phi(A)`.

`jetAggregate` is the sum over **all physical even transverse cells** of the genuine, normalized, level-one direction-1 C2fullOf component at longitudinal fine base 2Rq+4q+2j. The physical full-torus indices, level-zero collar membership, and selected plaquette membership are all constructed and proved, not hypotheses. There is no Bloch reduction or source-column normalization premise.

For application, use `v=W0(iE u)` and `A=iE(H0(C2 u))`; QH=1 supplies the displayed constraint equation. Choose phi = inner(pauliE3,·). Dictionary R3's exact source curl-energy identity then detects some free profile from `localized_curl_of_jetAggregate`.

Underlying exact normalization: sum of actual level-one direction-1 Q rows = (1/8) times the sum of the physical fine-field fluxes at the two adjacent longitudinal layers. This was derived from frozen Q1jet_flat, actual even-site tiling, and Qfull_level_one. Scalar curl telescopes transversely, and zero level-zero C2 forces zero collar-layer flux.

Still missing: a nonzero actual crossing `jetAggregate` (or directly CurlDetected), whole-kernel definiteness/KernelLine, and nested cofinal scales/radii. This result removes the tridiagonal source-column and physical-normalization obligations on the free-profile curl-energy route, NOT the crossing nondegeneracy problem.

Assembly guidance: include Flux.lean minus import; TorusAppendix.lean.txt; Coordinates.lean.txt; BlockingAppendix.lean.txt; DilatedAppendix.lean.txt. Geometry.lean.txt copies dilLu/dilTower/dil_unit_size/dil_fine_size verbatim into their original namespace: omit it when those declarations are already present. Add frozen ZXR2Flat6 import if not already available. The coordinate copies intentionally drop the unused ambient CfData instance in frozen NsPtB; no CfData premise is used.

The final named missing predicate is `DilatedFlux.TopJetDetected hq R u`: some physical top direction-1 neutral C2(WiEu) aggregate is nonzero. `neutral_localized_curl_of_topJet` specializes the main theorem to this predicate and the frozen pauliE3 functional. TopJetDetected itself is NOT proved for a crossing vector.

Full report: `AHP/round10/nonvanishing/r3/NOTES.md`. `CHECKS.json` passes all five final compilations, every declaration's standard-axiom record, 16 verbatim copied fragments, and shared byte identity. No numerics run this round.

Integration follow-up: `neutralFunctional` now uses the direct `inner_smul_right` proof instead of `simp`, following an assembly-only elaboration failure. Original/shared final files were freshly recompiled clean, unchanged statements and 82 standard-axiom records. A post-dictionary-prefix compatibility harness also compiles clean; it did not reproduce the earlier assembly-only failure before the fix, so no red/green claim is made. See the final NOTES subsection.
