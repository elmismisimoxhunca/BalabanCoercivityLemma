# Round 9 results: the guarded reading is still open

## Decision

**No verified attempt proves the pinned `GoalNeg2` or `GoalNeg1` without extra hypotheses. The guarded all-plaquette reading is therefore not refuted in Lean by round 9.** Nor has it been proved true.

`GoalNeg2` is the negation of `P428Target8SG selAll selAll`. `GoalNeg1` is the negation of the guarded pencil statement. A theorem saying “if X, then GoalNeg2” is not a refutation while X remains unproved. Standard axioms do not discharge that hypothesis.

All four final attempt files have recorded compiler exit 0, unchanged statement-pin prefixes, and logs without errors, warnings or `sorryAx`. Their audits report only `propext`, `Classical.choice` and `Quot.sound` (or no axioms). The qualitative attempts additionally have independent, byte-identical recompilations: both verification reports say **does-not-close**, because the main theorem has an extra hypothesis. The supplied analytic verification fields are null; their successful compilation and audit are not an independent unconditional-goal verification. The qualitative round-2 file also compiles snapshots of the analytic appendices, not necessarily their latest live versions.

For this report, the source hashes, pin prefixes, recorded exits, log diagnostics and equality of the qualitative verification copies were checked on disk. No new Lean compilation was run.

## Analytic route

### Round 1

`analytic-r1/Attempt.lean:4539` compiles
`goalNeg2_of_interiorSoft_vacuumLeftSpectral : InteriorSoft → VacuumLeftSpectral → GoalNeg2`.

It also compiles abstract separation near a vacuum kernel, bridges from cofinal vacuum separation, and joint continuity using the frozen exterior-path formula. Two premises were left: soft interior regularity and the left-twist vacuum spectral crossing/coupling statement. This was a conditional reduction only.

### Round 2: soft regularity is discharged, spectral coupling is not

`analytic-r2/Attempt.lean:7608` compiles
`goalNeg2_of_vacuumLeftCouplingD : VacuumLeftCouplingD → GoalNeg2`.

Unconditional progress includes `interiorSoft_proved` (line 7282), the explicit first-order correction form `dil_D1_form` (6904), existence of the vacuum angle derivative (7522), and positivity at the trivial exterior angle (7541). The round-8-twist analogue also conditionally implies `CofinalTwistSeparation` (7632).

**Exact remaining premise:** `VacuumLeftCouplingD` (7591). For every lower scale bound there must be a dyadic scale \(q=2^j\) above it; for each chosen scale and every lower radius bound there must be an even \(R\ge18\) above it. At each such instance, for every derivative \(J'\) of the localized source (existence and uniqueness are established), the left exterior twist must have an angle \(t_0\) such that:

1. The vacuum all-plaquette carrier \(A(0,t_0)\) has a nonzero kernel.
2. Its angle derivative is strictly negative on every nonzero vector of that kernel.
3. The form \(v\mapsto2\langle H_0 C^2_0(W_0v),J'\rangle\) is strictly positive on the whole nonzero kernel, or strictly negative on the whole nonzero kernel.

This is a cofinal spectral/nonvanishing assertion, not an assumption of positive-curvature regularity. It remains unproved. The proposed character reduction, identification of the crossing kernel, and nonzero coupling with finite-size control are not a finished proof. Numerical sector screens and exponentially small nonzero values do not establish these quantifiers.

## Qualitative route

### Round 1

`qualitative-r1/Attempt.lean:4680` compiles
`goalNeg2_of_cofinalVacuumCoupling : CofinalVacuumCoupling → GoalNeg2`.

The remaining premise requested cofinally many dyadic scales and even radii, some continuous exterior path and a bounded interior profile, with a vacuum sign crossing, soft regularity and definite first-order coupling on the crossing kernel. Abstract first-order separation and profile reflection compiled. Independent verification confirmed compilation, but not goal closure.

### Round 2: regularity and canonical crossing are discharged

`qualitative-r2/Attempt.lean:11729` compiles
`goalNeg2_of_cofinalCanonicalCoupling : CofinalCanonicalCoupling → GoalNeg2`, through `CofinalTwistSeparation` (11716).

Unconditional progress includes soft regularity and the actual two-sided correction derivative for every profile, every positive scale and even \(R\ge16\) (11653); the canonical round-8 vacuum crossing (11677); and separation for all sufficiently small positive curvatures **conditional on the per-instance coupling** (11699). The route also supplies the gauge flip and a charged-complex-line reduction, and uses the analytic route's flat-unit and smooth-family results.

**Exact remaining premise:** `CofinalCanonicalCoupling` (11711). With the same nested cofinal scale/radius quantifiers as above, the actual derivative
\[
D_e=\left.\frac{d}{d\varepsilon}\right|_{0}\mathrm{bulkD}(q,R,\mathrm{dilMask},\varepsilon)
\]
must be definite on the kernel of the round-8 vacuum carrier at `vacEdge`, the end of its initial positive-semidefinite interval in \([0,\pi]\). Precisely, some \(c>0\) must bound \(\langle u,D_eu\rangle\) below by \(c\|u\|^2\) for every kernel vector, or bound its negative below that way.

No regularity, crossing, slope, gap or prescribed-sign premise remains in this reduction. Definiteness itself remains unproved. It becomes the scalar condition \(c_1(q,R)\ne0\) only after identifying the kernel as one charged complex line; that identification must not be assumed from numerical screens.

Weaker conditional reductions also compile: `CofinalAnyProfileCoupling → GoalNeg2` (11906) allows some real profile; `CofinalAnyPathCoupling → GoalNeg2` (12102) additionally allows some continuous real-analytic exterior path starting at the trivial field and having a vacuum negative direction at \(\pi\). The latter still requires definite coupling on that path's canonical kernel at cofinally many instances. Neither premise is proved. Independent verification again rejects unconditional closure.

## Inverses at the proposed failure point

There is **no unconditional cofinal counterexample from this round**. The following describes the failure point produced **if the remaining coupling premise is supplied**, not a newly verified witness family.

Write \(A\) for the all-plaquette carrier and \(D\) for the localized correction. The separation conclusion is
\[
A\text{ is a unit},\qquad A-D\text{ is not a unit}.
\]
The qualitative construction can put the failure before the carrier crossing, where \(A\) is positive definite. The analytic separation theorem requires only that \(A\) be a unit. Neither construction uses the singular vacuum carrier at the reference crossing as the guarded failure point.

**Not every inverse in the printed construction exists there.** The distinction is:

- **Uncorrected all-plaquette inverse:** \(G=A^{-1}\) is a genuine inverse, so the pinned carrier guard is satisfied.
- **Localized data:** in the admissible small-curvature regime used by the bridge, localized `WellDefAt` supplies genuine inverses of the localized carrier, its corrected carrier, and its corrected constraint matrix. The uncorrected localized constraint matrix \(QG_{\rm loc}Q^*\) is also a unit. Thus the localized \(H\) used to define \(D\) is not obtained by collapsing a singular inverse to zero.
- **Uncorrected all-plaquette constraint inverse:** \((QGQ^*)^{-1}\), used in the all-plaquette \(H\), is genuine under these bridge hypotheses. This is not inferred merely from “A is a unit”: `DrRed1.Delta2_lit_eq_loc` transfers the constraint-unit property from the localized data. It then identifies the literal correction with \(D\).
- **Corrected all-plaquette inverse:** the same bridge identifies `G1invS selAll selAll` with \(A-D\). This operator is singular at the proposed failure point. Its genuine inverse **does not exist**. Lean nevertheless defines `G1` using `Ring.inverse`, which is zero on non-units; hence `G1 = 0` there.
- **Corrected all-plaquette constraint inverse:** `NmatS = Q G1 Q* = 0`. On the nontrivial coarse space used for the positive-energy test this has no genuine inverse. `Ring.inverse NmatS` is zero by totalisation, and `H1` is zero as well. The literal generated form consequently collapses to \(-a\langle B,B\rangle\); this is how the guarded inequality fails in the formal reading.

The smooth-family work also checks genuine flat-point inverses for the Dirichlet operator defining \(G'\), the gauge Gram matrix, the localized carrier and the localized constraint matrix; continuity keeps the required units for sufficiently small interior curvature. These auxiliary results do not restore either missing corrected all-plaquette inverse. Scalar normalisations such as \(\ell^{-1}\) and \(\eta^{-1}\) are harmless here: \(\ell=2\) and \(\eta>0\).

Thus the conditional construction attacks the **carrier-only guarded, totalised Lean reading**. It is not a counterexample satisfying the stronger demand that every printed inverse exist, nor does it refute a statement additionally guarded by full all-plaquette `WellDefAt`. See `lean/src/IngredientG1H1.lean` for `G`, `H`, `G1`, `H1`; `lean/src/DrRed1.lean` for the transfer and pencil identity; and `lean/src/GdGap.lean` for the full guard and collapse distinction.

## Bottom line

Round 9 removes substantial regularity work and, on the qualitative route, the crossing hypothesis itself. What is still missing is a proved cofinal nondegeneracy/coupling statement. No unconditional pinned negative goal has been verified. Even if that gap is closed using these reductions, the resulting failure has a genuine carrier inverse but singular corrected operators handled by totalisation—not every inverse in the printed construction exists.
