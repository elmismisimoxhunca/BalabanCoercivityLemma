# Round 11 / large-a / round 2

## Verdict

**closedGoal: none.** Neither `Round11.GoalLargeA`, its negation, nor an unrestricted fixed-large-mass slice has been proved.

There is now a genuinely **unguarded restricted large-mass theorem**, not just base-carrier domination:

**`Round11.LargeA.base_flat_large_mass_slice`**, `Attempt.lean:1601`, proves the original all-threshold touching slice for every blocking factor \(\ell\ge2\) and every \(a\ge272\), with exactly one additional background restriction:

\[
  U(e)=1\quad\text{whenever the base point of }e\text{ belongs to }\Omega_0.
\]

Exterior bonds and bonds entering the domain are arbitrary SU(2) links. The original `ClassCoupledFour` premise, proper and full domains, all tori, all k, the m/R threshold order, positive cap and coercivity constant, corner-selected Delta **and** J, and the full mass-subtracted final form are retained. There are **no inverse-guard hypotheses** in this restricted theorem.

Thus changing exterior links alone while leaving this interior flat cannot refute the headline at arbitrarily large mass. **272 is a sufficient, nonoptimal bound for this restricted family**, not an identified sharp transition and not a proved threshold for the whole four-bond class.

## What is new beyond round 1

The 136 curvature bound and 272 half-mass absorption estimate from `largea-r1` are retained verbatim. The new work resolves the algebraic corrected-guard problem that round 1 left open:

1. **`H_shift_on`**, line 1019: adding \(Q^*KQ\) to a carrier changes its Lagrange multiplier but not its constrained lift H, when the genuine base and base-Schur inverses exist. The proof works on a subspace containing the relevant constraint fibres.
2. **`Delta2_shift`**, line 1058, and **`local_base_shift`**, line 1292: the genuine localized correction is invariant under raising the mass, under the stated site units and localized base positivity/unit premises. This uses the actual weighted mass factorization `dataS_Mass_factor`, not a scalar-identity replacement.
3. **`corner_base_and_correction`**: identifies the corner correction with the localized half-mass correction using base guards only. No corrected corner guard is used circularly.
4. **`corrected_guards_transfer`** and **`corner_corrected_guards`**: positivity domination gives the corrected unit; agreement on the actual kernel of Q transfers its constrained inverse unit.
5. **`corner_wellDef_of_local_half`**, line 1349: all three corner guards follow from localized half-mass PSD of both carriers, localized half-mass well-definedness, and the two site units.
6. **`corner_wellDef_proper`**, line 1377: eliminates both site-unit hypotheses on proper domains using frozen `CoverOmega.delpA_unit`. This works for arbitrary backgrounds and positive mass; class smallness is not needed for these site units.
7. **`dataS_corner_eq_of_full` / `genForm_corner_eq_of_full`**: on full domains both selectors coincide, including the corrected inverse and both source terms. Consequently the full-domain branch needs no site-unit argument.
8. **`test_zero_of_local_bad_guard`**: if the localized half-mass data are not well defined, the positive localized headline forces every admissible competitor to vanish. This handles the bad-guard branch without assuming nonvacuity or nonempty Lambda.
9. **`touch_instance_of_half_positive`**, line 1440: actual pointwise unguarded transfer, with no corner guards or site units assumed. Only the two localized half-mass PSD assertions remain, and only in the proper-domain/well-defined-half-mass branch.
10. **`touch_slice_of_eventual_half_positive`**, line 1514: supplies the exact pinned `P428TouchFourAt`, conditional on the explicitly defined analytic input below. The proof intersects the frozen headlines at a and a/2 with the positivity thresholds. The source class inclusion is the compiled `ClassCoupledFour.toFrozen` proof.
11. **`local_base_psd_of_base_flat` / `local_both_psd_of_base_flat`**: discharge both localized PSD assertions for the entire base-point-flat family. Localized Delta is PSD there; frozen `G1invS_eq_Ginv_base` removes the correction. Applying item 9 and intersecting the two frozen headline thresholds gives `base_flat_large_mass_slice`.

## Exact remaining obstacle

`EventualHalfPositive` (`Attempt.lean:1497`) records the remaining input with all uniform quantifiers. For every sufficiently large m, then every sufficiently large R, there must be a positive cap such that, on the small-cap four-bond class, **if the domain is proper and the localized half-mass data are well defined**, then

\[
  G^{-1}_{\mathrm{in}}(a/2)\succeq0,
  \qquad G^{-1}_{1,\mathrm{in}}(a/2)\succeq0.
\]

This proposition is **defined, not proved**. `goalLargeA_of_eventual_half_positive` is only a conditional implication with it as an explicit hypothesis, not a closure of `GoalLargeA`.

Compared with round 1, there is no longer an unresolved corner corrected-guard implication, mass-shift identity, constrained inverse transfer, or site-unit extraction on proper domains. What remains is the uniform *analytic positivity* of both frozen localized carriers across the full curved class. The headline inequality by itself does not state either of these PSD properties.

A concrete next route is to export the existing localized coercivity evidence from the frozen construction: `RI6.thin_core_RI`'s internal thick-case `hcoer` and `hDS.1`, together with `MI21.G1inv_coercive_strat`, contain the relevant positive quadratic bounds. They must be assembled with uniform caps and transported through localization and thin-torus descent (`Thin.BDLink.ginv`, `Thin.BDLink.G1inv`, and the cover inner-product identities). The unrestricted all-tori export was **not implemented or verified here**. Do not infer it merely from the fact that the frozen headline compiles.

The all-positive-mass refutation question therefore remains open for curved interiors. No claim is made about the sharp threshold between the refutation track's low-mass windows and this restricted upper bound.

## Validation and scope

- Final file: `AHP/round11/largea-r2/Attempt.lean`, 1,638 lines.
- The 8,342-byte pin is embedded **verbatim exactly once**, following only frozen imports.
- Both `Attempt.lean` and its identical independent copy `Attempt.verify.lean` compiled with exit code **0**, using only `AHP/round3/lean1.sh <file>` directly with a 1,200-second timeout. No compilation in this continuation timed out.
- All **95 explicit declarations** have `#print axioms`; both logs report only subsets of `propext`, `Classical.choice`, `Quot.sound`.
- `AUDIT.json` records matching source hashes, pin bytes/hash, declaration coverage, frozen-only imports, and the forbidden-token scan. `audit.py` reproduces the audit without compiling.
- Final source SHA-256: `25838972ed3189ff4f252f52c3f4525fe7429a56e1df00d32dd89c18a7ac5410`.
- Main axiom line: `'Round11.LargeA.base_flat_large_mass_slice' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- No numerical experiment, `lake build`, reproduction script, git commit/push, protected-source edit, integration-checkout edit, or worktree operation was performed. Final sources, notes, audit and compiler evidence are retained; intermediate diagnostics are removed only inside this track directory.
