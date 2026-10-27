# Nonvanishing R4 — final hand-off

**GoalNeg2 and every original cofinal coupling premise remain OPEN.**

Published `R4_PolynomialCertificate.lean` (306 lines), independently compiled with clean exit 0. Local `PolynomialGrid.lean`, `MovingRoot.lean`, and `SeedObstruction.lean` also compile clean. All 29 distinct declarations individually audited; only propext, Classical.choice, Quot.sound. `nonvanishing/r4/CHECKS.json` passes.

## New finite certificate route

Namespace `AdalyFormal.Round10.Nonvanishing.PolynomialGrid`:

- `geometric_grid_ne_zero_eventually`: a nonzero bivariate polynomial P is nonzero at x=rho^(2^j), y=rho^((2^j)*R) for all sufficiently large j and, at each selected j, all sufficiently large R, assuming 0<rho<1. The quantifiers are nested, not diagonal.
- `geometric_grid_ne_zero_of_seed`: one exact nonzero evaluation of P, even off the physical grid, gives the required cofinal dyadic/even-radius form.
- `no_common_root_of_bezout`: U*A+V*B=C(P), A(x,y,t)=0, P(x,y)!=0 imply B(x,y,t)!=0. This allows arbitrary volume-dependent crossing roots t.
- `moving_root_cofinal_nonzero`: `MovingRootCertificate coupling` implies nested cofinal nonvanishing of coupling(2^j,R). The certificate explicitly contains the fixed polynomials, exact Bezout identity, nonzero seed of P, actual moving-root equation, and cleared numerator identity.
- `quotient_cofinal_nonzero`: the direct rational-function alternative, with nonzero denominators explicit.

**No such certificate is supplied for the actual coupling.** Multiple independent transfer roots, varying momenta, and inverse/jet identities are not implicitly covered by assuming one polynomial in these two geometric variables. No whole-kernel definiteness follows from this abstract scalar result.

## Exact warning / obstruction

`sample_no_nonzero_bezout` and `switchingRoot_not_cofinal` formalize the example A(T)=T(T-1), B(T)=T. The exact root T=1 gives a nonzero sample; T=0 is a common root. Choosing T=1 only at (q,R)=(2,18), and 0 elsewhere, gives an exact nonzero admissible-grid sample but no cofinal nonvanishing. Thus an exact sample of B plus an algebraic crossing equation is not a common-root-exclusion certificate. This is an obstruction to that shortcut, **not a refutation of the actual coupling premise**.

## Unchanged actual gap

R3 still provides the strongest actual-operator implication: TopJetDetected -> localized neutral curl -> some free-profile coupling, with the known flat constraint unit visible. Crossing-specific TopJetDetected/CurlDetected, whole-kernel charged-line containment or another common-profile definiteness proof, and nested cofinal coverage remain unproved. Dictionary R4's subsequently compiled `ColorObstruction.exists_charged_invisible` goes further: for every q>0,R there is an actual nonzero charged field with zero full jet and zero coupling to every profile. I inspected its statement/construction, exit 0 and standard-axiom record in `dictionary/r4/Actual.lean`; I did not independently recompile it. This field is NOT asserted to be a crossing field, so it refutes only the nonzero-plus-charged shortcut, not the actual premise.

Exact Lean statements, proofs in plain mathematics, limitations, and reproduction: `AHP/round10/nonvanishing/r4/NOTES.md`. No new numerics, large historical compile, build/REPRODUCE, protected edits, commits, pushes, or removals.
