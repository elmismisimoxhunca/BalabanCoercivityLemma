# Dictionary r1 hand-off — partial, GoalNeg2 OPEN

`R1_Dictionary.lean` is standalone (1345 lines, sole import frozen `DrEquiv`). Its own wrapper compilation exits **0**, no errors or warnings; 84 axiom records, all within `{propext, Classical.choice, Quot.sound}`. It is byte-identical to independently compiled `AHP/round10/dictionary/r1/Actual.lean`. Audit: `AHP/round10/dictionary/r1/CHECKS.json` (pass, 58 dictionary declarations with individual records).

## Proved on the named actual operators

Namespace `AdalyFormal.Round10.Dictionary.Actual`:

- `bulkD_U1`: finite-curvature correction commutes with every diagonal rotation.
- `corrDeriv_U1`: actual round-9 corrDeriv commutes, every q,R,profile,angle; no added regularity premise.
- `corrDeriv_U1_form`: quadratic-form invariance.
- `corrDeriv_no_charge_cross`: neutral/charged off-diagonal pairing is zero.
- `bulkB_U1`: actual localized B commutes.
- `vacuum_kernel_charge_split`: full canonical vacuum kernel splits orthogonally into the +1/−1 eigenspaces of the diagonal half turn. **No assertion that either summand vanishes or has dimension two.**
- `twist_deltaK_twoSite`: actual curved twist's all-plaquette **undressed Hessian** commutes with the round-6 two-site pullback.

The general dictionary also proves all-plaquette/localized carrier U(1) symmetry, H/C2 equivariance, and differentiation-preserves-commutation. It includes the original round-9 vacuum U(1) theorem verbatim.

## Spatial layer and what is not done

Namespace `.Translation` proves exact pullback covariance of frozen gradient, divergence, Laplacian, masks, curl, plaquette holonomy, the full curvature-dependent bilPlaq form, and deltaKLocCLM on invariant plaquette sets. No compressed inverse is used.

**Missing:** spatial transport of Qlev and nonlinear blocking paths/jets, hence translation of Rproj/Gp/W/Q/T and assembled A/B/corrDeriv; full transverse Fourier decomposition; block dimensions; crossing-kernel exclusion of all other characters; one-complex-line simplicity; nonzero coupling. None of the cofinal premises is proved.

## Correct the proposed exact dilation

`kscan.py` tests normalized limiting K with exponentially small finite-core tails, not an exact finite-volume q=1 isometry. Matching canonical q geometry with canonical q=1 radius R' would require

\[
2R'=2Rq,\qquad 8R'+8=(8R+8)q.
\]

`no_canonical_radius_dilation` proves these imply q=1. This is a length-matching obstruction, not a theorem excluding every abstract isometry. A generalized Bloch cell with independently specified collar/core lengths is the correct candidate for an exact local-stencil dictionary; it is not formalized yet.

## Next-round question

Nonvanishing's new source-dominance result suggests prioritizing the exact neutral source equations for H0*J' over an indiscriminate full Fourier development. Please pin the coarse-bond component/index offset and normalization of v0, and whether the requested crossing vector is left-only or symmetric. Full details and exact outstanding Lean statements: `AHP/round10/dictionary/r1/NOTES.md`.

The full historical round-9 concatenation was killed once by the host's 8 GiB command-memory cap and is not counted as compiled. The successful compact file copies only necessary prior declarations verbatim; `COPIES.json` audits them. No GoalNeg2 closure is claimed.
