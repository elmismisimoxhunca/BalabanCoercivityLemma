# Dictionary round 2 — actual J' stencil and neutral H0*J'

**GoalNeg2 remains OPEN. No cofinal coupling premise or actual tridiagonal source formula is proved.**

Published: `R2_SourceDictionary.lean`, independently compiled at this path and as `../../dictionary/r2/Source.lean`, both exit **0**, no warnings/errors. Sole import: frozen `DrEquiv`. Audit: 63 new declarations plus one reused dictionary declaration, 88 dependency records, all subsets of `{propext, Classical.choice, Quot.sound}`. Full report: `AHP/round10/dictionary/r2/CHECKS.json`.

## New actual-operator results

1. **Finite-curvature source formula.** `PhaseSource.JSU2Loc_phase` expands the actual localized JSU2 source of an arbitrary diagonal phase field into the antisymmetric plaquette sine-circulation followed by the backward-minus-forward divergence, times the frozen norm-one E3. The mesh-one source sign is fixed exactly.
2. **Explicit J' for the actual canonical family.** `Source.canonical_isSourceDerivative` (published line 1015) proves, for every q,R with no hypotheses:

   ```lean
   IsSourceDerivative q R (canonicalSourceStencil q R)
   ```

   The stencil is `pE (sourceLinear (plaqIn Ω0) fhat)`, where fhat is `dilMask` zeroed on the exterior, and `sourceLinear` is the explicit linear circulation/divergence formula. `sourceDerivative_eq_stencil` (1027) identifies every J' satisfying the exact round-9 predicate with this stencil. Arbitrary profiles have the same explicit first-order limit (`bulkSource_tendsto`).
3. **Full H0*J' is neutral.** `Source.neutralSource_U1` proves it is fixed by all diagonal phases. `neutralSource_component` identifies every physical component as its E3 coefficient times E3. No compressed inverse, Fourier assumption or unit hypothesis is used for these symmetry facts.
4. **Exact physical scalar sum.** `vacCoupling_neutral_top_sum` (910) expresses the actual analytic `vacCoupling` as `2 * sum` of neutral source and jet coefficients over physical level-one BIdx rows. Level-zero C2 is proved zero; source level-zero components are not assumed zero. `vacCoupling_U1` (931) proves phase invariance of the explicit H0-C2-J' form.

## Inverse-free interface for the next source step

`KKT.source_of_certificate` and its actual specialization `Source.flat_source_of_certificate` (948) prove:

\[
Qx=0,\quad Bx+Q^*h=J'\quad\Longrightarrow\quad H^*J'=h,
\]

assuming the two flat-point units B and Q B^{-1} Q*, already supplied by round 9. There is also a weak residual form and a direct coupling form. **These certificate implications are conditional; no physical certificate x,h has been constructed.**

`KKT.two_site_residual_iff` verifies the exact rational normalization linking the proposed recurrence to a scalar two-site residual:

\[
(3a+\ell)/2+h/8=d/2,\quad -(3a+r)/2+h/8=-d/4
\quad\Longleftrightarrow\quad
6a+\ell+r=3d/2,\quad h=d-2\ell+2r.
\]

This is not the missing physical lift theorem. In particular, a represents twice the fine alternating amplitude in this scalar normalization; the actual full-lattice Q* coefficient and discarded transverse components still need checking.

## What is still needed / question for nonvanishing

The exact proposed Lean source target is written in `AHP/round10/dictionary/r2/NOTES.md` §4. It asks for a finite recurrence sequence of length `4*q*(R+1)` and physical x,h satisfying the two residual equations with **the now-proved explicit J'**, and h's level-one direction-1 components equal to `δj0 - 2*a(j-1) + 2*a(j+1)` at longitudinal offset `2*R*q+4*q+2*j`. The other top directions must vanish. No full transverse Fourier theory is needed merely to state/check this certificate.

Can nonvanishing use the physical jet aggregated over level-one direction-1 rows at each longitudinal block, rather than a normalized numerical cell jet? Please pin the embedding that gives Q* coefficient h/8 and the factor between a and the fine alternating amplitude. Next priority is proving the physical certificate, then its jet dominance/nonzero seed.

Full-kernel definiteness, competing-character exclusion, cofinal nonvanishing, spatial covariance of the assembled W/Q/T/carrier, and the character splitting remain open. The canonical q=1 radius-isometry claim remains withdrawn.

Development files: `PhaseSource.lean` (243 lines, exit 0), `KKT.lean` (100 lines, exit 0), `SourceAppendix.lean` (fragment), compact builder and copy manifest in `AHP/round10/dictionary/r2/`. The published combined file has 1055 lines. No numerics, large assembly, build/REPRODUCE, commit or push was run.
