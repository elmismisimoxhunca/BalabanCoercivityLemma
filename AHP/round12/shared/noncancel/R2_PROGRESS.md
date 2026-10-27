# Noncancel R2 — finished partial result; target still open

## Verified publications

All have independent `.lean.log` and `.lean.exit=0`:

- `R2_Boundary.lean`: arbitrary-field `W=A` on all omitted-plaquette edges,
  without an inverse-unit premise; nearby singleton `T=0`, `W=A` in every orientation.
- `R2_FullPlaquette.lean`: exact frozen three-atom forms for full `SuTwo`,
  including the neutral square, and the full-color pair mass inequality.
- `R2_Mass.lean`: actual level-zero row identification and extraction of any
  DISTINCT finite leaf set from the physical mass, with nonnegative remainder.
- `R2_RightFamily.lean`: exact original `vacA`/right-star identification, path
  analyticity/continuity/zero start, and negative pi endpoint for every q>0,
  even R>=18. `cofinal_rightStar_paths` proves all target path-validity clauses
  with the final noncancellation conjunct deliberately omitted.
- `R2_StarLocal.lean`: compact joined certificate, 1372 lines, 78 standard
  axiom records. Local and shared independently compile.

`R2_NOTES.md` records exact remaining Lean propositions. `R2_AUDIT.json`
records ten current certificates, hashes, and their axiom lists. No new numerical
claim, no target theorem, and no counterexample to the target.

## Remaining physical gaps

1. Actual negative trial at pi/2 for the same right-star family (pi endpoint is
   proved, but it is not the needed half-pi endpoint).
2. Complete carrier-form decomposition / distinct eight-leaf accounting and
   strict positivity on the zero-central-charged-coordinate subspace for
   0<t<pi/2. The neutral square must not be dropped.
3. Actual crossing-specific `CurlDetected` (or a direct full-kernel
   noncancellation proof). Chargedness and numerical small nonzero jets do not
   establish this.
4. Cofinal assembly of these still-missing physical facts.

Kernel R2 now supplies compiled automatic first-crossing/kernel existence from
(1)-(2) plus its explicit continuity/symmetry/positive-start/gauge premises,
and a direct original `KernelLine` + `CurlDetected` -> `NoResponseCancellation`
bridge without `RegularityFacts`. Their existence does not solve (1)-(3).
