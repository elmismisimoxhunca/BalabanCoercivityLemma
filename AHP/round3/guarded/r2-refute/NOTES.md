# Guarded all-plaquette reading — round 3, negative attempt 2

**closedGoal: `none`.** Neither exact pinned negative goal is proved. The new numerical family repairs the previous thin-top/Lambda obstruction, and that repair is now compiled. Numerical quotient separation is not an exact in-class counterexample.

## Compiled partial result

File: `Attempt.lean`. The entire 352-line round-3 pin is preserved verbatim as its byte prefix. Only frozen `DrEquiv` is imported; the goal definitions, guards and quantifier order are unchanged.

Main declaration: **`AdalyFormal.Round3.Guarded.RefuteR2.wide_probe_geometry_and_competitor`**, **line 584**.

For every **even natural R**, it supplies all of:

- actual `TorusOK 2 2`;
- actual `Admissible 2 2 R 1` (all six clauses, including the exact base law);
- actual `LambdaOK2 2 2 R 1`;
- a named field satisfying `OnLambdaTildeIn` and `OnLambdaT`, with strictly positive `bondEnergy`.

The lifted fine torus has sides
\[
(12R+16,8,8),
\]
and the domains and region are
\[
\Omega_0=[4,12R+12)\times T^2,\qquad
\Omega_1=[2R+4,10R+12)\times T^2,\qquad
\Omega_j=\varnothing\quad(j\ge2),
\]
\[
\Lambda=[3R+4,3R+6)\times T_u^2.
\]
The unit torus has sides \((6R+8,4,4)\). The competitor is the genuine frozen `suTwoWitness` placed at `freeBond 2 (wideSeed R)`, not an arbitrary vector in the operator carrier. Frozen free-bond lemmas prove it avoids every relevant staircase and dropped bond.

Source anchors within `Attempt.lean`:

| Declaration | Line | Scope |
|---|---:|---|
| `wideLu`, `wideTower`, `wideLam` | 377, 380, 385 | Explicit lifted geometry and Lambda |
| `wide_torus` | 388 | Torus compatibility |
| `wide_admissible` | 410 | All frozen tower conditions |
| `wide_lambda` | 489 | Both LambdaOK and block-sum clauses |
| `wideBt` | 535 | Actual single-free-bond competitor |
| `wide_competitor` | 538 | Restrictions and positive energy |
| `wide_probe_geometry_and_competitor` | 584 | Combined partial certificate |

**Not in this theorem:** coverage, regularity, any background U, capped smallness, either spectral condition, or cofinal m. Here \(\ell=M=2\) and \(k=1\), so this is only \(m=1\), despite allowing arbitrarily large even R. It is not a replacement completion goal and not a weakened proof of GoalNeg1/GoalNeg2.

## What was tried numerically

The earlier narrow top slab forced Lambda empty. Widening only Omega0 cannot repair that. This attempt instead widened Omega1 and chose a central two-site unit strip for Lambda. Integer diagnostics at R=2,4,6,18 check the base law, both block closures, strict tower collar, factor-12 site/interior-plaquette coverage, Lambda inclusion and strict Lambda collar. The first six geometric/Lambda facts needed by the main theorem were subsequently proved in Lean as described above; the **coverage diagnostics remain numerical**.

The numerical calculations use the transverse period-two quotient with sides \((12R+16,2,2)\). The proposed physical lift has transverse sides eight. **The quotient itself fails TorusOK.** No Lean invariant-sector/lift theorem identifies its spectrum with the lifted operator, and a quotient carrier being nonsingular does not certify the full lifted carrier guard. The Lean geometry certificate concerns the lift, not the quotient.

At a fixed epsilon, exterior links with neither endpoint in Omega0 carry the diagonal angle theta. The two interior defects, repeated with transverse period two, are

- link `((2R+4,0,0),1)`: `exp(epsilon E0)`;
- link `((2R+5,1,0),2)`: `exp(0.7 epsilon E1)`.

Here E0 is diag(i,-i), and E1 has off-diagonal entries 1,-1. These backgrounds are not the base-point-identity family excluded in round 2. No proof of their `ClassCoupled` membership is supplied. A separate one-spike sweep sets the second defect to identity; its regularity and exact spectral separation are also unproved.

### Boundary-mode exploration

`numerics/wide_probe.py` assembles the localized carrier B, actual-formula site projector and W, raw first jet, localized source and constraint solution H. It computes a boundary Schur complement from a **full quotient-carrier inverse**, not an inverse/compression interchange. At a numerical carrier crossing it measures the genuine polarized second jet on lifted near-zero boundary modes. Before directional differentiation, fields are restricted to the raw map's actual path edges and normalized; the quadratic scale is restored afterwards.

For epsilon=0.08:

| R | quotient carrier dimension | numerical carrier root | projected correction diagnostic |
|---:|---:|---:|---|
| 2 | 1164 | 0.5864521388182432 | one isolated near-zero mode; quadratic value about 1.024e-7 |
| 4 | 2028 | 0.5865589202175632 | four modes within 1e-8; largest projected eigenvalue about 4.656e-11 |
| 6 | 2892 | 0.5865589686166691 | four modes within 1e-8; largest projected eigenvalue about 2.110e-14 |

At R=4 and R=6 the selected four-dimensional space is **not an exact kernel**: its measured carrier residuals are about 3.31e-9 and 1.50e-12, respectively, larger than the projected correction signals. The table therefore does not establish splitting at these radii. At R=18 only integer geometry diagnostics were run, not operator assembly.

At R=2 the sparse omitted-plaquette assembly agrees with the independently assembled all-minus-in expression to about 1.17e-16. This is a numerical consistency check, not a certified error bound or operator dictionary.

### Complete quotient correction and a numerical separating candidate

`numerics/corrected_probe.py` sums the Hessians of **all 37 weighted raw output rows**, using each row's exact finite list of path edges, scatters them into fine-bond coordinates and sandwiches by the computed W. No source coefficient is pruned and no freely chosen correction matrix is substituted. Hessians use steps 0.003 and 0.001. The localized corrected matrix is C=B-D. Both B and C are inverted on the full quotient carrier before the boundary Schur complement is taken.

At R=2 the final-step observations are:

| epsilon | carrier root | corrected root | corrected minus carrier | minimum quotient-carrier eigenvalue at corrected root |
|---:|---:|---:|---:|---:|
| 0.08 | 0.5864521388182432 | 0.5864520817096952 | -5.711e-8 | 1.249e-7 |
| 0.04 | 0.5864545876123239 | 0.5864545737216755 | -1.389e-8 | 3.038e-8 |

The corrected quotient residual is about 1e-14 at each root. The correction norm is approximately 0.0333 and 0.0165. A deterministic directional comparison with the unsplit complete raw evaluator differs by about 6.06e-11 and 3.04e-11. The Frobenius difference between the two Hessian-step matrices is about 2.43e-7 and 1.21e-7; **these exceed the displayed carrier gaps and are not certified error estimates**. Root-refinement changes are recorded in `corrected_results.json`. Neither apparent convergence nor a tiny residual establishes exact singularity.

Thus these are useful **floating-point quotient candidates**, not certified full-torus carrier-unit/corrected-singular points. In particular R=2 fails the reduction's room inequality \(17\ell\le RM\), and does not defeat an eventual threshold.

### Smallness diagnostic

`numerics/smallness_probe.py` repeats the boundary-mode calculation at R=2 with epsilon=0.04,0.02,0.01, for both the two-defect and single-defect configurations. For the two-defect family, the projected quadratic values are about 2.486e-8, 6.171e-9 and 1.539e-9. The one-defect family has two near-zero modes with projected eigenvalues approximately 1.400e-8, 3.434e-9 and 8.536e-10.

The observed roughly quadratic scaling motivates a small-amplitude perturbation argument. It proves neither nonvanishing for every positive amplitude, nor regularity under every cap, nor any cofinal quantifier. The one-spike field is not silently identified with the differently located, non-repeated frozen NV spike.

## Why the negative proof stopped

The repaired geometry and a positive-energy competitor are now exact. The next missing step is **not** Lambda non-vacuity. It is a source-specific, exact spectral argument on the lifted lattice:

1. Establish the numerical background's coverage/regularity and capped smallness in Lean (coverage is only an integer diagnostic here).
2. Prove a true corrected kernel at an exact parameter and a genuine unit of the entire lifted carrier at that same parameter. A quotient eigenvalue, a Rayleigh value, or a nonzero second-jet coupling at the *carrier's* singular point does not suffice.
3. Establish the spectral separation for arbitrarily large m and then cofinally in R, with R selected **before every positive cap**. None of the numerical runs addresses unbounded m. A split at R=2 cannot refute the pinned eventual assertion.

The collar-mode diagnostics also show why simply rounding a root difference to zero/nonzero is unsafe. Larger collars make the return far smaller than the numerical carrier residual and nearby mode splittings. An analytic nonvanishing/continuation proof, plus a full-lattice operator realization, is still required. No generic matrix counterexample is offered as a substitute.

## Formula traceability

All paths in this list are under `lean/src/`, except the explicitly named round-3 pin. The supporting scripts retain their original per-operator citations.

- Geometry: `ZStatementP428.lean:42,51,58,66,73,123,130,140,189,230,286`; `ZT4A.lean:57,88`; coverage/support: `ZR2A.lean:107,121`, `ZR6A.lean:27,33`.
- `geomOf`, bond carrier and constraints: `ZXR2Wire1.lean:20`, `ZXR2Ops3.lean:26,30,50`.
- Transport, gradient, curl: `AdalyFormal/Balaban/CovariantOperators.lean:247,301,315`; holonomy: `AdalyFormal/Target/ClayStatement.lean:1286`; pairing: `AdalyFormal/Balaban/SuTwoInner.lean:104`.
- Plaquette correction and Delta: `AdalyFormal/Balaban/DeltaPrime.lean:125,133`, `AdalyFormal/Balaban/DeltaPrimeOperator.lean:287–395`, `ZLocOps.lean:119,181,186`.
- Laplacian, site constraints/projector: `R2Ops1.lean:108,135,141,150,166,170`; padded inverse, W and gauge term: `ZR2Ops2.lean:27,63,67,100`.
- Raw map/jets: `R2Raw1.lean:36,43,68,74`, `R2RawX.lean:187`, `ZLocJet.lean:35,39,89,100`, `ZXR2Sector.lean:97,109`. Blocking/staircase/exp-log: `AdalyFormal/Balaban/UbarTowerCovariance.lean:237`, `AdalyFormal/Balaban/TowerLawCovariant.lean:171`, `AdalyFormal/Balaban/SuTwoLogExpCore.lean:164,226`.
- Source: `ZLocJ.lean:20,49,71`, `AdalyFormal/Balaban/SourceJ.lean:228`, `D1Lit.lean:56,59`.
- Mass/base data: `ZXR2Ops3.lean:98,102,134`; carrier, H and correction: `R2Algebra.lean:145,149,212,220,222`.
- Pinned response/shift/corrected operator: `AHP/round3/guarded/pin/Statement.lean:273,290,293`. The numerical Schur matrices are not redefined as these exact range-Theta responses.

## Verification and replay

Final Lean command, exclusively through the required lock wrapper:

```sh
LEAN_NUM_THREADS=1 AHP/round3/lean1.sh AHP/round3/guarded/r2-refute/Attempt.lean
```

Final exit **0**, no errors or warnings. Evidence: `Attempt.lean.log`, `Attempt.lean.exit`, `CHECKS.json`. All **56 local declarations** have individual dependency records; ten directly reused frozen helpers are printed too, for **66 records**. Every list is a subset of the permitted three. The main record is:

```text
'AdalyFormal.Round3.Guarded.RefuteR2.wide_probe_geometry_and_competitor' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Source SHA-256:

```text
139becc32cb7b989461b3ac9358d3c496d8843425966c6f559a263edb3e1e819
```

The first compile rejected elementary divisibility/simplification and dependent-rewrite steps; these were fixed. The next compile succeeded with style warnings; the final compile removed those warnings. No failed compile is counted as evidence. There was no independent second-agent replay or whole-project rebuild.

All three numerical drivers ran via `"$BB_CLI" heavy run --`, with `OPENBLAS_NUM_THREADS=1`, `OMP_NUM_THREADS=1`, `PYTHONDONTWRITEBYTECODE=1`. Their final exit files report zero. Each process sets a 1900 MiB address-space cap, below 2 GB. Maximum measured RSS across the runs: **780976 KiB**. Replay each driver using:

```sh
"$BB_CLI" heavy run -- env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 AHP/round3/guarded/r2-refute/numerics/wide_probe.py 2 4 6
# Replace the driver with smallness_probe.py or corrected_probe.py for those runs.
python3 AHP/round3/guarded/r2-refute/validate.py
```

Each driver has sibling `.log`/`.exit` files and a named results JSON. `assembly.py` and `delta_ops.py` are byte-identical copies of the earlier attempt's helpers; their historical standalone main programs were not run. The earlier scripts' `positive_competitor_not_certified` output flag records that the numerical script itself supplied no such proof; the later Lean theorem supplies it for the lifted geometry.

`validate.py` checks the exact complete pin prefix, sole frozen import, prohibited-token scan, fresh successful compilation, complete local print coverage, permitted dependencies, numerical exits/memory and agreement of the recorded geometries with the explicit Lean definitions. Those script checks do not certify numerical eigenvalues or class membership.

All authored files are under `AHP/round3/guarded/r2-refute/`. No protected file, other AHP path, Lake configuration, paper, note or expected result was edited. No direct Lean/Lake invocation, build, reproduction, dependency update, deletion, commit or push was performed. The supplied fresh reproduction and the pin's reading qualifications are inherited context, not newly repeated audits.
