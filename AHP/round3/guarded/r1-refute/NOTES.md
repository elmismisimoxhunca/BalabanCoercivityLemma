# Guarded all-plaquette reading — round 3, negative attempt 1

**Closed goal: none.** No exact in-class carrier-unit/corrected-singular configuration or cofinal family was constructed. Neither pinned negative goal has been weakened or proved.

## What was tried

The round-2 side-eight candidate is formally inadmissible and uncovered. This attempt instead tested block-aligned depth-one slabs with wider base collars, then checked the separate Lambda/test-field obligation. That check reveals another concrete obstruction: these new slabs have a top domain too narrow to admit any compatible nonempty Lambda.

The new numerical family has ell=M=2, k=1, a=1 and, at R=2,6,18,

\[
N=4R+16,\quad \Omega_0=[4,4R+8)\times T^2,\qquad
\Omega_1=[2R+4,2R+8)\times T^2,
\]

with higher domains empty. The proposed genuine fine torus has sides (N,8,8). The script evaluates a **period-two transverse quotient** with sides (N,2,2), not the full lifted carrier. The quotient itself fails TorusOK. No Lean invariant-sector/periodic-lift identification is proved; no full-torus guard is inferred from quotient eigenvalues.

In the lifted slab, exhaustive one-dimensional arithmetic checks the base law, block closure and strict collars. At R=6 and 18, it also finds common factor-12 level-zero cubes covering every base site and interior plaquette (3 and 27 possible x-intervals, respectively). At R=2 coverage fails. These are arithmetic diagnostics, **not compiled Admissible or ClassCoupled theorems**. The reduction's room inequality \(17\ell\le RM\) fails at R=2,6 and holds arithmetically at R=18; none of these is an eventual-threshold certificate. Transverse directions are full; the proposed cubes wrap those directions. This repairs the particular block-alignment and coverage mistakes of the earlier probes at the numerical level, not all headline hypotheses.

Links with neither endpoint in Omega0 carry the diagonal exterior angle. The only interior defects, repeated with transverse period two, are

- base (2R+4,0,0), direction 1: exp(0.08 E0);
- base (2R+5,1,0), direction 2: exp(0.056 E1).

E0=diag(i,-i), E1=[[0,1],[-1,0]]. This is not the base-point-identity family. Theta varies exterior links only. No arbitrary finite difference of Delta is substituted for Delta2.

## Numerical method and results

Files: `numerics/collar_probe.py`, `assembly.py`, `delta_ops.py`; result `collar_results.json`, log `collar_probe.log`, exit `collar_probe.exit`.

`assembly.py` and `delta_ops.py` retain round-2 formula transcriptions and their source anchors. The driver forms the actual-formula localized carrier, the site projector and W, localized source, raw first jet, and a polarized finite-difference second jet. Top H*J is computed by enforcing all level-zero constraints to be zero, then solving on their complementary coordinates. This is an algebraic/numerical implementation, not a Lean dictionary theorem. The correction is localized numerically by pruning coefficients below 2e-13; this is explicitly **not an exact locality proof**.

The driver uses a boundary Schur complement and a Woodbury update, not inversion of a compressed operator relabelled as a compressed inverse. With E the boundary inclusion and F the selected correction-support inclusion it computes

\[
G_{bb}=E^TB^{-1}E,\quad G_{bi}=E^TB^{-1}F,\quad
G_{ii}=F^TB^{-1}F,
\]
\[
E^T(C^{-1}-B^{-1})E
=G_{bi}(I-DG_{ii})^{-1}D G_{bi}^T.
\]

Here D in the last formula is the numerically selected correction matrix. The computed Schur matrices are `inverse(Gbb)+Theta_bb` and `inverse(Gbb+update)+Theta_bb`. This support-selection reduction is numerical, not the pinned range-Theta response identity proved in round 2.

| R | quotient carrier dimension | boundary-to-correction Green norm | boundary Green update norm | estimated corrected root minus carrier root |
|---:|---:|---:|---:|---:|
| 2 | 444 | 8.24e-2 | 1.09e-6 | +2.49e-8 |
| 6 | 1020 | 3.70e-5 | 2.24e-13 | +5.66e-15 |
| 18 | 2748 | 3.44e-15 | 1.94e-33 | -1.67e-15 |

The last two root differences are not resolved evidence of distinct roots; at R=18 the displayed root difference is vastly larger than the calculated perturbation and reflects floating-point sensitivity. No exact zero, inverse, interval guard, or inequality failure follows from this table. Even at R=2 the quotient guard on the full lifted torus is unproved and coverage fails.

Observed consistency checks: omitted-plaquette sparse assembly versus the dense all-minus-in expression at R=2 differs by 2.35e-17 or less; the second-jet Hessian difference between steps 0.003 and 0.001 has norm about 6.44e-8. The correction norm is about 0.0334. These are observed errors, not certified bounds. The boundary space used numerically has 72 real coordinates for these samples; it is not proved to equal the exact range of Theta.

The completed run exited 0, under a 1900 MiB address-space cap (strictly below 2 GB). Maximum recorded RSS: **521120 KiB**. The successful run took about 381 seconds excluding slot wait. An earlier foreground run was interrupted before R=18 and produced no exit record; its partial log and JSON are labelled `interrupted*` and are not the verification run.

Replay:

```sh
"$BB_CLI" heavy run -- env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 AHP/round3/guarded/r1-refute/numerics/collar_probe.py \
  > AHP/round3/guarded/r1-refute/numerics/collar_probe.log 2>&1
```

### Formula traceability

All paths in this list are under `lean/src/`; further anchors are retained in both supporting-script headers.

- `ZStatementP428.lean:42,51,58,66,73,123,130,140,189,286`: scaling, blocks, periodic distances, admissibility, boxes, class cubes, Lambda collar and torus compatibility.
- `ZR2A.lean:107,121`, `ZR6A.lean:27,33`: coverage and touching competitor support.
- `ZXR2Wire1.lean:20`, `ZXR2Ops3.lean:26,30,50`: geometry and bond/constraint carriers.
- `AdalyFormal/Balaban/CovariantOperators.lean:247,301,315`, `AdalyFormal/Target/ClayStatement.lean:1286`: parallel transport, gradient, curl and plaquette holonomy.
- `AdalyFormal/Balaban/DeltaPrime.lean:125,133`, `AdalyFormal/Balaban/DeltaPrimeOperator.lean:287–395`, `ZLocOps.lean:119,181,186`: plaquette correction and normalized Delta.
- `R2Ops1.lean:108,135,141,150,166,170`, `ZR2Ops2.lean:27,63,67,100`: Laplacian, site constraints, projector, padded inverse, W and gauge term.
- `R2Raw1.lean:36,43,68,74`, `R2RawX.lean:187`, `ZLocJet.lean:35,39,89,100`, `ZXR2Sector.lean:97,109`: raw maps, first/second jets and level factors. Exponential/logarithm and staircase anchors remain in `assembly.py`.
- `ZLocJ.lean:20,49,71`, `AdalyFormal/Balaban/SourceJ.lean:228`, `D1Lit.lean:56,59`: localized source and selector assembly.
- `ZXR2Ops3.lean:98,102,134`, `R2Algebra.lean:145,149,212,220,222`: mass, base data, carrier, H and the genuine second-order correction.
- `AHP/round3/guarded/pin/Statement.lean:273,290,293`: pinned response, actual selector difference and corrected local operator motivating the probe. These are not redefined as the numerical Schur matrices.

## Formal partial and stopping reason

The final Lean file retains **the entire round-3 pin verbatim as a byte prefix**, including the round-2 goal namespace, equivalent goal pairs and boundary-response definitions. Only frozen `DrEquiv` is imported. New results are in `AdalyFormal.Round3.Guarded.RefuteR1`.

The general lemma `lambda_empty_of_thin_top` (`Attempt.lean:402`) states: if the top domain is a coordinate strip with embedded unit endpoints p,q, with q an existing unit-torus coordinate and width q-p at most R M, then actual `LambdaOK` forces Lambda empty. It does not require any premise about U, a, class regularity or inverse values. The proof changes only coordinate zero of any proposed Lambda site to q, an exterior site no further than R M away, contradicting the strict Lambda collar.

`probeLu` and `probeTower` explicitly define the lifted numerical geometry for every R. `probe_torus` proves its TorusOK compatibility. `probe_lambda_empty` proves Lambda empty for every R at least one. `probe_energy_zero` then proves every actually supported competitor has zero bondEnergy.

**Main partial:** `AdalyFormal.Round3.Guarded.RefuteR1.probe_not_negative_witness` (`Attempt.lean:472`). It excludes the positive-energy/Lambda conjunction required by `CofinalPencilFailure` for this whole family, independently of U and any spectral claim. `probe_instIneq` additionally derives the actual all-plaquette instance inequality on these probes from the frozen no-test-field theorem. This is an excluded family, not a proof of either eventual positive goal.

Thus the numerical experiment stopped for an **exact geometric reason**, not just insufficient floating-point precision. Widening only Omega0 cannot repair the missing competitor. A future negative construction needs a wider top region supporting Lambda, an exact nonzero return and a carrier-unit/corrected-singular separation on that geometry, and actual regularity for arbitrarily small positive caps. One untested alternative is to add a distant broad top component supplying the competitor while retaining the narrow component's spectral experiment; that would require actual operator decoupling/lifting, coverage and class proofs, not just an abstract block-diagonal matrix. The present exclusion does not exclude such different towers. Any construction must still handle unbounded m and R with R chosen before every cap. This attempt supplies none of those missing spectral/cofinal obligations.

## Verification

Final compilation was exclusively through the prescribed shared-lock wrapper:

```sh
LEAN_NUM_THREADS=1 AHP/round3/lean1.sh AHP/round3/guarded/r1-refute/Attempt.lean
```

**Final exit 0; no errors or warnings.** Current evidence: `Attempt.lean.log`, `Attempt.lean.exit`, and `CHECKS.json`. All **52** locally named declarations have individual dependency records; five directly used frozen roots are additionally printed, for **57** records. Every dependency list is a subset of `propext`, `Classical.choice`, `Quot.sound`. The copied proposition-definition prints do not prove their bodies.

Main record, with line wrapping normalized:

```text
'AdalyFormal.Round3.Guarded.RefuteR1.probe_not_negative_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`validate.py` passed: complete pin byte-prefix equality, sole frozen import, no prohibited source token, declaration-print coverage, permitted dependencies, fresh source/log/exit order, successful numerical exit, memory below 2 GB, and exact agreement of the three recorded geometries with `probeLu`/`probeTower`'s arithmetic. Lean source SHA-256:

```text
64120c8ccc10e6f9906f3ebf85564744e372ebc18ea68881cec54402e2dc00e4
```

A foreground compilation timed out while waiting for the lock and was not counted. The first completed compilation rejected two helper names and a finite-coordinate bound elaboration; these were corrected before the successful final run. Waiting jobs were not bypassed, and other workers were not interrupted. No independent second-agent verification, printed-page image review, or whole-project reproduction is claimed. The supplied fresh reproduction pass and the pin's source-reading qualifications are taken as context. No printed-operator identification or altered class is asserted.

All authored files are under `AHP/round3/guarded/r1-refute/`. No protected source, other AHP item, lakefile, paper, note or expected result was edited. No direct Lean/Lake invocation, build, dependency update, reproduction, commit or push was performed.
