# Guarded all-plaquette reading — refutation attempt, round 2

**Closed goal: none.** Neither pinned negative goal is proved. The numerical separation survives a larger torus, but Lean proves that this candidate's tower is inadmissible and cannot satisfy the covered class. The other new result is an exact negation/certificate equivalence, not a witness for either side.

## 1. Compiled partial results

File: `Attempt.lean`. New namespace: `AdalyFormal.Round2.Guarded.RefuteR2`.

Furthest compiled logical partial result, at **line 358**:

```text
goalNeg2_iff_cofinalPencilFailure :
  AdalyFormal.Round2.Guarded.Pin.GoalNeg2 ↔
  AdalyFormal.Round2.Guarded.Pin.CofinalPencilFailure
```

The pin previously proved sufficiency of this certificate. The new converse at **line 341**, `goalNeg1_implies_cofinalPencilFailure`, proves necessity by classical negation of the actual pinned binders, using `max m₀ 1`. Consequently the certificate is equivalent to the literal negation of the guarded headline. This is **not** a proof of the certificate or of `GoalNeg2`. It imposes no continuous-path, endpoint-sign, flatness, or prescribed-geometry condition. In particular, R still precedes the universal positive smallness cap.

The candidate-specific partial result at **line 335**, `candidate_excluded`, proves, for **every** natural R, real alpha and eta, and link configuration U:

- `TorusOK 2 2 candidateLu`;
- `¬ Admissible 2 2 R 1 candidateTower`;
- `¬ ClassCoupled 2 2 12 1 candidateTower alpha eta U`.

Supporting declarations:

| Line | Declaration | Exact scope |
|---:|---|---|
| 265,267,270 | `candidateLu`, `candidateLf`, `candidateTower` | Unit sides four, fine sides eight; the numerical domain data. |
| 281 | `candidate_torus` | Enlarged torus satisfies compatibility at ell=M=2. |
| 285 | `original_torus_rejected` | Original unit sides (4,2,2) fail compatibility at ell=M=2. |
| 290 | `candidate_not_admissible` | Enlarged tower is not admissible for any R. |
| 302 | `candidate_no_described_cube` | No factor-12 described cube at any index. |
| 319 | `candidate_no_class_cube` | Hence no factor-12 class cube. |
| 324 | `candidate_not_covered` | Frozen site coverage is impossible. |
| 329 | `candidate_not_class` | Frozen coupled class is impossible, for every U/alpha/eta. |

### Why the numerical geometry is ruled out

The domains are

\[
\Omega_0=\{x:x_0<6\},\qquad
\Omega_1=\{x:2\le x_0<4\},\qquad
\Omega_j=\varnothing\ (j\ge2)
\]

on the fine side-eight torus. At level one, `bigSide 2 2 1 = 4`. The site `(2,0,0)` belongs to Omega1, but `(0,0,0)` does not, although both lie in the same aligned size-four block. This contradicts the block-closure conjunct of `Admissible`, independently of R.

There is a separate coverage obstruction. A factor-12 cube has side at least 24, so on this side-eight torus it contains every site, including `(6,6,6)` outside Omega0. At indices zero and one it cannot lie in the required union of strata. Thus there are no described cubes and no class cubes. The nonempty Omega0 is not covered. Changing epsilon, theta, or the proposed smallness bound cannot repair either obstruction.

These are exact geometry facts, not a proof that no other tower supports a counterexample.

## 2. Numerical attempt

### Changes from round 1

`numerics/assembly.py` copies the previous assembled-operator transcription and adds a side-length parameter plus period-four transverse repetition of its two interior defects. `numerics/delta_ops.py` is the copied supporting plaquette implementation. The new driver is `numerics/cover_probe.py`.

The driver first recomputes the prior small-torus candidate. It then enlarges fine sides from (8,4,4) to **(8,8,8)**. Its unit sides are (4,4,4), now compatible with ell=M=2. The enlarged **full touching-bond carrier has 3648 real coordinates**; the constraint matrix has rank **2496/2496** numerically. No flat-positive-subspace compression is used for the carrier spectral check.

At ell=2, k=1, a=1, links with neither endpoint in Omega0 carry `diag(exp(i theta), exp(-i theta))`. Other links are identity except, for y,z in {0,4}:

- base `(2,y,z)`, direction 1: `exp(epsilon E0)`;
- base `(3,y+1,z)`, direction 2: `exp(0.7 epsilon E1)`.

Here `E0=diag(i,-i)` and `E1=[[0,1],[-1,0]]`; epsilon is **0.16**. Thus this is a non-flat interior background, not the old zero-correction twist family. Theta changes exterior links only. The script uses the actual raw second-jet formula for the correction, approximated by central differences; it does **not** use an interior finite difference of Delta as Delta2.

### Formula references

The complete operator/file/line index is retained in `assembly.py:8-25` and `delta_ops.py:6-22`; the new driver also identifies the relevant carrier and correction formulas. Key frozen anchors, all under `lean/src/`:

- `ZXR2Wire1.lean:20`: `geomOf`.
- `ZXR2Ops3.lean:26,30,50,98,102,134`: touching carrier, constraint indices, mass and base assembly.
- `R2Ops1.lean:108,135,141,150,166,170`: Laplacian, site constraints, their kernel and image projector.
- `ZR2Ops2.lean:27,63,67,100`: weighted site term, padded inverse, W and gauge term.
- `ZLocOps.lean:119,181,186`: normalized plaquette correction and Delta.
- `R2Raw1.lean:36,43,68,74`: raw one-step map; `R2RawX.lean:187`: `qStepX`.
- `ZLocJet.lean:35,39,89,100` and `ZXR2Sector.lean:97,109`: genuine first/second jets and level scaling.
- `ZLocJ.lean:20,49,71` and `D1Lit.lean:56`: localized source and assembly sign.
- `R2Algebra.lean:145,149,212,222`: carrier, H, polarized correction and its diagonal form.
- `ZStatementP428.lean:286`: torus compatibility; `:73`: admissibility; `ZR2A.lean:107`: fixed-factor site coverage.

This is a floating-point transcription, not a proved dictionary between Python arrays and Lean operators. Derivatives are finite differences, not certified exact derivatives. Source symmetry and normalization checks do not remove that limitation.

### Results

The recomputed periodic-sector corrected-root estimate is

\[
\theta_*\approx0.5771896115174016.
\]

At this theta, the entire enlarged carrier spectrum is numerically positive, with minimum **1.1791868427941804e-6**. Its next eigenvalue is approximately **1.14506499e-4**. These are full-spectrum values, not values on the repeated sector only.

The localized carrier minimum is **0.11213004526201614**; the localized constraint-compression minimum is **0.011893787714567288**. The localized source norm is **2.059582465345381**, and the top component of H*J has norm **0.6348520603784245**.

An eigenvector is obtained in the small periodic sector and lifted with normalization 1/2 to the enlarged carrier. Independently of this proposed lift relation, the driver then evaluates the enlarged raw-jet Hessian action in **every one of the 3648 carrier coordinates**. The full corrected residual at theta* is:

| Hessian step | Full residual norm | Corrected Rayleigh value |
|---:|---:|---:|
| 0.003 | 1.56e-9 | 6.53e-12 |
| 0.001 | 5.15e-10 | 2.19e-13 |
| 0.0003 | 1.16e-9 | 5.97e-12 |

At theta* minus/plus 1e-7, the same normalized vector has corrected Rayleigh values approximately **+2.10763e-7 / -2.10763e-7** using step 0.001. The carrier minimum remains positive at both sampled points, approximately **1.38995e-6 / 9.68425e-7**.

**Important limitations:** positivity of one Rayleigh value at the left endpoint is not positive semidefiniteness of the corrected operator there. Three sampled positive carrier gaps do not certify its guard throughout an interval. A residual near zero is not an exact singularity. There is no interval-arithmetic certificate, no verified error bound for the finite differences, no Lean spectral proof, and no formal translation-invariance theorem. This is evidence for a numerical separation on the excluded tower, not a guarded headline counterexample.

Additional observed consistency errors:

- W acting on the normalized periodic lift: max error **2.60e-17**.
- H*J repeating across transverse cells: max error **2.57e-15**.
- Direct full correction action versus the predicted lifted action: norm error **1.98e-10** at step 0.001; other steps are in `cover_results.json`.
- Direct enlarged quadratic second differences agree with the small-cell normalized formula to approximately 1e-14.

All observations are retained in `numerics/cover_results.json` and `numerics/cover_probe.log`. Final script exit: **0**. Address space was capped at **3500 MiB**; recorded peak RSS **1,433,672 KiB**, below 4 GB; reported run time **156.43 seconds**, excluding the heavy-slot wait.

Replay from the workspace root:

```sh
"$BB_CLI" heavy run -- env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 AHP/round2/guarded/r2-refute/numerics/cover_probe.py \
  > AHP/round2/guarded/r2-refute/numerics/cover_probe.log 2>&1
echo $? > AHP/round2/guarded/r2-refute/numerics/cover_probe.exit
```

## 3. Why the negative goal remains open

1. The retained numerical candidate is **provably outside** the admissible covered class, not merely missing a class proof. Its tower must be replaced, not relabelled.
2. No exact carrier-unit/corrected-singular configuration has been constructed in Lean. The numerical raw-jet Hessian and root estimate cannot inhabit either pinned negative goal.
3. No positive-energy admissible competitor and `LambdaOK2` package was constructed for a separating in-class configuration.
4. The negative headline needs fixed ell and a, unbounded m and R, **R chosen before the arbitrary positive smallness cap**, and suitable witnesses for every cap. Epsilon=0.16 and one finite torus do not address these quantifiers.

A next attempt needs a block-aligned covered slab large enough to contain genuine factor-12 cubes before spending effort on the separating spectral root. It then needs an exact analytic argument that survives arbitrarily small interior perturbations at the requisite scales. The cofinal equivalence records the exact obligations; it does not supply them.

## 4. Verification and scope

Final serial Lean command:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/round2/guarded/r2-refute/Attempt.lean \
  > ../AHP/round2/guarded/r2-refute/Attempt.lean.log 2>&1
echo $? > ../AHP/round2/guarded/r2-refute/Attempt.lean.exit
```

Final exit **0**, no warnings or errors. All **53 locally named declarations** have individual dependency prints; the frozen pencil/headline equivalence is additionally printed, for **54 records**. Every record lists only subsets of `propext`, `Classical.choice`, `Quot.sound`. Proposition-definition prints do not prove their bodies.

`validate_artifacts.py` checked exact byte-prefix equality with the entire pin, sole import `DrEquiv`, all declaration print coverage, allowed dependency sets, clean prohibited-token scan, fresh successful compilation, numeric exit and memory. Its output is `VALIDATION.json`.

Final Lean SHA-256:

```text
9dc2dadd4dce68def40ed485c8a23c3d7cfc2d8f03776990b6e47dafa3a6d166
```

An initial compilation had elementary simplification/dependent-rewrite errors; these were repaired. One later compile command timed out while waiting for a heavy slot; the final completed replay overwrote the log and exit record. Only the current successful file is claimed. No independent second-agent verification is claimed.

All writes were under `AHP/round2/guarded/r2-refute/`; the sole deleted file was a local draft text file there. No AHP module is imported. No frozen source, lakefile, paper, note, expected result, or other thread's AHP directory was edited. No build, reproduction, dependency update, commit, or push was run.
