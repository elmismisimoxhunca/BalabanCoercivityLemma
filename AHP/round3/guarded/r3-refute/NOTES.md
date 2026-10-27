# Guarded all-plaquette reading — round 3, negative attempt 3

**closedGoal: `none`. Neither pinned negative goal is proved.** The new partial result certifies the single-defect family's complete class membership, capped positive parameters, geometry and competitor. Numerical exploration now checks all transverse Fourier sectors, rather than inferring the lifted carrier guard from the zero sector. Exact singularity, the full operator dictionary and cofinal m remain missing.

## Compiled partial result

Main declaration: **`AdalyFormal.Round3.Guarded.RefuteR3.wide_in_class_nonflat_competitor`**, **`Attempt.lean:924`**.

For every even natural **R >= 2**, every positive cap a0, and every exterior configuration V, it constructs positive alpha and epsilon such that:

- `12 * 2 * alpha <= a0`, and `0 < epsilon < 1`;
- actual `TorusOK 2 2`, all six clauses of `Admissible 2 2 R 1`, and `LambdaOK2 2 2 R 1` hold;
- the actual frozen **`ClassCoupled`** holds, including **both coverage clauses and per-cube regularity**;
- the explicit `wideBt` satisfies both test-field restrictions and has positive `bondEnergy`;
- there is a bond based in Omega0 on which this background is not identity.

The geometry is copied verbatim from the preceding attempt:

\[
L_f+1=(12R+16,8,8),\quad L_u+1=(6R+8,4,4),
\]
\[
\Omega_0=[4,12R+12)\times T^2,\qquad
\Omega_1=[2R+4,10R+12)\times T^2,\qquad \Omega_j=\varnothing\ (j\ge2),
\]
\[
\Lambda=[3R+4,3R+6)\times T_u^2.
\]

**This fixes ell=M=2, k=1, hence m=1.** It allows all even R >= 2, including R chosen before every cap, but does not supply the required unbounded m. The theorem contains **neither** spectral condition. It proves base-point nonidentity, not nonzero Delta2, nonzero boundary return, or a curvature statement.

### New exact ingredients

| Declaration | Line | Scope |
|---|---:|---|
| `wide_box` | 635 | Actual aligned rectangular-torus box; short transverse directions fully covered |
| `wide_region_cube` | 665 | Longitudinal clamping with genuine class-index uniqueness |
| `wide_cube_neighborhood` | 693 | Class cube containing the necessary coordinate neighborhood, R >= 6 |
| `wide_zero_cube` / `wide_cube_neighborhood_all` | 737 / 769 | Explicit small-collar cases R=2,4, completing every even R >= 2 |
| `wide_coverage` | 826 | **Both** frozen factor-12 site and fully-interior-plaquette coverage clauses |
| `widePattern` / `wideU` | 877 / 881 | Actual repeated single-defect background with arbitrary exterior links |
| `wide_regular` | 887 | Full per-cube regularity when `abs epsilon <= alpha / 80` |
| `wideU_nonflat` | 909 | A bond based in Omega0 has U != 1, for 0 < epsilon < 1 |
| `wide_in_class_nonflat_competitor` | 924 | Combined capped class/geometry/competitor/base-nonidentity certificate |

The interior pattern has direction-1 links at x0=2R+4 and both transverse coordinates even, carrying `Ug epsilon`; all other non-exterior links are identity. Only bonds with **neither endpoint** in Omega0 use V. Thus taking V constant diagonal `uTheta(theta)` gives the single-defect numerical path. The two-defect exploratory configuration has an additional noncommuting defect and is **not** certified by `wide_regular`.

The regularity proof uses frozen `ufield_perCubeRegular2` with the real field chi=2 epsilon on the selected links and zero elsewhere, eta=1/2. Frozen `perCubeRegular2_congr` permits the exterior change because every class cube lies in Omega0. This checks the actual pointwise, difference and curl-of-curl clauses, not merely a plaquette norm.

The main proof chooses

\[
\alpha=\tfrac12\min(a_0/24,1),\qquad \epsilon=\alpha/160.
\]

The small-R coverage proof uses real level-zero boxes, not new selectors: at R=2, longitudinal intervals [4,28) and [12,36); at R=4, [4,28), [10,34), [30,54), [36,60). At larger radii, the interval clamp chooses level zero or one as appropriate. All these boxes retain factor 12, alignment and unique index.

## Numerical work: lifting the candidate

`numerics/lift_probe.py` freshly recomputes the complete zero-sector correction/root from the preceding attempt's actual-formula raw-jet Hessians, then assembles **all 16 transverse Fourier sectors** for the physical fine torus (40,8,8), at R=2 and epsilon=0.04. It runs once with two defects and once with the single-defect pattern above.

Each sector has carrier dimension 1164; the sum of sector dimensions is **18624**, the lifted carrier dimension. Boundary phases are inserted into the primitive gradient, plaquette forms and raw-jet paths **before** the site projector, padded inverse, W, mass and carrier assembly. This is not a compression/inversion interchange. Local raw paths retain their unwrapped transverse coordinates; the zero-sector Jacobian agrees with the older quotient calculation to about 8.33e-13.

| Diagnostic at R=2, epsilon=0.04 | Two defects | Single defect |
|---|---:|---:|
| Numerical carrier root | 0.5864545876123239 | 0.5864546705731463 |
| Numerical corrected zero-sector root | 0.5864545737216755 | 0.5864546624744984 |
| Corrected minus carrier root | -1.3891e-8 | -8.0986e-9 |
| Smallest carrier eigenvalue over all 16 sectors at corrected root | 3.0382e-8 | 1.7714e-8 |
| Smallest eigenvalue among the 15 nonzero sectors | 0.1240833 | 0.1242465 |
| Corrected zero-sector kernel residual | 1.34e-14 | 1.45e-14 |
| Frobenius difference of the two Hessian-step correction matrices | 1.21e-7 | 9.83e-8 |

All 16 numerical carrier sectors were positive in both runs. This removes the earlier **numerical** omission of the nonzero transverse sectors. It does **not** prove a full lifted carrier unit. In particular, the displayed correction-step discrepancies exceed the tiny carrier gaps; neither discrepancy is a certified error bound. The corrected-root refinements (about 3.13e-13 and 2.17e-13) are only floating-point consistency observations.

`primitive_lift_check.py` separately evaluates the raw first derivative on the **complete physical lattice**, with 7680 fine bonds and 592 raw output rows, in four deterministic complex Fourier test directions. It compares that direct derivative with the local-path phase scatter. At derivative step 1e-5, the largest coordinate discrepancy is about **2.63e-13**. This checks a nontrivial primitive lift implementation numerically, not an exact intertwining theorem, and does not test every assembled inverse or the lifted corrected operator.

The single-defect numerical amplitude epsilon=0.04 is covered by `wide_regular` if alpha >= 3.2; the capped class then requires a0 >= 76.8. The main theorem's explicit tiny-amplitude choice instead works under **every** positive cap. **No spectral result was proved or numerically established uniformly for those choices.** Do not identify the finite-cap sample with the eventual smallness quantifiers.

## Why the negative proof stopped

Coverage and regularity are no longer missing for the single-defect lifted geometry. The remaining concrete obstacles are:

1. Prove exact nonzero correction/return and an exact corrected kernel at a parameter, together with a genuine unit of the **entire** lifted carrier at that same parameter. A finite-difference root, tiny residual or positive floating-point spectrum is not such a certificate.
2. Prove the Fourier-sector dictionary for the genuine frozen assemblies, including the correction and all inverse qualifications, or bypass it by a full-lattice argument. Only a numerical primitive check is supplied here.
3. Extend separation to arbitrarily large m and then cofinally in R, with R chosen before every positive cap. The constructed family fixes m=1; the spectral runs fix R=2. R=2 also fails the reduction's room condition 17 ell <= RM. No pointwise application of that reduction at the numerical sample is claimed.

The main result is therefore a **partial candidate-class certificate**, not a weakened replacement for either pinned negative goal. It establishes no sign or invertibility property of the pinned operators. No generic matrix counterexample is substituted.

## Formula traceability

All paths below are under `lean/src/` unless explicitly indicated. The numerical helper headers retain their finer per-formula citations.

- Geometry, class cubes, Lambda, torus: `ZStatementP428.lean:42,51,58,66,73,123,130,140,189,230,286`; `ZT4A.lean:57,88`; coverage: `ZR2A.lean:107,121`, `ZR6A.lean:27,33`.
- Geometry assembly/carrier: `ZXR2Wire1.lean:20`; `ZXR2Ops3.lean:26,30,50`.
- Transport, gradient, curl: `AdalyFormal/Balaban/CovariantOperators.lean:247,301,315`; holonomy: `AdalyFormal/Target/ClayStatement.lean:1286`; pairing: `AdalyFormal/Balaban/SuTwoInner.lean:104`.
- Plaquette correction and Delta: `AdalyFormal/Balaban/DeltaPrime.lean:125,133`; `AdalyFormal/Balaban/DeltaPrimeOperator.lean:287-395`; `ZLocOps.lean:119,181,186`.
- Laplacian/site constraints/projector: `R2Ops1.lean:108,135,141,150,166,170`; padded inverse, W and gauge term: `ZR2Ops2.lean:27,63,67,100`.
- Raw map/first and second jets: `R2Raw1.lean:36,43,68,74`; `R2RawX.lean:187`; `ZLocJet.lean:35,39,89,100`; `ZXR2Sector.lean:97,109`; blocking/staircase/exp-log: `AdalyFormal/Balaban/UbarTowerCovariance.lean:237`, `AdalyFormal/Balaban/TowerLawCovariant.lean:171`, `AdalyFormal/Balaban/SuTwoLogExpCore.lean:164,226`.
- Source: `ZLocJ.lean:20,49,71`; `AdalyFormal/Balaban/SourceJ.lean:228`; `D1Lit.lean:56,59`.
- Mass/base data: `ZXR2Ops3.lean:98,102,134`; carrier, H and correction: `R2Algebra.lean:145,149,212,220,222`.
- Pinned response/shift/corrected operator: `AHP/round3/guarded/pin/Statement.lean:273,290,293`. The numerical Schur matrices are **not** redefined as these exact range-Theta responses.

## Verification and replay

Final Lean compilation, only through the requested shared lock:

```sh
AHP/round3/lean1.sh AHP/round3/guarded/r3-refute/Attempt.lean
```

Final exit **0**, with **no errors or warnings**. Evidence: `Attempt.lean.log`, `Attempt.lean.exit`, `CHECKS.json`. All **69 local declarations** have individual dependency records; **89 records** including frozen roots, all subsets of the permitted three. Main record:

```text
'AdalyFormal.Round3.Guarded.RefuteR3.wide_in_class_nonflat_competitor' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Source SHA-256:

```text
5ce077b140883f7295fb2ba389c6e62d766d84c88afe9cb50899b40957a6f562
```

The complete 352-line pin and the preceding attempt's entire Lean source are exact byte prefixes. The sole import remains frozen `DrEquiv`. No pin, copied definition or goal statement was changed. Initial failed compilations were repaired; only the final clean run is counted. No independent second-agent replay or whole-project rebuild is claimed.

Numerical commands were run through `"$BB_CLI" heavy run --`, with single-threaded BLAS and bytecode writes disabled:

```sh
"$BB_CLI" heavy run -- env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 AHP/round3/guarded/r3-refute/numerics/lift_probe.py
# Repeat with --single for the one-defect sweep.
"$BB_CLI" heavy run -- env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 AHP/round3/guarded/r3-refute/numerics/primitive_lift_check.py
python3 AHP/round3/guarded/r3-refute/validate.py
```

All three final numerical exit records are **0**. Every process has a **1900 MiB address-space limit**, below 2 GB; maximum measured RSS was **287292 KiB**. Results are in `numerics/lift_results.json`, `lift_single_results.json`, `primitive_lift_results.json`, with sibling driver logs/exits. The four copied numerical helpers are byte-identical to the preceding attempt; their historical standalone main programs were not run.

`validate.py` passed: complete pin and inherited source prefixes; frozen-only import; prohibited-token scan; source/log/exit ordering; clean final compilation; complete local dependency-print coverage; allowed dependency sets; numerical exits, memory and expected sector/geometry accounting. These are artifact checks, not numerical certification.

Read the requested handoff, OPEN_ITEMS sections, Stage-B and round-2 results, guarded round-2 judgement in full, the pin and relevant round-2 attempts, and the immediately preceding positive/negative attempt records. The supplied reproduction pass and source-reading qualifications remain inherited context. All authored files are under `AHP/round3/guarded/r3-refute/`. No protected file or other AHP path was edited; no direct Lean/Lake command, build, reproduction, update, deletion, commit or push was run.
