# Guarded reading — refutation attempt, round 1

**Closed goal: none.** Neither pinned `GoalNeg1` nor `GoalNeg2` is proved. The new result is a compiled pointwise second-jet criterion plus an out-of-regime numerical candidate. It is not a refutation of `GuardPencilT`, `P428Target8SG`, or the printed lemma.

## 1. Compiled partial result

File: `Attempt.lean`; main declaration at line **322**:

`AdalyFormal.Round2.Guarded.RefuteR1.pencil_failure_iff_second_jet`.

For the **actual** `gparams` assembly, this identifies failure of the pinned `CPen` with existence of a nonzero vector satisfying the second-jet pairing equation against **every** vector of the full touching-bond carrier. It does not supply such a vector, the carrier guard, class membership, or the cofinal quantifiers.

Write
\[
M=(\mathrm{dataS}_{\rm all}) .Ginv,\qquad
D=(\mathrm{dataS}_{\rm in}).Delta2,\qquad
f(x)=\langle H_{\rm in}C_{2,\rm in}(x),J_{\rm in}\rangle.
\]
The proved equivalence is
\[
\neg\operatorname{IsUnit}(M-D)
\iff \exists v\ne0\;\forall x,\quad
\langle x,Mv\rangle=f(x+v)-f(x)-f(v).
\]
This is an exact full-space criterion, not a compression or a test of just one diagonal quadratic value.

Supporting new declarations:

| Declaration | `Attempt.lean` line | Content |
|---|---:|---|
| `second_jet_pairing` | 269 | Polarization of the genuine localized correction: `inner x (D y) = f(x+y)-f(x)-f(y)`. |
| `pencil_failure_iff_kernel` | 292 | Exact finite-dimensional equivalence with a nonzero solution of `M v = D v`. |
| `pencil_failure_iff_second_jet` | 322 | Main criterion above, using the actual `C2`, `H`, and `J`. |
| `guarded_failure_forces_second_jet` | 348 | Under the actual carrier guard, a pencil failure forces `D != 0` and a nonzero actual second-jet/source pairing. |
| `guarded_failure_forces_nonflat` | 379 | With admissibility and `3 <= R*M`, a guarded failure has a nonidentity link with base point in `Omega0`; excludes the whole base-point-flat family. |

These are partial reductions/exclusions, not weakened replacements for either negative goal. The last theorem uses the existing frozen base-flat identity; it is not a new construction of a non-flat counterexample.

### Pin and compilation audit

The entire pin file was copied verbatim into the initial part of `Attempt.lean`; only the additional frozen import `GdR6b` precedes that content. The appended partial results use a separate namespace. `verify_artifacts.py` confirms character-for-character equality of the copied prefix after removing that one import. All four goal definitions and the cofinal certificate are unchanged. No AHP file is imported. Imports are exactly `DrEquiv` and `GdR6b`.

Final command:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/round2/guarded/r1-refute/Attempt.lean > ../AHP/round2/guarded/r1-refute/Attempt.lean.log 2>&1
echo $? > ../AHP/round2/guarded/r1-refute/Attempt.lean.exit
```

**Final exit: 0; no warnings or errors.** The 28 printed dependency records all contain exactly `propext, Classical.choice, Quot.sound`. All 17 local theorem declarations (12 copied pin checks and 5 new partials) have dependency prints; six directly used frozen proof roots are additionally printed. The five proposition-definition prints do not prove those propositions.

Main dependency record, normalized onto one line:

```text
'AdalyFormal.Round2.Guarded.RefuteR1.pencil_failure_iff_second_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Raw forbidden-token scan of the Lean file: no hits. Final Lean SHA-256:

```text
6372b6a7f2c7947ee08af9f08212a6b029bb9d5514bb1b5df476fc429e78b971
```

Machine-readable audit: `CHECKS.json`. Intermediate tactic failures and an elaboration timeout were repaired; only the final successful compilation is claimed.

## 2. Numerical attempt: non-flat, two-parameter family

The earlier Stage-A probes only modeled `Delta` and used an interior finite difference as a surrogate correction. This attempt instead transcribes the site projector, padded inverse, `W`, gauge term, multi-level constraint and mass operators, localized source, and raw block jets. The correction is evaluated from the actual formula
\[
\langle v,Dv\rangle=2\langle H C_2(v),J\rangle.
\]
No finite difference of `Delta` is substituted for `Delta2`.

### Explicit small geometry and links

- Fine periodic side lengths: **(8,4,4)**; `ell=2`, `k=1`, `a=1`.
- `Omega0 = {x : 0 <= x[0] < 6}`; `Omega1 = {x : 2 <= x[0] < 4}`; higher domains empty.
- `Lam_j` uses the aligned stratum formula of `ZXR2Wire1.lean:20`.
- The touching-bond carrier has **960 real coordinates**; the constraint space has **624**, including **16 top-level bonds**. The carrier is not compressed to a flat positive subspace.
- On bonds with neither endpoint in `Omega0`, put `diag(exp(i*theta),exp(-i*theta))`.
- All other links are identity except two interior links:
  - base `(2,0,0)`, direction 1: `exp(epsilon*E0)`;
  - base `(3,1,0)`, direction 2: `exp(0.7*epsilon*E1)`.
- `E0 = diag(i,-i)` and `E1 = [[0,1],[-1,0]]`, orthonormal for the frozen trace-normalized inner product. The defects do not commute.

**This geometry is not in the headline regime.** Its unit sides are `(4,2,2)`, so `TorusOK` fails the strict requirement `ell < Lu(mu)+1` on two axes. There is no proof of an admissible factor-12 covered tower at `M=ell^m`, no `ClassCoupled` certificate, and no positive-energy admissible test field. No choice of small epsilon fixes those missing geometry requirements.

### Formula traceability

Every modeled operator has a frozen Lean file-and-line anchor in the header of `numerics/probe_assembled.py`; `numerics/delta_ops.py` retains the prior audited curl/plaquette implementation and its references. Key anchors:

- `R2Ops1.lean:108,150,166,170`: Laplacian, site constraint kernel, its image and orthogonal projector.
- `ZR2Ops2.lean:27,63,67,100`: site mass, padded inverse, `W`, gauge term.
- `ZXR2Ops3.lean:26,30,50,98,102,134`: carrier, constraints, mass and base assembly.
- `R2Raw1.lean:36,43,68,74` and `AdalyFormal/Balaban/UbarTowerCovariance.lean:237`: genuine raw block map, including staircase order from `TowerLawCovariant.lean:171`.
- `ZLocJet.lean:35,39,89,100` and `ZXR2Sector.lean:97,109`: local first/second jets and the level scaling.
- `ZLocJ.lean:20,49,71`, `D1Lit.lean:56`: localized source with the actual assembly sign.
- `R2Algebra.lean:145,149,222`: carrier, constraint solution, second-order correction.

This is a numerical transcription audit, not a Lean equivalence between the Python arrays and the frozen operators. The jets are central finite differences of the raw map, not exact derivatives certified in Lean.

### Results

`probe_assembled.py` searched epsilon `0`, `0.08`, and `0.16`, using a scalar exterior angle. All three carriers have a numerical zero crossing near theta `0.577`. At epsilon zero the source and correction vanish, as expected.

At epsilon `0.16`:

- Localized carrier minimum eigenvalue: `0.1121300452620243`.
- Localized `Q G Q*` minimum eigenvalue: `0.011893787714567365`.
- Constraint matrix numerical rank: `624/624`.
- Local source norm: `1.0297912326726908`.
- Top component of `H^T J` norm: `0.31742603018921234`.
- Literal carrier crossing estimate: theta `0.5771901710052161`.

`probe_separation.py` applies `Delta2` by polarized finite differences of the scalar raw-jet functional. LOBPCG acts on **all 960 carrier coordinates**, using the dense carrier plus the matrix-free correction; no fixed low-dimensional compression is used. It estimates a corrected-pencil zero **before** the carrier crossing:

| Hessian step | Corrected-root estimate | Carrier minimum there | Corrected eigenvalue estimate | Eigenpair residual |
|---:|---:|---:|---:|---:|
| 0.003 | 0.5771896115208347 | 1.1791796e-6 | -2.72e-13 | 5.78e-10 |
| 0.001 | 0.5771896115174016 | 1.1791868e-6 | -1.01e-12 | 5.06e-10 |
| 0.0003 | 0.5771896115159024 | 1.1791900e-6 | -3.34e-12 | 6.33e-10 |

At step `0.001`, the diagnostic bracket around the corrected-root estimate is:

| theta | Corrected lowest-eigenvalue estimate | Carrier minimum |
|---:|---:|---:|
| 0.5771895115174016 | +2.1076241e-7 | +1.3899487e-6 |
| 0.5771897115174015 | -2.1076379e-7 | +9.6842501e-7 |

This is a **numerical candidate for unit/singular separation of the assembled pencil on the small geometry**. It is not an exact root, an interval-arithmetic certificate, a proof that the iterative eigenpair is the lowest eigenpair, or a proof of any `IsUnit` proposition. The carrier has a numerical positive gap at the corrected-root estimate; this differs from merely revisiting the old failed-guard carrier crossing.

An important caution survived the experiment: at the *carrier's* first kernel vector the correction quadratic value is approximately **-1.3086e-6**, yet the fully corrected operator already has a negative eigenvalue there. Off-diagonal coupling matters. Testing only that one quadratic value would have predicted the wrong first-order picture. The compiled pairing criterion accordingly quantifies over **every** test vector.

### Numerical checks and replay

Retained checks:

- Optimized plaquette Gram implementation agrees with the copied prior implementation on selected plaquettes to tolerance `1e-12` (recorded error in `assembled_results.json`).
- Flat raw first jet agrees with the independent straight-path averaging formula: maximum error `6.94e-17`.
- Raw top map and localized source are constant under the tested exterior angle change: recorded error zero.
- `W` has zero rows outside the touching carrier: recorded error zero.
- Halving the first-jet differentiation step changes the matrix by at most `1.31e-12`.
- Matrix-free Hessian symmetry check: `3.43e-11`.
- Matrix-free quadratic value versus independent directional second difference: `2.46e-11`.
- These are floating-point checks and observed errors, not certified error bounds.

Scripts and results are under `numerics/`:

- `probe_assembled.py`, `assembled_results.json`, `probe_assembled.log`, `.exit`;
- `probe_separation.py`, `separation_results.json`, `candidate.npz`, `probe_separation.log`, `.exit`;
- `audit_numerics.py`, `audit_results.json`, `audit_numerics.log`, `.exit`;
- `delta_ops.py` is the copied supporting implementation; its old standalone main was not run here.

All three executed scripts exited **0**. They were run serially through `"$BB_CLI" heavy run --` with `OPENBLAS_NUM_THREADS=1`, `OMP_NUM_THREADS=1`, and `PYTHONDONTWRITEBYTECODE=1`. The new assembly sets a 3500 MiB address-space cap. Largest recorded RSS in the retained runs is **195448 KiB**, below 4 GB.

Example replay from the workspace root:

```sh
"$BB_CLI" heavy run -- env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 AHP/round2/guarded/r1-refute/numerics/probe_separation.py \
  > AHP/round2/guarded/r1-refute/numerics/probe_separation.log 2>&1
```

## 3. Why formalization stopped

The small numerical example is not an inhabitant of the pinned certificate. Closing either negative goal still needs:

1. **Actual headline geometry and regularity.** A genuine `TorusOK`/`Admissible`/`LambdaOK2`/`ClassCoupled` instance with coverage, positive capped alpha, and a nonzero admissible test field. The retained small geometry explicitly fails the torus requirement.
2. **An exact operator argument.** The secant root estimate and finite-difference Hessian are not Lean witnesses. One must prove a corrected-pencil kernel and the carrier guard using the real raw jets, or prove a suitable exact sign/continuity bracket with the guard on the interval.
3. **The cofinal quantifier order.** Fixed ell and a; every lower m threshold; a larger m; every lower R threshold; a larger R chosen **before** the universal positive smallness cap; then witnesses for every cap. Epsilon `0.16` on one torus supplies none of this. Scaling the small picture by assertion is not justified; the tiny separating gap may shrink with the collar and smallness.
4. **No shortcut through `G1inv_lit`.** Identifying it with the pencil uses the frozen reduction's geometric and localized well-definedness hypotheses. Those were not certified for this small geometry. The numerics concern the pencil formula, not a demonstrated failure of the fully defined printed inequality.

The new Lean criterion specifies the full exact equation a future candidate must satisfy. It does not discharge any of these construction obligations. No negative goal was weakened or claimed closed.

## 4. Scope hygiene

Read the supplied handoff, the requested open-item sections, Stage-B guarded disposition, guarded design/attack/decision, Stage-B Lean comparison, prior residual prosecution/review, and the pinned statement contract before pursuing the construction. Frozen operator definitions were read to build and check the transcription.

All writes by this attempt are under `AHP/round2/guarded/r1-refute/`. No `lake build`, `REPRODUCE.sh`, `lake update`, deletion, commit, push, or protected-file edit was performed. Pre-existing and concurrent changes in the shared Lean checkout were left untouched.
