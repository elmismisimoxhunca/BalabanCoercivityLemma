# Guarded structural route, round 5 / pass 1

**Closed goal: `none`. Stop the proposed observed-transfer proof route: the preliminary numerical test shows pole-like growth, not invisibility.** This is an obstacle supported by numerical evidence, not a proof of either negative pinned goal.

## 1. Contract and formal result

`Attempt.lean` begins with the entire round-3 pin byte-for-byte. In fact the complete verified round-4 `decay-r1/Attempt.lean` is its prefix. The only import is frozen `DrEquiv`; there are no AHP imports. Every goal and every copied operative definition is unchanged.

The requested `decay-r2/New.lean` is a fragment requiring the decay-r1 helpers, not a standalone module. I copied it after that prefix **inside this permitted directory**, compiled it first, repaired its concrete elaboration failures locally, and compiled again through the supplied wrapper. Neither the original fragment nor any earlier-round file was edited. The generic identity and observed estimate proof bodies are unchanged. The repairs unfold `localCorrected` in the specialization, make concrete operator arguments explicit, fix tactic indentation, and specialize the Hilbert-space instances before substituting the nested carrier. One helper, `response_unit_of_relative_small`, does that last specialization.

All following names have prefix `AdalyFormal.Round4.Guarded.DecayR2.` (retained for the copied fragment):

- `relativeReturn_apply` and `actual_relative_return_apply` now compile. With the actual local units and carrier guard, they prove exactly
  \[
  K_B^{-1}(K_C-K_B)y=\Theta A^{-1}D C^{-1}y.
  \]
  The carrier inverses are on the full carrier, not on a compression.
- **Main partial result: `actual_relative_return_norm_le_observed`.** For the genuine observation \(J=\Pi_{\texttt{jetInputZero}^{\perp}}\), with \(\|JC^{-1}y\|\le c\|y\|\) on \(\operatorname{range}\Theta\),
  \[
  \|K_B^{-1}(K_C-K_B)\|
  \le \|JA^{-1}\Theta\|\,\|D\|\,c.
  \]
  Its local-unit, carrier-unit and observed-local-inverse hypotheses are retained.
- `pencil_isUnit_of_observed_guard_decay` gives corrected invertibility when that product is less than one.
- `failure_requires_observed_amplification` gives the necessary opposite inequality under guarded failure.
- `goalPos2_of_observed_guard_decay` is **conditional** on `GShape CObservedGuardSmall`. That hypothesis is not proved and is not inserted into the pinned goal.

This advances verification of the previously unverified round-4 fragment. It does **not** produce a uniform estimate or a new unconditional positive theorem.

## 2. Numerical test: an admissible lifted geometry, not the excluded small cell

Read the required judgement, pin and mining material and all existing route NOTES. Routes without NOTES are covered by the obstacle text in the task. The numerical test uses the smallest radius in the **already certified single-defect wide family**, not a claim of minimality among all admissible towers:

\[
\ell=M=2,\quad k=1,\quad R=2,\quad a=1,
\quad L_f+1=(40,8,8),
\]
\[
\Omega_0=[4,36)\times T^2,\quad
\Omega_1=[8,32)\times T^2,\quad
\Lambda=[10,12)\times T_u^2.
\]

Take cap \(a_0=1\), \(\alpha=1/48\), \(\varepsilon=\alpha/160=1/7680\). The background is exactly the single-defect pattern of round 3: `Ug epsilon` on direction-1 bonds based at longitudinal coordinate 8 and even transverse coordinates; identity on other non-exterior bonds; the diagonal twist `u_theta` on bonds with neither endpoint in \(\Omega_0\). Thus \(24\alpha=1/2\le a_0\) and \(|\varepsilon|\le\alpha/80\).

The existing `wide_in_class_nonflat_competitor` at `AHP/round3/guarded/r3-refute/Attempt.lean:924` supplies the full class, geometry, cap and positive-energy competitor for this parameter choice and arbitrary exterior field. The same source's `wide_regular` retains the genuine per-cube conditions. I did **not** recompile those older theorems here or claim their conclusion follows from a numerical geometry check. The inherited `geometry()` output still labels the competitor as uncertified **by that numerical routine**; the mathematical provenance is the cited theorem. The interior (0,1)-plaquette at (8,0,0) has word `Ug epsilon` inverse; its computed distance from identity is \(1.8414239080\times10^{-4}\).

The computation first uses the real zero sector for translations by two transverse sites, represented by a (40,2,2) cell. **That cell does not satisfy TorusOK and is not substituted for the physical torus.** Each cell vector has sixteen repeated translates in the physical torus; division by four makes the lift isometric. Every primitive is period-two equivariant, as are the inverse and projection constructions. A separate check assembles **all sixteen Fourier sectors before inversion** and checks full-lattice raw directional derivatives. The complete numerical carrier dimension is 18,624, equal to the sum of the sixteen dimensions 1,164. An exact Lean Fourier/intertwining dictionary remains unproved.

### The observation is the pinned dressed observation

For \(k=1\), `rhoT 2 1 = 8`. Let O be W restricted to the union of those radius-eight balls based at every positive-level constraint bond. The calculation constructs an orthonormal basis for `range O.T` and uses its projector as J. This is the kernel-complement construction in `jetInputZero`, **not** a mask on interior plaquettes and **not** just the actual raw-path edges. Period-two invariance allows the physical union of balls to be computed in the cell. The numerical observation has 1,395 rows and rank 912; the smaller actual raw-path set has 918 rows.

The all-plaquette shift is scattered from omitted plaquettes, and \(A=B+E\Theta_bE^*\). For \(X=B^{-1}E\), \(S=(E^*X)^{-1}\), the calculated transfer is
\[
JA^{-1}\Theta = JXS(S+\Theta_b)^{-1}\Theta_bE^*.
\]
Each sample is also checked by a **direct solve of the complete 1,164-dimensional sector carrier A**. No replacement of a full inverse by an inverse of a compression is made.

## 3. Results: visible near-null modes and inverse growth

Numerical carrier crossing:
\[
\theta_*\simeq0.5864553920873952.
\]
At that root the unit-normalized reconstructed near-null vector has
\[
\|Az\|\simeq3.70\times10^{-15},\qquad
\|Jz\|\simeq0.999999999999579,
\]
while its W-dressed input restricted even to the smaller actual raw-path set has norm approximately **0.0443949**. The proposed invisibility mechanism is absent in this test; it is not merely an artifact of measuring the entire carrier inverse.

For \(\theta=\theta_* - d\):

| d | sector minimum eigenvalue of A | norm of J A inverse Theta |
|---:|---:|---:|
| 1e-2 | 2.188305e-2 | 52.9010 |
| 1e-3 | 2.187386e-3 | 539.315 |
| 1e-4 | 2.187285e-4 | 5,403.47 |
| 1e-5 | 2.187275e-5 | 54,045.0 |
| 1e-6 | 2.187274e-6 | 540,460 |
| 1e-7 | 2.187274e-7 | 5,404,614 |

The product of offset with observed-transfer norm tends numerically to approximately **0.5404614**. This is clear pole-like growth across five decades.

At the closest sample all sixteen independently assembled sectors have positive eigenvalues; their minimum absolute eigenvalue is **2.1872734111e-7**. Thus the sampled lifted carrier is numerically nonsingular, rather than merely the small sector having a guard. The matrices are Hermitian to floating-point precision.

Checks:

- Localized B minimum eigenvalue: 0.1234232287.
- Direct-vs-Schur transfer relative errors: at most 1.86e-9.
- Direct linear-solve residual: at most 4.20e-9 at the largest transfer.
- Omitted-plaquette scatter vs dense assembled shift: 1.40e-16 maximum entry error.
- First-jet refinement from step 2e-5 to 1e-5: operator difference 1.31e-15; corresponding mass-matrix difference 1.14e-15.
- Full (40,8,8) raw-derivative checks in sectors (0,0) and (1,2): maximum entry discrepancy 1.04e-14.
- Peak RSS: 240,912 KiB for the transfer test and 281,308 KiB for the lift checks. Both processes impose **1900 MiB address-space limits**, below 2 GB, and use single-thread BLAS.

All values are floating-point diagnostics. Refinement discrepancies and residuals are **not validated error bounds**, and a finite list of growing values is not a formal unboundedness theorem.

## 4. Stop condition and remaining obstacle

The requested preliminary test failed, so I did not attempt to prove a class-uniform bound from near-nullspace invisibility. The necessary missing premise is precisely a bound on `observedGuardTransfer`, and the numerics show that it can see the near-null mode strongly.

Important limits:

1. This is **R=2, m=1**, below the reduction's room condition. It rejects the naive structural explanation on the smallest tested admissible geometry. It does **not** exclude an eventual theorem with larger radius/scale thresholds, nor establish cofinal failure with R chosen before every cap.
2. Nonzero `Jz` does not itself prove nonzero `Dz`. The assembled source pairing might have cancellations on a smaller subspace than this conservative observation. The test neither assembles an exact D nor proves corrected singularity.
3. There is no exact full-carrier unit / corrected-nonunit separation. The positive-energy and class obligations alone do not provide either spectral fact.
4. No pinned goal is proved or refuted. The numerical obstacle supports pursuing the refutation route, but cannot be used as its certificate.

## 5. Verification and reproducibility

Only these commands were used for compilation/tests:

```sh
AHP/round3/lean1.sh AHP/round5/guarded/structural-r1/Attempt.lean
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 bb heavy run -- python3 AHP/round5/guarded/structural-r1/numerics/observe.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 bb heavy run -- python3 AHP/round5/guarded/structural-r1/numerics/lift_check.py
python3 AHP/round5/guarded/structural-r1/audit.py
```

The initial compile ended with exit 1 (concrete elaboration failures); after local proof repairs the second wrapper invocation ended with **exit 0**, no errors or warnings. No timeout or lost-process relaunch occurred. Final evidence is `Attempt.lean.log` / `.exit` and `CHECKS.json`. All **86 local declarations have individual dependency records**, each a subset of `propext`, `Classical.choice`, `Quot.sound`. The main record is:

```text
'AdalyFormal.Round4.Guarded.DecayR2.actual_relative_return_norm_le_observed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Final source SHA-256: `7d42aa1e1d15a3f1c816576babead3197ba0c4543c706e36c52096e7af108f18`.

The audit checks the exact pin/decay-r1 prefixes, unchanged generic decay-r2 proofs and definitions, all local dependency records, forbidden-token absence, frozen-only import, timestamp ordering, numerical result assertions and the verbatim provenance of the five reused Python helpers. Those helpers' historical main routines were **not** run; only `observe.py` and `lift_check.py` were run. The imported `corrected_probe.py` supplies a symbol required by the old lift module; its corrected-root routine was not called. There is no claim of a new correction computation.

This is builder verification, not an independent judge replay. All authored files are under `AHP/round5/guarded/structural-r1/`. No protected source, earlier AHP round, lakefile, paper, notes, expected output or extras was edited. No direct Lean/Lake invocation, build, reproduction script, dependency update, deletion, commit or push was performed.
