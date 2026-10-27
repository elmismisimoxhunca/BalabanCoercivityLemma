# Guarded IVT route — round 5, pass 2

**closedGoal: `none`. No pinned goal is proved.**

This pass proves the negative endpoint for the **actual curved** family, rather than borrowing the flat-interior endpoint. It also proves the exact first-crossing theorem, so an interval guard need not be separately postulated once initial positivity/unit conditions hold. Initial positivity and the correction sign on an exact crossing kernel remain open.

## Contract and verification

`Attempt.lean` begins with the complete 352-line round-3 pin byte-for-byte. In fact the entire pass-1 `ivt-r1/Attempt.lean` is an unchanged byte prefix. All four goals, selectors, class conditions and quantifier order remain unchanged. The only import is frozen `DrEquiv`; no AHP module is imported.

Required judgement/pin documents, the mining report, the four available round-4 route NOTES, and the supplied obstacles for routes without NOTES were consulted. No lost round-4 compilation is treated as verified. The inherited class and path proofs are freshly compiled within this file. The mining catalogue is not independently reverified.

Final commands, executed directly in the bash tool:

```sh
AHP/round3/lean1.sh AHP/round5/guarded/ivt-r2/Attempt.lean
python3 AHP/round5/guarded/ivt-r2/audit.py
```

Final wrapper exit **0**, no errors or warnings. All **136 local declarations** have individual dependency prints; all **156 dependency records**, including inherited frozen roots, use only the permitted three dependencies. `CHECKS.json` records prefix identity, frozen-only import, forbidden-token scan, source/log/exit timestamp ordering and hashes. This is builder verification, not an independent judge replay.

Main conditional declaration at line 2382:

```text
'AdalyFormal.Round5.Guarded.IVTR2.goalNeg2_of_initial_kernel_control' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The `hcontrol` argument of that theorem is **unproved**. Its dependency record does not establish that argument or close `GoalNeg2`.

Source SHA-256:

```text
b95973c476baecbdbce5ca1c04c414ae7bfb4388f1bda17a9b4dfb6e0532dd99
```

## New exact results

New declarations use namespace `AdalyFormal.Round5.Guarded.IVTR2`.

### 1. Actual curved negative endpoint, with no spectral premise

**`twistA_pi_negative` (2288)** proves, for every positive dilation q, every even R satisfying the room condition, and **every real curvature amplitude epsilon**,

\[
\exists v\in\operatorname{bondSupp},\qquad
\langle v,A(\pi)v\rangle<0.
\]

Here A is exactly the pinned all-plaquette carrier on pass 1's `twistU = dilU(..., Uth(...))`, with mass a=1. The theorem has no class-smallness, numerical, kernel, or interval-unit premise.

The proof constructs the outgoing bond at the right face

\[
x_0=12Rq+12q-1.
\]

`rightSite_bd` (2203) verifies the frozen `BdPt` predicate on the actual rectangular dilated torus. `right_face_agrees` (2241) proves that every link around a plaquette based there agrees with Uth: the interior defect is at \(2Rq+4q\), strictly away from this face. The same statement applies to the transverse back-shifted plaquettes.

`twist_delta_pi` (2260) consequently proves the **exact** value

\[
\langle X\delta_{(x,0)},\Delta_{\rm all}(U_\pi)X\delta_{(x,0)}\rangle
=-4\langle X,X\rangle.
\]

Frozen `Wop_sing`, `Tfull_sing_zero`, and `Mass_sing_le` apply to **arbitrary** backgrounds. Thus W fixes this vector, T kills it, and the mass term is at most \(\langle X,X\rangle\). Taking the frozen nonzero SU(2) witness gives strict negative carrier energy. The competitor witnessing positive bond energy is a different object; changing that competitor would not change D's kernel pairing.

This discharges the curved-path negative endpoint that pass 1 had left open. It does not prove the initial carrier or corrected carrier positive.

### 2. A first crossing with the preceding full-carrier guard

**`first_carrier_crossing` (1950)** proves a finite-dimensional topological fact. Given a continuous symmetric path A with A(0) PSD and a unit, and a negative direction at T>0, there is \(0<t<T\) such that:

- A(t) is PSD and not a unit;
- every A(s), \(0\le s<t\), is PSD and a unit;
- A(t) has a nonzero exact kernel vector.

Proof: the frozen IVT theorem first produces a nonunit before T. The nonunit locus is closed because units form an open set. Its intersection with the resulting compact interval therefore has a least point. Initial invertibility makes that point positive. A negative form at or before it would, by the same IVT theorem, yield an earlier nonunit, a contradiction. Finite-dimensional injectivity/surjectivity then gives a genuine nonzero kernel. No approximate eigenvector, uniform gap or spectral enumeration is used.

`twist_first_carrier_crossing` (2061) specializes to the actual curved path using pass 1's exact continuity and frozen symmetry. **`twist_first_crossing_of_initial` (2355)** now uses the newly proved negative endpoint, leaving only `PSD (A 0)` and `IsUnit (A 0)` as premises. It concludes the entire preceding full-carrier guard and the exact PSD singular crossing.

### 3. Conditional cofinal reduction, with the remaining premises named

`InitialKernelControl` (2368) is an **unproved proposition definition**, not a substitute goal. It requires:

1. A(0) PSD and a unit;
2. A(0)-D PSD;
3. at every PSD nonunit A(t) with \(0<t<\pi\), some exact kernel vector has strictly positive genuine D-pairing.

Item 3 is a sufficient condition, not asserted necessary or equivalent to the headline's failure. Requiring it at every PSD singular point avoids choosing or numerically identifying the first crossing in the premise. It remains a substantial sign problem.

`goalNeg2_of_initial_kernel_control` proves that arbitrarily small positive amplitudes satisfying this condition, at every positive q and even R>=18, imply the **unchanged** `GoalNeg2`. It reuses pass 1's cofinal proof: m and then R are chosen before the cap, after which epsilon is requested below \(\min(a_0/(3840q),1)\). Full frozen class, Lambda, geometry, cap and positive-energy competitor obligations remain present.

The negative endpoint is now a theorem, and the interval guard follows from initial positivity via first-crossing topology. Initial positivity and the exact kernel correction sign are **not** theorems here, even at one admissible instance. No cofinal separating witness is claimed.

### 4. Sign-transfer tolerance and arbitrary bounded masks

`correction_pairing_error` (2008) proves

\[
|\langle v,Dv\rangle-\langle w,Dw\rangle|
\le\|D\|\,\|v-w\|\,(\|v\|+\|w\|).
\]

`correction_positive_of_error_margin` (2029) transfers positivity when the approximate form strictly exceeds this error. It assumes an actual approximation radius; a carrier residual alone is **not** such a radius, especially for a nearly degenerate cluster. No numerical run below supplies all inputs to this theorem.

`maskedU` (2118) allows any real amplitude function f on non-exterior bonds, using Ug(f(e)), and arbitrary V on exterior bonds. `masked_regular` (2123) proves the genuine per-cube regularity if \(|f(e)|\le\alpha/80\). It applies the same frozen field bound with the field \(2f\); no stencil or coverage condition is weakened.

**`uniform_masked_class_family` (2147)** chooses one positive capped alpha and delta before **all** masks with \(\|f\|_\infty\le\delta\) and all exterior V. It supplies TorusOK, Admissible, LambdaOK2, both coverage clauses, full ClassCoupled, and the fixed positive-energy competitor. This permits a two-sided defect variant without a new geometry proof. It is nonspectral: it proves neither correction sign nor any unit/singular separation. The final conditional goal theorem still concerns the original single-defect `twistU`.

## Numerical checks

All processes use the inherited Taylor-arithmetic Q and C2 transcriptions, not a finite difference of Delta. Independent normalized finite differences check C2. These are floating-point transcriptions, not interval certificates or a formal Fourier dictionary. Computation is in the period-two transverse sector; no full-carrier unit is inferred from that sector. No all-16-sector rerun is claimed in this pass.

Every process imposes a **1900 MiB address-space ceiling**, below 2 GB, and single-threaded BLAS. Maximum reported RSS is **797376 KiB**. Local copies of inherited numerical helpers are retained under `numerics/`; their historical standalone-main comments are not descriptions of the new runs.

### Original single defect, smallest admissible R=2

Fine physical sides (40,8,8), q=1, epsilon=0.0001953125, alpha=0.03125, cap=0.75. This geometry is the previously admissible widened slab, not the excluded thin-top probe; it does not meet the separate reduction room condition.

At numerical carrier crossing \(\theta\approx0.5864553920826012\), the two projected D eigenvalues are about

\[
1.6369606\times10^{-13},\qquad1.6369616\times10^{-13}.
\]

Both signs remain positive under the independent C2 refinements. The carrier residual is about \(9.04\times10^{-15}\). This extends the sampled small-amplitude sign check; it does not certify an exact kernel pairing or an arbitrary-cap statement. The evaluated pre-crossing offsets do not by themselves exhibit corrected negativity at this smaller amplitude.

Data: `numerics/crossing_R2_eps0.000195313.json`.

### Two-sided diagnostic, R=6

To address pass 1's two nearly unobserved directions, a **different** mask places same-sign defects at x=16 and x=70, the first and last even sites of Omega1, on direction-1 bonds with both transverse coordinates even. This is not relabelled as the single-defect dilU. Its bounded mask is allowed by `masked_regular`; no spectral theorem has been transferred from one family to the other.

Fine physical sides (88,8,8), q=1, epsilon=0.0015625, alpha=0.25, cap=6. At the numerical carrier crossing, all four eigenvalues of D projected onto the approximate near-zero cluster are positive:

\[
4.2830384\times10^{-18},\quad4.2830384\times10^{-18},\quad
1.2614448\times10^{-17},\quad1.2614448\times10^{-17}.
\]

The independent C2 finite-difference refinements agree on these signs. Unlike the previous single-defect sample, this projected cluster has no numerically zero correction direction.

**Limitation:** carrier residual \(2.49\times10^{-14}\) still greatly exceeds these values. Positivity on an approximate four-dimensional cluster is not positivity on the exact first-crossing kernel without a rigorous subspace/error enclosure. No such enclosure is supplied. R=6 at q=1 also fails the reduction room inequality, and no other Fourier sectors were computed here. This is a candidate improvement, not a separating witness.

Data: `numerics/two_sided_R6_eps0.0015625.json`.

Commands:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 bb heavy run -- python3 AHP/round5/guarded/ivt-r2/numerics/crossing.py 2 0.0001953125
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 bb heavy run -- python3 AHP/round5/guarded/ivt-r2/numerics/two_sided.py 6 0.0015625
```

## Concrete remaining obstacle

The arbitrary-cap sign theorem remains missing. One must prove initial carrier positivity/invertibility and corrected PSD on the curved family, then prove strictly positive **genuine** D on an exact first-crossing kernel, for cofinal m and R and arbitrarily small amplitudes after R is fixed. This pass proves the negative endpoint for every amplitude and derives first-crossing topology from the initial conditions, but neither numerical cluster positivity nor interior holonomy proves the missing sign. A certified observation/subspace estimate or an exact spectral/raw-jet analysis is still needed. The two-sided variant would additionally need its own operator-path/sign development; nonspectral class membership alone does not transfer the single-defect reduction.

All authored files and deletions stayed inside `AHP/round5/guarded/ivt-r2/`. Temporary Lean fragments were removed after incorporation in the successful final file. Intermediate completed compiler errors were repaired; only the final zero-exit, warning-free log counts. No bash compilation timed out. No BB terminal, direct Lean/Lake command, build, dependency update, reproduction script, protected-file edit, earlier-round edit, commit or push was used.
