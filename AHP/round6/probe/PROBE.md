# Round 6 probe: the unchanged first-crossing family fails at very small amplitude

## Decision

**The sign is negative at an actual first crossing. Stop using the unchanged single-defect family to justify the all-q `InitialKernelControl` premise.**

All 32 requested grid points (`q=1,2`, `R=18,20,24,30`, `epsilon=10^-3,10^-4,10^-5,10^-6`) have positive correction on their **actual** first-crossing mode. However, this is misleading for arbitrary caps:

| q | R | epsilon | actual first character | unit-kernel correction |
|---|---|---|---|---|
| 2 | 18 | 10^-40 | (7,7) | **-1.7544653959652980e-215** |
| 2 | 18 | 10^-60 | (7,7) | **-1.7544653962414712e-195** |
| 2 | 18 | 10^-100 | (7,7) | **-1.8124680628969907e-170** |

The last value was independently recomputed at **400 and 500 significant digits**, agreeing to **235 relative decimal digits**. Its augmented-kernel residual divided by the absolute correction is about **3.64e-330**. A separate vacuum calculation gives a **negative first Taylor coefficient**, not merely one anomalous finite-amplitude sample:

\[
\left.\frac{d}{d\varepsilon}\langle v_\varepsilon,D_\varepsilon v_\varepsilon\rangle\right|_{0^+}
\simeq-1.81246810408949136824\times10^{-70}
\quad(q=2,R=18).
\]

This is strong numerical evidence against the proposed **arbitrarily-small-amplitude sign premise**. It is **not a Lean proof**, a validated interval certificate, a proof of the positive guarded statement, or an exclusion of every other sufficient premise/subfamily. In particular, a negative pairing on this kernel alone does not exclude a different vector giving a corrected crossing elsewhere.

The pinned `GoalNeg2` (`AHP/round3/guarded/pin/Statement.lean:158`) remains open. No Lean file was written or compiled in this probe.

## 1. Exact transcription and actual symmetry

The detailed operator-to-Lean dictionary is [SOURCES.md](SOURCES.md). The governing definitions are:

- `AHP/round5/guarded/ivt-r2/Attempt.lean:986-995`: dilated torus, tower and Lambda;
- `:1379-1387`: single-defect `dilPattern` and `dilU`;
- `:1703-1716`: `twistU`, `twistP`, **actual** `twistA` and **actual** localized `twistD`;
- `lean/src/R2Algebra.lean:145,149,222`: carrier, constrained H, and the correction identity;
- `lean/src/ZXR2Sector.lean:97,109`: normalized first and second raw jets.

Physical fine sides are

\[
(q(12R+16),8q,8q),
\]

with ell=2, k=1, a=1. The interior defect is in direction 1 at longitudinal coordinate \(q(2R+4)\), with **even** transverse coordinates. Increasing q does not change the blocking stride from 2 to 2q.

The true transverse translation group is

\[
C_{4q}\times C_{4q},
\]

acting by translations of **two fine sites**. Its characters are indexed by \((i_y,i_z)\), with phases \(e^{2\pi i i_y/(4q)}\), \(e^{2\pi i i_z/(4q)}\). Thus there are **16 characters for q=1 and 64 for q=2**, each represented on a longitudinal-by-2-by-2 cell. The cell is a representation, **not a replacement admissible torus**. The physical lift has normalization \(1/(4q)\).

Background, sets, staircase paths and blocking are equivariant. Linear primitives, adjoints, projections and invertible operators preserve these characters. Their inverses are taken in the complete character space before any boundary Schur complement.

The diagonal SU(2) background also preserves global diagonal conjugation. Using the orthonormal basis

\[
E_1=\operatorname{diag}(i,-i),\quad
E_2=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\quad
E_3=\begin{pmatrix}0&i\\i&0\end{pmatrix},
\]

the neutral coordinate separates from the charged coordinate \(z=v_2+i v_3\). Adjoint link transport acts on z by \(e^{2i\theta}\). A simple complex charged kernel consequently has **real dimension two**, not one.

The nonlinear second jet was **not** treated as a sector-preserving linear operator. A charged Bloch mode's neutral quadratic output is translation invariant. Its pairing with zero-character neutral H*J, including the physical lift normalization, is exactly the quantity transcribed in `correction()`.

### Operators, including full inverses

For the site-average kernel basis N, define

\[
L=P_{\Omega_0}\operatorname{lap}N,\quad H=L^*L,\quad
F=L^*\operatorname{grad}^*E,\quad G=\operatorname{grad}N.
\]

The basis is explicit and need not be orthonormal. Then

\[
WE=E-GH^{-1}F,\qquad T^*T=F^*H^{-1}F.
\]

Writing \(K=E^*\Delta_{in}E+\mathrm{mass}\), \(V=E^*\Delta_{in}G\), \(Z=G^*\Delta_{in}G\), the actual localized inverse is obtained by elimination from

\[
\begin{pmatrix}K&-V&-F^*\\-V^*&Z+H&H\\-F&H&0\end{pmatrix}.
\]

The further KKT system with Q and Q* yields \(H_{\rm constrained}^*J\). The genuine correction is

\[
\langle v,Dv\rangle=2\sum_b(H_{\rm constrained}^*J)_b C^{(2)}_b(Wv).
\]

All raw derivatives use analytic order-two Taylor arithmetic with mpmath trigonometric functions. There is no finite-difference Hessian, fixed truncated epsilon series, replacement by a curvature mask, or inverse of a boundary compression.

`rank_check.py` also checks the missing complementary constraint units: selecting the fine bond \((y+e_\mu,\mu)\) for every top coarse bond gives a strictly row-diagonally-dominant minor **before** Bloch phases are introduced. The observed minimum dominance margin is 1/8. Q0 uses separate identity columns. Thus the calculation does not silently assume that invertibility of the zero-character constraint matrix implies invertibility of every other character. These local row types are independent of separated q,R geometry; this is still numerical, not a formal rank theorem.

## 2. Which character actually crosses first?

| q | first charged character | leading fine transverse wave numbers | approximate first angle |
|---|---|---|---|
| 1 | (0,0) | (0,0) | 0.586558968638608839468526 |
| 2 | **(7,7)** | **(-pi/8,-pi/8)** | **0.563971517985560942179715** |

**Important correction to the provisional runs:** for q=2, the zero-character crossing near 0.586559 is **not first**. At that angle, the (7,7) Schur minimum is approximately -0.0731283; (7,0) and (0,7) are also negative. Consequently **none of the q=2 `s0_0` near-crossing tests is a guarded alternative witness**. Those artifacts are retained as explicitly superseded provisional diagnostics. The final q=2 tables use only `s7_7`.

Every requested point received a complete character screen: 2,560 neutral/charged character instances in total. The screening matrices were assembled at 70 or 90 decimal digits, but their spectral screening/inertia computations use **double precision**. The near-singular first character, kernel, tiny correction, and near-crossing margins use mpmath, up to **640 digits**. The actual-character audit separately checks the three potentially competing q=2 characters at the earlier (7,7) root.

At the true first root, the other-character Schur gap is at least approximately **0.2109158 for q=1** and **0.05196095 for q=2**. These are **boundary Schur gaps, not full-carrier eigenvalues**.

The first complex charged eigenvalue is simple in all tested cases. It yields a two-dimensional real kernel on which the real symmetric correction has the same scalar value in both U(1)-rotated directions. The next Schur eigenvalue can nevertheless be exceedingly small: near-degenerate left/right modes cannot be distinguished in ordinary double precision.

### Why a coarse angle grid is not the first-crossing argument

Substitution of diagonal exterior Uth into the plaquette formula gives the useful finite-dimensional identity

\[
\Theta(t)=\cos t\,\Theta(0)+\sin t\,\Theta(\pi/2),\qquad \Theta(0)\succeq0.
\]

`path_identity.py` checks it at 80 digits for every q=1,2 character and both neutral/charged parts. Expanding the cited plaquette coefficients also derives it algebraically; it is **not yet a Lean theorem** here.

If localized B is PD, then for \(0<t<\pi/2\),

\[
\frac{A(t)}{\sin t}=B\csc t+E_b\Theta(0)E_b^*\cot t+E_b\Theta(\pi/2)E_b^*
\]

is strictly decreasing in the Loewner order. This makes positivity before the first PSD singular point a monotonic-pencil consequence, not an inference from a sparse grid of angles. It also lets the completed later-angle screens rule out all already-positive characters at the earlier q=2 root. The three exceptional competitors were checked directly.

## 3. Requested amplitude grid: signs and margins

Every entry below is on the **actual first kernel**, normalized in the physical bond norm.

| q | R | correction at epsilon=10^-3 | correction at epsilon=10^-6 |
|---|---|---|---|
| 1 | 18 | 1.51805873019e-38 | 1.51803478084e-44 |
| 1 | 20 | 6.87838260923e-42 | 6.87827409379e-48 |
| 1 | 24 | 1.41215328858e-48 | 1.41213101003e-54 |
| 1 | 30 | 1.31363620576e-58 | 1.31361548144e-64 |
| 2 | 18 | 2.76173258478e-188 | 2.76173171327e-191 |
| 2 | 20 | 4.30639299250e-208 | 4.30639163355e-211 |
| 2 | 24 | 1.04707485946e-247 | 1.04707452904e-250 |
| 2 | 30 | 3.96984765054e-307 | 3.96984639780e-310 |

Both intermediate decades were computed and are in [TABLE.csv](TABLE.csv) and [SUMMARY.json](SUMMARY.json). The smallest requested-grid value is below the normal double range. Across the independent lower/higher precision runs, the worst relative agreement is **55.89 decimal digits**. At the highest precision, the largest augmented-kernel-residual/correction ratio is approximately **1.36e-69**.

### Initial positivity

All requested initial tests support **B PD and B-D PD**, a stronger statement than A(0) PD and A(0)-D PSD because the omitted t=0 plaquette contribution is PSD.

- Every character's augmented B and B-D inertia was screened.
- Zero-character inertias were additionally calculated by arbitrary-precision Hermitian LDL with 1x1/2x2 pivots at 70 digits for all 32 samples, with 100-digit rechecks at the radius/amplitude extremes.
- Selected nonzero q=2 characters received 100-digit inertia checks too.
- Zero-character double eigenvalue diagnostics put the B-D minimum between **0.1235464996841 and 0.1235466647748**; they are not full-lattice gap bounds.
- The negative epsilon=10^-100 example received a separate complete character screen and a 160-digit zero-character initial inertia check. Its initial B-D gap diagnostic remains approximately **0.1235466647746**.

**Precision qualification:** the full-character PD evidence is mixed precision. This is not a claim of mpmath eigendecomposition or interval certification of every full-lattice eigenvalue. The very small first-kernel correction and its sign reversals, in contrast, are independently recomputed at high precision.

### Alternative premise on the requested grid

For the same unit kernel vector v, choose

\[
t_1=t_c-\frac{|\langle v,Dv\rangle|}{2|\langle v,A'(t_c)v\rangle|}.
\]

The derivative estimate is a symmetric high-precision difference with angle step 10^-6; the resulting carrier and corrected forms are evaluated directly, not inferred from that derivative approximation. On all 32 grid points, the carrier Schur matrix at t1 is positive and the corrected test form is negative. Representative epsilon=10^-6 margins:

| q,R | t_c-t1 | A(t1) form | (A(t1)-D) form | first-character Schur minimum |
|---|---|---|---|---|
| 1,18 | 3.466853e-45 | 7.590174e-45 | -7.590174e-45 | 7.965891e-45 |
| 1,30 | 3.000005e-65 | 6.568077e-65 | -6.568077e-65 | 6.893200e-65 |
| 2,18 | 4.416609e-192 | 1.380866e-191 | -1.380866e-191 | 1.427946e-191 |
| 2,30 | 6.348647e-311 | 1.984923e-310 | -1.984923e-310 | 2.052599e-310 |

At **epsilon=10^-100**, this kernel-based alternative fails: the pre-crossing A form is **+9.0623403e-171**, while the corrected form is **+2.7187021e-170**, not negative. The carrier Schur minimum is positive, approximately **9.3713206e-171**. No different negative test vector is supplied there; this is not a proof that A-D is PSD throughout the interval.

## 4. Scaling, closed structure, and the noncommuting small limits

### q=1: apparent quadratic law, with a later mode-mixing transition

Let

\[
\rho_0=\frac{3-\sqrt5}{2}=0.381966011250105\ldots .
\]

The transverse-uniform tangential component in a flat level-zero collar obeys

\[
b_{x+1}-3b_x+b_{x-1}=0.
\]

Its decaying root is rho0; the finite collar also has a reflected growing solution. The data on the requested grid obey

\[
\langle v,Dv\rangle\approx
0.0188582729848\,\varepsilon^2\rho_0^{4R},
\]

with small-amplitude relative changes consistent with order epsilon squared, and finite-width corrections. The exponential rate per R is

\[
-4\log\rho_0=3.84969460047682758\ldots .
\]

The limiting half-space angle has the explicit form

\[
t_\infty^{(1)}=\arccos\frac{-1+\sqrt{193+32\rho_0}}{16}
=0.5865589686386088394685259869561093568\ldots .
\]

This comes from the normal/symmetric-tangential surface determinant
\(2+\cos t-\rho_0-8\sin^2t=0\).

**The grid coefficient is not the fixed-R epsilon-to-zero coefficient.** At q=1,R=18 the left/right mixing transition occurs around 10^-17. At epsilon=10^-18 the left-half mass is 0.50229786; at 10^-25 and 10^-40 it is effectively 1/2. The correction remains positive, but its normalized coefficient tends to

\[
\frac{\langle v,Dv\rangle}{\varepsilon^2\rho_0^{72}}
\simeq0.00942913649225007684,
\]

half the apparent grid coefficient. These tiny-amplitude values were checked at 160 and 200 digits.

### q=2: positive grid law is NOT the true small-epsilon law

Set

\[
k=-\pi/8,\quad T=4(1-\cos k),\quad
\rho_k=\frac{3+T-\sqrt{(3+T)^2-4}}2
=0.33698426526801936\ldots ,\quad s=3-2\sqrt2.
\]

The flat-collar transverse decay is rho_k. The limiting boundary angle is the first root of the explicit scalar equation

\[
(1+T\cos t+4\sin k\sin t)
\left(\frac{2+T-\rho_k}{1+T}+\cos t\right)
-4\bigl(1-\cos(2t+k)\bigr)=0.
\]

It gives

\[
t_\infty^{(2)}=0.56397151798556094217971533436172727\ldots .
\]

The q=2 requested-grid mode is overwhelmingly **right-localized**, unlike the q=1 grid mode. Its positive correction is dominated by the very small propagated H*J tail near the **right end of Omega1**. Although bare J is localized at the left defect, the assembled D is not merely a local curvature mask.

On this pre-asymptotic grid,

\[
\langle v,Dv\rangle\approx
5.06749306069\times10^{-7}\,\varepsilon\,(s\rho_k)^{8R}.
\]

The observed rate per R,

\[
-8\log(s\rho_k)=22.80372971486600328326\ldots,
\]

matches the fitted rate. The factors have separate origins: the collar-mode tail and the constrained neutral source transfer across Omega1. This is a useful structural identification, **not a positive coefficient valid uniformly down to epsilon=0**.

At smaller amplitudes, mixing with the other near-null boundary mode reverses the sign. At 10^-40 and 10^-60, the observed negative values are approximately proportional to **-1/epsilon** within that intermediate regime. Eventually, for fixed q,R, the exact vacuum splitting dominates and the true behavior is **negative and linear in epsilon**. At epsilon=10^-100 the left-half mass is 0.49999998863635, nearly a balanced mode. A fit of the positive-grid and intermediate negative terms places the sign change around 8e-36 for q=2,R=18; that crossover value itself was not bracketed or certified.

### Explicit finite sum for the true q=2 leading coefficient

The neutral leading source multiplier can be written without a large inverse. Let

\[
n=4q(R+1),\qquad \gamma=\operatorname{arcosh}3,
\]

\[
a_j=\frac32(-1)^j\frac{\sinh((n-j)\gamma)}{\sinh((n+1)\gamma)},
\quad 0\le j<n,\qquad a_{-1}=a_n=0,
\]

\[
h_j=\mathbf1_{j=0}-2a_{j-1}+2a_{j+1}.
\]

Then h_j is the direction-1 top component of \((H^*J)'(0)\); the other top directions vanish to first order. It comes from the constrained neutral tangential field `(a_j,-a_j)` and the tridiagonal system with diagonal 6 and off-diagonal 1. `leading_source.py` checks this formula against the complete KKT solve at 320 digits; at epsilon=10^-12 the discrepancies are of the expected order epsilon squared, including the last nonzero component.

For the finite-volume vacuum first kernel v0 in character (7,7), with its genuine W0 dressing, the coefficient is the explicit finite path-jet sum

\[
c_1(q,R)=2\sum_{j=0}^{n-1}h_j\,
 C^{(2)}_{0,\,(p+2j,0,0),\,1}(W_0v_0).
\]

Here C2 at zero background is a finite quadratic expression in path entries, evaluated analytically by `rawjet`; no epsilon extrapolation is used in this sum. `leading_vacuum.py` evaluates the finite-volume v0, not a half-space replacement. For q=2,R=18 it gives

\[
c_1(2,18)\simeq-1.81246810408949136824\times10^{-70}.
\]

The vacuum first complex kernel is numerically simple, with second Schur eigenvalue about 2.1149529514e-161. Thus the finite-volume first branch has an ordinary local small-epsilon expansion once epsilon is sufficiently tiny. The negative coefficient explains why positive samples, even very precise ones, cannot establish the arbitrarily-small-cap premise.

The sum still contains a finite-volume kernel/transfer computation. No closed scalar formula or parametric sign proof for all q,R has been obtained.

## 5. Reliability, failures, and reproduction

### What was checked

- Independent R=2 comparison with the retained round-5 transcription: carrier discrepancy 7.15e-15, first jet 2.78e-17, W 6.67e-16, H*J 1.31e-18, and a genuine random correction form discrepancy 3.31e-21.
- Arbitrary-precision sparse coefficients and residuals throughout the first-kernel solves. Double sparse LU is only a **preconditioner**; iterative-refinement residuals use the mpmath operator, not its double copy.
- Independent precision runs up to 640 digits, and 400/500 digits on the decisive negative example.
- Analytic second jets independently checked against their assembled local Hermitian quadratic forms.
- Full-character screens, constraint-minor rank checks, high-precision selected inertias, and the exterior trigonometric identity.
- No negative sign in the requested grid was inferred from residual-sized floating-point noise. The decisive negative example is **outside that grid**, in the amplitude regime the universal premise actually requires.

These are precision-stability tests, **not directed-rounding intervals, rigorous subspace enclosures, or a Lean Fourier dictionary**. An augmented residual alone is not an eigenvector error bound. No formal closure is claimed.

### Retained failed/interrupted work

- An initial `findroot` call accidentally exposed an optional second Python argument; it failed and was repaired.
- A scalar no-pivot LDL encountered a structural zero saddle pivot; it was replaced by Hermitian 1x1/2x2 elimination.
- Full-character double inertia screening needed local orthogonal congruences to avoid structural scalar pivots. Its imaginary-pivot contamination is recorded, not treated as a proof bound.
- A selected nonzero-character ARPACK gap diagnostic did not converge. That log is retained. Subsequent runs use the successful arbitrary-precision inertia check and explicitly do **not** claim the missing ARPACK gap.
- `batch_q2_R30_p180_a` timed out after completing its epsilon=10^-3 output; the epsilon=10^-6 calculation was interrupted. It was not relaunched. Later independent precision runs use different precisions.
- `finish_screen_q2` timed out during the epsilon=10^-5,R=30 screen after 14 complete grid screens. Its partial JSON is retained. A separately named **90-digit** screen supplies that case; the previously unstarted epsilon=10^-6 case was then run separately. Neither missing `.exit` is represented as success.
- The additional `ultratiny_q2_R18_p400` batch uses the **zero character** and is not a first-crossing result. Only the explicitly named `tiny_actual_p400` and `ultratiny_first_*_p500` results count for the negative first-kernel finding.
- The first three q=2,R=18,epsilon=10^-3 first-character files originally recorded an unadjusted cell DFT. That diagnostic field is explicitly renamed `legacy_unadjusted_cell_fold_weights_not_physical_Fourier_weights`; it is not evidence for a physical fine Fourier weight. Later files remove the Bloch phase before computing folded weights. This metadata correction does not change any operator, eigenvalue, kernel pairing or margin.

### Files and commands

- `PROBE.md`: this report;
- `SOURCES.md`: complete Lean-line/operator dictionary;
- `TABLE.csv`, `SUMMARY.json`: audited **actual-first-sector** grid and decisive negative case;
- `MANIFEST.json`: hashes of scripts/data at final audit;
- `q1_*_s0_0.json`: q=1 first-character results;
- `q2_*_s7_7.json`: q=2 actual first-character results;
- `q2_*_s0_0.json`: **non-first**, provisional/diagnostic results only;
- `leading_source.json`, `leading_vacuum.json`: closed-source formula and negative leading coefficient;
- `sectors_*.json`, `actual_sector_audit.json`, `initial_*.json`: complementary-sector/initial evidence. Check `complete:true` before using a sector screen.

Representative reproduction, directly in the bash tool:

```sh
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  "$BB_CLI" heavy run -- python3 AHP/round6/probe/probe.py \
  --q 2 --R 18 --eps 1e-100 --dps 500 --iy 7 --iz 7

PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  "$BB_CLI" heavy run -- python3 AHP/round6/probe/leading_vacuum.py

PYTHONDONTWRITEBYTECODE=1 python3 AHP/round6/probe/summarise.py
```

Every numerical job longer than a minute ran through the heavy scheduler. Each imposes a 7 GiB address-space cap; the largest recorded RSS is approximately **1.26 GiB**, well below 8 GB. All authored files and cleanup are confined to `AHP/round6/probe/`. No protected source, earlier round, lakefile, Lean olean, paper, notes, expected output, extras, git commit or push was touched. No Lean compiler, lake command, REPRODUCE script or BB terminal was used.
