# Guarded structural route — round 5, pass 2

**Closed goal: `none`. The observed-inverse proof route is stopped.** The new numerical test still shows pole-like growth at **R=18**, which satisfies the reduction's room condition. It does not prove unboundedness, corrected singularity, or either negative goal.

**Fresh compilation did not finish.** The wrapper's bash call timed out after 200 seconds, leaving an empty log and no `.exit`. Subsequent exit-file and process checks found no completion record or surviving process for this attempt. It was **not relaunched**, as instructed. The formal file is byte-identical to the previously compiled `structural-r1/Attempt.lean`; the prior log/exit are checked as prior evidence, not copied or relabelled as a new compile. In the structured result, `exitCode: -1` means **no recorded wrapper exit**, not an observed compiler exit code.

## 1. Formal deliverable and unchanged contract

Read the round-3 judgement and pin, round-4 mining report, all four existing round-4 route NOTES, and the task's obstacle text for routes without NOTES. The catalogue was read in bounded chunks; this is not a new independent verification of its 419 imported declarations. The pin and all proof bodies used in the final file were inspected.

`Attempt.lean` is the complete prior structural attempt copied verbatim, starting with the complete round-3 pin. No goal, definition, assumption, selector, or quantifier was changed. It imports only frozen `DrEquiv`. There are no AHP imports or new Lean declarations in this pass.

The furthest **previously compiled** partial result remains

`AdalyFormal.Round4.Guarded.DecayR2.actual_relative_return_norm_le_observed`

at `Attempt.lean:1101`. With the actual localized units and literal carrier guard, and the stated observed-C-inverse estimate, it proves

\[
 \|K_B^{-1}(K_C-K_B)\|
 \le \|JA^{-1}\Theta\|\,\|D\|\,c.
\]

The identity at `:986` and its actual-operator specialization at `:1085` are

\[
 K_B^{-1}(K_C-K_B)y=\Theta A^{-1}DC^{-1}y.
\]

All carrier inverses are full-carrier inverses. The conditional headline theorem at `:1166` still requires the unproved `GShape CObservedGuardSmall`; that premise is not inserted into a pinned goal. The original `decay-r2/New.lean` fragment was already copied and repaired in pass 1. This pass does not claim a fresh successful compile of it.

Prior dependency record, normalized from `structural-r1/Attempt.lean.log`:

```text
'AdalyFormal.Round4.Guarded.DecayR2.actual_relative_return_norm_le_observed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All **86** local declarations in the copied file have individual dependency prints. The audit checks all 86 records against the **prior** successful log, the prior exit 0, and byte identity. It does not manufacture a new `.exit` file or put the old log at the new path.

Source SHA-256: `7d42aa1e1d15a3f1c816576babead3197ba0c4543c706e36c52096e7af108f18`.

## 2. What changed since pass 1

Pass 1 observed growth at R=2, below the room threshold. This pass tests

\[
 \ell=M=2,\quad m=k=1,\quad a=1,\quad R=18,
 \qquad 17\ell=34\le RM=36.
\]

The physical fine torus is **(232,8,8)**, not the computational period-two cell. The tower and region are

\[
 \Omega_0=[4,228)\times T^2,\quad
 \Omega_1=[40,192)\times T^2,\quad
 \Lambda=[58,60)\times T_u^2.
\]

Use cap 1, alpha=1/48, epsilon=1/7680, so \(24\alpha=1/2\le1\). The background has the single direction-1 `Ug epsilon` defect at longitudinal coordinate 40 and even transverse coordinates; other non-exterior bonds are identity. Every exterior bond receives `u_theta`.

These are q=1 instances of `dil_in_class_nonflat_competitor` (`AHP/round4/guarded/refute-r1/Attempt.lean:1423`), whose theorem retains arbitrary exterior V, full class membership, admissibility, LambdaOK2, cap and a positive-energy competitor. Its interior holonomy calculation also applies. This is the mathematical provenance of the geometry/class conditions, not a claim that the numerical geometry checker proves them. That older family theorem was not recompiled here. The geometry check's `positive_competitor_not_certified` flag means only that **the Python routine** does not certify the competitor.

Only cap 1 and m=1 were tested. Satisfying the room inequality is not satisfying every eventual threshold in Total or the pinned headline.

## 3. Sparse implementation and the actual observation

`numerics/sparse_probe.py` avoids a dense 8076-dimensional sector carrier. It reuses unchanged formula transcriptions from pass 1 and checks a new sparse elimination against the dense code.

Let E embed the carrier in full bonds, let N span the kernel of the actual site constraint Q' on Omega0, and put

\[
 L=P_{\Omega_0}\,\mathrm{lap}\,N,\quad H=L^*L,
 \quad F=L^*\mathrm{grad}^*E,\quad G=\mathrm{grad}\,N.
\]

Q' has disjoint blocks in this k=1 geometry, so N is constructed from small block kernels. Since Q'N=0, the padded site inverse satisfies \(G_pL=N\). Thus

\[
 WE=E-GH^{-1}F,\qquad T^*T=F^*H^{-1}F.
\]

For the localized plaquette operator, set

\[
 K=E^*\Delta_{\rm in}E+\mathrm{mass},\quad
 V=E^*\Delta_{\rm in}G,\quad Z=G^*\Delta_{\rm in}G.
\]

The full-carrier B-inverse is obtained by eliminating auxiliary variables from the sparse Hermitian system

\[
 \begin{pmatrix}
 K&-V&-F^*\\
 -V^*&Z+H&H\\
 -F&H&0
 \end{pmatrix}.
\]

The auxiliary matrix has dimension 11268 and 401954 nonzero entries in the zero sector. This is not an inverse of a compressed B. The omitted-plaquette edges have identically zero G rows in this transcription. Consequently their W rows equal coordinate rows and Theta is scattered into the 72-dimensional boundary-coordinate set.

For boundary inclusion \(E_b\), define \(X=B^{-1}E_b\), \(S=(E_b^*X)^{-1}\). The transfer is computed through the **Schur identity following full inversion**, with independent full augmented-A solves as checks.

### A sub-observation gives a lower bound, not a replacement for J

J remains the orthogonal projection onto the complement of the actual `jetInputZero`, whose inputs are **W-dressed** fields on the union of the positive-level rhoT balls. Here rhoT=8.

Rather than computing a large, potentially ill-conditioned observation SVD, select those observed W rows whose G row is exactly zero and whose bond lies in the carrier. They are exact coordinate rows of WE in the transcription. Let P0 select these 528 coordinates. They lie in the row space of the genuine observation, so

\[
 P_0J=P_0,\qquad
 \|P_0A^{-1}\Theta\|\le\|JA^{-1}\Theta\|.
\]

The table below measures **this lower bound**, not equality with the whole observed norm. In particular, it does not replace J by an arbitrary interior mask. The selected sites have longitudinal coordinates between 30 and 198, in the union of the actual radius-eight read balls. The formula evaluated is

\[
 P_0A^{-1}\Theta
 =P_0XS(S+\Theta_b)^{-1}\Theta_bE_b^*.
\]

The exact numerical dictionary between this transcription and Lean, including the Fourier lift and sparse elimination, remains unformalized. All floating-point values below are diagnostics, not certified bounds.

## 4. Results at the room-condition radius

Zero-sector crossing:

\[
 \theta_*\simeq0.5865589686386086.
\]

The unit-normalized reconstructed mode has residual approximately \(3.94\times10^{-15}\) and

\[
 \|P_0z\|\simeq4.42127\times10^{-12}\le\|Jz\|.
\]

The observed tail is now **very small**, unlike at R=2. Numerically it is not zero. At \(\theta=\theta_*-d\):

| d | Lower bound on the observed-transfer norm | d times lower bound |
|---:|---:|---:|
| 1e-2 | 2.3222415e-10 | 2.3222415e-12 |
| 1e-3 | 2.3823661e-9 | 2.3823661e-12 |
| 1e-4 | 2.3884156e-8 | 2.3884156e-12 |
| 1e-5 | 2.3890209e-7 | 2.3890209e-12 |
| 1e-6 | 2.3890814e-6 | 2.3890814e-12 |
| 1e-7 | 2.3890875e-5 | 2.3890875e-12 |

This is the same pole-like growth over five decades, with a much smaller residue. It supports **decay rather than exact invisibility**. A finite sample does not prove divergence, and the sampled lower bounds themselves remain below one. No formal impossibility theorem for an eventual uniform bound is claimed.

Independent full augmented-A solves agree with the Schur transfer: largest relative sub-observation error **1.17e-9**, largest full solve residual **3.72e-9**. The zero-sector localized minimum eigenvalue is approximately 0.123546662, with eigenpair residual 2.39e-10.

### Full physical carrier diagnostic

All sixteen transverse Fourier sectors of the period-two lift were assembled **before** inversion. Their total carrier dimension is **129216**. At the closest sample:

- every localized sparse augmented system has a successful LU factorization;
- minimum absolute LU pivot over all sectors is approximately 0.3225;
- maximum localized inverse random-probe relative residual is 5.59e-15;
- every carrier Schur matrix has positive minimum eigenvalue, with minimum 2.2977297e-7 in the zero sector.

These support numerical nonsingularity of the full lifted carrier. **The Schur minimum is not a full-carrier eigenvalue**, and the LU pivot is not a singular-value lower bound. Nonzero-sector full localized eigenvalues were not computed successfully and are explicitly null in the data. No exact guard certificate follows from factorization diagnostics or random probes.

The initial run failed when ARPACK did not converge in sector (0,1). Its log, exit 1 and partial results are retained with `_first` names. The final run removes that unnecessary eigenvalue requirement for nonzero sectors and records LU/residual unit diagnostics instead; it completed with exit 0. The unsuccessful eigenvalue calculation is not reported as a passed test.

## 5. Validation and resource bound

The sparse-vs-dense checks at R=2 give maximum discrepancies:

- B action: 4.18e-14;
- W action: 5.78e-15;
- B inverse on boundary columns: 3.34e-16;
- raw first-jet matrix: 2.72e-15;
- omitted-plaquette shift: 1.40e-16;
- selected observation rows versus exact coordinate rows: 2.00e-16.

Independent dense Fourier code also checks sectors (0,1) and (1,2): their lowest-six eigenvalue discrepancies are at most **5.05e-14**. This tests the non-real phases, not just the zero-sector implementation.

Peak RSS: **405148 KiB** for the dense comparison tests and **297076 KiB** for the full R=18 diagnostic. Each numerical process enforces a **1900 MiB address-space limit = 1992294400 bytes**, below 2 GB, with single-thread BLAS. No oversized dense carrier is allocated at R=18.

Completed numerical commands:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 bb heavy run -- python3 AHP/round5/guarded/structural-r2/numerics/sparse_probe.py --check
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 bb heavy run -- python3 AHP/round5/guarded/structural-r2/numerics/sparse_probe.py --all-sectors
python3 AHP/round5/guarded/structural-r2/audit.py
```

Final numerical logs and exits are present. `CHECKS.json` explicitly separates prior Lean compilation from the absent fresh exit. The six copied Python helpers are byte-identical to pass 1; none of their historical main routines was executed. The only newly executed numerical main is `sparse_probe.py`.

## 6. Concrete obstacle and stopping decision

The proposed exact near-nullspace invisibility mechanism has no support in either tested geometry. At R=18 the observable tail is exponentially small-looking, but the inverse amplification still grows like the reciprocal distance to the crossing. Therefore I did not invest in a positive proof based on that mechanism, as instructed.

What remains unproved:

1. Exact unboundedness of the observed transfer, even on this one finite torus; the numerical pole is not a theorem.
2. An eventual claim for unbounded m and R, with R before every cap. This pass only moves the fixed-radius numerical obstacle into the room-condition regime.
3. Nonzero or positive action of the actual assembled D on the near-null mode. Nonzero Jz alone does not prove nonzero Dz or a positive correction pairing.
4. Simultaneous exact unit of A and non-unit of A-D, even once, let alone cofinally.
5. A fresh successful compile at the requested new path. The timeout was not retried and is not hidden.

Thus no pinned goal is closed, and no modified goal is substituted. The numerical result supports the refutation investigation but is not its certificate. The prior compiled conditional estimate is the furthest formal result retained here.

All authored files are under `AHP/round5/guarded/structural-r2/`. No protected source, earlier-round file, build configuration, paper, notes, expected output or extras was changed. No direct compiler/Lake command, reproduction, update, deletion, commit, push, persistent terminal or additional worker was used.
