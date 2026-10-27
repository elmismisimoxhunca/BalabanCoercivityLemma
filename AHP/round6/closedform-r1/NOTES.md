# Round 6 closed-form track, pass 1

**closedGoal: `none`. `GoalNeg2` remains open.**

The final file is `AHP/round6/closedform-r1/Attempt.lean`. It has a fresh successful compilation, but **no declaration closes a pinned goal**. The new unconditional result is the first part of the physical symmetry dictionary, not a Fourier block diagonalisation. The requested parametric crossing/sign computation was not obtained.

## Verification and unchanged contract

Read in full: `AHP/round5/RESULTS.md`, the round-5 `ivt-r1`, `ivt-r2`, `kernel-r2`, `structural-r1`, and `structural-r2` NOTES, the round-3 pin, and round-6 `probe/PROBE.md` and `probe/SOURCES.md`.

The entire **2396-line** `AHP/round5/guarded/ivt-r2/Attempt.lean` is an unchanged byte prefix. This includes the entire round-3 pin, the actual family, the first-crossing proof and `goalNeg2_of_initial_kernel_control` at line 2382. No goal, selector, class condition, mass parameter, or quantifier was altered. Only frozen `DrEquiv` is imported; no AHP module is imported.

Final commands, run directly in the bash tool:

```sh
AHP/round3/lean1.sh AHP/round6/closedform-r1/Attempt.lean
PYTHONDONTWRITEBYTECODE=1 python3 AHP/round6/closedform-r1/audit.py
```

Final wrapper exit: **0**. Errors: **0**. Warnings: **0**. All **166** local declarations, including the **30** new declarations, have individually matched dependency prints. All **186** dependency records are subsets of `propext`, `Classical.choice`, `Quot.sound`. `CHECKS.json` verifies the exact prefixes, import, forbidden-token absence, namespace-qualified print coverage, source/log/exit ordering and hashes. This is builder verification, not an independent replay.

Source SHA256:

```text
2849fe7e047e040fb9675a280beeff39e2a3cee4c4856e487058056d2a7e571d
```

Earlier completed exit-1 compilations exposed local elaboration issues and were repaired. No invocation timed out or was relaunched while incomplete. No numerical job was run.

## 1. New unconditional result on the actual physical carrier

New namespace: `AdalyFormal.Round6.Guarded.ClosedFormR1`.

**Main partial declaration:** `twoSite_exact_symmetry`, line **2643**.

```text
'AdalyFormal.Round6.Guarded.ClosedFormR1.twoSite_exact_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound]
```

For every positive q, every R, every real epsilon and exterior angle t, and either transverse direction, this theorem supplies an actual linear isometric equivalence of the **complete** touching-bond carrier and proves:

1. Its action is the explicit pullback by a two-fine-site translation.
2. The actual `twistU` is invariant under that translation.
3. The actual four-link `periodicPlaquetteHolonomy` is invariant too.

The physical fine torus remains the original one, with sides

\[
(q(12R+16),8q,8q).
\]

No period-two cell is substituted for it. No inverse of a compression is introduced.

### Supporting exact declarations

- `translation_shift` (2434): translations commute with each forward fine shift.
- `translation_tower` (2444): every tower level is invariant under any longitudinally zero translation.
- `translation_bondsOm0` (2451) and `translation_Zb` (2461): the **touching** support and exterior bond set are invariant. The support is the actual `lean/src/ZXR2Ops3.lean:26-35`, not the obsolete both-endpoints convention.
- `bondPullback` (2472), `carrierTranslationIsometry` (2488), and `carrierTranslation` (2499): an orthogonal permutation action on the full bond space, restricted to the actual carrier. Surjectivity follows from finite-dimensionality and the proved isometry, not from a spectral assumption.
- `twoSite_dilPattern` (2537): the defect parity pattern is invariant. The stride is **2**, not 2q.
- `twistU_twoSite` (2549) and `twist_holonomy_twoSite` (2558): actual field and holonomy invariance, for all amplitudes and angles.
- `carrierTranslation_inner` (2592), `carrierTranslation_add` (2599), and `carrierTranslation_commute` (2610): preservation of the original inner product, composition and commutativity on the full carrier.
- `twoSite_period` (2624): the displacement satisfies
  \[
  (4q)\,\tau_\mu=0
  \]
  on the physical torus. This proves a period, not a separate minimal-period theorem.

These establish the symmetry action and its background invariance. They **do not prove** that `twistA`, localized B, or `twistD` commute with it. The isometry is a coordinate translation, **not** a Fourier change of basis diagonalising the operators. In particular, invariance of a background plaquette word is not by itself a theorem about a varied Hessian, W dressing, constrained inverse, or nonlinear second jet.

## 2. New conditional obstruction to the old sign premise

**Conditional declaration:** `no_arbitrarily_small_control_of_negative_jet`, line **2712**.

```text
'AdalyFormal.Round6.Guarded.ClosedFormR1.no_arbitrarily_small_control_of_negative_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This formalises the implication suggested by the probe's negative leading coefficient, but **does not evaluate that coefficient or prove its hypotheses**.

At fixed q,R, suppose there are c<0, C>=0 and eta>0 such that for every amplitude between zero and eta there is a PSD singular carrier at an angle in (0,pi), and, for **every vector in its exact kernel**, the actual correction satisfies

\[
\left|\langle v,D_\varepsilon v\rangle
-c\varepsilon\|v\|^2\right|
\le C\varepsilon^2\|v\|^2.
\]

The theorem proves that arbitrarily small amplitudes cannot satisfy the unchanged `InitialKernelControl q R epsilon`. An explicit excluding cap is

\[
\delta=\min\left(\eta,\frac{-c}{C+1}\right)>0.
\]

The helpers are:

- `negative_linear_quadratic_bound` (2669): below that threshold, the linear-plus-quadratic upper bound is negative.
- `kernel_pairing_nonpos_of_remainder` (2680): the whole-kernel error bound makes every kernel pairing nonpositive.
- `not_initialKernelControl_of_negative_remainder` (2695): specialization to the genuine `twistA`, `twistD`, and original `InitialKernelControl`.

The estimate is deliberately required on the **whole** real kernel. A negative pairing on one vector alone cannot refute the premise's existential positive direction. The probe reports a complex-simple charged kernel, hence a two-dimensional real kernel; a formal U(1) dictionary would be needed to extend its scalar calculation to all those directions. No such dictionary is assumed as an established fact here.

This is a conditional failure theorem for one sufficient premise, **not** a proof of `GoalPos2`, `GoalNeg2`, or failure of every possible counterexample family.

## 3. Concrete obstruction to the requested closure

The inherited cofinal implication still requires an unproved amplitude theorem. The new symmetry facts do not supply any of its spectral premises.

There is also a substantive sign problem, not just an outstanding compiler step. The supplied probe reports, at the actual first charged character (7,7) for q=2,R=18,epsilon=10^-100,

\[
\langle v,Dv\rangle\simeq-1.8124680628969907\times10^{-170},
\]

and a separate finite-volume vacuum calculation reports

\[
c_1(2,18)\simeq-1.8124681040894914\times10^{-70}.
\]

These are the probe's high-precision **numerical evidence**, not new computations or Lean theorems. One finite negative amplitude alone does not logically disprove an existential arbitrarily-small-amplitude premise. The reported negative asymptotic coefficient makes the intended positive-sign proof untenable without first resolving the discrepancy in the exact operators. A certified negative whole-kernel expansion would instead feed the new conditional obstruction above.

The missing exact work is:

1. Prove naturality of the site averaging, support projections, W, mass, constrained H, localized source and raw second jet under the physical translation action. Then prove actual A/B/D commutation and a complete real/complex Fourier dictionary. The frozen definitions are `R2Ops1`, `ZR2Ops2`, `ZXR2Ops3`, `ZXR2Sector` and `R2Algebra`; no source transcriptions are promoted to definitions here.
2. Identify the actual first crossing across **all** characters and retain full complementary invertibility. The q=2 zero-character crossing is later and cannot supply the preceding positive-definite guard used by the proposed alternative.
3. Evaluate the finite-volume crossing kernel and the genuine pairing with the constrained source, including the near-degenerate left/right mixing. A half-space kernel or positive pre-asymptotic grid coefficient is not the fixed-radius epsilon-to-zero coefficient.
4. Prove a remainder estimate at fixed q,R, and the requested parametric q,R control. None is supplied by the current appendix. The positive remainder/sign assertion requested for the unchanged route is numerically contradicted in its true small-amplitude regime.
5. Alternatively, find a different actual separating witness or sufficient premise and prove its cofinal arbitrary-cap obligations. The probe's same-kernel pre-crossing test has positive corrected form at the decisive tiny amplitude; no other negative vector or post-crossing separating witness was proved here. This does not exclude such alternatives.

Consequently there is **no closed-form small-block evaluation, no proved initial positivity theorem, no uniform positive-sign/remainder theorem, and no pinned-goal closure**. The furthest new unconditional result is the exact physical symmetry partial at line 2643. The inherited line-2382 bridge remains conditional and unchanged.

## Hygiene

All authored files are under `AHP/round6/closedform-r1/`. No protected source, earlier AHP round, lakefile, olean, paper, notes directory, expected output or extras was edited. No deletion, commit, push, direct compiler/Lake command, reproduction script, dependency update or BB terminal was used. The audit script checks artifacts only; it models no numerical operator.
