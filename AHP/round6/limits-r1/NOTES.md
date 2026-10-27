# Round 6 adversarial limits, pass 1

**closedGoal: `none`. No obstruction at arbitrarily small positive amplitude was proved.**

The exact partial result concerns **epsilon = 0**, which the round-5 sufficient premise explicitly excludes. It must not be promoted to an obstruction to that premise or to either pinned goal. The supplied probe's negative small-positive-amplitude coefficient remains numerical evidence, not a theorem here.

## 1. Final source and verification limitation

`Attempt.lean` is the entire `AHP/round5/guarded/ivt-r2/Attempt.lean` followed by `Appendix.lean`. Thus the complete round-3 pin and round-5 bridge are verbatim byte prefixes. The sole import is frozen `DrEquiv`. No goals, family definitions, selectors, or quantifiers were changed.

The exact source now in `Attempt.lean` **did complete a wrapper compilation with exit 0** during this turn, before an attempted extension. However, the successful log was subsequently overwritten by the extension's timed-out wrapper invocation. Consequently there is **no complete retained dependency log and no fresh final replay**. This evidence limitation is not hidden as an ordinary successful final-path audit.

Compilation sequence, all directly in bash through the required wrapper:

1. First completed exit 1: missing qualification of `Ug_zero` and elaboration of `P.ell`.
2. Second completed exit 1: a conditional-expression simplification left the exterior case.
3. Third completed **exit 0**, for precisely `round5/guarded/ivt-r2/Attempt.lean + Appendix.lean`. `Appendix.lean` has not changed since that successful call.
4. Added an independent boundary-vector appendix and invoked the same wrapper. The bash call **timed out after 180 seconds**. The existing `.exit` was older than the new source, so it was identified as stale, not counted as the new run's exit. Two subsequent checks found no new exit or surviving matching process. The compile was **not relaunched**.
5. Preserved the timed-out source as `BoundaryDraft.lean` and its partial log as `BoundaryDraft.interrupted.log`. Moved the old successful exit record to `PriorSuccessfulRun.exit`. Restored `Attempt.lean` to the exact source from step 3. There is deliberately no `Attempt.lean.exit` or `Attempt.lean.log` pretending to be a fresh complete verification.

`VERIFICATION.json` records the pre-restoration hashes and timestamps. Final source SHA-256:

```
735d91253d71b315409743238b4cc5366c208476b092ce5784b37c73e4eaa5eb
```

`python3 AHP/round6/limits-r1/audit.py` passes the source/provenance checks. It finds 145 local declarations, each with a dependency print command; frozen-only imports; unchanged pin/bridge prefixes; and no forbidden constructs. The interrupted log has 138 complete dependency records, all using only `propext`, `Classical.choice`, `Quot.sound`, but stops before the new results. **That partial log is not an axiom audit of the new results.** `CHECKS.json` explicitly reports `completeFinalDependencyAudit: false`.

The earlier failed-run logs displayed permitted dependencies for the unchanged conditional obstruction lemmas, but are not complete successful-run evidence either. No axiom record for the zero-amplitude theorem is fabricated. Under the requested strict retained-print criterion, this pass therefore does **not** claim a fully audited final theorem package.

## 2. Exact partial statements in the previously successful source

All new names have prefix `AdalyFormal.Round6.Guarded.LimitsR1.`

### Genuine correction at zero amplitude

- `twistD_zero_amplitude`, line 2421: for every positive q, even R with `3 <= R*(2*q)`, every real mass a and exterior angle t,

  \[
  \operatorname{twistD}(q,R,0,a,t)=0.
  \]

  This is an equality of the actual full-carrier assembled correction, not a compressed matrix or only a diagonal pairing. It needs no inverse guard. The proof uses the frozen base-flat theorem `lean/src/GdR6b.lean:82` together with the exact `G1inv = Ginv - Delta2` identity. At epsilon zero, every link with base point in Omega0 is identity; the arbitrary exterior twist is retained.

- `vacuum_correction_pairing`, line 2445: the genuine correction form is exactly zero on every carrier vector, hence on any crossing kernel.
- `vacuum_pencil_iff_carrier_unit`, line 2454: the pinned `CPen` is equivalent to the carrier guard on this zero-amplitude path, at every angle and mass. Thus this path cannot supply a carrier-unit/corrected-nonunit separation.
- **`not_initial_control_zero`, line 2487**: for every positive q and even R with the room condition,

  \[
  \neg\operatorname{InitialKernelControl}(q,R,0).
  \]

  This does not assume that an initial unit or a crossing already exists. Assuming `InitialKernelControl` supplies initial PSD and the unit; the copied first-crossing theorem then produces a PSD nonunit inside `(0,pi)`. Its required positive correction form contradicts the exact zero correction. This holds at all the requested scales/radii, but **only at the excluded amplitude zero**.

### Conditional obstruction at positive amplitudes

`not_initial_control_of_kernel_nonpositive` (2495) states the logically correct obstruction: at one PSD singular point inside `(0,pi)`, the correction must be nonpositive on **every vector in the exact real kernel**. One negative sampled vector alone does not contradict the existential sign clause.

`no_small_control_of_kernel_expansion` (2508) proves a precise route from a *proved* uniform kernel expansion to an amplitude interval of failure. Its hypotheses require positive c, eta, nonnegative C and, for every `0 < epsilon < eta`, an actual PSD singular point t with

\[
\langle v,D_\varepsilon v\rangle
\le (-c\varepsilon+C\varepsilon^2)\|v\|^2
\quad\text{for every }v\in\ker A_\varepsilon(t).
\]

It concludes failure of `InitialKernelControl` for every

\[
0<\varepsilon<\delta,
\qquad \delta=\min\{\eta,c/(C+1)\}>0.
\]

**The expansion premise is not proved.** No numerical coefficient was inserted into it.

`not_round5_premise_of_small_obstruction` (2535) makes the quantifier issue explicit: one fixed admissible q,R with such an entire small-positive-amplitude interval already refutes the *all-q sufficient premise* of the round-5 bridge. That would not prove the positive pinned goal, nor negate the negative pinned goal: the bridge is only sufficient. This distinction is essential. An eventual negative result for the pinned goal would still need its own cofinal family.

## 3. Unverified boundary-vector extension

`Boundary.lean` proposes that the **bare outgoing boundary-bond vector** used in the negative-endpoint proof is killed by the genuine correction at every epsilon, a and t. The argument is that W fixes that vector (`lean/src/D1Geo2.lean:74`), while the second jet only reads bonds with both endpoints in Omega0 (`lean/src/ZR8DataA.lean:83`). The general polarization lemma in `JetLemma.lean` is copied verbatim from `AHP/round5/guarded/structural-r1/Attempt.lean:529-572`, with its namespace retained.

The attempted combined file is `BoundaryDraft.lean`. Its invocation timed out before reaching this extension. **Neither `twistD_rightVector_zero` nor `rightVector_orthogonal_correction_range` is counted as compiled.** They are not present in final `Attempt.lean`.

Even if this extension compiles later, it does not show that the actual crossing kernel is invisible. A crossing vector has a propagated interior tail, unlike the bare endpoint bond. This cannot resolve the negative tiny-amplitude sign or the observed-transfer pole.

## 4. Concrete remaining mathematical obstacle

Read the round-5 results, all five requested NOTES files, and the supplied round-6 probe report in full. The probe warns against treating its 32 positive samples as arbitrary-cap evidence. At q=2,R=18 it instead reports a negative leading coefficient and a negative exact-root numerical pairing at epsilon `1e-100`.

To turn that finding into a Lean obstruction at **positive** amplitudes, this pass still lacks:

1. An exact translation/Fourier dictionary for the actual carrier, W, constrained inverse, raw second jet, and assembled correction—not merely a cell matrix transcription.
2. A finite-volume kernel/branch identification, with PSD of the full carrier and exclusion of all other charged/neutral characters at the claimed first point.
3. A proof that the entire real crossing kernel is controlled. The probe reports one complex mode, hence two real dimensions; its scalar negativity needs a proved symmetry/spanning argument to cover all real kernel vectors.
4. An exact negative leading coefficient and remainder bound at fixed q,R as epsilon tends to zero. The extremely small finite-volume splitting cannot be replaced by the easier half-space or pre-asymptotic positive-grid law.

The epsilon-zero identity supplies none of these continuity/rank/expansion facts. No sign is proved at one positive amplitude here, let alone an interval. Neither initial corrected-PSD failure nor kernel invisibility for the actual crossing mode is proved.

No new numerical job was run. The probe's values are quoted only as prior evidence, not independently reproduced or interval-certified by this pass.

## 5. Scope and hygiene

All writes were under `AHP/round6/limits-r1/`. No protected file, earlier round, lakefile, build artifact, or other track was edited. No direct Lean/Lake command, build, dependency update, reproduction script, BB terminal, commit, push, or deletion was used. The required wrapper was the sole compilation entrypoint.

**Final disposition:** `closedGoal = none`; furthest previously compiled unconditional partial is `not_initial_control_zero`, with the missing retained successful dependency log explicitly disclosed. The unchanged positive-amplitude route remains formally unresolved. The negative numerical evidence is not upgraded to a theorem.
