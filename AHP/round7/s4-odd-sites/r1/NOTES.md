# S-4 odd sites, attack round 1

## Verdict

**Open; `closedGoal = none`.** No `Goal1`–`Goal4` is proved or refuted. The pin is unchanged. `Attempt.lean` begins with the exact bytes of `../pin/Statement.lean`, followed by the earlier partial proof copied verbatim (only its duplicate imports omitted), then the two new proof drafts.

**Compilation limitation:** no successful whole-file compilation of the final `r1/Attempt.lean` was obtained. Do not count its new declarations as verified. The furthest fully compiled partial result remains the pre-existing

```
AdalyFormal.Round7.S4OddSites.Partial.oddCfg_cofinal_class
```

in `../attempt/Partial.lean`. Its current source is unchanged and byte-identical to `../verify/Partial.lean`; both retained exit records are 0. Its actual retained dependency record is

```
'AdalyFormal.Round7.S4OddSites.Partial.oddCfg_cofinal_class' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Those are **prior builder/replay checks**, not new compiler successes in this round. The final assembly does not inherit whole-file verification merely by copying this theorem.

## Required reading and scope

Read HANDOFF, OPEN_ITEMS (including B, M, R, S), the fidelity Stage-B results, round-2/3/5/6 results, the original odd-sites attempt/note/prosecution/Sol verdict, the existing round-7 pin and partial proof, and the relevant frozen temporal-blocking and even-refutation modules before constructing the new drafts. No page-image verification, numerical experiment, full build, reproduction command, or dependency update was performed.

All four goals retain the actual `FamilyTorusSitesConstAt` body, with full `WellDefG` as an antecedent. Goal1/Goal2 quantify every odd scale at least 3, every factor at least 10 and every positive mass parameter. Goal3/Goal4 fix scale 13 but still quantify every allowed factor and mass parameter. The pointwise negative goals are stronger than negations of the universal positive goals. No goal was weakened to the factor-118 subfamily.

## Negative direction: principal-log blocking of the variable-step profile

The inherited profile is

\[
h_\ell=(1,-1,\ldots,1,-1,0)
\]

with odd period \(\ell\), used on the genuine hidden direction-0 slice. Its aligned integer block sums vanish; its steps have magnitudes 1 and 2, so the fixed-magnitude parity obstruction does not apply.

Already compiled in the prior partial file:

- `oddProfile_block_sum`: aligned square sums vanish at every odd scale.
- `oddProfile_not_const_step`: this is not a fixed-magnitude step profile.
- `sliceCfg_class`: arbitrary Cartan phases on the hidden slice satisfy the genuine per-cube regularity predicate.
- `oddCfg_cofinal_class`: torus compatibility, admissibility, Lambda, site coverage, failed plaquette coverage and all-positive-cap regularity, cofinally in exponent and radius, at factor \(9\ell+1\) with thin width 19.
- `oddCfg_holCos_01`: the genuine plaquette cosine is the cosine of the neighboring profile difference.
- `oddCfg_zero_wellDefG`: the entire inverse guard holds at parameter zero.

### New draft, not accepted as a theorem

`BlockingCertificate.lean` isolates the new blocking calculation. It copies the pin and the needed profile definitions/proofs, and imports only frozen `SoA3` and `SoPar`. Its new namespace is `AdalyFormal.Round7.S4OddSites.R1`.

The intended strengthening is:

1. `oddProfile_abs_le`, `oddProfile_mod_shift`, `oddProfile_real_sum`: boundedness, torus-compatible periodicity, and the real aligned sum.
2. `sliceCfg_isUTemp`: identify the actual configuration with the frozen temporal-profile class.
3. `oddCfg_regBg2_level0`: level-zero loop angles avoid the principal-log cut for \(|t|<\pi/2\).
4. `oddCfg_bg1_temporal`: the **actual first blocked gauge** is identity at all aligned coarse sites, at every odd scale, throughout that interval. The proof uses `blocked_cartan`, `loopVar_uPhi`, the full block counts and the real mean-zero sum; it does not replace blocking by an integer sum definition.
5. `oddCfg_bg2_temporal` and `oddCfg_unitBg_temporal`: propagate the aligned identity through the second blocking and the unit embedding.
6. `oddCfg_H0_bijective`: the H0 part of the full guard throughout the interval, using the actual temporal-background theorem.

This is a plausible route beyond the old arithmetic-only cancellation, but **the final scripts have no retained successful compiler check**. The first full-file trial reported local rewrite/elaboration errors in steps 4 and 6. Five repairs were applied (simplifying the stride-one multiplier, reducing the lambda before rewriting, specifying the sum-block theorem's arguments, explicitly deciding the Fin inequality, and qualifying `scaleUp_succ`). They were not successfully rechecked. These declarations must not be cited as compiled results.

Even a successful check would not settle the negative goal: H0 is only part of `WellDefG`; the remaining inverse conditions, level-one regularity/analyticity, the constrained coupled/perpendicular-sector calculation, and a genuine negative full form would remain. Variable steps give nonuniform weights, so the uniform-weight chain theorem `chain_instance_S` cannot simply be substituted into `main_neg_S`. The factor restriction \(c=9\ell+1\), in particular 118 at scale 13, also does not decide the all-factor negative goals.

## Positive direction: test the full-guard coverage shortcut

The prior compiled `no_eventual_geometric_upgrade` shows that arbitrarily large thresholds cannot make site coverage imply plaquette coverage. Thus the both-coverage theorem cannot be applied simply by increasing the thresholds.

The new, separately drafted `GuardedGeometry.lean` tests a stronger shortcut: add **all** actual class and geometry premises, the positive smallness cap, compatible Lambda, and **the full inverse guard**, and ask whether plaquette coverage follows eventually. Its new predicate is `R1Geometry.EventualGuardedCoverageUpgrade`.

`no_eventual_guarded_coverage_upgrade` is a proposed refutation of that shortcut at every scale at least 3 and factor \(9\ell+1\), using the inherited cofinal geometry and its **flat** member with the full inverse guard. The specialization at scale 13 has factor 118 and every positive mass. The proof deliberately uses parameter zero: flatness does not repair the missing geometric coverage.

**This draft also lacks a successful compiler exit.** It is not counted as a new theorem. If verified, it would exclude guard-to-coverage recovery, not a guard-sensitive analytic coercivity argument. In particular, the flat configurations are not negative-form witnesses. A direct uniform coercivity estimate on guarded sites-covered but plaquette-uncovered configurations remains absent.

## Compilation history and evidence boundary

Every invocation was direct in the bash tool through `AHP/round3/lean1.sh`; no terminal, direct lake invocation, build or reproduction script was used.

| Target | Observed outcome | What counts |
|---|---|---|
| First `Attempt.lean` version | Exit 1; local tactic/elaboration errors | No whole-file success. Initial log later overwritten by the next invocation. Its exit is preserved as `Attempt.first-pass.exit`. |
| Corrected `Attempt.lean` | Bash timeout at 600 seconds; no fresh exit; empty current log | Not relaunched after the timeout. The older exit was stale and is not used for the corrected source. |
| Separate focused `BlockingCertificate.lean` | Tool returned failure; no sibling exit, empty log | No compiler success or semantic failure code inferred. Not relaunched. |
| Separate `GuardedGeometry.lean` | Tool transport timeout (`504 command_timeout`); no sibling exit, empty log | Not relaunched. No new accepted declaration. |

The wrapper's shared lock was held by other workers during observed polls. Later process checks found no live s4-odd-sites wrapper/compiler; neither missing exit materialized. Polling checked files and processes directly; no sleep loop, duplicate launch, process termination, or lock modification was used. Lack of a fresh exit is reported as **-1 (missing evidence)**, not as a Lean exit status. The final `Attempt.lean` adds the independent geometry draft after the blocking draft and was not invoked again.

`CompilationHistory.json` records the interrupted source hash and stale-exit observation. `AUDIT.json` records current hashes, the unchanged pin prefix, verbatim inherited partial, frozen-only imports, print coverage and token scan. It also rechecks the prior partial's successful original/replay logs. Static checks do not establish elaboration or theorem truth.

## Concrete remaining obstacle

For a negative answer, construct an actual guarded, sites-covered, per-cube-regular odd-scale background with a violating admissible competitor, cofinally in scale and radius with the required cap order; a mean-zero profile or a scalar spectral crossing is insufficient. For a positive answer, prove a class-wide analytic estimate without recovering plaquette coverage as a geometric consequence. Neither was obtained. Fresh compilation of the new drafts is also still required before claiming their narrower blocking or guarded-geometry statements.

Only files under `AHP/round7/s4-odd-sites/r1/` were written in this attack. The existing pin/PIN.md and earlier partial/replay evidence were not changed. Protected sources and other workers' pre-existing changes were left alone; no deletion outside this directory, commit or push occurred. The mapped child has no durable goal (`get_goal` returned null).
