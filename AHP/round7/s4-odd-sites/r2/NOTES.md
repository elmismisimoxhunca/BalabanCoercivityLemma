# S-4 odd sites — attack round 2

## Verdict and accepted evidence

**Open; `closedGoal = none`.** No pinned goal is closed. The pin and `PIN.md` were not changed. Final `Attempt.lean` begins with the complete pin verbatim and includes the earlier partial proof verbatim except its duplicate imports. It has 55 declaration/print pairs, only frozen imports `SoA3` and `SoPar`, and no prohibited source tokens.

**No new Lean compilation succeeded in this round.** Four direct wrapper invocations ended without sibling `.exit` files. The first three logs are empty; the fourth reports both heavy slots busy. No timed-out/interrupted target was relaunched. Subsequent file/process checks found no surviving s4 round-2 invocation. The final assembled `Attempt.lean` was not invoked again. Static checks and an empty compiler log do not certify elaboration.

The furthest fully compiled partial result therefore remains:

- File: `../attempt/Partial.lean`.
- Declaration: `AdalyFormal.Round7.S4OddSites.Partial.oddCfg_cofinal_class`.
- Retained dependency line, freshly checked in the original and byte-identical replay logs:

```
'AdalyFormal.Round7.S4OddSites.Partial.oddCfg_cofinal_class' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both prior exits remain 0; both prior logs have 21 dependency records, all permitted. These are **prior builder/replay records**, not new compilation evidence. The theorem supplies cofinal genuine sites-covered, plaquette-uncovered geometry and arbitrary-positive-cap per-cube regularity for the variable profile, at factor \(c=9\ell+1\). It supplies neither a violating field nor a nonzero-parameter inverse certificate. The separate prior flat-member guard theorem remains valid.

`exitCode = -1` in this round's result means missing final compilation evidence, not an observed Lean exit code.

## Required reading and unchanged target

Read HANDOFF, OPEN_ITEMS (including B, M, R, S), fidelity Stage-B results, rounds 2/3/5/6 results, original odd-sites draft/note/prosecution/Sol verdict, round-7 pin and prior attempts, and the frozen temporal-blocking/analyticity/even-refutation sources used below. No source-page image was newly checked.

The four unchanged goals use the genuine `FamilyTorusSitesConstAt`, with full `WellDefG` as an antecedent. Goals 1/2 quantify every odd \(\ell\ge3\), every \(c\ge10\), and every positive mass. Goals 3/4 fix \(\ell=13\) but still quantify all allowed factors and masses. The negative goals are pointwise failures, stronger than exact negations of the positive universal propositions. Nothing was weakened to factor 118.

## Negative direction: what was developed

### Recovery of the principal-log blocking draft

The final file retains round 1's unverified `R1` extension: actual first/second blocked temporal identities, unit-background temporality and H0 bijectivity on \(|t|<\pi/2\), for the genuine profile

\[
h_\ell=(1,-1,\ldots,1,-1,0).
\]

This goes beyond merely summing integers, if successfully verified. It still has no successful retained compiler check. This round does not upgrade its status.

### New local full-guard draft

`GuardNearZero.lean`, also included in final `Attempt.lean`, adds namespace `R2`:

- `oddCfg_unitBg_eq_flat`: a direct equality for the actual unit background, using the inherited blocking calculation.
- `oddCfg_eq_cartanOf`, `blockAngG_smul'`, `cartan_loops_near_zero`: a generic linear Cartan representation and a finite-dimensional neighbourhood avoiding the principal-log cut.
- `cartan_bg1_ana_zero`, `oddCfg_towerOK_zero`: an attempted verification of actual first-level analyticity and both required levels of regularity at zero. No evenness is used in this local Cartan step.
- `oddCfg_wellDefG_near_zero`: the intended conclusion is a positive, geometry-dependent neighbourhood on which the **entire** frozen guard holds, including nonzero parameters. The proof uses the structural determinant proxy, its analyticity at the flat member, its known nonzero flat value, H0 from the blocking draft, and the padded site inverse theorem.

All these are **unverified scripts**, not accepted theorems. The flat-regularity subproof was statically repaired after interruption to use the frozen `RegBg2_of_RegBg (RegBg_flat ...)`; it was not recompiled. Even a successful check would only establish a local neighbourhood of zero, whose size can depend on the chosen finite geometry. It would not certify units near a negative chain crossing, a violating form, or uniform spectral control.

### New mixed-weight calculation

`WeightCertificate.lean`, also included in the final file, adds namespace `R2Weights`. The proposed actual-holonomy formulas give \(\cos(2t)\) on the first transverse edge and \(\cos t\) on the seam from the zero entry. At \(t=\pi/3\), these are respectively \(-1/2\) and \(1/2\), while \(|t|<\pi/2\). `oddCfg_mixed_weights` explicitly constructs both sites on a torus with the stated room.

Again, these scripts are **not compiled**. Their role is narrow: expose why the new mean-zero profile cannot reuse a spatially uniform cosine coefficient in the old Z-chain argument. Mixed signs of genuine plaquette weights would not by themselves establish negativity of the constrained full form, nor any inverse guard. No numerical experiment was run.

## Positive direction: the guarded geometric shortcut

The prior compiled `no_eventual_geometric_upgrade` already excludes recovering plaquette coverage from site coverage just by increasing thresholds.

This round also developed a shorter, direct proof attempt in `GuardedGeometry.lean`, namespace `R2Geometry`, independent of the new blocking drafts. It builds the flat guard directly from frozen flat inverse results and instantiates the sites-covered/plaquette-uncovered geometry at \(c=9\ell+1\), at arbitrarily large exponent and radius and every positive cap.

The proposed `no_eventual_guarded_coverage_upgrade` says that even **all** geometry, class and smallness premises plus the **full inverse guard** cannot imply eventual plaquette coverage. Its specialization uses scale 13 and factor 118. Its witness is flat. It would rule out that proof shortcut, not coercivity itself.

This focused invocation also timed out without an exit or dependency log, so the stronger guarded shortcut obstruction remains **unverified**. A direct, guard-sensitive analytic estimate is not ruled out and was not obtained.

## Compilation record

All invocations used `AHP/round3/lean1.sh <file>` directly in the bash tool. No terminal, direct Lake invocation, build, reproduction script or dependency update was used.

| Target | Tool outcome / retained files | Acceptance |
|---|---|---|
| Initial `Attempt.lean` (the old assembly, preserved as `InterruptedAttempt.lean`) | Tool code 1; empty log; no `.exit` | None |
| `GuardNearZero.lean` | Tool code 1; empty log; no `.exit` | None |
| `GuardedGeometry.lean` | Explicit timeout after 300 seconds; empty log; no `.exit` | None |
| `WeightCertificate.lean` | Tool code 1; log says both heavy slots busy; no `.exit` | None |
| Final `Attempt.lean` | New final concatenation, not invoked again | None |

Observed shared-lock contention came from another worker's round-8 Lean command. The weight-certificate log explicitly names two numerical jobs occupying the heavy slots. These observations explain why scheduling was a concern, but do not identify a definitive transport/process failure cause; no out-of-memory diagnosis is claimed. No other worker's process or lock was changed. A coordination message was sent, not a request to terminate work.

`CompilationHistory.json` distinguishes the interrupted first assembly from the final source. `AUDIT.json`, regenerated by `audit.py`, checks exact pin prefixes, frozen imports, print coverage, token hygiene, prior source/replay byte identity, prior exits and actual prior dependency lines. It does not replace compilation.

## Concrete remaining obstacle

For refutation: obtain nonzero-parameter full inverse guards in the **relevant spectral regime**, a variable-weight coupled/perpendicular-sector reduction, and an admissible positive-energy competitor violating the **complete** frozen form; then meet the exact cofinal threshold/cap order and the all-factor quantifiers. The local near-zero guard draft, even if compiled, would not supply these. The arithmetic family \(c=9\ell+1\) does not settle either all-factor negative goal.

For proof: obtain a class-wide analytic estimate without relying on a geometric upgrade to plaquette coverage. The original geometric obstruction already prevents the simplest use of the both-coverage theorem.

Additionally, all new scripts still require successful compiler evidence. No new analytic or geometric declaration is accepted in this round. Only files under `AHP/round7/s4-odd-sites/r2/` were written. No protected file, earlier-round source, pin, paper or statement sheet was edited; no commit/push occurred. The mapped child has no durable goal (`get_goal` returned null).
