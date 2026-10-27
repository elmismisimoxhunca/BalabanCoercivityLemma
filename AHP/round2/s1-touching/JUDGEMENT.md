# S-1 touching — round 2 judgement

## Decision

**Status: `closed-reduced`, for the explicitly coverage-repaired primary pin only.**

The independently verified positive attempt proves the exact preferred reduction `Round2.S1.GoalPos2`, and also the exact primary headline `Round2.S1.GoalPos1`. The added common-cube corner coverage forces the base domain to be empty or the whole torus. On this class the corner-selected operators and complete quadratic form agree with the frozen ones, and the headline follows from the existing frozen theorem.

**This does not settle Balaban's unmodified touching convention on proper nonempty domains.** The decisive coverage assumption is not supplied by the printed convention. The separate shell fallback remains undecided.

`closed-reduced` is appropriate because the pin expressly designates GoalPos2 as the preferred alternative route settling its primary question, not merely an intermediate comparison. GoalPos3 is a separate fallback, not a conjunct of that route. This status must not be reported as closure of every listed goal or of printed S-1.

## Exact goal accounting

All names below have namespace `Round2.S1`.

| Pinned goal | Disposition | Evidence |
|---|---|---|
| `GoalPos1 = P428TouchConsistent` | **Proved and independently verified** | `r1-prove/Attempt.lean:575`, `goalPos1_proved` |
| `GoalPos2 = TouchCoverageCollapse ∧ (P428TouchConsistent ↔ P428Target8Extreme)` | **Proved and independently verified** | `r1-prove/Attempt.lean:689`, `goalPos2_proved` |
| `GoalNeg1`, `GoalNeg2` | No negative proof; their paired positive propositions are proved, so these negations are ruled out logically | No separate negation-of-negation declaration is claimed |
| `GoalPos3 = P428Target8Shell` / `GoalNeg3` | **Neither proved nor refuted** | Both attempts explicitly leave the shell question open |

The first two accepted declarations print:

```text
'Round2.S1.goalPos1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Round2.S1.goalPos2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are proof-dependency records, not just the pin's dependency prints for proposition definitions. Their independently compiled closed types appear in `r1-prove/Attempt.verify.log:33–34`; their dependency records are at lines 84 and 45 respectively.

## What is now proved, in plain words

1. **The extra coverage removes all proper nonempty base domains.** A product box that touches all four edges of a square contains every corner of that square (`r1-prove/Attempt.lean:420–449`). Class cubes of a nested tower lie in its base. Consequently every corner-selected plaquette lies wholly inside the base (`corner_eq_inside_of_coverage`, line 501). Membership then propagates along every coordinate shift; periodic connectivity makes the base empty or the whole torus (`coverage_collapse_nested`, line 622; exact pinned `touchCoverageCollapse_proved`, line 628). Only the base is classified; higher domains are not asserted to be constant. The stronger nested-tower lemma does not require the headline's size or radius bounds.
2. **The comparison reaches the actual full form.** Lines 527–557 propagate selector equality through both Delta and J, the selected data, corrected operator, totalized inverse, mass subtraction, and nonlinear term. `instIneq_corner_iff_of_eq` at line 546 compares genuine `D1Lit.InstIneqS` with frozen `InstIneq`, not raw Delta or a substitute matrix. No invertibility or flatness premise is added.
3. **The exact primary headline holds.** `touchConsistent_of_frozen` at line 560 transfers touching regularity and coverage to the frozen class and reuses `AdalyFormal.M2RightInv.p428Target8` (`lean/src/RI6.lean:323`). All original quantifiers, thresholds, positive constants, the cap and `SidePow6` remain. `goalPos1_proved` packages that result.
4. **The exact reduced package holds.** `touchConsistent_iff_extreme` at line 684 establishes the pinned headline equivalence, and `goalPos2_proved` conjoins it with collapse. The extreme-to-touching implication uses collapse, class inclusion and actual-form equality. The opposite implication restricts the already-proved frozen headline and does not use its touching-headline premise, as PIN.md explicitly permits. Thus this is not a reverse class-inclusion theorem, a bijection of configurations, or a correspondence of arbitrary witnesses for the constants.

## Refutation attempt

`r1-refute/NOTES.md` correctly reports `closedGoal: none`. There is no independent `VERIFY.md` for that attempt; none was supplied or found. It contributes corroborating, builder-compiled partial results, not an accepted negative closure:

- `corner_instIneq_iff_frozen`, `r1-refute/Attempt.lean:492`: full instance equivalence under nesting and the pinned corner coverage.
- `old_slab_family_excluded`, line 526: every configuration on the specified old cofinal slab family fails the primary corner class, independently of phases and caps.

The builder's compilation exit is 0 and its main dependency line is:

```text
'Round2.S1.corner_instIneq_iff_frozen' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The search therefore did not produce a counterexample to any pinned goal. Negative raw-Delta directions outside primary coverage, finite coverage enumerations, and small-phase samples are not proofs of a headline or its negation. No numerical result is used to justify this judgement.

## Verification basis and current-file checks

I read the pin, both complete attempts and their NOTES, the positive attempt's complete independent verification report, and the mandated handoff/open-item/Stage-B records and S-1 specification, attack, decision and structural Lean comparison. The positive verifier independently recompiled the unchanged attempt with exit 0; see `r1-prove/Attempt.verify.log`, `Attempt.verify.exit`, `Attempt.verify.audit.json` and `Attempt.VERIFY.md`.

This judgement pass **did not run another Lean compilation or numerical experiment**. Its read-only text/hash/log audit confirmed against the current files:

- Both attempts retain all **22 pinned definitions byte-for-byte**, including namespace/variable context through the pin's checks and prints.
- The positive log contains **72 permitted dependency records**, covering all **67 local declarations** and five imported helpers. Both accepted theorem headers and printed closed types match the pin. The current pin, positive source, verifier log and exit hashes all match the verifier's recorded audit.
- The refuter's builder log contains **56 permitted dependency records**, covering all **47 local declarations** and nine imported helpers. This check is not a new independent recompilation.
- Both inspected logs have no errors or warnings. Both attempt sources have zero raw forbidden-token hits, and every import resolves under `lean/src`; neither imports another AHP file.

Current SHA-256 identifiers:

| Artifact | SHA-256 |
|---|---|
| `pin/Statement.lean` | `0ad24d3129dc87c72d1fdc8281a9f7f08a66526a17ef2a697431b8ad8be5ea7c` |
| `r1-prove/Attempt.lean` | `d45e27d564812a3b7679b3efdaad008ba833a74604dac5dc66cf32fd78bc5d40` |
| `r1-prove/Attempt.verify.log` | `153aef38bce2a0d463ab46fd1907e808a32d11075111d53410026def37385b40` |
| `r1-refute/Attempt.lean` | `d0ad2c5d323199275db34f7c0df294d81aae1b41d8b0de7fa450a98965100386` |
| `r1-refute/Attempt.lean.log` | `ee82326a344546c6962e68bea4928301e4faa30e3d47060e0e1507462cf3081c` |

## What remains open, and why this is not printed-statement closure

- **Original S-1:** a source-justified endpoint/corner reading permitting proper nonempty domains is not proved or refuted. The pin adds site coverage and requires all four edges of each one-corner plaquette to touch **one common class cube**. The collapse is a consequence of that extra requirement and product-box geometry, not of Balaban's touching convention alone. It cannot be used to say his domains collapse or his printed lemma is proved.
- **Shell fallback:** `P428Target8Shell` remains open in both directions. Its frozen coverage allows proper domains, while its `ReadBond` regularity controls additional edges with neither endpoint in the cube. The primary comparison does not apply to that different class. Stage B supplies a flat proper-domain hypothesis family and structural comparisons, not shell coercivity.
- **Retained fidelity qualifications:** product boxes, unique indices and common factor 12 are not replaced by arbitrary block unions or per-cube factors. Corner Delta/J remain a boundary interpretation rather than identification with the unrestricted displayed sums. Guarded derivative stencils, three-dimensional SU(2), periodic geometry, distance, exact base collar, Lambda/support conventions, parameter ranges and quantifier order remain those of the pin. The full Q/jet/C and eta/tau-star dictionaries and printed-inverse existence are not established here. Equality of the totalized operators introduces no new inverse-existence conclusion.
- **Source verification:** the independent verifier read the cited CMP99 pages and CMP109 p.251, but could not obtain the CMP102 p.277 image. That principal quotation remains inherited in this verification record. This judgement makes no new page-image verification claim.
- **Not supplied:** reverse class inclusion, arbitrary-union transfer, non-flat richness or a nonzero-test witness for the surviving extreme class. None is silently inferred from a true headline.

The next substantive S-1 task needs an explicitly approved, source-justified non-collapsing coverage statement, or a separate proof/refutation of the already pinned shell fallback. Changing coverage silently would change the question.

Only `AHP/round2/s1-touching/JUDGEMENT.md` was written by this judgement pass. No source, pin, attempt, compilation log, protected file, or other AHP path was edited; no build, reproduction, update, deletion, commit or push was run.
