# Round 3 results

**S-1's exact unguarded proper-domain pin fails; S-3's normalized branch holds, with the raw branch still open; the guarded all-plaquette question remains open.** These are results about the specified formal statements, not a verdict on Balaban's unqualified printed lemma.

This report consolidates the three item judgements. A read-only check against the current files confirmed the decisive S-3 and S-1 source/log hashes, byte-identical independently compiled copies, exit 0, and permitted dependency lists. Their independent logs contain 143 and 44 dependency records respectively; S-3 has 28 nonfatal warnings, S-1 none. The guarded pin and all six attempts still match their independently compiled judge copies and recorded source hashes: seven exits 0, no diagnostics, 578 permitted dependency records including repetitions. Every checked dependency list is a subset of `propext`, `Classical.choice`, `Quot.sound`.

This consolidation ran no Lean compilation, build, reproduction script, dependency update or numerical experiment, and did not independently reread source-page images. Existing compilation evidence was produced through `AHP/round3/lean1.sh`. Only this report was written; protected files and other workers' changes were left untouched. Paths below are relative to `AHP/round3/`.

## S-3 remaining summands — `partly-closed`

**What holds.** With the unit constraint and its quadratic remainder both divided by the blocking factor, the pinned physical construction agrees exactly with the frozen construction: separate mass subtraction, final nonlinear J term, independent-field energy, reconstructed C, whole quadratic form and full instance inequality. Both linked p.421 H/C conventions are covered under the unchanged round-two inverse guards. The scale is \(c=1\), with \(a\) unchanged. The form comparison is for every field, not just a constrained or flat subspace.

**Compiled declarations settling the normalized branch:**

- `s3-rest/r1-prove/Attempt.lean:1268`: `AdalyFormal.Round3.S3Rest.goalPos2_proved : GoalPos2`.
- `s3-rest/r1-prove/Attempt.lean:1252`: the stronger `AdalyFormal.Round3.S3Rest.restComparison_normalized`, requiring the inverse guard but not the configuration predicate.

```text
'AdalyFormal.Round3.S3Rest.goalPos2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round3.S3Rest.restComparison_normalized' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Independent evidence: [Attempt.VERIFY.md](s3-rest/r1-prove/Attempt.VERIFY.md), `Attempt.verify.lean.log`, `Attempt.verify.lean.exit` and `Attempt.verify.audit.json` beside it. The complete pin is preserved byte-for-byte. This goes beyond round 2's first-summand identity.

**What does not follow.** The primary raw-constraint `GoalPos1` is not closed. The positive theorem includes singular-corridor totalizations without an extra corridor-invertibility premise; no verified unrestricted raw/normalized reduction covering those cases has been supplied. The separate mass and energy identities already cover both representations; the missing step is the remaining raw operator comparison and its assembly.

The refuter's `AdalyFormal.Round3.S3Rest.RefuteR1.negative_goals_impossible`, at `s3-rest/r1-refute/Attempt.lean:1277`, is builder-compiled with exit 0 and this permitted line:

```text
'AdalyFormal.Round3.S3Rest.RefuteR1.negative_goals_impossible' depends on axioms: [propext, Classical.choice, Quot.sound]
```

It excludes both strong negative witnesses, but has no independent verification. Even accepting it would not prove `GoalPos1`: those witnesses are stronger than exact negations, require genuine corridor inverses, and include a separate no-rescaling-repair obligation. The accepted normalized positive theorem already excludes its paired negative witness.

**Pin versus print.** CMP99b p.427 does not specify Dtilde's coefficients. The pin uses CMP109 p.267's lifted remainder and explicit reference to (3.156); that later passage also changes gauge fixing, so transfer remains qualified. The comparison retains the coupled dropped-bond solve, frozen independent-field domain, inside-plaquette operators, componentwise averaging primitives, added coverage and periodic three-dimensional SU(2) geometry. It does not identify the source's local single-variable solve or its full support/axial/global-Q1 parametrization. The lower-bound statement follows (3.158); (3.157) itself is a Gaussian identity, not the inequality proved equivalent here.

**Still open:** the raw positive branch; the source transfer and constraint/operator identifications; inverse existence from regularity, positivity and guarded non-vacuity. No new uniform coercivity threshold or Gaussian covariance theorem is established. See [the judgement](s3-rest/JUDGEMENT.md).

## S-1 on proper domains — `closed-fails` for the exact unguarded pin

**What fails.** The full four-bond touching-class headline with corner-selected Delta and J is false. Unlike round 2's collapsing corner-coverage class, this class admits proper nonempty domains. The refutation supplies such slabs, actual coverage, compatible Lambda, arbitrarily small positive class caps and a genuine positive-energy admissible competitor in the required cofinal threshold order.

The background is identity on endpoint-touching bonds but carries exterior phases that the retained corner operators can still read. The actual carrier reaches a non-unit point. There the totalized inverse convention makes the complete selected form nonpositive, contradicting a positive lower bound on the competitor. This is a full-form refutation, not merely a negative raw-Hessian direction or numerical crossing.

**Compiled declaration settling the pin:**

- `s1-proper/r1-refute/Attempt.lean:354`: `Round3.S1Proper.goalNeg1_proved : Round3.S1Proper.GoalNeg1`.

```text
'Round3.S1Proper.goalNeg1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Here `GoalNeg1` is exactly the negation of `GoalPos1 = P428TouchFour`. Therefore neither alternative of this pin remains undecided. Independent evidence: [Attempt.VERIFY.md](s1-proper/r1-refute/Attempt.VERIFY.md), `Attempt.verify.lean.log`, `Attempt.verify.lean.exit` and `Attempt.verify.audit.json`. The positive attempt supplies a reduction to unit conditions, not a competing proof of the headline; it has no separate independent verification.

**Pin versus print.** Endpoint/corner selection alone does not identify CMP99's Dirichlet boundary operator: the retained background products can read exterior links. Added site and common-cube four-touch-edge coverage do not cover every selected corner plaquette. The pin retains factor-12 product boxes, guarded derivative stencils, separate per-cube gauges, frozen tower/Lambda/support conventions and totalized inverses. The contradiction fixes blocking factor two, so it does not decide the later odd-\(L>11\) convention. CMP102 p.277's quotation remains inherited evidence; the verifier could not independently obtain that page.

**Still open beyond the pin:** inverse-guarded or inverse-existence-presupposing corner assertions, a fully source-identified boundary interpretation, shell coercivity, odd blocking factors and remaining printed dictionaries. In particular, this singular-carrier counterexample does **not** refute Balaban's unqualified printed lemma or settle the separate guarded item. See [the judgement](s1-proper/JUDGEMENT.md).

## Guarded all-plaquette reading — `open`

**No compiled declaration settles a pinned goal.** `GuardPencilT` and `P428Target8SG selAll selAll` remain equivalent formulations of one undecided question; neither their truth nor their negation is established. Conditional implications are not closure.

Three passes produced stronger partial results. The positive side proves actual shell and jet locality, an inverse-relative stability criterion and a mixed-source description of boundary return. Its final route still assumes the cancellation it needs:

- `guarded/r3-prove/Attempt.lean:981`: `AdalyFormal.Round3.Guarded.R3Prove.goalPos2_of_diagonal_mixed_boundary_source_zero` proves `GoalPos2` **if** the eventual diagonal mixed-source cancellation holds. That premise remains unproved.

The negative side first excluded a thin-top probe, then repaired its geometry and competitor, and finally proved complete class membership:

- `guarded/r3-refute/Attempt.lean:924`: `AdalyFormal.Round3.Guarded.RefuteR3.wide_in_class_nonflat_competitor` supplies torus compatibility, admissibility, Lambda, both coverage clauses, regularity, capped positive parameters and a positive-energy admissible competitor for every even radius at least two. It fixes \(\ell=M=2\), \(k=1\), hence \(m=1\). Its base-point nonidentity conclusion is not a curvature or nonzero-correction theorem.

These are independently compiled partial results, with axiom lines:

```text
'AdalyFormal.Round3.Guarded.R3Prove.goalPos2_of_diagonal_mixed_boundary_source_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round3.Guarded.RefuteR3.wide_in_class_nonflat_competitor' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All six attempts and the pin were independently replayed by the judge; [judge/VERIFY.md](guarded/judge/VERIFY.md) and [judge/CHECKS.json](guarded/judge/CHECKS.json) record every copy, exit, hash and dependency check. It is now stale to say that class membership or a competitor is missing for the final single-defect family. What is missing is spectral separation and cofinality in the exponent.

**Still open mathematically:** prove eventual corrected boundary-response invertibility from the carrier guard throughout the pinned class, or construct exact full-carrier-unit/corrected-singular witnesses cofinally in \(m\) and then \(R\), with \(R\) chosen before every positive cap. Raw locality does not control inverse-propagated inputs, and invertibility alone gives no uniform inverse-response gap. The final candidate proves neither spectral condition and does not extend to unbounded \(m\). Numerical Fourier-sector sweeps and finite-difference checks remain exploratory, not exact operator or singularity certificates.

**Pin versus print.** Only Ginv is guarded; other inverses remain totalized. This is not the already-proved full-guard headline. Both selectors are all-plaquette, but the frozen carrier/Dirichlet sandwich and both-endpoint class remain, with added site/interior-plaquette coverage. No touching or shell repair is substituted. Factor-12 boxes, parameter ranges, threshold order, per-cube gauges, geometry and source/operator qualifications remain. The localized S-3 normalization results do not prove this all-plaquette inverse implication. See [the judgement](guarded/JUDGEMENT.md).

The round-two S-2 results and Stage-B coverage-row/sheet work were not expanded here. Their qualified results remain; the protected statement sheet was not edited, and its supported coverage-row correction remains unintegrated.

## Short table

| Item | Status | Settled in this round | Still open |
|---|---|---|---|
| S-3 remaining summands | `partly-closed` | Normalized branch: full comparison, scale one, unchanged mass parameter | Raw branch and disclosed source/existence identifications |
| S-1 proper domains | `closed-fails` | Exact unguarded four-bond-class corner-operator headline refuted | Guarded/source-identified boundary readings, shell and odd-scale variants |
| Guarded | `open` | Conditional proof routes and complete in-class candidate at fixed exponent | Both directions of the Ginv-only guarded headline |
