# Round 2 results

This report covers the four supplied round-two items. **Two pins hold, one primary pin is settled by reduction, and the guarded pin remains open. None of these verdicts certifies the whole printed coercivity lemma.** “Closed” below always refers to the stated pin, not every question in OPEN_ITEMS S-1–S-3.

The report uses the item judgements and independent compilation evidence. A read-only check against the current files confirmed source hashes, successful exit records, and permitted axiom lists for the four decisive S-1/S-2/S-3 attempts. It also confirmed that the guarded pin and four attempts are byte-identical to their independently compiled copies under `guarded/judge/`. The decisive logs contain 72, 40, 48 and 59 dependency records respectively; the five guarded logs contain 226 records including repetitions. Every dependency list is a subset of `propext`, `Classical.choice`, `Quot.sound`. S-3's positive attempt has 27 nonfatal warnings; the other checked logs have none, and all have exit 0 and no errors. The independent audits record unchanged pinned definitions and clean forbidden-token checks.

This consolidation ran no Lean compilation, build, reproduction script, dependency update or numerical experiment. It did not independently reread source-page images. Only this report was written; all existing sources, logs, judgements and protected files were left unchanged. Paths below are relative to `AHP/round2/`.

## S-2 non-vacuity — `closed-holds` for the four-bond pin

**Result.** The four-bond touching class has proper nonempty admissible domains, compatible Lambda, positive capped smallness, and genuine nonzero admissible test fields at arbitrarily large pinned scales. The witness uses a flat background with blocking factor and depth both two. It supplies actual factor-12 coverage, rather than assuming it. The stronger construction works for every positive cap, every integer m at least one, and every natural radius at least 18; the cofinal theorem chooses the radius before receiving the cap.

The corner branch has the opposite outcome: its coverage forces the base domain to be empty or the whole torus. Thus the two branches are decided, not contradictory.

**Compiled declarations settling the pin:**

- `s2-nonvacuity/r1-prove/Attempt.lean:293`: `AdalyFormal.AHP.Round2.S2Nonvacuity.goalPos1_proved : GoalPos1`.
- `s2-nonvacuity/r1-refute/Attempt.lean:519`: `AdalyFormal.AHP.Round2.S2Nonvacuity.goalNeg2_proved : GoalNeg2`.
- `s2-nonvacuity/r1-refute/Attempt.lean:524`: `AdalyFormal.AHP.Round2.S2Nonvacuity.not_goalPos2 : ¬ GoalPos2`.

Their independent axiom lines are:

```text
'AdalyFormal.AHP.Round2.S2Nonvacuity.goalPos1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.AHP.Round2.S2Nonvacuity.goalNeg2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.AHP.Round2.S2Nonvacuity.not_goalPos2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both attempts have independent `Attempt.verify.log`, `Attempt.verify.exit` and `Attempt.VERIFY.md` files beside them. The positive witness also rules out `GoalNeg1` through the compiled incompatibility implication; no separate standalone negation theorem is claimed. The negative goals assert universal saturation and are stronger than the exact negations of cofinal existence.

**Pin versus print.** This is an existence/saturation question, not the printed quadratic inequality. Four-bond coverage is not the printed one-corner selector. Both branches retain added site and single-box plaquette coverage, aligned product boxes with a common factor 12, frozen tower/Lambda/test-field conventions, and finite periodic three-dimensional SU(2) geometry. The corner obstruction comes from requiring one contained product box to touch all four edges of every one-corner plaquette; the source quotation does not supply that requirement.

**Still open.** No pinned non-vacuity branch remains undecided. The Stage-B four-bond non-vacuity hold is discharged, but identification with the full printed class is not. Odd blocking factors greater than eleven, non-flat richness and all-depth witness families are not supplied. There is no new changed-operator coercivity or inverse-existence conclusion. See [the judgement](s2-nonvacuity/JUDGEMENT.md).

## S-1 touching — `closed-reduced` for the coverage-repaired primary pin

**Result.** Added common-cube corner coverage forces the base domain to be empty or the whole torus. The corner and inside selectors then agree, and that equality propagates through Delta, J, the corrected inverse and the complete form. The existing frozen theorem supplies the primary headline. Only the base domain is classified; higher domains are not asserted to be constant.

**Compiled declarations settling the primary pin:**

- `s1-touching/r1-prove/Attempt.lean:689`: `Round2.S1.goalPos2_proved : GoalPos2`, the conjunction of coverage collapse and equivalence with the frozen headline restricted to empty/whole-torus bases.
- `s1-touching/r1-prove/Attempt.lean:575`: `Round2.S1.goalPos1_proved : GoalPos1`, the primary touching headline itself.

```text
'Round2.S1.goalPos2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Round2.S1.goalPos1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Evidence is in `s1-touching/r1-prove/Attempt.verify.log`, `Attempt.verify.exit` and `Attempt.VERIFY.md`. Both exact positive goals passed independent recompilation. Their paired negative goals are consequently ruled out logically; no separate double-negation declarations are claimed. The refutation attempt closed no negative goal.

**Pin versus print.** The pin changes both class regularity and the Delta/J selectors to endpoint/corner conventions, but adds site coverage and the same common-box corner coverage responsible for S-2 saturation. Those are not consequences of Balaban's touching convention. Product-box geometry is essential to the proof. The equivalence is between headlines, not reverse class inclusion; one direction may use the already-proved frozen theorem. Totalized inverses remain, with no new existence claim. The verifier could not independently image-check CMP102 p.277, so its central quotation remains inherited evidence.

**Still open.** Original S-1 on proper nonempty domains is neither proved nor refuted. The separate shell fallback, `GoalPos3`/`GoalNeg3`, is also undecided: it retains frozen coverage and imposes stronger regularity on additional edges. A source-justified non-collapsing touching formulation still needs its own result. Printed boundary-operator, averaging/constraint and inverse-existence identifications remain qualified. Thus “closed-reduced” does not mean all six pinned alternatives or the printed convention are settled. See [the judgement](s1-touching/JUDGEMENT.md).

## Guarded all-plaquette reading — `open`

**Result.** No compiled declaration settles either `GuardPencilT` or `P428Target8SG selAll selAll`, or either negation. They are two equivalent formulations of the same open question. Successful compilation of reductions does not establish their unresolved right-hand sides.

The independently compiled partial results are:

- `guarded/r1-prove/Attempt.lean:441`: `AdalyFormal.Round2.Guarded.R1Prove.goalPos2_iff_boundary_kernel`, reducing the headline to eventual location of the corrected kernel.
- `guarded/r1-refute/Attempt.lean:322`: `AdalyFormal.Round2.Guarded.RefuteR1.pencil_failure_iff_second_jet`, a pointwise criterion using the actual second jet.
- `guarded/r2-prove/Attempt.lean:554`: `AdalyFormal.Round2.Guarded.R2Prove.goalPos2_iff_boundary_response`, reducing the headline to eventual corrected boundary-response invertibility.
- `guarded/r2-refute/Attempt.lean:358`: `AdalyFormal.Round2.Guarded.RefuteR2.goalNeg2_iff_cofinalPencilFailure`, an equivalence with a failure certificate for which no witness was constructed.
- `guarded/r2-refute/Attempt.lean:335`: `AdalyFormal.Round2.Guarded.RefuteR2.candidate_excluded`, excluding the enlarged numerical tower from admissibility and the covered class despite its valid torus compatibility.

The dependency records, with line wrapping normalized, are:

```text
'AdalyFormal.Round2.Guarded.R1Prove.goalPos2_iff_boundary_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round2.Guarded.RefuteR1.pencil_failure_iff_second_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round2.Guarded.R2Prove.goalPos2_iff_boundary_response' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round2.Guarded.RefuteR2.goalNeg2_iff_cofinalPencilFailure' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round2.Guarded.RefuteR2.candidate_excluded' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Independent serial recompilation of the pin and all four attempts is documented in [guarded/judge/VERIFY.md](guarded/judge/VERIFY.md), `CHECKS.json`, and each compiled copy's `.lean.log`/`.lean.exit`. Numerical separation was only exploratory evidence. The first candidate fails torus compatibility; the enlarged candidate is formally excluded by block closure and coverage. Neither is an in-class counterexample.

**Pin versus print.** Only the carrier `Ginv` is guarded. Other inverses remain totalized; the already-proved full-guard theorem is a different statement. The pin retains all-plaquette operators with the frozen carrier/Dirichlet sandwich, both-endpoint class regularity, added coverage, factor-12 boxes, explicit threshold order and the frozen geometry. It does not substitute a touching-class repair. The S-3 first-term result below does not establish the all-plaquette dictionary or the missing inverse implication.

**Still open.** A positive proof needs uniform corrected boundary-response invertibility throughout the eventual class. A negative proof needs an exact in-class carrier-unit/corrected-singular separation, a positive-energy admissible competitor, and a cofinal family with radius chosen before every positive smallness cap. Neither was obtained. See [the judgement](guarded/JUDGEMENT.md).

## S-3 normalization — `closed-holds` for the guarded first-term pin

**Result.** Both supported, linked H/C conventions give exactly the frozen first summand, with scalar one, under the unchanged inverse guards. The physical pairing and inverse scaling account for eta; explicit top-level insertion equals tau-star. The stronger comparison works for every field B, not only constrained fields, and is not restricted to flat backgrounds, depth one or full support.

**Compiled declarations settling the pin:**

- `s3-normalisation/r1-prove/Attempt.lean:822`: `AdalyFormal.Round2.S3Pin.goalPos1_proved : GoalPos1`.
- `s3-normalisation/r1-prove/Attempt.lean:831`: `AdalyFormal.Round2.S3Pin.goalPos2_proved : GoalPos2`.

```text
'AdalyFormal.Round2.S3Pin.goalPos1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round2.S3Pin.goalPos2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Evidence is in `s3-normalisation/r1-prove/Attempt.verify.log`, `Attempt.verify.exit` and `Attempt.VERIFY.md`. Both exact goals passed independent recompilation with the 27 nonfatal warnings noted above. The ratio-witness negative goals are excluded by these positive theorems and the compiled incompatibility helpers; neither negative witness exists within the pinned comparison. The failed earlier abstract-matrix recipe is not an accepted normalization counterexample.

**Pin versus print.** The print's first term displays neither external eta nor tau-star. The pin independently reconstructs its physical pairings, weighted adjoints, inverse chain and insertion, while sharing the genuine frozen averaging jets. It tracks the argument of C in (3.14) and keeps the two H/C conventions offered on p.421 linked. This corrects the old Stage-A power count. The comparison keeps the frozen inside-plaquette localization and class/geometry conventions and explicitly assumes every inverse used on both sides exists. It is not a proof of those assumptions from small-field regularity. Inversion is performed on the full multilevel space; no inverse/compression interchange is asserted.

**Still open.** Both first-term goals are settled, but broader OPEN_ITEMS S-3 is only partially discharged. Common units for the separate mass subtraction, final nonlinear J term and bondEnergy remain to be checked. Comparisons of mass and J inside G1 do not settle those other summands. Inverse existence, positivity, guarded non-vacuity, printed averaging/class identification and the full support/constraint dictionary remain outside this closure. See [the judgement](s3-normalisation/JUDGEMENT.md).

The coverage-row and statement-sheet work from Stage B was not rerun or expanded here. Its existing qualified results remain; the protected sheet has not been edited. These round-two conclusions supersede only the corresponding old “still open” descriptions, not their remaining source-fidelity qualifications.

## Short table

| Item | Pinned status | Settled | Still open beyond that result |
|---|---|---|---|
| S-2 non-vacuity | `closed-holds` | Four-bond proper-domain witnesses; corner saturation | Full printed-class identification and stronger witness families |
| S-1 touching | `closed-reduced` | Coverage collapse, full-form comparison and primary headline | Proper-domain printed touching reading; shell fallback |
| Guarded | `open` | Reductions and exclusion of the tried geometry only | Both directions of the Ginv-only guarded headline |
| S-3 normalization | `closed-holds` | Both guarded first-term identities, scalar one | Other summands, inverse existence and remaining printed dictionaries |
