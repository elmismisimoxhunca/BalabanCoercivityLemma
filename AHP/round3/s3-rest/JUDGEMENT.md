# Judgement — S-3 remaining summands

**Status: `partly-closed`.** The normalized unit-constraint branch, **GoalPos2**, is proved and independently verified. The primary raw-constraint **GoalPos1** is not closed by the supplied attempts. No negative witness was produced. This is not a certification of the complete printed coercivity lemma.

## What is now proved

Under the unchanged round-two inverse guards, dividing **both** the unit constraint and its quadratic remainder by ell gives exact agreement of:

- the separate mass subtraction and final nonlinear J subtraction;
- the whole quadratic form, for every unit-bond field B;
- the reconstructed C and independent-field bond energy, for every independent field Bt;
- the complete frozen and pinned printed instance inequalities, for every real gamma.

The scale is **\(c(\ell,k)=1\)**, with **a unchanged everywhere**. Both linked p.421 H/C conventions and every pinned depth are covered. No extra corridor-invertibility or support assumption was added to the positive goal.

All names in the next table have prefix `AdalyFormal.Round3.S3Rest`. Paths are relative to this directory.

| Pinned branch | Disposition | Decisive evidence |
|---|---|---|
| `GoalPos2`, normalized constraint and remainder | **Closed: holds** | `r1-prove/Attempt.lean:1268`, `goalPos2_proved : GoalPos2`; independent `r1-prove/Attempt.VERIFY.md` |
| `GoalPos1`, raw constraint and remainder | **Open in the supplied verified results** | No proof of this goal or compiled unrestricted raw/normalized equivalence |
| `GoalNeg2` | Excluded by the accepted positive theorem and the pin's incompatibility helper | `pin/Statement.lean:529`, `GoalNeg2_implies_not_GoalPos2`; no new standalone negation theorem added here |
| `GoalNeg1` | No witness; refuter supplies a builder-compiled impossibility theorem, not a positive-goal closure | `r1-refute/Attempt.lean:1277`; no independent verification report |

The stronger accepted theorem `restComparison_normalized` at `r1-prove/Attempt.lean:1252` needs only `InversesExist P r`, not the configuration predicate. Thus the result is not obtained by exploiting contradictory class or test-field assumptions. It does not establish that the inverse guards have admissible inhabitants.

The separate mass and energy identities at lines **1107** and **1111** need no inverse guard and do not depend on the unit-constraint reading. Their units are therefore settled for both branches. The outstanding raw-branch obligation is not a new mass/energy calculation: it is the unrestricted remaining operator comparison and its assembly into the exact pinned goal.

### Why the nonlinear comparison is substantive

In the accepted attempt, lines 1117–1160 identify the genuine normalized first jet, matching second coefficient, coupled corridor matrix/lift, Dtilde and C. `H0inv_eq_ring_inverse` at line 1128 covers both the bijective and singular branches, so it does not silently strengthen the pin. Lines 1163–1219 compare physical H1 through the full multilevel inverse and use top spacing one for both H/C conventions. Lines 1221–1233 cancel the physical source's inverse-cubed mesh factor against the fine pairing and identify the complete final nonlinear term, including its factor two. Lines 1235–1270 combine this with the reused first-term identity and transfer the unchanged independent-field domain through the inequality.

This is more than the round-two first-summand theorem. It uses actual background-derived jets and J, not freely chosen matrices or second jets.

## Evidence accepted and checked

The independent verifier compiled a byte-identical copy exclusively through the authorized wrapper:

```text
AHP/round3/lean1.sh AHP/round3/s3-rest/r1-prove/Attempt.verify.lean
```

Its `Attempt.verify.lean.exit` is **0**. Its log contains **143/143** requested dependency records, **0 errors**, and **28 nonfatal warnings**. Every dependency list is a subset of `propext`, `Classical.choice`, `Quot.sound`. In particular:

```text
'AdalyFormal.Round3.S3Rest.restComparison_normalized' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round3.S3Rest.goalPos2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This judgement re-read the pin, both attempts' NOTES, the sole attempt verification report, the new proof bodies and reused round-two proof. A fresh read-only source/hash/log audit confirmed:

- The complete **26,607-byte, 575-line** pin is a byte-identical prefix of both attempts and the positive verification copy.
- The positive source and verification copy are identical; all five hashes in `Attempt.verify.audit.json` still match the actual files.
- The round-two dictionary and reused proof block are unchanged. The sole import is frozen `ZT5A`.
- The accepted main declaration has exactly `GoalPos2`, in the correct namespace, without additional premises or a substituted goal.
- Raw forbidden-token scans of the pin and both attempts are clean, including implementation attributes and opaque stand-ins.
- The pin's own log has 23 permitted dependency records, exit 0 and no warnings/errors. Printing dependencies of a proposition definition is not counted as proving it.

Current decisive hashes:

```text
pin/Statement.lean
799b0124e2075c575d18c83c68af06e8501f6ee50f9d88b57647d8c2deb9ab3b
r1-prove/Attempt.lean and Attempt.verify.lean
9aa7238ddbff572aea7b0f0394eb22325280451f46087ec6e99da0f3518ae6a2
r1-prove/Attempt.verify.lean.log
25c714d0d87a315a0db64008db860dd9e285898afc45cda2a6975579c9f7c678
```

This judge ran **no new Lean compilation or numerical experiment**. Acceptance rests on the successful independent compilation of the unchanged artifact, checked against its current bytes and evidence. No build, reproduction script or dependency update was run.

## Refutation attempt: a useful obstruction, not closure

`AdalyFormal.Round3.S3Rest.RefuteR1.negative_goals_impossible` at `r1-refute/Attempt.lean:1277` states **\(\neg\mathrm{GoalNeg1}\land\neg\mathrm{GoalNeg2}\)**. The builder's current successful log records:

```text
'AdalyFormal.Round3.S3Rest.RefuteR1.negative_goals_impossible' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The fresh text/log audit confirms its source/log hashes match `AUDIT.json`, exit 0, **144/144** permitted dependency records, **29** nonfatal warnings and no errors. There is **no independent VERIFY.md or replay** for this attempt; the judge does not relabel its builder evidence as independent verification.

Its mechanism is concrete: `nonlinear_eq` at line 1261 equates the final nonlinear terms for both unit readings under the original inverse guards **plus H0 bijectivity**. `energy_eq` at line 1115 equates the independent energies. Hence both nonzero-denominator ratios required by a `ScaleWitness` are one. The separate `NoGammaMassRepair` obligation is never reached.

Even accepting this auxiliary impossibility theorem does **not** prove `GoalPos1`: the negative witnesses are deliberately stronger than exact negations, and they require genuine corridor inverses, whereas the positive goals include singular-corridor totalizations. The attempted numerical scalar/trace prefilter is exploratory evidence only, not a realized lattice counterexample or closure evidence.

Consequently neither `closed-fails` nor `closed-reduced` is justified. `partly-closed` reflects the unresolved raw positive branch, not an obligation to prove incompatible positive and negative alternatives.

## Pin versus print; remaining work

1. **Close the raw branch formally.** Supply a verified exact `GoalPos1`, or a verified raw/normalized reduction that actually settles it. The current raw operator lemmas require H0 bijectivity and do not cover the full positive pin, including singular-corridor extensions. No such unrestricted reduction is compiled in the supplied attempts.
2. **Dtilde's source identification remains qualified.** CMP99b p.427 does not specify its coefficients. The pin uses CMP109 p.267's lifted remainder. This judge directly inspected both saved page images: the later page displays the lift and explicitly refers to (3.156), but also explicitly changes delta-function gauge fixing to exponential gauge fixing. That is supporting source evidence, not a proof of transfer to every earlier setting. A CMP99b-only identification remains a reading question.
3. **Coupled versus local constraint solve.** The reconstructed inverse solves the retained coupled dropped-bond system. Neither attempt proves equivalence to the source's local single-variable solve, its global coarse-lattice right inverse, or exact parametrization of all printed support/Ax/global-Q1 fields. The positive instance inequality retains the frozen independent-field domain.
4. **Existence and analytic conclusions.** At singular corridors the normalized theorem compares totalized extensions, not ordinary inverses. It supplies no inverse existence from small-field regularity, positivity, guarded non-vacuity, uniform coercivity threshold, Gaussian integral or covariance theorem. In particular, (3.157) itself is a Gaussian identity; the compared lower-bound assertion follows (3.158).
5. **Other fidelity conventions remain.** Finite periodic three-dimensional SU(2), aligned tiling/padding, factor-12 class and added coverage, both-endpoint class regularity, inside-plaquette Delta/J, and genuine componentwise averaging primitives are retained. Their complete printed/analytic identification, the touching-operator issue and source power/odd-L conventions are not settled by this normalization result.

**Approved plain-language conclusion:** The normalized representation now has exactly the same mass, nonlinear term, energy, C and full inequality as the frozen construction, under the pinned inverse guards, with no rescaling of gamma or a. The separately pinned raw representation is not yet fully verified, and the disclosed source and analytic identifications remain open.

Only this `JUDGEMENT.md` was written by the judge. Existing attempts, evidence, protected sources and other AHP paths were left unchanged; no commit or push was made.
