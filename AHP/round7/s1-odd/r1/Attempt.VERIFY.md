# Independent verification: S-1 odd, round 1

**Verdict: not verified; no closes-goal certification.** Static checks pass, but the required independent exit-0 replay is missing. This is an incomplete verification, not a detected mathematical or Lean elaboration failure.

## Replay and interruption

Copied `Attempt.lean` byte-for-byte to `Attempt.verify.lean`, without editing either file. Invoked directly through the bash tool:

```sh
AHP/round3/lean1.sh AHP/round7/s1-odd/r1/Attempt.verify.lean
```

The bash invocation timed out after 200 seconds. As instructed, it was **not relaunched**. Subsequent polls, most recently at 2026-10-22T13:56:43Z, found no `Attempt.verify.lean.exit`; `Attempt.verify.lean.log` remained empty (0 bytes). Process inspection found no surviving matching replay/wrapper process. Consequently no independent Lean success, failure code, dependency output, or completed type check can be reported. Missing exit evidence is not exit 0. The builder's existing successful log does not replace this replay.

No direct Lake command, build, reproduction script, dependency update, or numerical computation was run.

## Required checks

1. **Independent exit 0: NOT ESTABLISHED.** Missing replay `.exit` and empty replay log after the timeout. This alone prevents closes-goal.
2. **Exact main type: source check PASS; independent compiler confirmation unavailable.** At line 477 the attempt declares `theorem goal1_proved : Goal1 := not_touchFour_every_ell` inside `Round7.S1Odd`. The namespace has no surrounding section variables or extra hypotheses; the earlier `Round3.S1Proper` namespace is closed. `Goal1` is the unchanged pinned `Round7.S1Odd.Goal1`, universally quantified over every natural ell at least two and every real mass strictly between zero and four. There is no replacement definition, local notation, or custom elaborator changing the target. The theorem is not merely the old ell-two negative headline. The successful builder log prints its dependency record, but the fresh replay supplies no compiler evidence.
3. **Pin preservation: PASS.** All 7,926 bytes of `AHP/round7/s1-odd/pin/Statement.lean` occur exactly once, unchanged, starting at byte offset 29 in both attempt and replay. The preceding bytes are exactly `import D1Final\nimport GdPlaq\n`. This preserves the complete pin, including its original import, definitions, comments, goals, and namespace delimiters; no pin alteration was found afterward.
4. **Dependencies: builder evidence PASS; independent replay evidence MISSING.** There are 51 source `#print axioms` commands and 51 dependency records in `Attempt.lean.log`. Every recorded list is a subset of `propext`, `Classical.choice`, `Quot.sound`. The parser includes apostrophe-bearing declaration names. The original main record is:

   ```text
   'Round7.S1Odd.goal1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   The empty replay log cannot certify these records independently; this check is not counted as a fresh replay pass.
5. **Forbidden tokens: PASS.** Whole-source word-token scanning, including comments, found none of `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`. The source uses ordinary definitions, theorem proofs, and tactics, without declaration substitution. Imports are only `D1Final`, `GdPlaq`, and `D1Lit`, each present under `lean/src`; there are no AHP imports.

## Integrity

The original and replay remain byte-identical, 24,232 bytes each.

- Original and replay SHA-256: `ab9a9c0e1ed1592b3791f729652dc7474754897e93ea124d8b708927f6dffb39`
- Complete pin SHA-256: `0c7cc8458e7d862e549c8e091325d906c3c448fb0ac7f08c9827a62cac9f3e4f`

The original attempt and its builder artifacts were not edited. This verification wrote only the byte-identical replay, the wrapper-created empty replay log, and this report under `AHP/round7/s1-odd/r1/`. No exit record was synthesized.

## Scope and outstanding action

The source targets failure of the exact unguarded four-bond-class, corner-operator slice for all ell at least two and all masses strictly between zero and four, with the pinned threshold order retained. Its odd-ell-greater-than-eleven restriction is also present. The singular-carrier mechanism does not settle inverse-guarded readings, odd sites-only coverage, masses at least four, or Balaban's unqualified printed assertion.

Independent verification remains incomplete. A new authorized replay with sufficient time to acquire the serialized/heavy slot and finish is needed; this verifier did not restart the timed-out invocation. No closes-goal result is issued.
