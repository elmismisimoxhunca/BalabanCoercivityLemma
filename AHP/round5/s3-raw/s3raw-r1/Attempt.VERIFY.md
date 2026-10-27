# Independent verification: s3-raw / s3raw-r1

**Verdict: closes-goal — exact pinned GoalPos1.**

## Replay

Copied `Attempt.lean` byte-for-byte to `Attempt.verify.lean` without editing the attempt. Executed directly in the bash tool:

```sh
AHP/round3/lean1.sh AHP/round5/s3-raw/s3raw-r1/Attempt.verify.lean
```

The replay completed normally. `Attempt.verify.lean.exit` contains `0`; `Attempt.verify.lean.log` contains zero errors and 28 warnings (deprecations and tactic/simp linters).

## Required checks

1. **Compilation: PASS.** Fresh serialized replay exited 0, independently of the author's original log.
2. **Exact target and unchanged pin: PASS.** All 26,607 bytes of `AHP/round3/s3-rest/pin/Statement.lean` are an identical prefix of both attempt and verification copy. The sole `GoalPos1` definition is the pinned definition. At line 1488, inside `AdalyFormal.Round3.S3Rest`, the successfully compiled declaration is explicitly:

   ```lean
   theorem goalPos1_proved : GoalPos1 :=
     GoalPos1_iff_GoalPos2.mpr goalPos2_proved
   ```

   There are no section variables, local notation changes, or alternate declarations shadowing this target. Its type is exactly `AdalyFormal.Round3.S3Rest.GoalPos1`, without additional hypotheses. The only import is the frozen module `ZT5A`; no AHP module is imported.
3. **Axioms: PASS.** Independently parsed all 161 dependency records, including multiline lists and the apostrophe-bearing declaration `inverse_smul'`. Their declaration names match all 161 `#print axioms` commands in order. Every record has an empty dependency set or a subset of `propext`, `Classical.choice`, `Quot.sound`. Main record:

   ```text
   'AdalyFormal.Round3.S3Rest.goalPos1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```
4. **Forbidden tokens: PASS.** Whole-source word-token scan, including comments, found no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`.

The first audit parser undercounted one record because it excluded apostrophes inside declaration names. After correcting that parser, all 161 records matched in order and all assertions passed; no Lean source or replay output was changed.

## Identity evidence

- Original and verification copy SHA256: `33ce45abad8892fc2c522708add52f2121b07f647b8e4953b00b7a74fe3ad9e1`
- Pin SHA256: `799b0124e2075c575d18c83c68af06e8501f6ee50f9d88b57647d8c2deb9ab3b`
- Replay log SHA256: `bdade3583f20d55d7b4a62c62e3b796413a01578c7d63f9ed5425b374ab528e4`

## Scope

The proof transfers the verbatim normalized comparison through raw/normalized equivalence. Nonzero scalar multiplication preserves corridor invertibility; singular matrices have zero totalized inverses, and nonsingular inverse scaling cancels the matching constraint/remainder scaling. No corridor-invertibility premise is added.

This closes the exact pinned raw normalization comparison, not an unconditional analytic coercivity theorem or a new source-reading audit. The pin's disclosed geometric, source-reading, and singular-corridor interpretation qualifications remain unchanged.

Only the verification copy, its generated `.log`/`.exit`, and this report were created by this verification. The attempt and pin were not edited.
