# Independent verification — S1 odd, round 2

## Verdict: incomplete; not `closes-goal`

The source-level checks pass, but the required independent replay has **no completion evidence**. This is not a demonstrated Lean proof failure. No attempt source was edited, and the replay was not relaunched.

## Replay

Created `Attempt.verify.lean` byte-for-byte from `Attempt.lean`, checked with `cmp`, and invoked directly through the bash tool:

```sh
AHP/round3/lean1.sh AHP/round7/s1-odd/r2/Attempt.verify.lean
```

The call had a 2400-second timeout budget. The tool returned `Command exited with code 1`, without diagnostic output. Subsequent inspection found an empty `Attempt.verify.lean.log`, no `Attempt.verify.lean.exit`, and no visible matching wrapper, flock, or Lean process. In particular, the tool's code 1 is **not an observed Lean exit code**. The exact interruption cause is undetermined. The absent exit file was checked again after the call; no second invocation was made.

## Required checks

1. **Independent exit 0: NOT ESTABLISHED.** `Attempt.verify.lean.exit` is absent. The original builder's `Attempt.lean.exit` contains 0, but it is not independent replay evidence.
2. **Exact pinned type without extra hypotheses: PASS at source level.** At line 477, inside `namespace Round7.S1Odd`, the declaration is exactly:

   ```lean
   theorem goal1_proved : Goal1 := not_touchFour_every_ell
   ```

   This namespace has no ambient variables or section hypotheses. `Goal1` resolves to the unchanged `Round7.S1Odd.Goal1`, not a conditional bridge. Its definition quantifies every natural ell at least 2 and every real mass satisfying `0 < a` and `a < 4`, and negates the exact fixed-ell/fixed-mass slice. There is no added inverse, sign, realization, or class-existence premise. The proof of `not_touchFour_every_ell` constructs the class and geometry, obtains the actual non-unit corner carrier, and applies the frozen full-form contradiction. Fresh compiler confirmation remains missing with the replay.
3. **Unchanged pin: PASS.** All 7,926 bytes of `AHP/round7/s1-odd/pin/Statement.lean` occur exactly once, unchanged, starting at byte offset 29. The only preceding bytes are `import D1Final\nimport GdPlaq\n`. The pin itself starts with `import D1Lit`. All three imports refer to frozen modules under `lean/src`; there are no AHP imports. Pin SHA256: `0c7cc8458e7d862e549c8e091325d906c3c448fb0ac7f08c9827a62cac9f3e4f`.
4. **Permitted dependency records: PASS for original builder log; NOT ESTABLISHED for replay.** The source has 51 `#print axioms` commands. The original log contains 51 dependency records, all subsets of `propext`, `Classical.choice`, `Quot.sound`, with no warnings or errors. The parser includes apostrophe-bearing declaration names. The independent log is empty, so it provides no dependency records and is not treated as a vacuous pass. Original main record:

   ```text
   'Round7.S1Odd.goal1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

5. **Forbidden tokens: PASS.** A whole-source raw word-token scan, including comments and strings, found zero occurrences of `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `opaque`, or `sorryAx`. The source contains no local syntax/notation, metaprogram, or stand-in replacing the goal.

## Identity and scope

Original and replay source SHA256 are both:

```text
ab9a9c0e1ed1592b3791f729652dc7474754897e93ea124d8b708927f6dffb39
```

Both sources are 24,232 bytes and remain byte-identical. The independent log is zero bytes (SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). Original source and builder logs were not modified.

The secondary `goal2_proved : Goal2` restricts the result to odd ell greater than 11. Neither result addresses masses at least 4, inverse-guarded readings, odd-ell sites-only coverage, or Balaban's unqualified printed assertion. The proof uses a singular carrier and totalized inverses.

**Conclusion:** no source defect was found, and the builder's successful compilation is corroborated as existing evidence, but the mandatory independent exit and axiom checks remain unverified. This verification cannot certify `closes-goal`. Completion needs an authorized successful independent replay; this verifier did not retry the interrupted invocation.
