# Independent verification: S-2 odd, round 1

**Verdict: closes-goal.** All five required checks pass for `AdalyFormal.AHP.Round7.S2Odd.Goal1`.

## Fresh replay

Copied `Attempt.lean` byte-for-byte to `Attempt.verify.lean`, without editing the attempt or replay. Ran directly through the bash tool:

```sh
AHP/round3/lean1.sh AHP/round7/s2-odd/r1/Attempt.verify.lean
```

The invocation completed normally. `Attempt.verify.lean.exit` contains **0**. The fresh log contains **zero errors and zero warnings**. No direct Lake command, build, dependency update, reproduction script, or numerical job was run.

## Required checks

1. **Compilation: PASS.** Independent wrapper replay exited 0; evidence is `Attempt.verify.lean.log` and `Attempt.verify.lean.exit`.
2. **Exact main type: PASS.** The source declares `theorem goal1_proved : Goal1 := goal1_of_goal2 goal2_proved` inside `AdalyFormal.AHP.Round7.S2Odd`. The fresh compiler check prints `AdalyFormal.AHP.Round7.S2Odd.goal1_proved : Goal1`, without any parameters or additional hypotheses. `Goal1` is the unchanged pinned declaration in that namespace. In particular its leading quantifier is universal over every natural ell at least two, and its exponent/radius/cap order is retained. The compiled `goal2_proved : Goal2` supplies the stronger all-exponents, all-radii-at-least-18 construction.
3. **Pin preservation: PASS.** The complete bytes of `AHP/round7/s2-odd/pin/Statement.lean` occur exactly once, unchanged, at byte offset 32 in the attempt and replay. The only preceding bytes are `import D1Final\nimport ZR8Class\n\n`. The complete pin includes its `import ZT5A`, definitions, goals, namespace delimiters, and checks. No goal replacement occurs afterward.
4. **Dependencies: PASS.** All **46** source `#print axioms` commands have dependency records in the fresh log. Every list is a subset of `propext`, `Classical.choice`, `Quot.sound`; one declaration has no axioms. The parser includes apostrophe-bearing names. The main record is:

   ```text
   'AdalyFormal.AHP.Round7.S2Odd.goal1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

5. **Forbidden constructs: PASS.** A whole-source word-token scan, including comments, finds none of `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`. Imports are only `D1Final`, `ZR8Class`, and `ZT5A`, each present under `lean/src`; there are no AHP imports. The source has 28 local definitions/theorems. Inspection of the extension confirms ordinary proof terms and tactics, with no alternate elaborator or declaration substitution.

## Integrity

SHA-256:

- Original and byte-identical replay: `000f5c6e860d67172468f2fa762344fd17de9586943ecc9c3b9c4659723ee835`
- Current complete pin: `fcba7f81a4d1e8f358d2bae1c7627f017919795b2bf3de257c39b3d68afaca41`
- Independent replay log: `f671f4866cc7c562f5338fffb1e3b4c85c484e04077dd8ab4fa6023dc091bf74`

The original attempt was not modified. This verification wrote only the replay, its wrapper outputs, and this report under `AHP/round7/s2-odd/r1/`.

## Scope

This closes the exact four-bond proper-domain non-vacuity pin, including odd blocking factors greater than eleven. The witnesses are flat and have depth two, with actual factor-12 coverage, positive capped smallness, compatible geometry/Lambda, and positive-energy admissible competitors. It does not identify the class with the printed class, establish non-flat richness, settle odd sites-only coverage, or prove any guarded operator conclusion. The broader guarded question remains outside this verification.
