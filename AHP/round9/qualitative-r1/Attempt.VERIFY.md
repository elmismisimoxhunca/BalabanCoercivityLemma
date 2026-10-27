# Verification: qualitative route, round 1

**Verdict: does not close the goal.** The independently compiled attempt proves a conditional reduction, not an unconditional `GoalNeg2` or `GoalNeg1`.

## Reproduction

Copied `Attempt.lean` byte-for-byte to `Attempt.verify.lean` and compiled the copy exactly once using:

```sh
AHP/round3/lean1.sh AHP/round9/qualitative-r1/Attempt.verify.lean
```

- Exit status: **0**, confirmed by `Attempt.verify.lean.exit`.
- Compiler output: `Attempt.verify.lean.log`; no errors or warnings.
- Source and copy: identical, 240829 bytes.
- SHA-256 of both: `b3b6e86b9cb17cb2e0c8a7a7c93bacdf1b348514e159e27d48f00058d5b841be`.

## Required checks

1. **PASS — compilation:** exit 0.
2. **FAIL — exact unconditional target type:** at line 4680, the main declaration is
   ```lean
   theorem goalNeg2_of_cofinalVacuumCoupling (h : CofinalVacuumCoupling) : GoalNeg2 :=
     goalNeg2_of_cofinalPathSeparation (cofinalPathSeparation_of_cofinalVacuumCoupling h)
   ```
   Its qualified name is `AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalVacuumCoupling`. Its type is `AdalyFormal.Round9.Guarded.Qualitative.CofinalVacuumCoupling → AdalyFormal.Round2.Guarded.Pin.GoalNeg2`, **not** exactly `GoalNeg2` or `GoalNeg1`. The extra premise is explicit and is not proved here. `GoalNeg2` resolves to the unchanged pin definition; no replacement definition of either negative goal occurs.
3. **PASS — pin fidelity:** the complete 16596-byte contents of `AHP/round3/guarded/pin/Statement.lean` occur unchanged at byte offset 0 in both the original and verification copy.
4. **PASS — axiom audit:** all 256 `#print axioms` commands have corresponding dependency records: 254 lists and 2 axiom-free records. Every listed axiom belongs to `{propext, Classical.choice, Quot.sound}`. The main declaration lists exactly those three axioms. Multiline lists and the declaration name ending in an apostrophe were included in the audit.
5. **PASS — forbidden constructs:** a lexical scan excluding nested comments, line comments, and string literals found no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque` tokens in executable source. The sole import is `DrEquiv`.

## Remaining gap

`CofinalVacuumCoupling` (line 4657) remains an additional, unproved cofinal premise. Successful compilation and permitted axiom dependencies certify the conditional theorem only; they do not discharge that premise. Accordingly, **closes-goal: false**.
