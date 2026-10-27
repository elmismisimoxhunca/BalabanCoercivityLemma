# Independent verification: qualitative, round 2

**Verdict: does-not-close-goal.** The copy compiles cleanly, but the main theorem has an additional, unproved coupling hypothesis. This agrees with the attempt report's explicit non-closure claim.

## Checks

1. **PASS — fresh compilation exits 0.** Copied `Attempt.lean` byte-for-byte to `Attempt.verify.lean`, then invoked exactly once:
   ```sh
   AHP/round3/lean1.sh AHP/round9/qualitative-r2/Attempt.verify.lean
   ```
   `Attempt.verify.lean.exit` contains `0`. The copy's log contains no errors, warnings, or `sorryAx`. No other compiler invocation was used.
2. **FAIL — main declaration is not an unconditional pinned goal.** At line 11729:
   ```lean
   theorem goalNeg2_of_cofinalCanonicalCoupling (h : CofinalCanonicalCoupling) : GoalNeg2 :=
     goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalCanonicalCoupling h)
   ```
   In namespace `AdalyFormal.Round9.Guarded.QualitativeR2Joint`, its type is `CofinalCanonicalCoupling → AdalyFormal.Round2.Guarded.Pin.GoalNeg2`, not exactly `GoalNeg2` or `GoalNeg1`. `CofinalCanonicalCoupling` (line 11711) requires definiteness of the actual correction derivative at cofinally many dyadic scales and even radii; no proof of that premise is supplied. The alternative theorems at lines 11906 and 12102 likewise require `CofinalAnyProfileCoupling` and `CofinalAnyPathCoupling`, respectively. Successful compilation therefore verifies conditional reductions, not closure.
3. **PASS — unchanged pin.** All 16,596 bytes of `AHP/round3/guarded/pin/Statement.lean` occur unchanged as the exact prefix of both source and verification copy.
4. **PASS — allowed axiom dependencies.** All 774 source `#print axioms` commands have corresponding dependency records in the fresh log, matched in order by declaration basename. Of these, 772 list dependencies drawn only from `propext`, `Classical.choice`, and `Quot.sound`; two report no axioms. The main theorem lists exactly the standard three. Multiline lists and declaration names ending in apostrophes were included.
5. **PASS — forbidden constructs absent.** A whole-file token scan, including comments, finds no `sorry`, `admit`, singular `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`.

## Reproducibility

Source and copy remain byte-identical after compilation: 628,675 bytes, 12,189 lines.

- Source/copy SHA-256: `b6dc8553ad1b8a7fdc5ff731b5c7df0fde0009979bdc90dbaba23b10efc5d052`
- Fresh log SHA-256: `ecec4700816494dff17f2104fb52ca55dc59d4b153dd7a8f16dc1ab1983b120e`
- Compiler evidence: `Attempt.verify.lean.log`, `Attempt.verify.lean.exit` in this directory.

No attempt or pin text was modified. Only the requested verification copy/report and the compiler wrapper's verification log/exit artifacts were created. **Closure remains unverified because check 2 fails; no closes-goal claim is warranted.**
