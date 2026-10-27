# Independent verification — LongArm

## Verdict

**FAIL: the claim is not accepted as stated.** The verbatim copy compiles cleanly and passes the axiom/token checks, but the named main declaration does **not** have type `TailEndpointNegative`, and `TailEndpointNegative` is not one of the permitted `GoalNeg2` premises and has no compiled bridge to `GoalNeg2` in the supplied artifact.

## Verification performed

- Copied `AHP/round14/pathchoice/r2/LongArm.lean` to `AHP/round14/pathchoice/r2/LongArm.verify.lean`.
- Compiled only with:
  ```sh
  AHP/round3/lean1.sh AHP/round14/pathchoice/r2/LongArm.verify.lean
  ```
- `AHP/round14/pathchoice/r2/LongArm.verify.lean.exit` contains `0`.
- Source and verification copy are byte-identical (`cmp` passes), with SHA-256
  `ea553e4e37fcd03d762115dca4915d88d903047df35291b93a7bb0d4ca89ab5e`.
  Thus every declaration in the verification copy is verbatim from the requested source.
- The verification log is byte-identical to the original `LongArm.lean.log`, with SHA-256
  `2b6f295454e33ebcf18c1b6d29eefe53d155bff7f88f8d8256d7457b2541b216`.
- All 378 `#print axioms` commands are accounted for: 376 dependency records and 2 no-axiom records. Every dependency set is a subset of `{propext, Classical.choice, Quot.sound}`.
- No warnings, errors, `sorry`/`sorryAx`, `admit`, `unsafe`, `partial`, `implemented_by`, `extern`, or added `axiom` declarations were found by the source/log checks.

## Main-declaration and goal check

The requested name
`AdalyFormal.Round14.PathChoice.tailKernelLinePackage_of_crossingPositive`
does not occur in `LongArm.lean`; it is defined in `LongCrossing.lean:11628-11630` as:

```lean
theorem tailKernelLinePackage_of_crossingPositive (hpos : TailCrossingPositive) :
    TailKernelLinePackage :=
  tailKernelLinePackage_of_inputs tailEndpointNegative hpos
```

Its exact type is therefore:

```lean
TailCrossingPositive → TailKernelLinePackage
```

It is **not** `TailEndpointNegative`. It also has the explicit remaining hypothesis `hpos : TailCrossingPositive`; the negative endpoint is discharged separately by `tailEndpointNegative`.

The separate theorem `tailEndpointNegative` does have type `TailEndpointNegative`, but that predicate concerns the modified `tailRightStar` path. It is not definitionally `GoalNeg2`, original `P3`, original `CofinalP3`, or `CofinalAnyPathNoResponseCancellation`. Neither `LongArm.lean` nor the quoted `LongCrossing.lean` declarations provide a bridge from `TailEndpointNegative` or `TailKernelLinePackage` to `GoalNeg2`. `GoalNeg2` remains `¬ P428Target8SG selAll selAll` in `AHP/round3/guarded/pin/Statement.lean:157-158`.

The existing `LongCrossing.lean.log:90-92` does report only `[propext, Classical.choice, Quot.sound]` for `tailKernelLinePackage_of_crossingPositive`, so its axiom hygiene is consistent with the claim. That does not repair the type/goal mismatch; this verification did not recompile `LongCrossing.lean`.

## Conclusion

The artifacts support the narrower statement in `NOTES.md`: the modified path has a proved negative-`pi` endpoint, while its kernel-line package remains conditional on `TailCrossingPositive`. They do not establish the requested main-declaration type or closure of an accepted `GoalNeg2` premise. Original `P3`, `CofinalP3`, and `GoalNeg2` remain open.
