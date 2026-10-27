# Sheet Q3 verification — ACCEPT

Verified Stage B entry 6 against `../DECISION.md` §4.2 after the coordinator's fresh reproduction confirmation. `ReadingB.lean` was not edited.

## Independent compilation

Executed from the existing project, one Lean file only:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/fidelity/sheet-variants/lean/ReadingB.lean > ../AHP/fidelity/sheet-variants/lean/ReadingB.verify.log 2>&1
rc=$?
printf '%s\n' "$rc" > ../AHP/fidelity/sheet-variants/lean/ReadingB.verify.exit
```

Exit code: **0**. Complete output in `ReadingB.verify.log`:

```text
'AdalyFormal.Fidelity.SheetVariants.readingB_of_layer' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Checks

- The sole required theorem and its fully qualified `#print axioms` output are present. All listed axioms are standard; no additional proof helpers exist.
- Imports are exactly `THL6` and `RB2`; namespace is exactly `AdalyFormal.Fidelity.SheetVariants`. Open namespaces resolve the contracted frozen names; no local shadowing, extra variables, or hypotheses occur.
- Both definition declarations, `ReadingBTower` and `P428Target8_ReadingB`, match the decision's §4.2 code block byte-for-byte after trimming surrounding whitespace. All binders, strict positivity conditions, thresholds, the single radius, class predicate, operators, and conclusion are preserved.
- The theorem signature is exactly `readingB_of_layer : Target8Layer → P428Target8_ReadingB`, with no added or dropped hypotheses or weakened conclusion.
- Inspected frozen `Target8Layer` at `lean/src/THL6.lean:164`, `AdmNoBase` at `lean/src/THL2.lean:23`, and `Om0Unit` at `lean/src/RB2.lean:41`. The proof propagates the supplied layer hypothesis and its original witnesses, applying it to `hS.1`, the first conjunct of `ReadingBTower`. It does not substitute an independently proved analytic headline.
- Whole-file token scan found none of `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `extern`. The permitted command `#print axioms` is present.
- Source SHA-256 before and after compilation: `0bb62eca78a15ad9c1f6235c7596a25735f1fc0af09db00b29fb727bc10a9b3c`.

**Accepted:** `AdalyFormal.Fidelity.SheetVariants.readingB_of_layer`.
**Missing or failed declarations:** none.

Acceptance is limited to the contracted conditional reading-B restriction. It does not establish proper-domain analytic non-vacuity, identify source intent, or provide unconditional printed-assertion fidelity closure. No build, reproduction run, protected-file edit, commit, or push was performed by this verifier.
