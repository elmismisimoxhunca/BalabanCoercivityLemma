# GlobalGauge independent verification

**Entry:** STAGE_B.md §8, `sheet-q6a`  
**Verdict:** accept (all three declarations)  
**Contract:** `AHP/fidelity/sheet-variants/DECISION.md` §4.4

The coordinator supplied the reproduction-pass confirmation. Independently recompiled the existing file without editing it; no build or reproduction script was run.

## Command and evidence

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/fidelity/sheet-variants/lean/GlobalGauge.lean > ../AHP/fidelity/sheet-variants/lean/GlobalGauge.verify.log 2>&1
rc=$?
printf '%s\n' "$rc" > ../AHP/fidelity/sheet-variants/lean/GlobalGauge.verify.exit
```

Exit code: **0**. Complete output: `GlobalGauge.verify.log`; status: `GlobalGauge.verify.exit`.

Source SHA-256 before and after recompilation and inspection:
`b4eb7a7b13b99e75d638dd6d4c51af7b3df34f95032a1939d9656b5b373d72f0`.

## Checks

- Import is exactly `ZT5A`; namespace is `AdalyFormal.Fidelity.SheetVariants`. Namespace opens refer to the decision-authorized frozen namespaces. No extra section variables, local shadow definitions, or altered notation.
- `GlobalRegular` and `ClassCoupledGlobal` match the contract text exactly after whitespace normalization, including every bound and guard.
- All three theorem signatures match the contract text exactly after whitespace normalization. No hypotheses are added or removed; no conclusion is weakened. `global_flat` retains all five strict positivity hypotheses.
- All three required qualified `#print axioms` commands are present outside the namespace. Their output is present in the fresh log:

| Declaration (namespace above) | Axioms | Result |
| --- | --- | --- |
| `global_imp_perCube` | `propext, Classical.choice, Quot.sound` | pass |
| `globalClass_imp_frozenClass` | `propext, Classical.choice, Quot.sound` | pass |
| `global_flat` | `propext, Classical.choice, Quot.sound` | pass |

- No additional top-level proof helpers require axiom prints. The local positivity facts in `global_flat` are covered by its transitive axiom report.
- Forbidden-token scan is clean: no `sorry`, `admit`, `axiom`, `sorryAx`, `native_decide`, `unsafe`, `implemented_by`, or `extern` tokens.
- Inspected actual frozen definitions at `lean/src/ZR2A.lean:47` (`PerCubeRegular2`) and `lean/src/ZR6A.lean:124` (`ClassCoupled`): the first implication moves the common gauge inside each cube's existential without altering its guards, and the second preserves coverage unchanged. The flat proof uses gauge one and matrix field zero with positivity for all strict bounds.

## Acceptance scope

Only the exact global-to-per-cube and class inclusions and flat regularity non-emptiness are accepted. This supplies neither coverage nor a nonzero admissible test field, and establishes neither strict inclusion nor a global-gauge analytic headline. No declarations failed or were omitted. The `.lean` file was not changed.
