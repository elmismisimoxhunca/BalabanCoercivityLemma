# Independent verification — Stage B entry 4

**Verdict: accept — checked conditional class/headline comparisons only.**

Verified `ClassInclusion.lean` independently after the coordinator's reproduction-pass confirmation. The source was not edited.

Source SHA-256: `f3dabe1f66f069d97943debb296d6ebb23af764389b0f68f8e51c06e0dfed002`.

## Compilation evidence

Executed:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean > ../AHP/fidelity/s2-inclusion/lean/ClassInclusion.verify.log 2>&1
echo $? > ../AHP/fidelity/s2-inclusion/lean/ClassInclusion.verify.exit
```

Independent exit code: **0**. Complete output: [ClassInclusion.verify.log](ClassInclusion.verify.log); exit record: [ClassInclusion.verify.exit](ClassInclusion.verify.exit). No warnings or errors appeared.

## Declaration checks

All names below have prefix `AdalyFormal.AHP.FidelS2Inclusion.`. Every requested axiom print is present, in the required order. Each reports exactly `propext`, `Classical.choice`, `Quot.sound` (multiline records included).

| Declaration | Exact contract signature | Axioms | Result |
|---|---|---|---|
| `touchCover_cubeBond` | match | standard only | pass |
| `CoversPlaqFour.toFrozen` | match | standard only | pass |
| `CoversPlaqCorner.toFour` | match | standard only | pass |
| `PerCubeRegularTouch.toFrozen` | match | standard only | pass |
| `ClassCoupledFour.toFrozen` | match | standard only | pass |
| `ClassCoupledCorner.toFour` | match | standard only | pass |
| `ClassCoupledCorner.toFrozen` | match | standard only | pass |
| `targetFour_of_frozen` | match | standard only | pass |
| `targetCorner_of_four` | match | standard only | pass |
| `targetCorner_of_frozen` | match | standard only | pass |

Compared all ten source signatures against the exact Lean block in `../DECISION.md`, including automated whitespace-normalized equality. The first seven inherit precisely `{L : PeriodicLatticeExtent}` from the ambient `variable` declaration; this is the explicit extent binder in the decision. No extra ambient hypotheses exist. No binders, hypotheses or conclusions were added, dropped, reordered or weakened.

## Definitions, imports and safety

- Direct imports are exactly `ZT5A`, `ZR2Ops2`, `ZR8Class`; namespace and opened namespaces agree with the contract.
- Inspected the complete source, including helpers. The full-file forbidden-token scan found no `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by` or `extern` tokens.
- Touching bonds use endpoint disjunction. Four-bond coverage and one-corner coverage retain the specified antecedents and a single frozen `IsClassCube` witness; the product-box argument supplies frozen coverage, rather than assuming predicate monotonicity.
- Touching regularity retains all three strict bounds and the per-cube existential gauge and field. Site coverage and the shared cube factor are unchanged.
- Compared regularity, coverage and headline structure with frozen sources in `lean/src/ZR2A.lean`, `lean/src/ZR6A.lean`, and `lean/src/ZT5A.lean`. Both local headline definitions preserve factor 12, positivity, smallness, quantifier order, `TorusOK`, `Admissible`, `LambdaOK2`, and frozen `InstIneq`; no local operator replacement or shadow definition weakens the conclusion.
- All ten declarations passed; none are missing or failed. Additional proof helpers are not separate entry-4 acceptance targets; their dependencies are covered transitively by the requested axiom checks wherever used.

## Acceptance boundary

This accepts only the conditional inclusions authorized by the decision. It does **not** close S-2 statement fidelity or certify the printed convention, reverse/strict inclusion, shell-class inclusion, or changed operators. Proper nonempty admissible-domain class inhabitation, Lambda/nontrivial test-field evidence, and class-identification obligations remain unresolved.

Only this verification report and the independent `.verify.log` / `.verify.exit` files were written. No Lean source, frozen file, lake configuration, builder log, or builder exit record was modified; no reproduction, build, commit, push or removal command was run.
