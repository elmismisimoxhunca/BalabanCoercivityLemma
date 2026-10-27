# Entry 10 (`sheet-q13`) — independent verification

**Verdict: accept.** Both required declarations pass all five checks. No declarations are missing or failed. The coordinator supplied the fresh reproduction/olean gate confirmation; reproduction and `lake build` were not rerun.

## Independent compilation

Executed from the workspace with the prescribed command, using verification-specific output paths:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/fidelity/sheet-variants/lean/QuantifierOrder.lean > ../AHP/fidelity/sheet-variants/lean/QuantifierOrder.verify.log 2>&1
echo $? > ../AHP/fidelity/sheet-variants/lean/QuantifierOrder.verify.exit
```

Exit code: **0**. Complete output is in `QuantifierOrder.verify.log`; saved status is in `QuantifierOrder.verify.exit`.

## Declaration checks

Both declarations are in `AdalyFormal.Fidelity.SheetVariants`.

| Declaration | Exact DECISION §4.6 signature | Required axiom output | Result |
| --- | --- | --- | --- |
| `total_imp_frozen` | Exact text match; no added/dropped hypotheses or changed conclusion | `[propext, Classical.choice, Quot.sound]` | Pass |
| `threshold_order_toy` | Exact text match, including every natural-number binder, threshold inequality, conjunction and negation | `[propext, Quot.sound]` | Pass |

Both fully qualified `#print axioms` commands required by STAGE_B entry 10 are present outside the namespace, and both output lines are present. Every reported axiom is allowed. No extra proof helper declarations exist.

The sole import is the required `TT_F`. The namespace and `open AdalyFormal.StatementLaneG` resolve the contract's unqualified frozen headline without substitutions or shadow definitions. `total_imp_frozen` directly re-exports `AdalyFormal.Total.P428Target8Total.toTarget`, located in `lean/src/TT_F.lean` (not `lean/TT_F.lean`). The toy proof retains the exact unrestricted natural-number quantifier patterns.

A whole-file token scan found none of `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `extern`. Full source inspection found no altered definitions, hidden hypotheses, custom notation, or additional declarations.

The `.lean` file was not edited. SHA-256 before and after verification:

```text
af934ea7d9b3e4ef592058c70ac0d110916b929b98812e44ea58488e370dc5eb
```

## Accepted scope

Only the existing Total-to-frozen implication and abstract threshold-order separation are accepted. This is not non-implication between actual closed coercivity propositions. Total's earlier choice of thresholds/constants, quantification over every cube factor at least 10 rather than 12, and well-definedness conclusion remain distinct. No broader fidelity closure is claimed.
