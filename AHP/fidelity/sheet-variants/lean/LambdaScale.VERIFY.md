# Entry 7 (`sheet-q4`) verification

**Verdict: accept.** Independently recompiled `LambdaScale.lean`; exit code **0**. All four contracted declarations and both proof helpers pass. No source edits were made.

## Recompilation evidence

The coordinator's supplied confirmation of the fresh 2026-10-21 reproduction pass satisfied the Stage B gate. This verification did not run `REPRODUCE.sh` or `lake build`.

Command executed:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/fidelity/sheet-variants/lean/LambdaScale.lean > ../AHP/fidelity/sheet-variants/lean/LambdaScale.verify.log 2>&1
rc=$?
printf '%s\n' "$rc" > ../AHP/fidelity/sheet-variants/lean/LambdaScale.verify.exit
```

Complete output: `LambdaScale.verify.log`. Exit evidence: `LambdaScale.verify.exit` (`0`). One nonfatal `unnecessarySeqFocus` tactic-style warning at line 78; no compilation errors.

Source SHA-256, identical before and after verification:

```text
0d1d59cad99bd2cd23e9a8f9280398cd72f331b93afbac83f08cbec8fa6b95d7
```

## Contract and axiom audit

All names below are in `AdalyFormal.Fidelity.SheetVariants`.

| Declaration | Signature check | Axioms printed in independent output | Result |
|---|---|---|---|
| `unitEmb_val` | Exact section 4.3 signature | `propext`, `Quot.sound` | pass |
| `pdist_emb_scales` | Exact section 4.3 signature | `propext`, `Classical.choice`, `Quot.sound` | pass |
| `lambda_collar_scale_iff` | Exact section 4.3 signature | `propext`, `Classical.choice`, `Quot.sound` | pass |
| `headline_fine_side_ge16` | Exact section 4.3 signature | `propext`, `Classical.choice`, `Quot.sound` | pass |
| `scaleUp_length` | Additional arithmetic helper; no contracted signature | `propext`, `Quot.sound` | pass |
| `pcd_scale` | Additional arithmetic helper; no contracted signature | `propext`, `Quot.sound` | pass |

Every theorem has a qualified `#print axioms` command outside the namespace and exactly one corresponding dependency line in the verification output. Every listed dependency is permitted. No declaration is missing or failed.

The four required signatures and the complete `unitEmb` definition were compared programmatically to `DECISION.md` section 4.3, normalizing whitespace only. All match exactly: no added/dropped hypotheses, reordered binders, altered conclusions, or extra section variables. The total modulo definition is preserved. In particular, the first three statements retain `0 < ell ^ k`; the last retains precisely the specified `TorusOK`, `2 ≤ ell`, and `2 ≤ k` assumptions.

The sole import is exactly `ZStatementP428`. Namespace and opens resolve to the intended frozen definitions; inspected `lean/src/ZStatementP428.lean` definitions of `scaleUp`, `bigSide`, `pcd`, `pdist`, and `TorusOK`. There are no local substitutions for these predicates, custom notation, or hidden assumptions.

A whole-file forbidden-token scan found no `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `extern`. All six proof bodies were inspected; no unverified external computation or placeholder was used.

## Accepted scope

Only the coordinate identity, periodic-distance scaling for arbitrary rectangular unit extents, strict collar-atom equivalence on embedded site pairs, and fine-side lower bound 16 are accepted. This does not identify the full fine complement with the embedded unit complement, decide the source's common-radius convention, or certify an analytic headline/non-vacuity claim.

Files written by this verification: `LambdaScale.verify.log`, `LambdaScale.verify.exit`, and this report, all in the authorized directory. `LambdaScale.lean` was left unchanged.
