# Entry 11 (guarded): independent verification

**Verdict: accept** — all three contracted declarations pass every check.

Contract: `AHP/fidelity/guarded/DECISION.md`, Exact Stage-B signatures and acceptance rule. The coordinator supplied the required fresh reproduction confirmation; the stale NOT READY note in `STAGE_B.md` is superseded.

## Independent compilation

Executed from the existing project, without editing `UthCross.lean`:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/fidelity/guarded/lean/UthCross.lean > ../AHP/fidelity/guarded/lean/UthCross.verify.log 2>&1
echo $? > ../AHP/fidelity/guarded/lean/UthCross.verify.exit
```

Exit code: **0**. The fresh log contains exactly the three required fully qualified axiom lines, with no errors or warnings.

| Declaration in `AdalyFormal.FidelityGuarded` | Exact signature | Fresh axiom output | Result |
| --- | --- | --- | --- |
| `Ginv_lit_psd_at_zero` | Match | `[propext, Classical.choice, Quot.sound]` | Pass |
| `Uth_hits_nonunit` | Match | `[propext, Classical.choice, Quot.sound]` | Pass |
| `Uth_singular_is_not_a_split` | Match | `[propext, Classical.choice, Quot.sound]` | Pass |

## Statement and source audit

- All three signatures were compared mechanically, character-for-character from the declaration name through the conclusion (excluding the implementation delimiter), against their respective Lean blocks in `DECISION.md`; all match.
- Namespace is exactly `AdalyFormal.FidelityGuarded`. The scoped opening and all nine namespace openings match the contract. There are no surrounding variable declarations, local aliases, notations, or replacement definitions altering the statements.
- The seven imports exactly match the suggested contract imports: `D1Main`, `D1Final`, `GdGap2`, `GdFam`, `GdR5b`, `GdR6a`, `GdR6b`. No `DrSkeleton` or AHP draft imports.
- Target 1 retains its nonnegative parameter premise and actual literal `Ginv` PSD conclusion.
- Target 2 retains arbitrary positive `α₀`, the full specified `ClassCoupled` membership, the half-open interval, and failure of the actual literal guard. No initial invertibility premise or stricter lower endpoint was substituted.
- Target 3 retains all geometry binders, zero local correction, unconditional actual-operator equality, and the exact unit equivalence. No invertibility premise was inserted. Its proof uses `G1invS_eq_Ginv_theta` and uniqueness of the actual operators, not a conditional pencil identity.
- Whole-file token scan, including comments, found none of: `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`. The legitimate `#print axioms` commands are present for all three targets.
- No declarations are missing or failed; no signature was weakened. The verifier did not edit the Lean source or run `lake build` or `REPRODUCE.sh`.

Verified source SHA-256:

```text
f206f691c8d56be9a6ba73c9c5992be3d34bc0ec67e076b96e99cb51f00fa63b
```

**flat-path comparison audited; item 5 remains open**.
