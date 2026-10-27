# Stage B entry 9 (sheet-q12): ACCEPT

Independently verified `NormHS.lean` against `STAGE_B.md` entry 9 and `sheet-variants/DECISION.md` §4.5. The coordinator's fresh reproduction confirmation supplies the Stage-B gate. The source was not edited.

## Independent compilation

Executed from the confirmed workspace:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/fidelity/sheet-variants/lean/NormHS.lean > ../AHP/fidelity/sheet-variants/lean/NormHS.verify.log 2>&1
rc=$?
printf '%s\n' "$rc" > ../AHP/fidelity/sheet-variants/lean/NormHS.verify.exit
```

Exit status: **0**. Complete output is in `NormHS.verify.log`; status is in `NormHS.verify.exit`. No build or reproduction script was run.

## Declaration audit

All names below have prefix `AdalyFormal.Fidelity.SheetVariants.`.

| Declaration | Contract signature | Required axiom print | Verdict |
|---|---|---|---|
| `bondEnergyHS_eq_two` | Exact text match | `propext, Classical.choice, Quot.sound` | PASS |
| `instIneqHS_iff` | Exact text match, including `γ / 2` | `propext, Classical.choice, Quot.sound` | PASS |
| `target_iff_hs` | Exact text match | `propext, Classical.choice, Quot.sound` | PASS |

A mechanical text comparison confirmed all four definitions (`bondEnergyHS`, `InstIneqHS`, `CoercG8AtHS`, `P428Target8_HS`) match the decision's code block verbatim, and each theorem signature matches verbatim after removing `theorem` and its proof body. No added/dropped hypotheses, narrowed binders, or weakened conclusions. Namespace and both imports match the contract. No section variables or shadow definitions alter these signatures.

All three required qualified `#print axioms` commands occur after the namespace closes; all three corresponding output lines are present. Every listed axiom is allowed. There are no additional named proof-helper declarations requiring prints; `hscale` is a local proof term within `instIneqHS_iff` and its dependencies are covered by that theorem's axiom print.

## Proof and safety review

- `bondEnergyHS_eq_two` unfolds the two energies and sums `RMapLipschitz.norm_sq_eq_half_frobSq` over bonds, using ring arithmetic.
- `instIneqHS_iff` transports that identity through unchanged support hypotheses and the identical right-hand form.
- `target_iff_hs` transports constants `γ / 2` and `2 * γ`, preserving positivity and every headline binder. It does not invoke independent analytic conclusions.
- Whole-source token scan found no `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `extern`. Full source inspection found no bypass mechanisms.
- Source SHA-256 before and after verification: `7a19645bb0c7b5c25b5539fcdbd9451a19a8f44aea7adefb6d61150bd7ecf304`.

**Accepted: 3/3 declarations. Failed or missing: none.** Acceptance is only the Q12 left-hand norm re-expression and its instance/headline transport, not S-3 closure, changed operators, or independent analytic/non-vacuity certification. Only verification artifacts under `AHP/fidelity/sheet-variants/lean/` were written.
