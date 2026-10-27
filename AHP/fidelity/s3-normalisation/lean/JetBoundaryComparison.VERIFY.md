# Independent verification — s3-normalisation (Stage B entry 2)

**Verdict: accept** — all three required declarations pass every check.

The coordinator's fresh reproduction confirmation supplied the Stage B gate. This verification did not run `REPRODUCE.sh` or `lake build`, and did not modify the Lean source.

## Independent compilation

Executed from the existing Lean project:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/fidelity/s3-normalisation/lean/JetBoundaryComparison.lean > ../AHP/fidelity/s3-normalisation/lean/JetBoundaryComparison.verify.log 2>&1
rc=$?
printf '%s\n' "$rc" > ../AHP/fidelity/s3-normalisation/lean/JetBoundaryComparison.verify.exit
```

Exit code: **0**. Complete output: `JetBoundaryComparison.verify.log`; exit record: `JetBoundaryComparison.verify.exit`.

## Declaration audit

All names below are in `AdalyFormal.AHP.FidelS3Normalisation`.

| Declaration | Exact decision signature | Required axiom output | Result |
| --- | --- | --- | --- |
| `raw_level_zero` | Identical binders and `C2rawB G U 0 A = 0` | `propext, Classical.choice, Quot.sound` | PASS |
| `linear_level_zero` | Identical binders and `QlinB G U 0 A = A` | `propext, Classical.choice, Quot.sound` | PASS |
| `plainH_eq_uniformBody_at_depth_one` | Identical binders, including `(j : ℕ) (hj : j ≤ 1)`, and full nested scalar-action equality | `propext, Classical.choice, Quot.sound` | PASS |

The source was manually reviewed and each signature was also compared programmatically to the decision's Lean code block: exact text equality after trimming outer whitespace. No hypotheses were added or dropped and no conclusion was weakened. There are no surrounding variable declarations or local replacement definitions. The sole import is `ZXR2Sector`; namespace and all three opens exactly match the decision. All three qualified `#print axioms` commands are present outside the namespace; each has matching output in the independent compilation log. Multiline axiom output was checked in full.

Whole-file forbidden-token scan found none of: `sorry`, `admit`, `axiom`, `sorryAx`, `native_decide`, `unsafe`, `implemented_by`, `extern`. No additional proof helpers or declarations occur.

Source SHA-256 before and after verification (unchanged):

```text
5bb512bb0d3e40cb91213473180cc9bd1eb3e6eade9879cea36b29fbccfcf8c0
```

## Acceptance scope

Accept only the three structural comparisons authorized by `DECISION.md`. These establish the actual level-zero jet facts and the depth-one coefficient identity, not a full Schur-complement identity or printed-normalisation fidelity. **S-3 remains unresolved.**

Only this report and the independent `.verify.log` / `.verify.exit` records were written, all in the assigned target directory.
