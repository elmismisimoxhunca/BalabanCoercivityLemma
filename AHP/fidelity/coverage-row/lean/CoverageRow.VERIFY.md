# Coverage row — independent Stage-B verification

**Verdict: accept.** All three required declarations pass all five checks.

The coordinator supplied the fresh reproduction/olean gate confirmation. This verification did not run `REPRODUCE.sh` or `lake build` and did not edit `CoverageRow.lean`.

## Independent compilation

Executed from the existing project exactly as required, with verification-specific output filenames:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/fidelity/coverage-row/lean/CoverageRow.lean > ../AHP/fidelity/coverage-row/lean/CoverageRow.verify.log 2>&1
rc=$?
printf '%s\n' "$rc" > ../AHP/fidelity/coverage-row/lean/CoverageRow.verify.exit
```

Exit code: **0**. Complete output:

```text
'coverage_row_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'coverage_row_both' depends on axioms: [propext, Classical.choice, Quot.sound]
'coverage_row_ell2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Contract and safety checks

An executable byte-for-byte comparison confirmed that the complete source is exactly the `DECISION.md` Lean block prefixed by the three frozen imports `NuA3`, `CaT1`, `CaT2d`. This checks all binders, hypotheses, conclusions, fully qualified source applications, global namespace placement, and requested axiom commands; there are no extra definitions, hypotheses, or altered conclusions.

| Declaration | Exact decision signature and application | Requested axiom output present | Allowed axioms only | Result |
|---|---|---|---|---|
| `coverage_row_fails` | Yes | Yes | Yes | Pass |
| `coverage_row_both` | Yes | Yes | Yes | Pass |
| `coverage_row_ell2` | Yes | Yes | Yes | Pass |

The whole-file forbidden-token scan found no `sorry`, `admit`, `axiom`, `sorryAx`, `native_decide`, `unsafe`, `implemented_by`, or `extern`. The permitted `#print axioms` commands are present for all three local declarations. A programmatic check confirmed exactly one output line for each target and that each printed axiom set is a subset of the allowed three.

SHA-256 before and after independent compilation and inspection:

```text
9f60a35f39ecdeabf97ac3f25212997220cf070373f3a63f20c6cd31b81b12e2
```

## Scope

Acceptance is limited to the three existing-result re-exports and the proposed stale-row correction. It does not decide the printed source's intended coverage, any case with `c < 10`, or additional sites-only scales. The protected statement sheet was not edited. Files written by this verifier: `CoverageRow.verify.log`, `CoverageRow.verify.exit`, and this report, all within the authorized target directory.
