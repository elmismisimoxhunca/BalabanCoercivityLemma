# Independent verification — sheet-q2b

**Verdict: accept.** All three required declarations and the sole proof helper pass. No source edits were made.

## Recompilation

The coordinator's fresh reproduction confirmation supplied the Stage B gate. Independently ran:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/fidelity/sheet-variants/lean/CollarNonStrict.lean > ../AHP/fidelity/sheet-variants/lean/CollarNonStrict.verify.log 2>&1
rc=$?
printf '%s\n' "$rc" > ../AHP/fidelity/sheet-variants/lean/CollarNonStrict.verify.exit
```

Exit status: **0**. Complete output: `CollarNonStrict.verify.log`; status: `CollarNonStrict.verify.exit`. Only three unused-simp-argument warnings occur.

Source SHA-256 before and after compilation:
`3d37f3fd397449588c754546302e5d02db65d29316e69fae08ac97c465553fa0`.

## Declaration and axiom audit

All names below are in `AdalyFormal.Fidelity.SheetVariants`.

| Declaration | Signature check | Axioms printed by independent compilation | Result |
|---|---|---|---|
| `admissible_imp_nonstrict` | Exact section 4.1 signature | `propext, Classical.choice, Quot.sound` | Pass |
| `admissibleNonStrict_k1_iff` | Exact section 4.1 signature | `propext, Classical.choice, Quot.sound` | Pass |
| `collar_separator` | Exact section 4.1 signature | `propext, Classical.choice, Quot.sound` | Pass |
| `pdist_L8` | Coordinate-expansion helper; not an additional contract target | `propext, Classical.choice, Quot.sound` | Pass |

Each required axiom print is present, including the additional helper print. Multiline axiom output was parsed as complete lists; every list contains only permitted standard axioms.

Compared all three required signatures against `DECISION.md` section 4.1 both by inspection and by whitespace-normalized text equality. Binders, hypotheses, implications, equivalence and conjunction match exactly; nothing was added, dropped or weakened. There are no ambient variable declarations. `AdmissibleNonStrict`, `L8` and `collarSep` likewise match the contract definitions exactly after whitespace normalization. The sole import is the authorized `ZT5A`; namespace and opens comply. The frozen `Admissible`, `bigSide`, `BlockClosed`, `pcd` and `pdist` definitions were inspected in `lean/src/ZStatementP428.lean`; no local shadowing or replacement appears.

A whole-file token scan found no `sorry`, `admit`, `axiom`, `sorryAx`, `native_decide`, `unsafe`, `implemented_by` or `extern`. The concrete finite geometry uses ordinary kernel-checked `decide`, not native computation. All four theorem declarations have axiom prints; there are no other new proof helpers needing a print.

## Scope

Acceptance covers predicate inclusion, depth-one equivalence, and the disclosed geometry-only separator with parameters `2 1 1 2`. The separator lies outside the headline regime. This is neither a non-strict coercivity theorem nor an analytic counterexample. No protected file, Lean source, lake configuration, or git history was changed.
