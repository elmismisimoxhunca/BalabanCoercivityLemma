# Verification

The recorded reproduction passed with **2,782 registered modules and 573 complete axiom records**. The allowed dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduce

From the repository root:

```sh
./REPRODUCE.sh
```

The script builds the registered modules, checks every complete `#print axioms` record, compares the results with `expected/`, and checks the forbidden-token inventory. Success ends with `ALL CHECKS PASSED`.

With an existing compatible mathlib build:

```sh
PACKAGES_FROM=/path/to/compatible/.lake/packages ./REPRODUCE.sh
```

The script’s header documents concurrency and memory controls. Its validator tests run separately:

```sh
python3 -m unittest discover -s tools/tests -v
```

## Evidence

| File | Content |
|---|---|
| [`summary.json`](summary.json) | Verification scope and counts. |
| [`reproduction-summary.txt`](reproduction-summary.txt) | Build/check exits and expected-output comparisons. |
| [`checks/`](checks/) | Complete raw axiom output from Check1–Check19 and CheckR7. |
| [`axioms-main.txt`](axioms-main.txt), [`axioms-r7.txt`](axioms-r7.txt) | Normalized complete axiom records. |
| [`validator-tests.txt`](validator-tests.txt) | Validator test results. |
| [`blueprint-recheck.json`](blueprint-recheck.json) | Source/log/citation checks for the supplemental blueprint, not a Lean compilation. |
| [`FILES.sha256`](FILES.sha256) | File hashes, excluding the hash list itself. |

## Scope of the check

The recorded run used existing project and mathlib caches. It is not an independent cold rebuild; the complete network-install path remains untested.

Five legacy modules contain `sorry` declarations, listed in [`expected/forbidden_tokens.expected.txt`](../expected/forbidden_tokens.expected.txt). They occur in the import chain of a historical result, but the checked theorem dependencies do **not** use `sorryAx`. The distinction is between importing a file that contains an unused placeholder and depending on that placeholder in a proof.

The root build does not certify every exploratory file under `AHP/`, numerical calculations, or fidelity to the intended reading of the source. The development and its reviews were AI-assisted; those reviews are not human expert endorsement.
