# Release verification evidence

The cache-assisted reproduction finished on **2026-10-27 at 05:49:36 UTC**, exit 0, ending `ALL CHECKS PASSED`.

| Evidence | Meaning |
|---|---|
| [`summary.json`](summary.json) | Machine-readable verification scope and counts. |
| [`reproduction-summary.txt`](reproduction-summary.txt) | Build exit, all numbered Check exits, complete-record counts, exact expected-output comparisons, and the legacy-token inventory result. |
| [`checks/`](checks/) | The actual complete raw output of Check1–Check19 and CheckR7 from this run. |
| [`axioms-main.txt`](axioms-main.txt), [`axioms-r7.txt`](axioms-r7.txt) | Canonical complete records validated from those raw outputs. |
| [`complete-axiom-normalization.json`](complete-axiom-normalization.json) | The five historical first-line expectations expanded from their retained complete records, without changing the allowed axiom set. |
| [`validator-regression-before.txt`](validator-regression-before.txt) | Four focused failures against the old shell gate: continuation-line axioms, truncation, and incomplete accepted output. |
| [`validator-tests.txt`](validator-tests.txt) | All ten tests passing after the complete-record validator was installed. These are validator tests, not substitute Lean proofs. |
| [`blueprint-recheck.json`](blueprint-recheck.json) | Static source/log/citation check of the round-15 blueprint; not a Lean or TeX build. |
| [`FILES.sha256`](FILES.sha256) | Hashes of the published files, excluding this hash list itself. |

The core contains 2,782 registered modules and 573 checked records (572 main plus R7). Its 2,807 tracked `lean/` files were compared byte-for-byte with the accepted integration snapshot. The public release did not modify mathematical sources or imports.

**Limits:** the run reused project and mathlib caches copied with copy-on-write isolation. It is not a fresh cold build or an end-to-end network-install test. It does not build every research attempt under `AHP/`, independently validate the numerical computations, or settle source-fidelity interpretation. The five explicitly allowlisted legacy placeholder modules remain present; the checked theorem dependencies do not use `sorryAx`.

In the run summary and test diagnostics, the private checkout prefix is replaced by `$CHECKOUT`. Raw axiom outputs and the mathematical source/log evidence are otherwise preserved. The original private backup retains the unredacted diagnostics.
