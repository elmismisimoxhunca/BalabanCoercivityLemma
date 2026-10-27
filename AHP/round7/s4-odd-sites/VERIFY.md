# S-4 pin and partial verification

**PASS for compilation and dependency hygiene; analytic verdict OPEN.** No pinned goal was proved. This is builder verification, not a separate-model review or whole-project rebuild.

| Source | Original / replay exit | Dependency records per run | Diagnostics |
|---|---:|---:|---:|
| `pin/Statement.lean` | 0 / 0 | 10 | 0 |
| `attempt/Partial.lean` | 0 / 0 | 21 | 0 |

Replays are byte-identical `verify/Statement.lean` and `verify/Partial.lean`. Every invocation ran directly in the bash tool through `AHP/round3/lean1.sh <file>`, which serializes Lean and writes the sibling `.lean.log` and `.lean.exit`. None timed out. No direct lake command, build, reproduction script or dependency update was run.

The audit `verify/audit.py` checked the current files and saved `VERIFY.json`:

- all four final exits are 0;
- all 62 printed dependency records (including the two replays) are subsets of `propext`, `Classical.choice`, `Quot.sound`;
- every locally declared definition, abbreviation and theorem has a matching dependency print;
- no final errors, warnings or failed-proof dependency markers;
- zero raw matches of prohibited proof constructs, including opaque stand-ins;
- source/log/exit timestamp order;
- each source imports only frozen `SoA3` and `SoPar`;
- exact byte equality of original/replay sources;
- the local `FamilyTorusSitesConstAt` definition is verbatim from frozen `CaT2d.lean`, independently of its successful `rfl` equality theorem.

Source SHA-256:

```
pin/Statement.lean
27a16f875b66d6fce71129ca3b0c08f1e4579fcac86fc742b1c186ffc00385ab

attempt/Partial.lean
dba5828837f1378b65e1ca9fade00d42c4755d712b0900e47395d3e6f5719698
```

Full log hashes and per-declaration dependency lists are in `VERIFY.json`. The audit is reproducible with `python3 AHP/round7/s4-odd-sites/verify/audit.py` and does not invoke Lean.

Only files under `AHP/round7/s4-odd-sites/` were written by this worker. The pre-existing `lean/lakefile.toml` modification and other workers' untracked compact-development files were not edited. No commit, push, deletion, numerical experiment, or source-page image verification was performed. No durable goal was present in the mapped child (`get_goal` returned null).

Compilation establishes the statement's well-formedness, exact connection to the frozen body, and the listed partial theorems. It does **not** establish any of Goal1–Goal4, a nonzero-parameter guard, a violating full form, a positive analytic bound, or agreement with Balaban's unqualified printed statement.
