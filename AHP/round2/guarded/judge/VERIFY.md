# Independent judge verification — guarded

Date: 2026-10-21. **Verdict: partial results accepted; `does-not-close` for every attempt.**

No earlier attempt-level `VERIFY.md` / `Attempt.VERIFY.md` existed when this pass started. All four workflow `verify` fields were null. The following is a new source/type review and serial recompilation, not a claim that those absent verifiers passed.

## Recompilation

For each of the five relative paths below, a byte-identical copy of the original source was made under this directory and compiled separately. The original sources and builder evidence were not overwritten.

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
# FILE is one of the paths in the table, prefixed by ../AHP/round2/guarded/judge/.
"$BB_CLI" heavy run -- lake env lean "$FILE" > "$FILE.log" 2>&1
echo $? > "$FILE.exit"
```

| Copy / fresh evidence | Exit | Dependency records | Diagnostics |
|---|---:|---:|---|
| `pin/Statement.lean`, `.lean.log`, `.lean.exit` | 0 | 17 | None |
| `r1-prove/Attempt.lean`, `.lean.log`, `.lean.exit` | 0 | 56 | None |
| `r1-refute/Attempt.lean`, `.lean.log`, `.lean.exit` | 0 | 28 | None |
| `r2-prove/Attempt.lean`, `.lean.log`, `.lean.exit` | 0 | 71 | None |
| `r2-refute/Attempt.lean`, `.lean.log`, `.lean.exit` | 0 | 54 | None |

All 226 records (including repeated pin records and frozen helpers) list only subsets of `propext`, `Classical.choice`, `Quot.sound`. All requested dependency prints are present. The four main records, normalized to one line:

```text
'AdalyFormal.Round2.Guarded.R1Prove.goalPos2_iff_boundary_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round2.Guarded.RefuteR1.pencil_failure_iff_second_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round2.Guarded.R2Prove.goalPos2_iff_boundary_response' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round2.Guarded.RefuteR2.goalNeg2_iff_cofinalPencilFailure' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The first judge invocation for round-1 refutation terminated with a tool error, leaving an empty log and no exit file. A process check found no remaining invocation. That interrupted invocation was rejected as evidence; the completed serial retry produced the retained exit 0 and complete log. No concurrent judge Lean invocations were used.

## Source and statement checks

- Every compiled copy is byte-identical to its current original; hashes are in `CHECKS.json`.
- The whole pin is an unchanged prefix in the pin and three attempts. In round-1 refutation, removing only the additional frozen `import GdR6b` at line 2 restores that exact prefix. All copied goal, class-prefix, selector and assembly definitions are unchanged, not merely whitespace-equivalent.
- Sole other import: frozen `DrEquiv`. Both modules are in `lean/src`; no AHP imports.
- Raw whole-file scan, including comments and strings, found no forbidden term or `opaque` declaration. The legitimate `#print axioms` commands are not an `axiom` declaration.
- Read the appended namespaces, definitions and proof bodies. There is no replacement of the pinned goals by new operators or additional headline assumptions. Round-2 positive's generic response algebra is specialized to the actual selector difference and localized corrected operator.
- The main theorem types are equivalences, not proofs of either side. The conditional positive theorems retain unproved `GShape` assumptions. The geometry exclusion is about one specified tower. None has the unconditional type of a pinned positive or negative goal.
- `GShape_imp` in frozen `DrEquiv.lean:60` supplies localized well-definedness after combining thresholds; the eventual equivalences do not silently add it to the headline, but also do not preserve numerical threshold choices pointwise.
- The cofinal converse keeps the radius before the universal positive smallness cap and does not add a path or sign hypothesis. It supplies no cofinal witness.

`audit.py` checks source/copy identity, pin-prefix identity, imports, forbidden tokens, final exit/log freshness, diagnostics, dependency sets and print coverage. It is an artifact checker, not a Lean parser or mathematical closure detector; the no-closure conclusion additionally rests on the statement/body review recorded in `../JUDGEMENT.md`.

## Limits

No new proof of either pinned direction, numerical replay, exact Python/Lean dictionary, printed-page image review, full build or reproduction run is claimed. The provided fresh reproduction prerequisite was used. Source and log writes were confined to the guarded item's directory. Current attempts and builder logs were left intact.
