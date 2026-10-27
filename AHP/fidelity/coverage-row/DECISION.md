# Decision: coverage-row

**Decision: already-settled.** Adopt the row-6 correction in `ROW6.md`, subject to the Stage-B compilation and axiom gate. Send three exact re-exports to Stage B, not a new search or a new analytic argument. No Lean files were written or compiled in Stage A.

## Basis and scope

Read `HANDOFF.md`, all of `paper/OPEN_ITEMS.md` (including B, K–N, R and S), `notes/statement_sheet.tex`, `SPEC.md` and `ATTACK.md`. Re-read the source declarations and their bodies in `lean/src/NsCS1.lean`, `NuA3.lean`, `CaT1.lean`, `CaT2d.lean` and `ZT4A.lean`.

The sentence at `notes/statement_sheet.tex:189` saying that the coverage-free granting-existence body is undecided is stale against B1. The precise replacement is:

- For every natural \(c\ge10\), every \(\ell\ge2\) and every real \(a>0\), `FailsAtEll c ell hell a`, namely the negation of the full threshold body `NcwdhBodyAt`, is the conclusion of `NcwdhFam.ncwdh_fails_ge_two` (`lean/src/NuA3.lean:120`). This is not merely a headline negation at some scale.
- Keeping both coverage clauses gives `CovAssume.P428Target8NCWDHcov c` for \(c\ge10\), by `p428Target8NCWDHcov_of_total` (`lean/src/CaT1.lean:84`). This is a weakening of Total, not new analytic content or a new invertibility conclusion.
- Only at \(\ell=2\), the constant-family both-coverage body holds while its sites-only body fails, with \(c\ge10\), \(a>0\), exactly as `covPlaq_separately_necessary_two` states (`lean/src/CaT2d.lean:144`). Its name must not become an unscoped necessity claim.

The guard is the actual `WellDefG = WellDef ∧ GuardsUnit` (`lean/src/ZT4A.lean:51`), not just an informal assumption about one inverse. In particular, the negative branch is not the earlier junk-value example. The explicit source witness `ConstFamWitnessTwo` (`lean/src/NuA3.lean:82-97`) includes admissibility, a class cube, positive smallness, per-cube regularity, `WellDefG`, an uncovered bond and a strict violating test-field inequality; `constFam_witness_two` constructs it at arbitrary requested thresholds. The sites-only branch uses the witness carrying site coverage in `lean/src/CaT2d.lean:135-141`. Thus the selected negative statements are not achieved by empty hypotheses or an absent inverse. The positive statement retains the existing covered class; it is not a claim that an empty class suffices to resolve fidelity.

These are facts about the disclosed formal class. Nothing here decides whether Balaban's sentence on p.396 implies site-and-plaquette coverage. That is **reading-only**, with no Lean target. The sites-only odd-scale and remaining even-scale cells in section M remain outside this correction. No claim for \(c<10\), touching-plaquette coverage, or insufficient printed regularity hypotheses is admitted.

## Attack disposition and corrections

Accept the substantive attack verdict. Corrected `SPEC.md`, `ROW6.md` and `numerics/extent_check.py` where applicable:

| Citation or wording | Accepted correction |
|---|---|
| `FamilyTorusCovConstAt` | `lean/src/CaT1.lean:117` |
| `FamilyTorusSitesConstAt` | `lean/src/CaT2d.lean:122` |
| `failEllCS_two` | `lean/src/NuA1.lean:44-53` |
| `ncwdhCovBodyAt_of_total` | `lean/src/CaT1.lean:92` |
| p.396 quotation in the docstring | `lean/src/ZR6A.lean:6-7` |
| \(R\ge c\) | Chosen in `constFam_witness_two`, `lean/src/NuA3.lean:99-105`; not a field of `ConstFamWitnessTwo` |
| Python `neC0` subtraction | Explicit valid-domain assertion added; grid has \(M\ge1\), so Lean Nat subtraction does not truncate |

Reject one attack nit: the current file has `def CubeBond` at **`lean/src/ZStatementP428.lean:145`**, with its body at 146. Line 144 is its docstring. The original SPEC citation was correct and is retained. `ATTACK.md` is preserved as the review record; this decision supersedes that nit.

Both scalar-arithmetic scripts were rerun and their stdout compared with the stored outputs: both matched exactly. These are 36-point integer checks in each script, not operator simulations, class-membership checks or proofs. No torus was instantiated and no dense or sparse operator was allocated; the extents 30/120, 120/480 and 264/1056 demonstrate why the existing witness was not simulated under the side-8 cap. Geometry checks are supporting evidence only, not a substitute for the source witnesses and the later compilation gate.

## Exact Stage-B declarations

Proposed file: `AHP/fidelity/coverage-row/lean/CoverageRow.lean`.
Imports: `NuA3`, `CaT1`, `CaT2d`.
Use fully qualified proposition and source names to avoid namespace ambiguity:

```lean
theorem coverage_row_fails
    (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell : 2 ≤ ell)
    (a : ℝ) (ha : 0 < a) :
    AdalyFormal.NcwdhStrong.FailsAtEll c ell hell a :=
  NcwdhFam.ncwdh_fails_ge_two c hc ell hell a ha

theorem coverage_row_both
    (c : ℕ) (hc : 10 ≤ c) : CovAssume.P428Target8NCWDHcov c :=
  CovAssume.p428Target8NCWDHcov_of_total c hc

theorem coverage_row_ell2
    (c : ℕ) (hc : 10 ≤ c) (a : ℝ) (ha : 0 < a) :
    CovAssume.FamilyTorusCovConstAt c 2 (le_refl 2) a ∧
      ¬ CovAssume.FamilyTorusSitesConstAt c 2 (le_refl 2) a :=
  CovAssume.covPlaq_separately_necessary_two c hc a ha

#print axioms coverage_row_fails
#print axioms coverage_row_both
#print axioms coverage_row_ell2
```

After the parent confirms the cold reproduction gate passed, compile with `lake env lean` from the existing `lean/` project, pointing to the proposed file outside that directory. Preserve exit status and axiom output under this target directory. Accept only axiom subsets of `propext`, `Classical.choice`, `Quot.sound`. Imported print output is not a substitute for checking the three named re-exports. A failed import, failed compilation or unexpected axiom blocks Stage-B closure.

## Completion status

Stage-A decision and correction text are ready. Current Lean compilation and axiom checks remain pending; no fresh formal closure is claimed. The actual statement sheet was not edited, as required. No `lean`, `lake`, or `REPRODUCE.sh` command was run; no protected path was written; no commit or push was made.
