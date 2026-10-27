# Corrected row 6 of `notes/statement_sheet.tex`

The sheet was not edited. This file is the replacement text for the longtable row that begins `6 &` (Part C, `notes/statement_sheet.tex:189`).

## What the sheet says now

> If dropped, the encoded statement is false: `P428Target8NC` (coverage dropped) is refuted at \(\ell=3\), \(a=\tfrac12\), via an in-class \(U\) at which \(G^{-1}\) is not invertible (Lean junk value \(0\)). Whether a coverage-free lemma presupposing the printed inverses holds is not decided.

The first sentence is still accurate for the junk-value encoding. The second sentence is stale. `paper/OPEN_ITEMS.md` section B1 (updated 2026-10-19) supersedes it: the encoded coverage-free granting-existence body is false for every natural \(c \ge 10\), every \(\ell \ge 2\) and every real \(a > 0\), and the body with both coverage clauses retained is true as a weakening of Total. Those statements are about the disclosed formal class, not about whether Balaban's printed regularity hypotheses are sufficient.

## Exact name of the false-for-all-\(c\) statement

`NcwdhFam.ncwdh_fails_ge_two` (`lean/src/NuA3.lean:120`).

```lean
theorem ncwdh_fails_ge_two (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    FailsAtEll c ell hell a
```

`FailsAtEll` is `¬ NcwdhBodyAt` (`lean/src/NsCS1.lean:59`). `NcwdhBodyAt` (`NsCS1.lean:50`) is the per-(\(\ell\), \(a\)) body of `P428Target8NCWDHc` (`NsCS1.lean:55`): the coverage-free headline at cube factor \(c\), with `WellDefG` a hypothesis of the inequality (`InstIneqWDH`, `lean/src/CvS1.lean:70`; `CoercG8AtNCWDH` keeps `PerCubeRegular2` and drops `CoversOm0p`, `CvS1.lean:74`). `WellDefG` is `WellDef ∧ GuardsUnit` (`lean/src/ZT4A.lean:51`, `GuardsUnit` at line 46): the three printed inverses are units, so this is the form that presupposes them, not the junk value \(0\).

The proof is the case split at `NuA3.lean:122`: \(\ell = 2\) by `ncwdh_fails_two` (`lean/src/NuA1.lean:56`), \(\ell \ge 3\) by `ncwdh_fails_all` (`lean/src/NtFinal.lean:29`).

`AdalyFormal.NcwdhStrong.not_P428Target8NCWDHc` (`NtFinal.lean:37`) is the weaker headline negation \(\forall c \ge 10,\; \neg\,\texttt{P428Target8NCWDHc}\, c\). It does not by itself say the body fails at every \(\ell\) and every \(a\). The theorem that matches B1's quantifiers is `ncwdh_fails_ge_two`. The constant-family sibling with the same quantifiers is `famConst_ge_two` (`NuA3.lean:126`); it is not the encoded single-factor statement.

## Drop-in row

```latex
6 & \textbf{Coverage} (A7) is an added hypothesis. The print does not state it. & If it is dropped, two encoded statements are false. Both are about the disclosed formal class, not a verdict that Balaban's printed regularity hypotheses are insufficient. (i)~Junk-value encoding: \texttt{P428Target8NC} (coverage \texttt{CoversOm0p} removed; non-units become the inverse \(0\)) is refuted at \(\ell=3\), \(a=\tfrac12\). (ii)~Granting existence: the body \texttt{NcwdhBodyAt} (\texttt{PerCubeRegular2} kept, \texttt{WellDefG} a hypothesis of the inequality) is false for every \(c\ge 10\), every \(\ell\ge 2\) and every \(a>0\). The body that keeps both coverage clauses (\texttt{ClassCoupled}, same \(c\)) holds for every \(c\ge 10\). At \(\ell=2\) only, on the constant family, that body holds and the body with site coverage and per-cube regularity but no plaquette coverage fails; the declaration name is not an unscoped necessity claim. Not claimed: \(c<10\); ``holds for all \(c\)''. & (i)~\texttt{not\_P428Target8NC} (\texttt{CvN6.lean:183}), \texttt{tip\_counterexample} (\texttt{CvN6.lean:144}), \texttt{coverage\_necessary} (\texttt{CvN7.lean:15}). (ii)~Exact name: \texttt{NcwdhFam.ncwdh\_fails\_ge\_two} (\texttt{NuA3.lean:120}); headline negation \texttt{not\_P428Target8NCWDHc} (\texttt{NtFinal.lean:37}) does not state the \(\ell\) and \(a\) quantifiers. Both clauses: \texttt{CovAssume.p428Target8NCWDHcov\_of\_total} (\texttt{CaT1.lean:84}). Ell \(=2\) scoped pair: \texttt{covPlaq\_separately\_necessary\_two} (\texttt{CaT2d.lean:144}). \\
```

## What remains open

Only whether Balaban's words "the conditions are imposed on \(\Omega_0\)" mean this coverage.

The printed sentence (sheet clause A7; also the docstring of `lean/src/ZR6A.lean:6`) is: "these regularity conditions do not impose any constraints on \(U\) outside the domain \(\Omega_0\)" (CMP99b p.396). The sheet's check question is whether "the class cubes cover \(\Omega_0\) (sites and plaquettes)" is a fair reading of that sentence. `ClassCoupled` (`ZR6A.lean:124`) is `CoversOm0p ∧ PerCubeRegular2`, and `CoversOm0p` (`ZR6A.lean:33`) is site coverage `CoversOm0c` (`ZR2A.lean:107`) and plaquette coverage `CoversPlaqOm0c` (`ZR6A.lean:27`). None of the declarations above says that this conjunction is what the printed sentence means. That reading stays open. It is not a Lean target.

Other coverage cells (sites-only at odd \(\ell\), and the even cases left open in `OPEN_ITEMS.md` section M) are a different hypothesis: site coverage is kept. They are not what row 6 left undecided, and this correction does not close them.
