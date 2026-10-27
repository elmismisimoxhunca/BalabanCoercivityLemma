# ATTACK: coverage-row

Verdict: **PASS WITH NITS.** The mathematical content is accurate as a reading
of existing Lean declarations; the numerics are honest, reproducible and
correctly transcribed; the scope guardrails match `OPEN_ITEMS.md` B1 and J.
Six line citations are off by one or two lines, and one row names a Prop where
it means a theorem. None of these touch the mathematics, but they should be
fixed before Stage B so they do not propagate into `CoverageRow.lean` comments.

Method: every cited Lean line was read in `lean/src/`; the committed numerics
were re-run and diffed; one attack-side check (`numerics/attack_geom_check.py`)
was written and run for the Ω₀ question. No Lean was compiled.

## 1. Does the variant say what it claims about the print? — YES

- The stale sentence is real: `notes/statement_sheet.tex:189` (row 6, verified
  at that exact line) says "Whether a coverage-free lemma presupposing the
  printed inverses holds is not decided." `OPEN_ITEMS.md` B1 (updated
  2026-10-19) supersedes it. `ROW6.md` is a faithful correction.
- "Presupposing the printed inverses" is the right description:
  `InstIneqWDH` (`CvS1.lean:70`) is `WellDefG → InstIneq`;
  `WellDefG = WellDef ∧ GuardsUnit` (`ZT4A.lean:51`, `:46`), and `GuardsUnit`
  is the three printed inverses as units. The counterexample family
  (`ConstFamWitnessTwo`, `NuA3.lean:82-97`) carries `GenP.WellDefG` as a
  conjunct, so the refutation is genuinely inside the class where every
  inverse exists — not a junk-value artifact. Confirmed against the junk-value
  row `not_P428Target8NC` (`CvN6.lean:183`), which is kept separate and correct.
- Quantifier check on `ncwdh_fails_ge_two` (`NuA3.lean:120`):
  `(c) (hc : 10 ≤ c) (ell) (hell : 2 ≤ ell) (a) (ha : 0 < a) : FailsAtEll`,
  `FailsAtEll = ¬ NcwdhBodyAt` (`NsCS1.lean:59`), `NcwdhBodyAt` (:50) is the
  per-`(ell,a)` body of `P428Target8NCWDHc` (:55). The case split
  `ell = 2 ∨ 3 ≤ ell` routes to `ncwdh_fails_two` (`NuA1.lean:56`) and
  `ncwdh_fails_all` (`NtFinal.lean:29`). Matches "false for every c ≥ 10,
  every ℓ ≥ 2, every a > 0" exactly.
- `not_P428Target8NCWDHc` (`NtFinal.lean:37`) is indeed only
  `∀ c ≥ 10, ¬ P428Target8NCWDHc c`; the SPEC's warning to use
  `ncwdh_fails_ge_two` for the per-`(ℓ,a)` claim is correct and necessary.
- Both-coverage body: `P428Target8NCWDHcov` (`CaT1.lean:61`);
  `coercCov_iff` (:65) is `Iff.rfl` pinning the class hypothesis to
  `CoversOm0p ∧ PerCubeRegular2`, i.e. `ClassCoupled` (`ZR6A.lean:124`,
  verified: `CoversOm0p` at :33 is `CoversOm0c ∧ CoversPlaqOm0c`;
  `CoversOm0c` `ZR2A.lean:107`, `CoversPlaqOm0c` `ZR6A.lean:27` — all as
  quoted). `p428Target8NCWDHcov_of_total` (:84) applies
  `AdalyFormal.Total.p428Target8Total` and projects `.2`, with `hW`
  (WellDefG) introduced at :88 — so "weakens ∧ to →, adds no analytic
  content, does not assert invertibility" is accurate.
- The ℓ = 2 row: `covPlaq_separately_necessary_two` (`CaT2d.lean:144`) is
  literally `FamilyTorusCovConstAt c 2 _ a ∧ ¬ FamilyTorusSitesConstAt c 2 _ a`.
  `FamilyTorusCovConstAt` keeps `ClassCoupledF (constFam c)` (verified:
  `ClassCoupledF` in `MXQ_Tor.lean:36` is sites + plaquettes + per-cube
  regularity); `FamilyTorusSitesConstAt` keeps `CovSitesF ∧ PerCubeRegularF`
  and drops plaquette coverage (def body verified). SPEC and ROW6 state only
  the scoped pair and explicitly disclaim an unscoped necessity claim —
  consistent with `OPEN_ITEMS.md` J ("the name is unreconciled; use the scoped
  content") and K's must-not-write list.
- "Not claimed: c < 10; 'holds for all c'" — matches the declarations
  (every hypothesis is `10 ≤ c`) and J's must-not-write list.
- The one open item (whether Balaban's p.396 sentence means this coverage) is
  correctly declared a reading question, not a Lean target. The printed
  sentence is quoted in `ZR6A.lean`'s module docstring (see nit N5 for the
  line number).

## 2. Proper nonempty Ω₀ — CHECKED (attack-side, evidence)

`extent_check.py` never touches the tower geometry. I wrote
`numerics/attack_geom_check.py` (output `numerics/attack_geom_check.out.txt`),
transcribing `tw3` (`NsCvNe1.lean:23-25`), the `neS` coordinates
(`NsCvNe2.lean:107-114,122`) and the `Geo3` arithmetic clauses
(`NsCvNe1.lean:48-71`).

- All 36 grid points (M ∈ 1..4, R ∈ {1,10,21}, cf ∈ {10,12,16}, ℓ = 2)
  satisfy every `Geo3` clause and give Ω₀ = [P0, Q0) with
  0 < Q0 − P0 < N (nonempty, proper).
- The three named rows: formula_min P0=5, Q0=71, N=120 (width 66);
  failEllCS_two-smallest P0=20, Q0=284, N=480 (width 264);
  constFam_witness_two R≥c P0=56, Q0=824, N=1056 (width 768). All proper and
  nonempty.
- Caveat: this is integer evidence only. Nonempty/proper Ω₀ is in any case a
  consequence of the committed `ne_admissible_two`; the positive body's
  hypothesis class is the frozen `ClassCoupled` class whose non-vacuity is
  established elsewhere in the repo. SPEC claims no new non-vacuity evidence,
  which is the honest position.

## 3. Numerical operator transcription — MATCHES, output reproduces

Every formula in `extent_check.py` was re-derived against the cited line:

- `neNu` (:105), `neA'` (:107), `neB'` (:108), `neN` (:115), `neLu` (:106),
  `neS` k=2 (:122), `CfData.cf ≥ 10` (:31-33): exact.
- `scaleUp` (`ZStatementP428.lean:42-43`): `(Lu μ + 1) * ell^k` — exact.
- `neC0` (`NuTwoUnc.lean:33`) and the docstring identity (:32): exact.
- Identity `neN = neNu * ell^2` matches the `ring` step `hN` inside
  `ne_scaleUp` (:130-133, the identity is at :133). `neB' − neA' =
  (cf−1)·ell·(ell·M)` (:107-108) and `neA' ≤ neC0 < neC0+1 < neB'` verified
  algebraically and on the grid.
- Re-run: `python3 numerics/extent_check.py` reproduces
  `extent_check.out.txt` byte-for-byte. 36 = 4·3·3 grid checks, sides
  30/120, 120/480, 264/1056 — all as reported, all > 8.
- "Tolerances": there are none — pure integer arithmetic, no floats, no
  approximations. `operator_modelled no` is honest; no `genForm`, `Ginv`,
  `WellDefG` or inequality was evaluated.
- Scope honesty: the M=1 row is labelled "not a witness of the declaration" —
  correct, since `failEllCS_two` takes `m = max m₀ 2`, forcing M = 2^m ≥ 4
  (verified `NuA1.lean:46-53`). The cap conclusion "a side-at-most-8 torus
  cannot host the witness" is scoped to the `neS` witness and does not
  overclaim about other towers. `ne2_bond_uncovered` (`NuTwoUnc.lean:87`)
  was not re-run, and the SPEC says so.

Nit N6 (no consequence): `neC0` in Lean is truncated ℕ-subtraction. The
Python transcription agrees with Lean only where `ell*M + 1 ≤ neA' +
cf*(ell*M)`, i.e. M ≥ 1. The script never states the guard; its grid starts
at M = 1, so all 36 checks and all three rows are on the valid domain. A one
-line comment would make the guard explicit.

## 4. Line-citation errors (nits; fix before Stage B)

| Where | Cited | Actual |
|---|---|---|
| SPEC, design JSON: `FamilyTorusCovConstAt` | `CaT1.lean:130` | **:117** |
| SPEC: `FamilyTorusSitesConstAt` | `CaT2d.lean:116` | **:122** |
| SPEC table, script docstring, design JSON: `failEllCS_two` | `NuA1.lean:45` / `:45-54` | theorem at **:44** (proof through :53) |
| SPEC: `ncwdhCovBodyAt_of_total` | `CaT1.lean:91` | **:92** |
| SPEC, ROW6: printed sentence in `ZR6A` docstring | `ZR6A.lean:4` | quote at **:6** (:4 is the module title) |
| SPEC: `CubeBond` | `ZStatementP428.lean:145` | `def` at **:144** (:145 is the body line; borderline) |

Nit N7 (naming): SPEC table and the script row say "`ConstFamWitnessTwo`
also takes R ≥ c (`NuA3.lean:104`)". The Prop `ConstFamWitnessTwo`
(`NuA3.lean:82`) states no such bound; it is the proof
`constFam_witness_two` (:99) that chooses `R ≥ max (max R₁ c) 1` (:103) and
derives `hRc : c ≤ R` (:105) to feed `exists_classCube_ne_two`. The extent
arithmetic (264/1056) is unaffected, but the citation should name the
theorem `constFam_witness_two` (:99-105), not the Prop. Consistent with
`CaT2d.lean`'s docstring that site coverage at ℓ = 2 also needs R ≥ cf.

## 5. Stage-B plan — sound

Verified without compiling: `NuA3`, `CaT1`, `CaT2d` are roots of
`AdalyFlatLib` (`lean/lakefile.toml`, lines 1702, 2665, 2669 of the roots
list). `CaT2d` imports `CaT1` (line 2). Namespaces: `ncwdh_fails_ge_two` is
in `NcwdhFam` (`NuA3.lean:10`), `not_P428Target8NCWDHc` in
`AdalyFormal.NcwdhStrong` (`NtFinal.lean:19`), both cov declarations in
`CovAssume` (`CaT1.lean:20`, `CaT2d.lean:17`). The three re-exports apply
existing theorems with exactly matching signatures; opening
`AdalyFormal.NcwdhStrong` is unneeded for the three re-exports but harmless.
The plan correctly adds no declaration about Balaban's sentence.

## Summary

- Print fidelity of the correction: **accurate**.
- Hypothesis class admits proper nonempty Ω₀: **yes** (new attack-side
  numeric evidence + committed `ne_admissible_two`).
- Operator/line transcription: **exact**; output reproduces byte-for-byte;
  no hidden tolerances.
- Defects: six line numbers off by one/two; one Prop-vs-theorem naming; one
  implicit M ≥ 1 guard. All documentation-level; none mathematical.
- Prediction "already-settled" stands: the row-6 staleness is real, the
  corrected text matches the declarations, and the only open item is the
  reading of Balaban's sentence, correctly out of Lean scope.
