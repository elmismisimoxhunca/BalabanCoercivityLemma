# SPEC: coverage-row

Prediction: **already-settled**.

Item 3 of the statement-fidelity list is the stale sentence in row 6 of `notes/statement_sheet.tex`. The formal alternatives are already Lean declarations in `lean/src`. This note checks them against that source. It does not add a proof, and it does not edit the sheet. A numerical result below is evidence about integer extents, not a proof, and nothing in the arithmetic is called a theorem.

## Variant statements (Lean text, as in the source)

Coverage in the frozen class is both clauses at one cube factor:

```lean
-- ZR2A.lean:107
def CoversOm0c ... : Prop :=
  ∀ x ∈ S.Om 0, ∃ sites j, IsClassCube ell M c k S sites j ∧ x ∈ sites

-- ZR6A.lean:27
def CoversPlaqOm0c ... : Prop :=
  ∀ p, (∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e) →
    ∃ sites j, IsClassCube ell M c k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e

-- ZR6A.lean:33 and :124
def CoversOm0p ... := CoversOm0c ell M c k S ∧ CoversPlaqOm0c ell M c k S
def ClassCoupled ... := CoversOm0p ell M c k S ∧ PerCubeRegular2 ell M c k S α₀ η U
```

`CubeBond` (`ZStatementP428.lean:145`) requires both endpoints in the set.

### Coverage-free, granting existence: false on the stated range

`CoercG8AtNCWDH` (`CvS1.lean:74`) is the inner claim with `PerCubeRegular2` instead of `ClassCoupled`. The conclusion is `InstIneqWDH` (`CvS1.lean:70`): `WellDefG → InstIneq`. `WellDefG` (`ZT4A.lean:51`) is `WellDef ∧ GuardsUnit` (`ZT4A.lean:46`), the three printed inverses as units. This is the sheet's "lemma presupposing the printed inverses", not the junk-value encoding `P428Target8NC`.

```lean
-- NsCS1.lean:50, :55, :59
def NcwdhBodyAt (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=
  ∃ m₀, 1 ≤ m₀ ∧ ∀ m, m₀ ≤ m → ∃ R₀, ∀ R, R₀ ≤ R →
    P428Genuine8NCWDHc c ell (ell ^ m) R (by omega) a
def P428Target8NCWDHc (c : ℕ) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → NcwdhBodyAt c ell hell a
def FailsAtEll (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop := ¬ NcwdhBodyAt c ell hell a

-- NuA3.lean:120. This is the false-for-all-c statement.
theorem ncwdh_fails_ge_two (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    FailsAtEll c ell hell a := by
  rcases (show ell = 2 ∨ 3 ≤ ell by omega) with rfl | h3
  · exact ncwdh_fails_two c hc a ha          -- NuA1.lean:56
  · exact ncwdh_fails_all c hc ell h3 a ha   -- NtFinal.lean:29
```

`not_P428Target8NCWDHc` (`NtFinal.lean:37`) only concludes \(\neg\,\texttt{P428Target8NCWDHc}\, c\) for each \(c \ge 10\). Use `ncwdh_fails_ge_two` when the claim is "every \(c\), every \(\ell\), every \(a\)".

The junk-value row, which the sheet already records and which remains true, is separate: `not_P428Target8NC` (`CvN6.lean:183`), `tip_counterexample` (`CvN6.lean:144`, \(\ell=3\), \(a=1/2\), \(R \ge 28\)), `coverage_necessary` (`CvN7.lean:15`).

### Both coverage clauses: holds on the stated range

`P428Target8NCWDHcov` (`CaT1.lean:61`) is `P428Target8NCWDHc` with `PerCubeRegular2` replaced by `ClassCoupled`. `coercCov_iff` (`CaT1.lean:65`) pins that to `CoversOm0p ∧ PerCubeRegular2`.

```lean
-- CaT1.lean:84
theorem p428Target8NCWDHcov_of_total (c : ℕ) (hc : 10 ≤ c) : P428Target8NCWDHcov c := by
  -- weakening of AdalyFormal.Total.p428Target8Total:
  -- WellDefG ∧ inequality  becomes  WellDefG → inequality
```

The per-(\(\ell\), \(a\)) form is `ncwdhCovBodyAt_of_total` (`CaT1.lean:92`). Range is \(c \ge 10\) only. Do not write "holds for all \(c\)". The proof adds no analytic content and does not assert invertibility; `WellDefG` stays a hypothesis (`CaT1.lean:88`, `hW`).

### Ell = 2, constant family, plaquette clause dropped

```lean
-- CaT2d.lean:144
theorem covPlaq_separately_necessary_two (c : ℕ) (hc : 10 ≤ c) (a : ℝ) (ha : 0 < a) :
    FamilyTorusCovConstAt c 2 (le_refl 2) a ∧ ¬ FamilyTorusSitesConstAt c 2 (le_refl 2) a
```

`FamilyTorusCovConstAt` (`CaT1.lean:117`) keeps `ClassCoupledF (constFam c)`. `FamilyTorusSitesConstAt` (`CaT2d.lean:122`) keeps `CovSitesF ∧ PerCubeRegularF` and drops plaquette coverage. The conjunction is only at \(\ell = 2\). `OPEN_ITEMS.md` section J: the name says "separately necessary"; the scoped content is this pair of bodies. Do not write an unscoped necessity claim.

## Prediction

Already settled, in the sense of B1:

| statement | range | source | verdict in the source |
|---|---|---|---|
| `NcwdhBodyAt` (coverage-free, `WellDefG →` inequality) | \(c \ge 10\), \(\ell \ge 2\), \(a > 0\) | `ncwdh_fails_ge_two` | false |
| `P428Target8NCWDHcov` (both coverage clauses) | \(c \ge 10\) | `p428Target8NCWDHcov_of_total` | holds |
| `FamilyTorusCovConstAt` and not `FamilyTorusSitesConstAt` | \(\ell = 2\), \(c \ge 10\), \(a > 0\) | `covPlaq_separately_necessary_two` | that pair |

These are readings of existing declarations. They do not say the printed hypotheses are insufficient, and they do not say Balaban's sentence means coverage.

What remains open is only whether Balaban's words "the conditions are imposed on \(\Omega_0\)" mean this coverage. The printed sentence is the negative form quoted in clause A7 and in `ZR6A.lean:6`: the regularity conditions do not constrain \(U\) outside \(\Omega_0\). See `ROW6.md`.

## Numerical method and results

No operator was modelled. `genForm`, `Ginv`, `WellDefG` and the inequality were not evaluated. The ell = 2 witness lives on `neS` (`NsCvNe2.lean:122`), whose fine side is `neN` (`NsCvNe2.lean:115`). The side cap for this stage is 8. The script `numerics/extent_check.py` transcribes only the extent and coordinate formulas and checks 36 parameter triples. Output: `numerics/extent_check.out.txt`.

| parameters | why these | unit side `neNu` (`NsCvNe2.lean:105`) | fine side `neN` |
|---|---|---|---|
| \(\ell=2\), \(M=1\), \(R=1\), \(c=10\) | smallest positive inputs with \(c \ge 10\); not a witness of the declaration | 30 | 120 |
| \(\ell=2\), \(m=2\), \(M=4\), \(R=1\), \(c=10\) | smallest `failEllCS_two` (`NuA1.lean:44`) | 120 | 480 |
| \(\ell=2\), \(m=2\), \(M=4\), \(R=10\), \(c=10\) | construction `constFam_witness_two` chooses \(R \ge c\) (`NuA3.lean:99-105`); this is not a bound in the Prop | 264 | 1056 |

Each fine side equals `neNu * ell^2`, which is the identity in the proof of `ne_scaleUp` (`NsCvNe2.lean:130-133`) together with `scaleUp` (`ZStatementP428.lean:42-43`). On this grid (\(M \ge 1\), so the Nat subtraction in `neC0` does not truncate), `neC0 + 1 = neA' + (cf-1)*(ell*M)` (`NuTwoUnc.lean:32-33`) and `neA' ≤ neC0 < neC0+1 < neB'` (`NsCvNe2.lean:107-108`). That places the named direction-0 step inside the thin interval. It does not show that the bond lies in no class cube; that is `ne2_bond_uncovered` (`NuTwoUnc.lean:87`), which was not re-run.

Every one of these sides is greater than 8, including the unit side. A side-at-most-8 torus cannot host the witness, so no smaller cartoon was substituted.

## Stage-B Lean plan

Do not re-prove. After `REPRODUCE.sh` has built the oleans, compile one re-export under `AHP/fidelity/coverage-row/lean/CoverageRow.lean` with `lake env lean` from `lean/`. Imports, all roots of `AdalyFlatLib` (`lean/lakefile.toml`):

```lean
import NuA3
import CaT1
import CaT2d
```

`NuA3` brings `ncwdh_fails_ge_two`. `CaT1` brings `p428Target8NCWDHcov_of_total`. `CaT2d` imports `CaT1` and brings `covPlaq_separately_necessary_two`. Open `NcwdhFam`, `AdalyFormal.NcwdhStrong`, `CovAssume`.

Declarations, each the application of the existing declaration, nothing else:

```lean
theorem coverage_row_fails
    (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    FailsAtEll c ell hell a :=
  ncwdh_fails_ge_two c hc ell hell a ha

theorem coverage_row_both
    (c : ℕ) (hc : 10 ≤ c) : P428Target8NCWDHcov c :=
  p428Target8NCWDHcov_of_total c hc

theorem coverage_row_ell2
    (c : ℕ) (hc : 10 ≤ c) (a : ℝ) (ha : 0 < a) :
    FamilyTorusCovConstAt c 2 (le_refl 2) a ∧
      ¬ FamilyTorusSitesConstAt c 2 (le_refl 2) a :=
  covPlaq_separately_necessary_two c hc a ha
```

Check with `#print axioms` on those three names. Expected output: only `propext`, `Classical.choice`, `Quot.sound`, inherited from the imported declarations. `sorryAx` is a failure. This file does not decide the reading of Balaban's sentence; do not add a declaration about it.

The corrected row text to keep with the sheet, without editing the sheet, is `AHP/fidelity/coverage-row/ROW6.md`.
