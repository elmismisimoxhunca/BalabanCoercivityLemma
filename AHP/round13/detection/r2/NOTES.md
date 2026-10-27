# Detection R2 — actual alternating-area dictionary; P3 still OPEN

## Verdict

**P3 is neither proved nor disproved. The nested cofinal detection family and
GoalNeg2 remain open.** No numerical nonzero value is promoted to a theorem.
This round proves an exact finite mixed-color expansion for the genuine dressed
jet and specializes it to the **original actual crossing generator**. It does
not prove that the resulting weighted area sum is nonzero.

R1's flat-N unit and top-jet/curl bridge are reused verbatim. The new work is not
another linear-continuation lemma: it identifies precisely the quadratic
quantity that a continuation or sign argument would have to preserve.

## Clean compiled artifacts

All commands were sequential `bb heavy run -- AHP/round3/lean1.sh <file>`.
Each source has its own `.lean.log` and `.lean.exit=0`.

| Local file | Publication in `AHP/round13/shared/detection/` | Lines | Axiom records, each execution | Local/shared exits |
|---|---|---:|---:|---|
| `Area.lean` | `R2_Area.lean` | 86 | 5 | 0 / 0 |
| `ColorArea.lean` | `R2_ColorArea.lean` | 741 | 51 | 0 / 0 |
| `PhysicalArea.lean` | `R2_PhysicalArea.lean` | 4436 | 286 | 0 / 0 |

`AUDIT.json` / `audit.py` verify all six executions, zero warnings/errors in the
final logs, all 36 new declarations' dependency records, seven verbatim source
fragments, publication byte identity, and absence of forbidden proof mechanisms.
Every printed axiom set is a subset of `{propext, Classical.choice, Quot.sound}`.
Imports are frozen `DrEquiv` and, in the physical join inherited from R1,
`ZXR2Flat6`. No AHP file is imported as an unbuilt module.
These are **builder/publication executions, not independent review**.

## 1. Exact genuine mixed-color dictionary

Namespace `AdalyFormal.Round13.Detection.ColorArea`, publication
`R2_ColorArea.lean`:

- `colorCarrier` masks a real scalar array to the actual touching-bond carrier
  and multiplies it by a specified Pauli vector. An atom outside the carrier
  is zero; no unsupported bond is inserted.
- `color_one_zero`, `color_two_zero` prove vanishing of the genuine entire
  dressed flat jet for either single real color.
- `quarter_pauliE1`, `quarter_pauliE2`, `flatJet_color_quarter` use exact SU(2)
  quarter rotation to show the mixed jet is alternating in the two scalar
  color arrays. No numerical phase is used.
- `flatJet_area` (:639) gives an exact expansion of the **full**
  `Color.flatJet G a = C2fullOf G 1 (Wop G 1 a (iE G ...))`.
- `carrier_color_decompose` shows every charged carrier is exactly the sum of
  its actual two scalar colors. No nonzero jet is inferred from chargedness.
- `neutralJet_area` (:707) gives the corresponding exact genuine `BIdx` row.

Write the charged entry of a carrier as \(z_e=g_e+i f_e\), with E1 coefficient
\(f_e\) and E2 coefficient \(g_e\). For a genuine row \(p\), let
\[
K_p(e,d)=\left\langle E_3,
  C^2_0\bigl(W_0 i_E(E_1\delta_e+E_2\delta_d)\bigr)(p)\right\rangle,
\]
where both atoms are masked to the true carrier. The compiled identity is
\[
\left\langle E_3,C^2_0(W_0 i_Eu)(p)\right\rangle
 =\frac12\sum_{e,d}(f_e g_d-g_e f_d)K_p(e,d).
\]
`areaCoefficient_skew` and `areaCoefficient_diagonal` prove
\(K_p(d,e)=-K_p(e,d)\) and \(K_p(e,e)=0\). The factor \(1/2\) pays for
ordered-pair double counting; the frozen `C2fullOf` normalization is separately
retained inside each coefficient.

The coefficients are **defined by actual two-bond inputs to W/C2**, not by an
arbitrary skew matrix or numerical stencil. However, this is a **global finite
bond expansion**, not an evaluated local 2x2x2 block formula. No coefficient
sign, sparsity, Fourier diagonalization, or recurrence identity is proved.
In particular, W is not replaced by the identity in the interior.

## 2. Exact specialization to the original crossing generator

Namespace `AdalyFormal.Round13.Detection.PhysicalArea`, publication
`R2_PhysicalArea.lean`:

- `aggregateCoefficient` (:4340) sums the above coefficients over the original
  even transverse `topIdx` cells in direction 1.
- `areaSum` (:4345) is the full weighted determinant sum, with no normalization
  of the input generator and no discarded cells or bond pairs.
- `kernelLine_half` derives the exact charged-color hypothesis from the
  quarter-turn clause of the **original** `KernelLine`.
- `crossing_physicalJetAggregate_area` (:4400) proves:

```lean
{q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
(V : ℝ → LinkCfg (L q R)) (u : TwistSpace q R)
(hline : KernelLine q R V u) :
physicalJetAggregate hq hj u = (1 / 2 : ℝ) * areaSum hq hj u
```

The actual `pathU`, `pathP`, `pathA`, `vacA`, `psdEdge`, `vacEdge`, and
`KernelLine` block is copied verbatim from round-12 `ActualResponse.lean`.
Thus the theorem refers to the original canonical crossing, not an arbitrary
selected-character vector. It supplies an identity for any generator satisfying
that predicate; **it does not construct such a generator**.

`crossing_topJet_iff_area` (:4407) proves, for that same generator,

```lean
TopJetDetected hq R u ↔
  ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

`crossing_curlDetected_of_area` (:4419) combines this with R1's proved flat N
unit. It **explicitly assumes** the nonzero area sum, so it is a conditional
handoff, **not a proof of P3**. The exact nonvanishing assertion remains missing.

Literal accepted dependency record:

```text
'AdalyFormal.Round13.Detection.PhysicalArea.crossing_physicalJetAggregate_area' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Why the proposed shortcuts still do not close P3

The round-10 scalar recurrence lemma requires a recurrence and nonzero seed for
the scalar coupling itself. A reversible recurrence for the *linear carrier*
does not supply that. `R2_SourceFamily` separates a jet that is already nonzero;
its `hne` does not follow from an interface field value.

R1 already proved genuine zero jets for arbitrary single-color fields and an
exact linear-recurrence counterexample to area nonvanishing. Its read-only
analysis of retained right-star data also found mixed signs among the physical
cell contributions. This round neither repeats those proofs nor assumes a
common sign over cells. The new exact identity shows what is missing instead:
control of the **weighted sum of mixed-color areas**, including cancellations.
A nonzero individual area is still insufficient unless its weighted contribution
cannot cancel. No such physical sign or weighted-current propagation theorem
has been established here. No new numerical solve or interval certificate was
run.

## Exact remaining P3 (verbatim)

With the original shared-package opens:

```lean
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round12.Noncancel.RightFamily (rightStar)
```

The following proposition is **unproved**:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

Using this round's `PhysicalArea` and the original `DilatedFlux` opens, an exact
sufficient remainder is also **unproved**:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

The weaker original nested cofinal family remains unproved:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    CurlDetected (2^j) R u
```

For the new area route, the sufficient nested input (also **unproved**) is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    ∃ k : ℕ, ∃ hk : k < blockCount (2^j) R,
      areaSum (by positivity : 0 < 2^j) hk u ≠ 0
```

This must use the **same** scales, radii, right-star path, crossing and vector as
P2/KernelLine. No cofinal witness is chosen here. The already-compiled per-instance
handoff preserves those data, but no new monolithic cofinal/GoalNeg2 join is
claimed. P1 is recorded as closed by the sibling track in the supplied handoff;
this track does not reprove it or infer P2 from it.

## Reproduction and scope

```sh
python3 AHP/round13/detection/r2/build.py --publish
# Run each local and published file sequentially through lean1.sh.
bb heavy run -- AHP/round3/lean1.sh AHP/round13/detection/r2/Area.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/detection/r2/ColorArea.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/detection/r2/PhysicalArea.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/shared/detection/R2_Area.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/shared/detection/R2_ColorArea.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/shared/detection/R2_PhysicalArea.lean
python3 AHP/round13/detection/r2/audit.py
```

Only `AHP/round13/detection/r2/` and `AHP/round13/shared/detection/R2_*` were
written. No prior round, frozen module, lakefile, integration checkout, git
commit or push was changed. No large historical join, `lake build`, or
`REPRODUCE.sh` was run. No deletion was performed.
