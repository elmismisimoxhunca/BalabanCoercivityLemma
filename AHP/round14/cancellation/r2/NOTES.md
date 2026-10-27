# Cancellation R2 — charged-line and dominant-area structure; P3 remains open

## Verdict and audit boundary

**P3, CofinalP3, and GoalNeg2 are not proved.** This round supplies compiled
exact `U(1)`/charged-line identities for the genuine `areaSum`, and a separate
compiled sign-preservation theorem for a convergent normalized coefficient
matrix. These are algebraic/analytic interfaces, not a physical area-seed proof.
No numerical value is used as a proof premise, and no conditional result below
is called a proof of the pinned goal.

The required round-13 blueprint, GAPS, detection R1/R2 notes, and the round-14
R1 cancellation/transfer/assembly notes were read before work. R1's compiled
charged-area algebra is reused conceptually; it is not recompiled here.

## Compiled deliverables

The local source and its byte-identical publication were each compiled with
`bb heavy run -- AHP/round3/lean1.sh <file>`:

| File | Lines | Exit | Axiom records | SHA-256 |
|---|---:|---:|---:|---|
| `AHP/round14/cancellation/r2/AreaStructure.lean` | 4667 | 0 | 298 | `8f82949c0a5a92817ab1343ceab8218c96a41730b9a22787954dfae2ba040b0f` |
| `AHP/round14/shared/cancellation/R2_AreaStructure.lean` | 4667 | 0 | 298 | same |

The source consists of the round-13 `R2_PhysicalArea.lean` verbatim, followed
by the new `AdalyFormal.Round14.Cancellation` declarations. Imports remain only
frozen `DrEquiv` and `ZXR2Flat6`. Both final logs have no warnings or errors and
no `sorryAx`. Every printed axiom set is a subset of
`{propext, Classical.choice, Quot.sound}`. There is no `sorry`, `admit`, new
`axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`.
No `lake build`, `REPRODUCE.sh`, or AHP module import was used.
`audit.py` rechecks those conditions, publication byte identity, the 298 records
per execution, all new declarations, and the auxiliary numerical exits; its
`AUDIT.json` and `audit.exit=0` are included.

## 1. Exact structure on the genuine charged line

The new theorems compute the scalar colours under the quarter-turn:

```lean
realPart (G q R) (adEL (rotGauge (Real.pi/4)) (G q R) u) e =
  -imagPart (G q R) u e
imagPart (G q R) (adEL (rotGauge (Real.pi/4)) (G q R) u) e =
  realPart (G q R) u e
```

Consequently `areaSum_affine` (:4520) proves, for the actual physical
`aggregateCoefficient` and `areaSum`,

```lean
areaSum hq hj (a • u + b • adEL (rotGauge (Real.pi/4)) (G q R) u) =
  (a^2+b^2) * areaSum hq hj u
```

Thus the weighted mixed-colour area on one charged real line really is a fixed
real number per instance, multiplied by `a²+b²`. `areaSum_quarter` is the
`a=0,b=1` special case. `areaSum_affine_ne_zero` and
`areaSum_ne_zero_of_mem_charged_span` (:4565) propagate nonvanishing to every
nonzero vector in that real span. This is an area-level counterpart of the
round-12 one-generator response reduction; it does not show that the fixed
number is nonzero.

`areaSum_eq_chargedArea` (:4584) also identifies the actual expression with the
charged form used in the new dominant-coefficient theorem:

```lean
areaSum hq hj u = chargedArea (aggregateCoefficient hq hj)
  (fun e => (realPart (G q R) u e : ℂ) +
    (imagPart (G q R) u e : ℂ) * Complex.I)
```

This is an exact identity, not a positivity assertion. The coefficient matrix
is real skew, so its Hermitian form is not definite in general.

## 2. Exact sign control from a dominant matrix

For finite `ι`, `chargedArea K z` is
`∑ e,d, (z e * conj (z d)).im * K e d`. The new theorem
`tendsto_chargedArea` proves that matrix convergence implies convergence of the
normalized charged area:

```lean
(hK : Tendsto (fun n => (r^n)⁻¹ • K n) atTop (𝓝 K0)) →
  Tendsto (fun n => chargedArea (K n) z / r^n) atTop
    (𝓝 (chargedArea K0 z))
```

The useful sign result is `chargedArea_eventually_pos_of_matrix_limit` (:4627):

```lean
(hr : 0 < r) (z : ι → ℂ) (hpos : 0 < chargedArea K0 z)
(hK : Tendsto (fun n => (r^n)⁻¹ • K n) atTop (𝓝 K0)) :
  ∀ᶠ n in atTop, 0 < chargedArea (K n) z
```

The companion `chargedArea_eventually_ne_zero_of_matrix_limit` handles either
nonzero sign. Thus a positive leading symplectic coefficient is enough; there
is no need for every cell or every character contribution to have one sign.
This is a compiled sign-control theorem, but the physical matrix limit and its
positive leading coefficient remain unproved.

## 3. Numerical structure evidence only

Artifacts are under `AHP/round14/cancellation/r2/`:

- `row_profile.py`, `analyze.py`, and `PROFILE_ANALYSIS.json`;
- `row_profile_right_q1_R20_p40.log` (partial run stopped by the shell timeout
  after row 74), and the exit-0 `..._tail72.{json,log,exit}` continuation;
- `row_profile_right_q1_R20_p80_early80.{json,log,exit}` (exit 0);
- `structure_right_q1_R22_p40.{json,log,exit}` (exit 0);
- `analyze.{log,exit}` (exit 0).

At right-star `q=1,R=20`, all 84 computed longitudinal row aggregates were
positive, from approximately `8.17664e-140` through `7.00378e-44`. Rows 0–7
were independently recomputed at 80 digits and agreed with the 40-digit run to
relative error at most `3.0e-12`. The last row agrees with the independently
computed R1 Hermitian value. The row ratios vary widely, so this is **not**
evidence for a simple low-order recurrence across rows. These are non-interval
computations, not a sign certificate.

At `R=20` and `R=22`, the symmetric nine-bond boundary vector has the same
numerical norm squared `16.3525647283`. In the dominant Hermitian basis the
largest positive/negative area contributions are respectively
`7.94844e-44` / `-9.44666e-45` at `R=20`, and
`5.91876e-48` / `-7.03440e-49` at `R=22`, with positive totals. The remaining
Hermitian eigenvalues still occur in `±` pairs, so no definite-Hermitian or
common-character-sign shortcut follows.

For the last physical row, the `R=20,22,24,26,28,30` area values have successive
ratios approximately `13429.2445, 13429.2397, 13429.2385, 13429.2382,
13429.2381`. Normalizing by that fitted rate gives a nearly constant
`0.0133612072`. This **suggests** a dominant matrix limit and positive leading
coefficient, but supplies neither the limit, an exact rate, a common index type,
nor a nonzero-coefficient proof. It is not a `RadiusLaurentData` or
`RadiusDominantData` certificate.

## 4. Exact statements still missing

The original P3 remains exactly:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

The sharper per-instance seed from transfer R1 is also still unproved:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

By `areaSum_eq_chargedArea`, the last conjunct can equivalently be written

```lean
∃ j : ℕ, ∃ hj : j < blockCount q R,
  chargedArea (aggregateCoefficient hq hj)
    (fun e => (realPart (G q R) u e : ℂ) +
      (imagPart (G q R) u e : ℂ) * Complex.I) ≠ 0
```

A possible next-round dominant-collar certificate has the following exact
schema. It is **not supplied here**:

```lean
∃ (r : ℝ) (K0 : ι → ι → ℝ) (z : ι → ℂ),
  0 < r ∧ 0 < chargedArea K0 z ∧
  Tendsto (fun n => (r^n)⁻¹ • K n) atTop (𝓝 K0)
```

To use it physically, one must additionally identify `K`, `K0`, and `z` with
the actual aggregate coefficients and crossing-generator coordinates at the
same indices, including a common finite index type and all radius-dependent
choices. Then `chargedArea_eventually_pos_of_matrix_limit` gives eventual
positive area, while `areaSum_eq_chargedArea` returns to the genuine area.
No such physical identification or cofinal instance is constructed in R2.

## Scope

Writes are confined to `AHP/round14/cancellation/r2/` and
`AHP/round14/shared/cancellation/`. Earlier rounds, frozen modules, the lakefile,
and the integration checkout were not edited. No git commit or push was made.
