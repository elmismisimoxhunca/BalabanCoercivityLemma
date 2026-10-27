# Round 14 transfer R1 — exact Laurent transfer and generator-only P3 reduction

## Verdict and audit boundary

**P3, CofinalP3, and GoalNeg2 remain open.** This round proves the scalar
transfer algebra and a new conditional reduction of the original universal
`CofinalP3` to one Laurent-certified area observable. It does **not** identify
the frozen right-star carrier with the scalar recurrence, and it does **not**
prove the required physical `CofinalLaurentAreaSeed` certificate. No numerical
value is used as a proof premise, and no conditional theorem below is presented
as a physical proof.

The useful strengthening over the round-13 area remainder is that only **one
crossing generator and one physical top row** are needed at each selected
instance. The round-12 charged-line response argument then detects every vector
satisfying the original `KernelLine` predicate. No common cell sign, single
nonzero determinant, or independent second detected family is assumed.

## Compiled artifacts

All compiles used only `AHP/round3/lean1.sh <file>`, sequentially, with a long
shell timeout. Every `.exit` is `0`; every final log has zero warnings/errors
and only dependency records contained in
`{propext, Classical.choice, Quot.sound}`. There is no `sorry`, `admit`, new
axiom, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque` in the
sources. No AHP artifact is imported as a Lean module.

| Local file | Publication in `AHP/round14/shared/transfer/` | Lines | Axiom records, each execution | Local/shared exits |
|---|---|---:|---:|---|
| `Transfer.lean` | `R1_Transfer.lean` | 169 | 17 | 0 / 0 |
| `Generator.lean` | `R1_Generator.lean` | 4937 | 317 | 0 / 0 |

Local and published sources are byte-identical, and the published files were
compiled separately after the final local edits.

SHA-256:

- `Transfer.lean` / `R1_Transfer.lean`:
  `2ac74c53b95db2d329bccee333b9c5f7e517720602636cd3e17cea7a01623118`
- `Generator.lean` / `R1_Generator.lean`:
  `f2989c5b2704e6bac353fd25e936fb6f380145040b6823fe71f939c5ed68de47`

These are builder and separate-publication executions, not independent
mathematical review.

## 1. Exact two-layer and Laurent transfer algebra

Namespace `AdalyFormal.Round14.Transfer`, `Transfer.lean`.

For `mode r a b n = a*r^n + b*(r⁻¹)^n`, `mode_recurrence` (:27) proves
\[
  x_{n+2}=(r+r^{-1})x_{n+1}-x_n.
\]
`mode_orientedArea` (:35) gives the exact adjacent-layer determinant identity
\[
  x_n y_{n+1}-y_n x_{n+1}=(a d-b c)(r^{-1}-r),
\]
where `x = mode r a b` and `y = mode r c d`. Thus a nonzero amplitude
 determinant and `r⁻¹-r ≠ 0` propagate nonzero oriented area to every layer
(`mode_orientedArea_ne_zero`, :43). This is an exact two-branch identity, not a
claim that the physical `areaSum` has already been put in this form.

For the more general quadratic observable
\[
  \operatorname{laurent}(r,A,B,C,n)=A r^n+B+C(r^{-1})^n,
\]
`laurent_mul_pow` proves
\[
  r^n\operatorname{laurent}(r,A,B,C,n)
    =(A X^2+B X+C)\big|_{X=r^n}.
\]
Consequently any nonzero coefficient among `A,B,C` gives eventual nonvanishing
when `0 < r < 1` (`laurent_eventually_ne_zero`), and hence cofinal nonvanishing
(`laurent_cofinal_ne_zero`, :105). The proof uses finiteness of the roots of a
nonzero polynomial on the injective geometric progression. It covers a mixed
term and an exponentially smaller remainder; it does not require a common sign
or a normalized-limit estimate.

`RadiusLaurentData` (:121) packages this identity on the exact admissible
progression `R = 2*(n+9)`. The compiled consequences are:

```lean
theorem radius_cofinal_nonzero_of_laurent (observable : ℕ → ℕ → ℝ) (q : ℕ)
    (h : RadiusLaurentData observable q) :
    ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ observable q R ≠ 0
```

and, with `DyadicLaurentData`,

```lean
theorem dyadic_cofinal_nonzero_of_laurent (observable : ℕ → ℕ → ℝ)
    (h : DyadicLaurentData observable) :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ observable (2^j) R ≠ 0
```

For a quadratic flat-collar observation one can take `r = ρ^2`; for a linear
observation one can take `r = ρ`. The physical identification is still missing.

## 2. One detected generator is enough for universal KernelLine detection

`Generator.lean` contains the independently compiled round-13 physical area
file, the operative round-12 charged-line response lemmas, and minimal verbatim
copies of `starLinks`, `starPath`, `rightSite`, `rightStar`, original `P3`, and
original `CofinalP3`. Frozen imports remain only `DrEquiv` and `ZXR2Flat6`.

`AreaSeedRightStar` (:4758) is the following existential sufficient condition:

```lean
def AreaSeedRightStar : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
    ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
      ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

The compiled implications are:

```lean
theorem p3_of_detectedRightStar (h : DetectedRightStar) :
    AdalyFormal.Round13.Assembly.R1.P3

theorem p3_of_areaSeed (h : AreaSeedRightStar) :
    AdalyFormal.Round13.Assembly.R1.P3
```

The proof applies `crossing_curlDetected_of_area` to the supplied generator,
then `all_kernel_detected_of_generator` to any other `KernelLine` vector. The
latter uses the exact quadratic response scaling on the charged real span; it
is not an appeal to chargedness alone.

The nested version `cofinalP3_of_areaSeed` (:4791) has exactly the original
`CofinalP3` conclusion, with no quantifier interchange.

## 3. Exact remaining transfer certificate

The main new conditional endpoint is:

```lean
theorem cofinalP3_of_laurentAreaSeed (h : CofinalLaurentAreaSeed) :
    AdalyFormal.Round13.Assembly.R2.CofinalP3
```

Its only hypothesis is the compiled proposition `CofinalLaurentAreaSeed` (:4910),
which is **unproved** and is the exact remaining statement for this track:

```lean
def CofinalLaurentAreaSeed : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∃ observable : ℕ → ℕ → ℝ,
    RadiusLaurentData observable (2^j) ∧
    ∀ n : ℕ, ∃ u : TwistSpace (2^j) (2*(n+9)),
      KernelLine (2^j) (2*(n+9)) (rightStar (by positivity) (2*(n+9))) u ∧
      ∃ k : ℕ, ∃ hk : k < blockCount (2^j) (2*(n+9)),
        areaSum (by positivity : 0 < 2^j) hk u = observable (2^j) (2*(n+9))
```

Recall the included exact interface:

```lean
def RadiusLaurentData (observable : ℕ → ℕ → ℝ) (q : ℕ) : Prop :=
  ∃ r A B C : ℝ, 0 < r ∧ r < 1 ∧ (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧
    ∀ n : ℕ, observable q (2*(n+9)) = laurent r A B C n
```

and

```lean
def laurent (r A B C : ℝ) (n : ℕ) : ℝ := A*r^n+B+C*(r⁻¹)^n
```

Thus the physical work left is precisely to:

1. derive the genuine flat right-star collar recurrence and its two transfer
   roots from the frozen carrier;
2. identify a same-generator physical `areaSum` with the three-term Laurent
   form (including any mixed and remainder coefficients); and
3. prove that at least one Laurent coefficient is nonzero from the two-layer
   star-side seed.

The already compiled `rightStar_kernelLine` can supply the line conjunct at the
same indices. Once the above certificate is supplied,
`cofinalP3_of_laurentAreaSeed` gives the original `CofinalP3`, and the existing
independently verified `goalNeg2_of_cofinalP3` can be applied. Neither of those
last two steps supplies the missing certificate.

For the stronger all-instance formulation, the original statement remains
unproved as well:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

By `p3_of_areaSeed`, it suffices to prove `AreaSeedRightStar`; by
`cofinalP3_of_laurentAreaSeed`, the nested `CofinalLaurentAreaSeed` is enough
for the pinned cofinal route. No proof of either area predicate is included.

## Reproduction and scope

```sh
AHP/round3/lean1.sh AHP/round14/transfer/r1/Transfer.lean
AHP/round3/lean1.sh AHP/round14/transfer/r1/Generator.lean
AHP/round3/lean1.sh AHP/round14/shared/transfer/R1_Transfer.lean
AHP/round3/lean1.sh AHP/round14/shared/transfer/R1_Generator.lean
```

Only `AHP/round14/transfer/r1/` and `AHP/round14/shared/transfer/` were written.
No earlier round, frozen module, lakefile, integration checkout, git commit or
push was changed. No `lake build`, `REPRODUCE.sh`, large historical join,
numerical solve, or deletion was run.
