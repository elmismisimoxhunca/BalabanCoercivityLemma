# Round 15 seed R1 — charged leading interface and an exact collar-rate candidate

## Verdict and audit boundary

**The physical area seed is still open.**  This round does not prove
`AreaSeedRightStar`, `CofinalUnitDominantAreaSeed`, `CofinalP3`, or `GoalNeg2`.
It supplies a compiled reduction from a precise charged-leading certificate,
plus exact algebra for a numerically extracted collar-rate candidate.  The
frozen right-star operator has **not** been identified with that candidate in
Lean, and no physical leading charged-area constant is claimed to be nonzero.

The main conditional theorem is

```lean
theorem AdalyFormal.Round15.Seed.cofinalUnitDominantAreaSeed_of_chargedLeading
    (h : AdalyFormal.Round15.Seed.DyadicChargedLeadingCertificate) :
    AdalyFormal.Round14.Transfer.Physical.CofinalUnitDominantAreaSeed
```

No inhabitant of `DyadicChargedLeadingCertificate` is supplied.  Thus this is a
snap-together interface for the physical dictionary, not an unconditional
proof of the target.

## Compiled artifacts

| File | Exit | Content |
|---|---:|---|
| `AHP/round15/seed/r1/Seed.lean` | 0 | 5934 lines: main certificate reduction, fixed finite computation, exact rate algebra |
| `AHP/round15/shared/seed/R1_Seed.lean` | 0 | Byte-identical reusable publication |

Both compilations used only

```sh
bb heavy run -- AHP/round3/lean1.sh <file>
```

The logs contain no warnings, errors, or `sorryAx`.  All 27 new declaration
records are checked in `AUDIT.json` (`audit.py`, `audit.log`, and `audit.exit=0`)
and are contained in `{propext, Classical.choice, Quot.sound}`.  The source
contains no `sorry`, `admit`, new `axiom`, `native_decide`, `unsafe`,
`implemented_by`, `extern`, or `opaque`.  Only frozen `DrEquiv` and
`ZXR2Flat6` are imported; no AHP file is imported as a Lean module.  No
`lake build` or `REPRODUCE.sh` was run.

## 1. Exact missing physical input

`ChargedLeadingData` keeps the finite seed, the common index type, the matrix
limit, and the genuine physical generator/area identification separate.  Its
exact compiled statement is:

```lean
def ChargedLeadingData (q : ℕ) (hq : 0 < q) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (r : ℝ) (K : ℕ → ι → ι → ℝ)
    (K0 : ι → ι → ℝ) (z : ι → ℂ),
    ChargedLeadingMatrix r K K0 z ∧
    ∀ n : ℕ, ∃ u : TwistSpace q (2*(n+9)),
      KernelLine q (2*(n+9)) (rightStar hq (2*(n+9))) u ∧ ‖u‖ = 1 ∧
      ∃ k : ℕ, ∃ hk : k < blockCount q (2*(n+9)),
        areaSum hq hk u = chargedArea (K n) z
```

where

```lean
def ChargedLeadingMatrix {ι : Type*} [Fintype ι]
    (r : ℝ) (K : ℕ → ι → ι → ℝ) (K0 : ι → ι → ℝ) (z : ι → ℂ) : Prop :=
  0 < r ∧ z ≠ 0 ∧ chargedArea K0 z ≠ 0 ∧
    Tendsto (fun n => (r^n)⁻¹ • K n) atTop (𝓝 K0)
```

and

```lean
def DyadicChargedLeadingCertificate : Prop :=
  ∀ j : ℕ, ChargedLeadingData (2^j) (by positivity)
```

The observable is totalized off the admissible progression by

```lean
def radiusChargedObservable {ι : Type*} [Fintype ι]
    (K : ℕ → ι → ι → ℝ) (z : ι → ℂ) : ℕ → ℕ → ℝ :=
  fun _ R => chargedArea (K (R/2 - 9)) z
```

`radiusDominantData_of_chargedLeadingMatrix` proves that the matrix limit gives
exactly the already compiled `RadiusDominantData`.  The main theorem then uses
the same `n`, generator, top row, and charged seed at every radius.  The full
carrier norm is one, as required by `CofinalUnitDominantAreaSeed`.

**Nonzero `z` and nonzero `chargedArea K0 z` are deliberately separate
hypotheses.**  A nonzero vector can have zero charged area, and no
scalar-decoupling, definite-Hermitian, common-sign, or spectral-gap assumption
is hidden in the interface.

The remaining physical work is exactly to supply, at each dyadic scale:

1. the frozen flat-collar recurrence and its interface to the star and
   `Omega_1`;
2. a common finite coordinate dictionary for the crossing generator and the
   top-row area coefficients;
3. the star-side seed and its proof of nonzero flat unique continuation;
4. the normalized matrix limit and the **fixed finite** computation
   `chargedArea K0 z ≠ 0`; and
5. the same-generator identity with the genuine `areaSum`.

Item 4 is not implied by item 3.

## 2. Fixed finite computation included

For an interface sanity check, `fixedMatrix` is the rational skew matrix on
`Fin 2` with off-diagonal entries `-1` and `1`, and `fixedSeed` is `(1,i)`.
The compiled exact computation is

```lean
theorem fixedLeadingConstant : chargedArea fixedMatrix fixedSeed = 2
```

with `fixedLeadingConstant_ne_zero` and `fixedSeed_ne_zero`.  This is only a
finite-model verification that the charged-leading interface is computable;
it is **not** the physical right-star leading constant.

## 3. Full collar recurrence found numerically — evidence, not Lean identification

`collar_probe.py` reconstructs the retained `q=1,R=22,c=(0,1)` resolvent and
checks the actual flat-collar equations.  The important negative lesson is
that the naive three-direction block is insufficient: four transverse
sublattice positions mix.  The required state has

\[
  4\ \text{sublattice positions}\times 3\ \text{directions}=12
  \ \text{components per character}.
\]

The complete 12-component blocks satisfy, in the flat collar,
\[
  A_-v_{x-1}+A_0v_x+A_+v_{x+1}=0.
\]
The sampled relative residuals are approximately `1e-65` to `1e-57` in the
deep-collar checks, while the absolute full-resolvent residual is
`1.36e-46`.  The smaller three-component and central-cell tests fail by large
relative errors, so they must not be used as a scalar-decoupling shortcut.
`A_+` is singular; even an invertible naive transfer matrix is not available.

`analyze_transfer.py` performs exact Gaussian-rational Bareiss arithmetic on
the extracted integer/Gaussian-integer blocks (all nonintegral residuals below
`1e-40`).  It obtains the degree-20 pencil determinant

\[
  p(x)=x^4H(x)^2,
\]
where
\[
\begin{aligned}
H(x)={}&x^8-28x^7+286x^6-1288x^5+2387x^4\\
      &-1288x^3+286x^2-28x+1,
\end{aligned}
\]
and
\[
 H(x)=(x^4-10x^3+25x^2-10x+1)
       (x^4-18x^3+81x^2-18x+1).
\]

`candidateH_factor` compiles this polynomial factorization.  It does **not**
compile the assertion that the determinant of the frozen operator is this
candidate.  The numerical transfer has several reciprocal root pairs and
structural zero/infinite directions.  No spectral gap or single dominant-mode
ansatz is inferred.

One root branch is particularly relevant to the retained area series.  Define
\[
 \rho=\frac{5-\sqrt2-\sqrt{23-10\sqrt2}}2.
\]
Then `dominantRho_pos`, `dominantRho_lt_one`, `dominantRho_add_inv`, and
`dominantRho_quartic` compile
\[
 0<\rho<1,\qquad \rho+\rho^{-1}=5-\sqrt2,
\]
and
\[
 \rho^4-10\rho^3+25\rho^2-10\rho+1=0.
\]
The generic transform `q10_eq_transform` proves that the quartic becomes
\(y^2-10y+23\) under \(y=x+x^{-1}\).  Other, larger transfer roots exist, so
the name `dominantRho` refers only to the branch seen in the sampled area
observable, not to a proved spectral-dominance theorem.

Since the quadratic area is evaluated four layers further inward for each
increment of `R` by two, the candidate rate per radius step is \(\rho^8\).
Numerically, using the extracted root gives
\[
 \rho^8\approx 7.4464388308\times10^{-5},
\]
while the retained Laurent-window value is approximately
\[
 7.4464352709\times10^{-5},
\]
a relative discrepancy of about `4.8e-7`, consistent with the double-precision
eigenvalue extraction.  This is strong evidence for the recurrence candidate,
but it is not an interval certificate or a Lean premise.  It also does not
show that the physical seed projects onto this branch, that the projection is
nonzero, or that the leading charged area is nonzero.

Numerical files and successful exit records:

- `collar_probe.py`, `collar_probe.log`, `collar_probe.exit`,
  `collar_q1_R22_c0_1.json`;
- `analyze_transfer.py`, `analyze_transfer.log`, `analyze_transfer.exit`,
  `transfer_polynomial.txt`.

All Python diagnostics used less than 2 GiB and are evidence only.

## 4. What remains unproved

The exact remaining statement is `DyadicChargedLeadingCertificate` displayed
above.  In particular, the following are still missing:

- a Lean proof that the frozen all-plaquette operator and its dressing have
  the 12-component constant-coefficient blocks on every required flat-collar
  row and character;
- the exceptional `Omega_1` interface rows and the star-side boundary problem;
- the seed's projection onto the \(\rho\) branch and proof that this projection
  is nonzero;
- a fixed-size leading matrix `K0` and exact charged-area evaluation
  `chargedArea K0 z ≠ 0`;
- the genuine `areaSum` identity and full-norm normalization.

Consequently `AreaSeedRightStar`, `CofinalUnitDominantAreaSeed`,
`CofinalP3`, and `GoalNeg2` remain open.  The conditional theorem in this
round must not be cited as an unconditional proof of any of them.

## Scope

Writes were confined to `AHP/round15/seed/r1/` and
`AHP/round15/shared/seed/`.  Earlier rounds, frozen modules, the lakefile,
integration checkout, and other round-15 tracks were not edited.  No git
commit or push was made.
