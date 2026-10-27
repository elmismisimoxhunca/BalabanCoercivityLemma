# Round-15 numerics R1 — exact collar dictionary and leading constants

## Verdict and evidence boundary

This track supplies a numerical operator dictionary and independent
high-precision checks for the other tracks.  It does **not** prove
`AreaSeedRightStar`, any cofinal area/dominant seed, P3, CofinalP3, or
GoalNeg2.  No new Lean declaration is introduced here.  The results below are
not interval certificates, and no numerical value is a Lean premise.

The reusable package is `AHP/round15/shared/numerics/`, especially its
`README.md`, `characters/`, `characteristic_q*_c*.json`,
`dominant_right_q*.json`, `LEADING_SUMMARY.json`, and `LAURENT_REVIEW.json`.

## 1. Exact per-layer recurrence, including interfaces

All 336 Fourier characters were extracted:

- q=1,R=22: 16 characters in `characters/q1_R22/`;
- q=2,R=20: 64 characters in `characters/q2_R20/`;
- q=4,R=18: 256 characters in `characters/q4_R18/`.

With \(N=4q\), \(s=q(10R+12)\), and \(h=q(12R+12)\), the 12-component state is
four transverse cells times three directions.  The actual constant-coefficient
collar equations are

\[
  K_-v_{x-1}+K_0v_x+K_+v_{x+1}=0,
  \qquad s+1\le x\le h-2.
\]

The files give the exact \(K_-,K_0,K_+\) at `blocks["-1"]`, `blocks["0"]`, and
`blocks["1"]`.  The augmented physical/multiplier equations on
\(s-4\le x\le s\) and on \(x=h-1\) are written explicitly in
`interface_rows`; the shared `descriptors.json` identifies every column.
Thus the exceptional star and `Omega_1` rows are not silently replaced by a
bulk scalar recurrence.

Direction zero is eliminated with exact rational/cyclotomic arithmetic.  The
remaining eight transverse blocks are `reduced_blocks.A/B/C`.
`reduced_determinants.A` and `.C` are equal and nonzero for all four dominant
characters at each q, so their 16-by-16 transfer companions are defined.  No
invertibility of the unreduced 12-component block is assumed.

`audit_characters.py` checks all file counts, shapes, exact determinant
identities, constant rows, and SHA-256 records.  It passes.  The q=1 solve
records have maximum absolute resolvent residual \(1.54\times10^{-46}\) and
maximum augmented null residual \(1.56\times10^{-46}\).  The q=2 records have
maximum absolute resolvent residual \(6.15\times10^{-47}\).  The q=4 dominant
interface records have absolute resolvent residual \(8.24\times10^{-63}\) and
maximum relative row residual \(5.03\times10^{-58}\).  These are non-interval
residuals, not exact-zero proofs.

The coefficient field is explicit in every file.  q=1 uses Gaussian-rational
entries; q=2 uses \(\mathbf Q(\zeta_8)=\mathbf Q(i,\sqrt2)\), so real and
imaginary parts can be written in \(\mathbf Q(\sqrt2)\); q=4 uses the quartic
field \(\mathbf Q(\zeta_{16})\), not merely \(\mathbf Q(\sqrt2)\).  No rational
or \(\mathbf Q(\sqrt2)\) closed form is claimed for the area amplitude itself.

## 2. Exact characteristic factor and rate

For each q, all four characters
\((0,1),(0,N-1),(1,0),(N-1,0)\) have exactly zero residual between the
16-by-16 companion characteristic polynomial and

\[
  (Q_5^2-a^2x^2)^2(Q_9^2-a^2x^2)^2,
  \quad Q_5=x^2-5x+1,\quad Q_9=x^2-9x+1,
  \quad a^2=2+\zeta_N+\zeta_N^{N-1}.
\]

The `characteristic_q*_c*.json` files contain the exact matrices, determinant
entries, characteristic polynomial, factor, and zero residual.  Put
\(y=5-\sqrt{a^2}\) and \(\rho=(y-\sqrt{y^2-4})/2\).  The rate per
\(R\mapsto R+2\) is \(\rho^{8q}\):

- q=1: \(y=5-\sqrt2\), rate
  \(7.446438830808222444\times10^{-5}\);
- q=2: \(y=5-\sqrt{2+\sqrt2}\), rate
  \(7.234910171247043634\times10^{-8}\);
- q=4: \(y=5-\sqrt{2+\sqrt{2+\sqrt2}}\), rate
  \(2.447093793466790288\times10^{-14}\).

This is an exact algebraic factorization of the numerically transcribed
matrices, not yet a Lean identification with the frozen operator and not a
proof of branch projection.

## 3. Direct leading constants and stability

At every even \(R=18,20,\ldots,40\), independent flat solves evaluate the four
slowest characters.  With

\[
  A_R=N^{-2}\sum_c\operatorname{areaSum}_c(R),
  \qquad K_R=A_R/\rho^{4qR},
\]

the direct normalized constants are:

- q=1: \(K=0.0133612068931633503479\), with
  \(|K_{40}/K_{18}-1|=6.30\times10^{-22}\);
- q=2: \(K=0.0019184541381844317668645407795820\), with
  \(|K_{40}/K_{18}-1|=8.86\times10^{-56}\);
- q=4: \(K=0.0001653700585858785228210904209427\), with
  \(|K_{40}/K_{18}-1|=2.22\times10^{-57}\).

The maximum successive-rate discrepancies are \(7.35\times10^{-12}\) at q=1,
\(2.95\times10^{-29}\) at q=2, and \(1.37\times10^{-56}\) at q=4.  The
corresponding absolute resolvent residuals are \(1.32\times10^{-46}\),
\(6.15\times10^{-47}\), and \(8.24\times10^{-63}\).  The q=4 drive has root
\(1.2080305442108319045317604810224168\) and boundary null residual
\(7.09\times10^{-40}\).
`independent_checks` in `LEADING_SUMMARY.json` compares the dominant-character
area with retained full-area runs.  The small remaining difference is the
subleading contribution; it is not hidden by a common-sign assertion.

These data support a normalized-limit candidate only.  They do not prove the
existence of a common finite seed, a nonzero seed projection, a normalized
matrix limit, or a nonzero charged area.

## 4. Failed same-row Laurent fit

`LAURENT_REVIEW.json` reproduces the failed q=1 fit at 170 digits.  The
three-term prediction fitted on \(R=20,22,24,26\) fails at held-out \(R=28\)
with relative errors about \(8.77\times10^5\), \(8.77\times10^5\), and
\(2.01\times10^6\), including sign reversals.

The naive ansatz has characteristic roots \(r,1,r^{-1}\), but the physical top
row has five distinct decaying character rates.  The omitted subleading modes
shift the fitted leading coefficient enough to make extrapolation ill-conditioned.
Using all five measured rates gives an order-five recurrence whose predictions
at \(R=30,32,34\) have relative errors below \(4\times10^{-10}\) in the reported
checks.  This explains the failed fit numerically; it does not prove an exact
Laurent representation or cofinal nonvanishing.

## 5. Exact statements still missing

The shortest per-instance physical seed remains exactly

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

This is `AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar`, and it is
still unproved.  The preferred normalized cofinal alternative is exactly

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∃ observable : ℕ → ℕ → ℝ,
  RadiusDominantData observable (2^j) ∧
  ∀ n : ℕ, ∃ u : TwistSpace (2^j) (2*(n+9)),
    KernelLine (2^j) (2*(n+9)) (rightStar (by positivity) (2*(n+9))) u ∧
    ‖u‖ = 1 ∧
    ∃ k : ℕ, ∃ hk : k < blockCount (2^j) (2*(n+9)),
      areaSum (by positivity : 0 < 2^j) hk u = observable (2^j) (2*(n+9))
```

This is `CofinalUnitDominantAreaSeed`, also still unproved.  The sharper
round-15 charged-leading input remains

```lean
∃ (ι : Type) (_ : Fintype ι) (r : ℝ) (K : ℕ → ι → ι → ℝ)
  (K0 : ι → ι → ℝ) (z : ι → ℂ),
  ChargedLeadingMatrix r K K0 z ∧
  ∀ n : ℕ, ∃ u : TwistSpace q (2*(n+9)),
    KernelLine q (2*(n+9)) (rightStar hq (2*(n+9))) u ∧ ‖u‖ = 1 ∧
    ∃ k : ℕ, ∃ hk : k < blockCount q (2*(n+9)),
      areaSum hq hk u = chargedArea (K n) z
```

with

```lean
0 < r ∧ z ≠ 0 ∧ chargedArea K0 z ≠ 0 ∧
  Tendsto (fun n => (r^n)⁻¹ • K n) atTop (𝓝 K0)
```

The numerical package does not supply the common finite index type and seed
`z`, a proof that its projection is nonzero, a proof that `chargedArea K0 z`
is nonzero, the same-generator identity with genuine `areaSum`, or the
full-carrier norm condition.  Consequently the conditional arrows to P3 and
GoalNeg2 remain conditional.

## 6. Reproduction and scope

The main commands are listed in `AHP/round15/shared/numerics/README.md`.
`audit_characters.py` and `CHARACTER_AUDIT.json` verify all 336 dictionaries.
`leading_summary.py` regenerates the rate/constant table, and
`laurent_review.py` regenerates the failed-fit analysis.

All Python runs used less than 2 GiB per process.  No `lake build`,
`REPRODUCE.sh`, Lean compilation, git commit, or push was run.  No earlier
round, frozen module, lakefile, or integration checkout was edited.  A separate
pre-existing q=4 sweep that used the q=2 drive is not used as a physical q=4
crossing-generator certificate; the q=4 leading run uses an independent q=4
drive.
