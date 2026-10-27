# Round-15 exact-collar numerics

**R2 update:** see [R2_README.md](R2_README.md) for the all-336-character exact
characteristic factor and determinant audit, four repaired q=4 dictionary
files, closed-form determinant fields, and the refreshed leading/Laurent
checks. The R2 audit corrects the four malformed q=4 `reduced_blocks.A` fields
and the degree-of-field wording without changing the R1 evidence files.

This directory contains an explicit numerical dictionary for the **frozen flat
right-star collar**, plus independent high-precision evaluations of the
corresponding leading area constants.  Everything here is numerical evidence,
not an interval certificate and not a Lean theorem.  In particular, no scalar
 decoupling, seed projection, spectral gap, full-carrier normalization, or
`AreaSeedRightStar` proof is asserted.

## 1. Operator convention

For a character \((i_y,i_z)\), set \(N=4q\), \(s=q(10R+12)\), and
\(h=q(12R+12)\) (called `s` and `hi` in the files).  The 12 state components
are four transverse sublattice cells times three bond directions:

```text
cells = [(0,0),(1,0),(0,1),(1,1)]
order = [(cell,direction) for direction in [0,1,2] for cell in cells]
```

The exact-collar files use

\[
  K_-v_{x-1}+K_0v_x+K_+v_{x+1}=0,
  \qquad s+1\le x\le h-2.
\]

`blocks["-1"]`, `blocks["0"]`, and `blocks["1"]` are \(K_-,K_0,K_+\).
The `constant_row_comparisons` show the exceptional rows explicitly.  The
`interface_rows` retain the actual augmented system on \(s-4\le x\le s\) and on
\(x=h-1\), including physical bonds and both multiplier blocks.  The shared
`descriptors.json` maps every augmented column to its kind and physical layer.
The optional `solve` object contains the actual full-resolvent and augmented
null residuals; these are separate non-interval numerical checks, not proof of
exact vanishing.

Direction zero is then eliminated *exactly*.  The files call the resulting
8-component transverse blocks `A`, `B`, and `C`.  `detA=detC` is nonzero for
all checked dominant characters, so the 16-by-16 companion matrix is defined.
No invertibility is assumed for the unreduced 12-component block.

## 2. Exact coefficient fields

The JSON coefficient representation is a list of rational terms
\(\sum_k c_k\zeta_N^k\), where \(\zeta_N=e^{2\pi i/N}\).  The extraction uses
high-precision PSLQ only to identify the coefficients; the subsequent Schur
complements, determinants, transfer companion, characteristic polynomial, and
factor tests use exact rational arithmetic in \(\mathbf Q(\zeta_N)\).

- \(q=1\): \(\mathbf Q(\zeta_4)=\mathbf Q(i)\), so the matrices are explicit
  Gaussian-rational matrices.
- \(q=2\): \(\mathbf Q(\zeta_8)=\mathbf Q(i,\sqrt2)\).  Entries are exact in
  the real quadratic/cyclotomic representation; real and imaginary parts can
  be rewritten in \(\mathbf Q(\sqrt2)\).
- \(q=4\): \(\mathbf Q(\zeta_{16})\) is used explicitly.  It is a quartic
  cyclotomic field and is **not** contained in \(\mathbf Q(\sqrt2)\).  No
  \(\mathbf Q(\sqrt2)\)-only closed form is claimed.

There is no claim that the leading area constant itself is rational or in
\(\mathbf Q(\sqrt2)\).  The exact closed forms obtained here are the operator
matrices, their determinants, the characteristic polynomial, and the algebraic
rate.  The area amplitudes remain high-precision numerical values.

## 3. Characteristic factor and rate

`characteristic_q*_c*.json` computes the characteristic polynomial of the
16-by-16 transfer companion exactly.  For every one of the four slowest
characters at each \(q\), the factor residual is exactly zero for

\[
  (Q_5^2-a^2x^2)^2(Q_9^2-a^2x^2)^2,
  \quad Q_5=x^2-5x+1,\quad Q_9=x^2-9x+1,
  \quad a^2=2+\zeta_N+\zeta_N^{N-1}.
\]

Put \(y=5-\sqrt{a^2}\) and
\(\rho=(y-\sqrt{y^2-4})/2\).  The candidate area ratio per \(R\mapsto R+2\) is
\(\rho^{8q}\).  Numerically this is

- \(q=1\): \(y=5-\sqrt2\), ratio \(7.446438830808222444\times10^{-5}\);
- \(q=2\): \(y=5-\sqrt{2+\sqrt2}\), ratio
  \(7.234910171247043634\times10^{-8}\);
- \(q=4\): \(y=5-\sqrt{2+\sqrt{2+\sqrt2}}\), ratio
  \(2.447093793466790288\times10^{-14}\) (see `LEADING_SUMMARY.json` for the
  full-precision value).

The four characters used for the leading channel are
\((0,1),(0,N-1),(1,0),(N-1,0)\).  Their common factor is exact; the measured
ratios are independent numerical checks, not a proof of the rate.

## 4. Leading area and stability

`dominant_right_q*.json` contains independent flat solves at every even
\(R=18,20,\ldots,40\).  Define

\[
  A_R=\frac1{N^2}\sum_{c\in\{(0,1),(0,N-1),(1,0),(N-1,0)\}}
      \operatorname{areaSum}_c(R),
  \qquad K_R=A_R/\rho^{4qR}.
\]

This is only the dominant-character area, not the full top-row area.  The
`independent_checks` in `LEADING_SUMMARY.json` compare it with retained full
area runs.  They also show the subleading channels vanishing relative to the
leading one.

The direct normalized constants \(K_R\) are stable to the displayed numerical
precision.  At present the computed values include

- \(q=1\): \(K\approx 0.0133612068931633503479\), with
  \(|K_{40}/K_{18}-1|\approx 6.3\times10^{-22}\);
- \(q=2\): \(K\approx 0.0019184541381844317668645407795820\), with
  \(|K_{40}/K_{18}-1|\approx 8.9\times10^{-56}\);
- \(q=4\): \(K\approx 0.0001653700585858785228210904209427\), with
  \(|K_{40}/K_{18}-1|\approx 2.22\times10^{-57}\).

The q=1 direct residuals are at most \(1.32\times10^{-46}\); the largest
successive-rate discrepancy is \(7.35\times10^{-12}\).  The corresponding
q=2 bounds are \(6.15\times10^{-47}\) and \(2.95\times10^{-29}\).  The q=1,q=2
runs use 70-digit working precision; the q=4 drive uses 40 digits.  The q=4
absolute resolvent residual is \(8.24\times10^{-63}\), and its largest
successive-rate discrepancy is \(1.37\times10^{-56}\).  These residuals and
stability figures are evidence only.  In particular, they do not supply the
common finite seed, its nonzero projection, or a `RadiusDominantData` proof.

## 5. Failed same-row Laurent fit

`LAURENT_REVIEW.json` reproduces the original q=1 three-term fit at 170 digits.
The predicted and actual \(R=28\) values have relative errors approximately
\(8.77\times10^5\), \(8.77\times10^5\), and \(2.01\times10^6\), including sign
reversals.

The problem is the mode count, not a tiny roundoff in the fit.  The ansatz has
only the characteristic roots \(r,1,r^{-1}\), while the physical top row has
five distinct decaying character rates.  The omitted subleading modes shift
the fitted leading coefficient enough to cause catastrophic extrapolation.
An order-five recurrence with all five measured rates predicts the held-out
\(R=30,32,34\) data, with relative errors below \(4\times10^{-10}\) in the
reported tests.  This checks the explanation numerically; it does not prove an
exact recurrence or cofinal nonvanishing.

## 6. Files and reproduction

- `cyclotomic.py`: exact cyclotomic arithmetic and identification;
- `exact_collar.py`, `extract_all.py`: operator extraction;
- `characters/q1_R22`, `characters/q2_R20`, `characters/q4_R18`: all
  \(16+64+256=336\) exact per-character operator dictionaries and `INDEX.json`
  hashes;
- `characteristic.py`, `characteristic_q*_c*.json`: exact transfer polynomial
  and factor residuals;
- `dominant_sweep.py`, `dominant_right_q*.json`: direct dominant areas and
  residuals;
- `leading_summary.py`, `LEADING_SUMMARY.json`: rates, normalized constants,
  and independent full-area comparisons;
- `laurent_review.py`, `LAURENT_REVIEW.json`: the failed-fit reproduction;
- `audit_characters.py`, `CHARACTER_AUDIT.json`: all-character structural
  audit (currently passing).

Typical commands are

```sh
python3 AHP/round15/shared/numerics/extract_all.py --q 1 --R 22 \
  --dps 70 --out AHP/round15/shared/numerics/characters/q1_R22
python3 AHP/round15/shared/numerics/characteristic.py \
  --input AHP/round15/shared/numerics/characters/q1_R22/c0_1.json \
  --out AHP/round15/shared/numerics/characteristic_q1_c0_1.json
python3 AHP/round15/shared/numerics/dominant_sweep.py --q 1 --dps 70 \
  --drive AHP/round14/cancellation/r2/structure_right_q1_R22_p40.json \
  --reuse AHP/round15/numerics/r1/area_sweep_right_q1_R20_22_24_p50.json \
  --out AHP/round15/shared/numerics/dominant_right_q1.json
python3 AHP/round15/shared/numerics/leading_summary.py
python3 AHP/round15/shared/numerics/laurent_review.py
python3 AHP/round15/shared/numerics/audit_characters.py
```

`attach_residuals.py` and `compact_characters.py` respectively attach completed
residual records and deduplicate augmented descriptors.  All scripts use less
than 2 GiB per process.  No `lake build`, `REPRODUCE.sh`, or Lean declaration is
part of this numerical package.

## 7. What remains unproved

The exact remaining physical statement is still
`AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar` (or its cofinal
unit-dominant form).  This package does not prove the common finite-coordinate
identification, nonzero seed projection, normalized matrix limit, nonzero
charged area, same-generator identity, or full-carrier normalization needed by
that statement.  It also does not prove the original P3, CofinalP3, or
GoalNeg2.  A separate pre-existing q=4 sweep that used the q=2 drive is not
used as a physical q=4 crossing-generator certificate here; the q=4 leading
run is driven independently at q=4.
