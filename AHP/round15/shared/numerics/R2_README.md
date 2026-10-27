# Round-15 numerics R2 — exact factors, rates, and amplitude data

Everything in this package is **numerical evidence and exact arithmetic on the
numerically transcribed operator**, not a Lean identification or an interval
certificate. It does not prove `AreaSeedRightStar`, a cofinal dominant seed, P3,
or `GoalNeg2`.

## 1. Collar and interface convention

For \(N=4q\), \(s=q(10R+12)\), and \(h=q(12R+12)\), the retained R1 files in
`characters/q1_R22`, `characters/q2_R20`, and `characters/q4_R18` give the
12-component equations

\[
 K_-v_{x-1}+K_0v_x+K_+v_{x+1}=0,\qquad s+1\le x\le h-2.
\]

The state order is three bond directions times the four cells
`(0,0),(1,0),(0,1),(1,1)`. The `interface_rows` and shared `descriptors.json`
retain the augmented physical/multiplier equations at the star and `Omega_1`
interfaces. After exact direction-zero elimination, the eight-component
recurrence is \(C v_{x-1}+B v_x+A v_{x+1}=0\). R2 checks \(A=C\) exactly for all
336 characters.

**R1 packaging correction.** In the four dominant q=4 source files,
`reduced_blocks.A` is accidentally a numeric string. The exact 12-block data,
`B`, and `C` are intact. `R2_repaired/q4_R18/` contains separate repaired copies
obtained by recomputing the Schur reduction exactly; recomputed `B`,`C` match the
retained matrices and `A=C`. The R1 files are unchanged. Use these repaired
copies, or `R2_EXACT_FACTORS_q4.json`, for those four characters.

## 2. Universal exact characteristic factor and determinant

For a character \((i_y,i_z)\), define

\[
 a=2\cos(\pi i_y/N),\quad b=2\cos(\pi i_z/N),\quad
 X=a^2=2+\zeta^{i_y}+\zeta^{-i_y},\quad
 Z=b^2=2+\zeta^{i_z}+\zeta^{-i_z},
\]

where \(\zeta=e^{2\pi i/N}\). With \(L(t)=(t^2-7t+1)^2\), R2 verifies exactly

\[
 \chi_T(t)=\big((L(t)-(X+Z)t^2)^2-4XZt^4\big)^2
\]

for every one of the 336 reduced 16-by-16 companions. Equivalently, the four
reciprocal-pair traces \(7\pm a\pm b\) each occur with multiplicity two. There
are 9, 25, and 81 distinct \((X,Z)\) classes at q=1,2,4; the explicit polynomials
are in `R2_EXACT_FACTORS_q*.json`.

The same exact audit gives

\[
 \boxed{\det(A)^{-1}=(25-X-Z)^2-4XZ},\qquad A=C.
\]

Thus every transcribed reduced `A` is invertible and the displayed companion is
defined. This is not a spectral-gap or physical-seed assertion.

For the dominant character, the determinant inverse has the closed forms

- q=1: \(329\), so \(\det A=1/329\);
- q=2: \(331-54\sqrt2\), so
  \(\det A=(331+54\sqrt2)/103729\);
- q=4: with \(u=\sqrt{2+\sqrt2}\),
  \(329+u^2-54u=331+\sqrt2-54u\).

Consequently the q=4 dominant determinant is **not** in \(\mathbf Q(\sqrt2)\).
More generally, q=1 entries are Gaussian rational, q=2 entries lie in
\(\mathbf Q(i,\sqrt2)\), and q=4 entries lie in \(\mathbf Q(\zeta_{16})\).
Correction to R1 wording: \(\mathbf Q(\zeta_{16})\) has degree **8** over
\(\mathbf Q\); its maximal real subfield \(\mathbf Q(u)\) has degree 4.
`R2_CLOSED_FORM.json` includes exact determinant forms for all 115 classes.

## 3. Rates and leading constants

For nonuniform characters put \(s=7-|a|-|b|\); the small root is
\(\rho=(s-\sqrt{s^2-4})/2\), and the area rate per \(R\mapsto R+2\) is
\(\rho^{8q}\). At \((0,0)\), the retained charged-area data suppress the `y=3`
channel, so the first surviving channel uses `s=7`. These formulas are exact for
the transcribed companion; their use as the physical area rate remains numerical
evidence.

`R2_LEADING_STABILITY.json` recomputes every even R=18,...,40 normalization from
the retained direct flat solves. It uses four dominant characters and
\(K_R=A_R/\rho^{4qR}\). The R=40 values and R=18-to-R=40 relative changes are

```text
q=1  K=0.013361206893163350347922853212791184761977075727611479605501179451
     change=-6.300029267408676870e-22
q=2  K=0.0019184541381844317668645407795820411190356630723843760966048050193
     change=-8.861857111196134064e-56
q=4  K=0.00016537005858587852282109042094267766531758433271716630894373698531
     change=+2.224615148725537086e-57
```

The rate normalization is evaluated at 170 working digits, but the reused areas
have their original finite precision; this is not a claim of 170-digit accuracy.
The maximum absolute flat-resolvent residuals in the leading sweeps are
\(1.32\times10^{-46}\), \(6.15\times10^{-47}\), and \(8.24\times10^{-63}\),
respectively. No exact amplitude closed form is established. Bounded PSLQ
searches over \((1,\sqrt2,K)\) found no relation with coefficients up to \(10^9\)
at tolerance \(10^{-45}\); this is **not** a nonexistence proof. The amplitude
still involves the interface problem, crossing drive, mode projection, and
quadratic dressed-jet observable, not just the exact determinant/rate.

## 4. Why the same-row Laurent fit failed

`R2_LAURENT_REVIEW.json` reproduces the q=1 fit at 170 working digits. Fitting
the three-term ansatz on R=20,22,24,26 and testing R=28 gives relative errors
\(2.0091\times10^6\), \(8.7716\times10^5\), and \(8.7673\times10^5\) in
 directions 0,1,2, all with sign reversals. The assumed roots `r,1,r^-1` are
wrong: five slow decaying character channels are visible. A small
\(4.78\times10^{-7}\) mismatch in the fitted recurrence coefficient is amplified
by cancellation during extrapolation.

A five-slowest-rate model fitted on R=20,...,28 predicts R=30,32,34; its
 tangential errors are below \(5.2\times10^{-30}\). Its full-area leading
constant agrees with the independent four-dominant-character value to
\(5.28\times10^{-21}\) relative difference. The exact companion has further
branches, so this is still not an exact order-five Laurent certificate.

## 5. Reproduction and audit

```sh
python3 AHP/round15/numerics/r2/exact_factors.py --q 1 \
  --out AHP/round15/shared/numerics/R2_EXACT_FACTORS_q1.json
python3 AHP/round15/numerics/r2/exact_factors.py --q 2 \
  --out AHP/round15/shared/numerics/R2_EXACT_FACTORS_q2.json
python3 AHP/round15/numerics/r2/exact_factors.py --q 4 \
  --out AHP/round15/shared/numerics/R2_EXACT_FACTORS_q4.json
python3 AHP/round15/numerics/r2/repair_q4.py
python3 AHP/round15/numerics/r2/closed_form.py
python3 AHP/round15/numerics/r2/laurent_r2.py
python3 AHP/round15/numerics/r2/leading_r2.py
python3 AHP/round15/numerics/r2/audit.py
```

`R2_AUDIT.json` and `numerics/r2/AUDIT.json` are byte-identical and pass. The
scripts use less than 2 GiB each. No Lean compilation, `lake build`,
`REPRODUCE.sh`, commit, or push is part of this package.
