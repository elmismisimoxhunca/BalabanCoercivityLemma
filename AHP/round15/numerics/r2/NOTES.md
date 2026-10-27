# Round-15 numerics R2 — all-character exact factors and leading data

## Verdict and evidence boundary

This round introduces **no Lean declaration** and proves no physical area seed.
It supplies exact rational/cyclotomic arithmetic on the retained numerical
operator dictionaries, together with non-interval high-precision area evidence.
`AreaSeedRightStar`, `CofinalUnitDominantAreaSeed`, P3, CofinalP3, and
`GoalNeg2` remain open. No conditional statement is called an unconditional
proof.

The reusable entry point is `AHP/round15/shared/numerics/R2_README.md`. The final
`AUDIT.json` and shared `R2_AUDIT.json` are byte-identical; `audit.exit=0`.

## 1. Exact per-character recurrence and the universal factor

R1's 12-component flat-collar equations and augmented interface rows are
retained for all 336 characters. R2 checks the reduced eight-component identity
\(A=C\) exactly and verifies, for every reduced 16-by-16 companion,

\[
 \chi_T(t)=\big((L(t)-(X+Z)t^2)^2-4XZt^4\big)^2,
 \qquad L(t)=(t^2-7t+1)^2.
\]

Here \(X=2+\zeta^{i_y}+\zeta^{-i_y}\) and
\(Z=2+\zeta^{i_z}+\zeta^{-i_z}\). Equivalently the four traces
\(7\pm a\pm b\), with \(a^2=X,b^2=Z\), each occur with multiplicity two. All
characteristic-factor residuals are exactly zero: 16 at q=1, 64 at q=2, and 256
at q=4. The 9+25+81 distinct exact polynomials and per-character source hashes
are published in `R2_EXACT_FACTORS_q*.json`. All twelve R1 dominant
characteristic polynomials match the new computation byte-for-byte after
canonical JSON hashing.

The exact determinant identity is

\[
 \det(A)^{-1}=(25-X-Z)^2-4XZ.
\]

It is checked by exact multiplication for every character, as are `detA=detC`
and `A=C`. This makes the transcribed companions well-defined without assuming
invertibility of the unreduced 12-component block. It does not prove a physical
spectral gap or a nonzero mode projection.

### R1 q=4 packaging defect and repair

The four R1 dominant q=4 files `(0,1),(0,15),(1,0),(15,0)` contain a numeric
string in `reduced_blocks.A`, not an exact 8-by-8 matrix. R1's structural audit
did not check the reduced matrix shapes, so its pass did not detect this. R2
recomputes `A,B,C` from the intact exact 12-block matrices using the original
Schur formula. Recomputed `B,C` equal the retained matrices exactly and `A=C`.
Four separate repaired dictionaries and hashes are published under
`shared/numerics/R2_repaired/q4_R18/`; the R1 files are unchanged. The final
audit explicitly checks this repair.

## 2. Closed-form determinant fields; amplitude remains open

For the dominant character, exact determinant inverses are

- q=1: \(329\);
- q=2: \(331-54\sqrt2\);
- q=4: \(331+\sqrt2-54\sqrt{2+\sqrt2}\).

Thus q=1 determinant data are rational and q=2 real determinant data have an
explicit \(\mathbf Q(\sqrt2)\) form. The q=4 dominant determinant is not in
\(\mathbf Q(\sqrt2)\): with \(u=\sqrt{2+\sqrt2}\), its inverse is
\(329+u^2-54u\), and membership in \(\mathbf Q(\sqrt2)\) would force the
degree-four number \(u\) into that quadratic field. `R2_CLOSED_FORM.json`
contains all 115 distinct determinant records.

This also corrects R1's field wording: \(\mathbf Q(\zeta_{16})\) has degree 8
over \(\mathbf Q\), while its maximal real subfield has degree 4.

No exact rational or \(\mathbf Q(\sqrt2)\) closed form for the **leading area
amplitude** is established. Bounded PSLQ searches over \((1,\sqrt2,K)\), with
coefficient bound \(10^9\) and tolerance \(10^{-45}\), returned no relation at
q=1,2,4. That is not a nonexistence proof. The exact determinant and rate do
not determine the amplitude: the star/`Omega_1` interface, crossing drive,
seed projection, and dressed-jet quadratic form are still required.

## 3. Leading constants and R=18,...,40 stability

`R2_LEADING_STABILITY.json` recomputes all 36 radius/scale normalizations from
the retained direct four-dominant-character solves. With rate \(\rho^{8q}\) per
two radius units and \(K_R=A_R/\rho^{4qR}\), the R=40 constants are

- q=1: `0.013361206893163350347922853212791184761977075727611479605501179451`;
- q=2: `0.0019184541381844317668645407795820411190356630723843760966048050193`;
- q=4: `0.00016537005858587852282109042094267766531758433271716630894373698531`.

The R=18-to-R=40 relative changes are respectively
\(-6.30003\times10^{-22}\), \(-8.86186\times10^{-56}\), and
\(2.22462\times10^{-57}\). The maximum flat-resolvent absolute residuals in the
leading sweeps are \(1.32\times10^{-46}\), \(6.15\times10^{-47}\), and
\(8.24\times10^{-63}\). The normalization was evaluated at 170 working digits,
but reused areas retain their original finite precision; no 170-digit accuracy
or interval claim is made.

## 4. Laurent failure reproduced and explained

`R2_LAURENT_REVIEW.json` reproduces the original q=1 three-term fit. Held-out
R=28 relative errors are \(2.0091\times10^6\), \(8.7716\times10^5\), and
\(8.7673\times10^5\), with sign reversals in all three directions. The ansatz
has the wrong roots `r,1,r^-1`; five slow decaying character channels are
visible. A tangential recurrence-coefficient mismatch of only
\(4.78\times10^{-7}\) is amplified by extrapolation cancellation.

The five-slowest-rate model fitted through R=28 predicts R=30,32,34 with
 tangential errors below \(5.2\times10^{-30}\). Its full-area leading constant
and the independent four-dominant-character constant differ by only
\(5.28\times10^{-21}\) relatively. The exact companion has further branches,
so this remains a numerical model, not an exact finite Laurent certificate or a
normalized-limit proof.

## 5. Exact Lean statements still missing

The per-instance target remains

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

This is `AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar`; no inhabitant
is supplied. The preferred cofinal normalized alternative remains

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∃ observable : ℕ → ℕ → ℝ,
  RadiusDominantData observable (2^j) ∧
  ∀ n : ℕ, ∃ u : TwistSpace (2^j) (2*(n+9)),
    KernelLine (2^j) (2*(n+9)) (rightStar (by positivity) (2*(n+9))) u ∧
    ‖u‖ = 1 ∧
    ∃ k : ℕ, ∃ hk : k < blockCount (2^j) (2*(n+9)),
      areaSum (by positivity : 0 < 2^j) hk u = observable (2^j) (2*(n+9))
```

No common finite charged seed, nonzero seed projection, normalized matrix
limit, nonzero `chargedArea K0 z`, same-generator identity, or full-carrier
normalization is proved. The exact arithmetic here is on numerically
transcribed matrices, not yet a Lean dictionary for the frozen physical
operator.

## 6. Reproduction and scope

The complete command sequence is in `shared/numerics/R2_README.md`. Successful
local records are `exact_factors_q{1,2,4}.{log,exit}`, `repair_q4.{log,exit}`,
`closed_form.{log,exit}`, `laurent_r2.{log,exit}`, `leading_r2.{log,exit}`, and
`audit.{log,exit}`; every `.exit` is zero. Each Python process used less than
2 GiB. No Lean compilation was needed or run. No `lake build`, `REPRODUCE.sh`,
earlier-round edit, integration-checkout edit, git commit, or push was made.
