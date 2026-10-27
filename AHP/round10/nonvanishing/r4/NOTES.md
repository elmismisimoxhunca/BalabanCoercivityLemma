# Nonvanishing round 4 — finite polynomial certificates for a moving crossing

## Decision

**GoalNeg2 is NOT proved. No original round-9 cofinal coupling premise is proved.**

This final round proves an abstract finite-certificate alternative for the transfer/recurrence route, and an exact obstruction to treating one nonzero algebraic sample as a transport theorem. The new certificate has **not** been constructed for the frozen operators. The earlier physical result `TopJetDetected -> CurlDetected` remains conditional on crossing-jet detection; this round does not discharge that condition.

Published: `AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean` (306 lines). It and the three local compact files compile independently through the required wrapper, with exit 0, no diagnostics, and only `propext`, `Classical.choice`, `Quot.sound`. All 29 declarations have individual dependency records; `CHECKS.json` passes.

## 1. Why this route

A flat-collar recurrence for a vector is not a recurrence for the scalar coupling evaluated at a radius-dependent crossing. The crossing angle, the normalized kernel, and inverse-based quantities all vary with the volume. Round 1 already supplied correct cofinality theorems **if** the scalar has a reversible recurrence or a fixed finite-dimensional transfer representation. Those hypotheses remain unproved for the actual coupling.

This round permits the crossing root to vary arbitrarily with scale and radius. It replaces a scalar recurrence with a finite polynomial identity that excludes common zeros of a crossing polynomial and a coupling numerator. Thus it addresses the moving-root problem rather than silently ignoring it. It is still a sufficient criterion, not its application to the actual operators.

No source-column inversion, source domination, canonical q=1 dilation, or single-character/full-kernel identification is assumed to have been established. R3's free-profile energy identity already bypasses the source-column problem when a genuine nonzero physical jet is available.

## 2. Nested geometric grid nonvanishing

Let P(X,Y) be a nonzero real bivariate polynomial. Write it as a polynomial in Y with polynomial coefficients in X. Fix 0 < rho < 1. Then:

1. Choose a nonzero coefficient p_i(X). It has finitely many roots.
2. The values X_j = rho^(2^j) are distinct. Hence for all sufficiently large j, P(X_j,Y) is a nonzero polynomial in Y.
3. For each such fixed j, the values Y_(j,R) = rho^((2^j)*R) are distinct. Hence P(X_j,Y_(j,R)) is nonzero for all sufficiently large R.

The thresholds are **nested**: there is J such that for every j >= J there is N_j such that every R >= N_j works. There is no asserted radius bound uniform in j. Restricting to even R >= 18 gives exactly the requested cofinal ordering.

One exact evaluation P(x0,y0) != 0 proves P != 0. The seed need not lie on the physical grid, because it certifies a polynomial identity rather than a numerical asymptotic approximation.

Main compiled statements, namespace `AdalyFormal.Round10.Nonvanishing.PolynomialGrid`:

```lean
theorem geometric_grid_ne_zero_eventually (p : ℝ[X][X]) (hp : p ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∃ N : ℕ, ∀ R : ℕ, N ≤ R →
      evalTwo p (ρ ^ (2 ^ j)) (ρ ^ ((2 ^ j) * R)) ≠ 0

theorem geometric_grid_ne_zero_of_seed (p : ℝ[X][X]) (x₀ y₀ : ℝ)
    (hseed : evalTwo p x₀ y₀ ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      evalTwo p (ρ ^ (2 ^ j)) (ρ ^ ((2 ^ j) * R)) ≠ 0
```

`evalTwo p x y` is the ordinary exact evaluation P(x,y), implemented by first mapping the coefficient polynomials through evaluation at x and then evaluating at y. The preceding abstract `grid_ne_zero_eventually` accepts any injective scale sequence and, for each scale, any injective radius sequence over a field. It therefore also supports convenient injective arithmetic subfamilies without repeating the root argument.

## 3. Moving crossing roots: the finite Bezout certificate

Let A(X,Y,T) describe a selected crossing equation and B(X,Y,T) a cleared coupling numerator. Suppose fixed polynomials U,V,P satisfy

    U*A + V*B = P(X,Y).

At any (x,y,t) where A(x,y,t)=0 and P(x,y)!=0, necessarily B(x,y,t)!=0. No continuity, sign, simplicity, or fixed value of t is needed for this algebraic implication. If

    denominator * coupling = B(x,y,t),

then the coupling is nonzero too. The cleared-product formulation does not need a separate denominator assumption for this implication: if the coupling vanished, the product would vanish. Obtaining this identity from an inverse-based formula still requires legitimate handling of its denominators. The separate theorem `quotient_cofinal_nonzero` explicitly assumes nonzero denominators when supplied an actual quotient formula.

A polynomial resultant computation could produce such a Bezout identity after clearing coefficient denominators. **No resultant or Bezout identity for the actual carrier/coupling is computed or proved here.** Nor is an exact nonzero coupling sample automatically a nonzero seed for P; section 4 proves that this distinction matters.

The exact compiled interface is:

```lean
structure MovingRootCertificate (coupling : ℕ → ℕ → ℝ) where
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  A : (ℝ[X][X])[X]
  B : (ℝ[X][X])[X]
  U : (ℝ[X][X])[X]
  V : (ℝ[X][X])[X]
  P : ℝ[X][X]
  bezout : U * A + V * B = Polynomial.C P
  seedX : ℝ
  seedY : ℝ
  seed : evalTwo P seedX seedY ≠ 0
  crossing : ℕ → ℕ → ℝ
  denominator : ℕ → ℕ → ℝ
  root : ∀ j R : ℕ, 2 ∣ R → 18 ≤ R →
    evalThree A (rho ^ (2 ^ j)) (rho ^ ((2 ^ j) * R)) (crossing j R) = 0
  numerator : ∀ j R : ℕ, 2 ∣ R → 18 ≤ R →
    denominator j R * coupling (2 ^ j) R =
      evalThree B (rho ^ (2 ^ j)) (rho ^ ((2 ^ j) * R)) (crossing j R)

theorem moving_root_cofinal_nonzero (coupling : ℕ → ℕ → ℝ)
    (d : MovingRootCertificate coupling) :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ coupling (2 ^ j) R ≠ 0
```

This certificate is intentionally separate from the actual block reduction. It has not been supplied for any frozen crossing coupling. In particular, a numerical exponential fit does not establish `root`, `numerator`, or `bezout`.

Limitations of this sufficient form:

- It requires one fixed finite collection of coefficient polynomials and one fixed rho. Several independent transfer roots, Jordan factors, a varying Bloch phase, or general matrix-transfer entries need a genuinely more general representation theorem; they are not implicitly encoded here.
- The chosen polynomial A must be appropriate to the relevant branch. A full characteristic polynomial may have a factor sharing roots with B in irrelevant sectors, in which case this global common-root exclusion is too strong. Factor selection must itself be justified.
- Scalar nonvanishing still does not establish definiteness on an unexamined multidimensional kernel.

## 4. Exact obstruction: one nonzero sample is not a coprimality certificate

The compact file proves the following counterexample, **not about the frozen operators**:

    A(T)=T(T-1), B(T)=T.

At T=1, A=0 and B=1. At T=0, both vanish. Every identity U*A+V*B=P(X,Y) therefore has P(x,y)=0 for every x,y (`sample_no_nonzero_bezout`). A nonzero sample of B at one root says nothing about common roots elsewhere.

Select the exact root

    t(q,R)=1 if (q,R)=(2,18), and 0 otherwise.

Every selected point is a root of the same polynomial A, and the exact rational coupling sample at the dyadic/even point (2,18) is 1. Nevertheless the numerator is identically zero for every R >= 19, at every q. `switchingRoot_not_cofinal` proves failure of the required nested cofinal conclusion.

This refutes only the shortcut “an algebraic crossing equation plus one exact nonzero sample implies cofinal nonvanishing.” It does **not** refute the actual cofinal coupling premise, actual analytic branch-control arguments, or the possibility of a correct transfer/resultant proof. A recurrence, suitable branch control, or a nonzero common-root-exclusion certificate still has to be supplied.

## 5. Exactly what remains for GoalNeg2

No actual crossing jet or coupling is proved nonzero in this round. The actual endpoint is still, for example:

```lean
AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyProfileCoupling
```

whose exact original content is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
    QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R)
      (corrDeriv (2^j) R f)
```

On the already-compiled R3 free-profile route, the exact per-vector remaining predicate is:

```lean
def TopJetDetected {q : ℕ} (hq : 0 < q) (R : ℕ)
    (u : ↥(bondSupp (G q R))) : Prop :=
  ∃ j : ℕ, ∃ hj : j < blockCount q R,
    jetAggregate hq hj neutralFunctional
      (Wop (G q R) flatCfg 1 (iE (G q R) u)) ≠ 0
```

This must hold for a genuine crossing generator, with the entire crossing kernel contained in its charged complex line or another common-profile definiteness argument. These must be established at nested cofinal scales and radii. R3's physical Q/flux theorem and dictionary energy identity propagate this condition; they do not generate it.

On this round's alternative route, the new exact missing input is `MovingRootCertificate coupling`, with `coupling` **proved to be the actual selected crossing quadratic form**, together with the entire-kernel argument. We have neither that certificate nor the identification. The elementary seed counterexample explains why the current finite numerical/nonzero samples cannot supply it by themselves.

Dictionary R4 subsequently compiled `dictionary/r4/Actual.lean` (2185 lines). I inspected its actual final construction, recorded exit 0, absence of diagnostics, and the standard-axiom record for `Dictionary.ColorObstruction.exists_charged_invisible`. For every q>0 and every R it constructs a genuine nonzero charged carrier field with `vacJet q R u = 0` and `∀ f, profileCoupling q R f u = 0`. It is **not a crossing field**. Thus nonzero-plus-charged is insufficient even for the actual frozen operators, not only for abstract quadratic models. This independently owned result strengthens the caution, but does not refute the requested crossing premise. I did not modify or independently recompile that dictionary file.

A concrete top-block charged C2 stencil plus the actual crossing amplitude relations would still be needed for a local phase/sign argument. None is inferred from a nonzero linear recurrence solution. No mathematical obstruction disproving the actual requested premise was found.

## 6. Files and verification

| File | Lines | Declarations | Wrapper exit |
|---|---:|---:|---:|
| `PolynomialGrid.lean` | 114 | 10 | 0 |
| `MovingRoot.lean` | 224 | 18 | 0 |
| `SeedObstruction.lean` | 306 | 29 | 0 |
| `shared/nonvanishing/R4_PolynomialCertificate.lean` | 306 | 29 | 0 |

The shared file is byte-identical to `SeedObstruction.lean` and independently compiled. `audit.py` checks every declaration, all raw dependency records, imports, prohibited-device absence, no diagnostics, source/log/exit freshness, and exact assembly/publication byte identities. It explicitly records actual goal, actual cofinal premise, actual polynomial certificate, actual crossing jet, and whole-kernel definiteness as **not proved**.

Reproduction commands (no historical concatenation):

```sh
python3 AHP/round10/nonvanishing/r4/build.py
AHP/round3/lean1.sh AHP/round10/nonvanishing/r4/PolynomialGrid.lean
AHP/round3/lean1.sh AHP/round10/nonvanishing/r4/MovingRoot.lean
AHP/round3/lean1.sh AHP/round10/nonvanishing/r4/SeedObstruction.lean
AHP/round3/lean1.sh AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean
python3 AHP/round10/nonvanishing/r4/audit.py
```

The first `PolynomialGrid.lean` development compilation failed because recursive `ext` descended through both polynomial variables; it was repaired with one explicit `Polynomial.ext`. A deprecated tactic warning was also removed. All final logs are fresh and clean. No compiler timed out or was relaunched while pending. A cross-track BB messaging command timed out once; this was not a compilation, and later separately delivered status messages succeeded.

No numerical solve was run, and no numerical evidence is used as a proof step. No large assembly, lake build, REPRODUCE, protected-source edit, earlier-round edit, commit, push, worktree operation, or removal was performed. Authored deliverables are confined to this track's r4 directory and its own new shared nonvanishing files.
