# Round 14 transfer R2 — two-layer coefficients and dominant collar data

## Verdict and audit boundary

**P3, CofinalP3, and GoalNeg2 remain open.** This round does not derive the
frozen right-star flat recurrence and does not prove a nonzero physical area
seed. It supplies two compiled refinements of the R1 transfer interface:

1. an exact two-layer quadratic transfer calculation with explicit leading,
   mixed, and growing coefficients; and
2. a dominant normalized-limit certificate which permits an arbitrary
   remainder instead of requiring an exact three-term Laurent identity.

A crossing generator can also be normalized to unit **full-carrier** norm
without changing the original `KernelLine` or destroying area nonvanishing.
The numerical nine-boundary-bond norm used by the probes is not this norm.
All implications below remain conditional on their displayed physical input.

## Compiled artifacts

| Local file | Reusable publication | Lines | Exit local/shared | Total axiom records | New R2 records |
|---|---|---:|---:|---:|---:|
| `AHP/round14/transfer/r2/Collar.lean` | `AHP/round14/shared/transfer/R2_Collar.lean` | 5357 | 0 / 0 | 347 | 30 |

The sources are byte-identical and were compiled separately through
`bb heavy run -- AHP/round3/lean1.sh <file>`. Both logs are clean: no warnings,
errors, or `sorryAx`. Every record is a subset of
`{propext, Classical.choice, Quot.sound}`. No `sorry`, `admit`, new axiom,
`native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque` occurs.
The only frozen imports are `DrEquiv` and `ZXR2Flat6`; no AHP file is imported
as a Lean module. `audit.py` checks these facts and writes `AUDIT.json`.

- Source SHA-256:
  `f0ebf914cfed386bc7432f906c41d189b0df7d77f552832c8f35b6ca425189da`
- Each final log SHA-256:
  `72f802dd5b6b24cbe2f72a979e6f74b15f56e295f2ca8f561d598003d5d92870`

These are builder and separate-publication executions, not independent
mathematical review.

## 1. Exact two-layer quadratic transfer

Namespace `AdalyFormal.Round14.Transfer`, source lines 5127–5165.

For
\[
  x_n=a r^n+b(r^{-1})^n,
\]
the fixed adjacent-layer quadratic observation is

```lean
q00 * x_n^2 + q01 * x_n * x_(n+1) + q11 * x_(n+1)^2.
```

`twoLayerQuadratic_eq_laurent` proves that it is exactly
`laurent (r^2) A B C n`, where

```lean
A = a^2 * (q00 + q01*r + q11*r^2)
B = a*b * (2*q00 + q01*(r+r⁻¹) + 2*q11)
C = b^2 * (q00 + q01*r⁻¹ + q11*(r⁻¹)^2)
```

These are `twoLayerDecay`, `twoLayerMixed`, and `twoLayerGrow`. Thus a fixed
quadratic functional of the two-layer seed has an explicit leading constant;
there is no common-sign assumption. The use of `r^2` on the Laurent side is
essential: the linear transfer branches are `r` and `r⁻¹`, so the quadratic
branches are `r^2` and `(r^2)⁻¹`.

`twoLayerQuadratic_eventually_ne_zero` proves that if `0 < r < 1` and any one
of those three explicit seed coefficients is nonzero, the observation is
nonzero at every sufficiently large layer. The accepted record is
`Collar.lean.log:514`, exactly `[propext, Classical.choice, Quot.sound]`.
This is scalar transfer algebra, not yet a dictionary for the frozen carrier
or the physical `areaSum`.

## 2. Dominant data allow an arbitrary remainder

`RadiusDominantData` (:5179) is the compiled proposition

```lean
def RadiusDominantData (observable : ℕ → ℕ → ℝ) (q : ℕ) : Prop :=
  ∃ r K : ℝ, 0 < r ∧ K ≠ 0 ∧
    Tendsto (fun n => observable q (2*(n+9)) / r^n) atTop (𝓝 K)
```

It asks for one nonzero normalized limit, not an exact finite Laurent
recurrence. Positive `r` may be below or above one, covering either orientation
of a leading branch. `dominant_cofinal_index` and
`radius_cofinal_nonzero_of_dominant` extract cofinal nonzero observations.

`radiusDominantData_of_laurent` (:5186) proves every R1
`RadiusLaurentData` certificate yields `RadiusDominantData`. The proof selects
the growing inverse, constant, or decaying normalization according to which
Laurent coefficient is nonzero. Hence the new interface genuinely subsumes R1
while allowing subleading modes and other remainder terms.

`dominantAreaSeed_of_laurent` (:5299) lifts this to the physical seed
interface, and the main conditional theorem is

```lean
theorem cofinalP3_of_dominantAreaSeed (h : CofinalDominantAreaSeed) :
    AdalyFormal.Round13.Assembly.R2.CofinalP3
```

with permitted record at `Collar.lean.log:555`. No inhabitant of
`CofinalDominantAreaSeed` is supplied.

## 3. Unit-full-norm generators and exact area scaling

`areaSum_smul` (:4987) proves for the genuine physical area sum

```lean
areaSum hq hj (c • u) = c^2 * areaSum hq hj u
```

and `areaSum_smul_ne_zero` preserves nonvanishing when `c ≠ 0`.
`kernelLine_smul` proves that the original `KernelLine` is also preserved by
nonzero real scaling. With `normalize u = ‖u‖⁻¹ • u`, this gives a unit
representative on the same charged line.

The per-instance normalized seed is **equivalent** to R1's seed:

```lean
theorem unitAreaSeedRightStar_iff : UnitAreaSeedRightStar ↔ AreaSeedRightStar
```

and the nested versions are likewise equivalent by
`cofinalUnitAreaSeedRightStar_iff`. Consequently

```lean
theorem p3_of_unitAreaSeed (h : UnitAreaSeedRightStar) :
    AdalyFormal.Round13.Assembly.R1.P3

theorem cofinalP3_of_unitAreaSeed (h : CofinalUnitAreaSeedRightStar) :
    AdalyFormal.Round13.Assembly.R2.CofinalP3

theorem cofinalP3_of_unitDominantAreaSeed (h : CofinalUnitDominantAreaSeed) :
    AdalyFormal.Round13.Assembly.R2.CofinalP3
```

compile with only the standard permitted axioms. They are conditional
reductions, not physical P3 proofs.

## 4. Exact remaining statements

### Preferred per-instance normalized seed — still unproved

`UnitAreaSeedRightStar` is exactly:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧ ‖u‖ = 1 ∧
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

By the compiled equivalence, proving this is equivalent to proving R1's
`AreaSeedRightStar`, and it yields the original P3.

### Preferred cofinal transfer certificate — still unproved

`CofinalUnitDominantAreaSeed` is exactly:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∃ observable : ℕ → ℕ → ℝ,
  RadiusDominantData observable (2^j) ∧
  ∀ n : ℕ, ∃ u : TwistSpace (2^j) (2*(n+9)),
    KernelLine (2^j) (2*(n+9)) (rightStar (by positivity) (2*(n+9))) u ∧
    ‖u‖ = 1 ∧
    ∃ k : ℕ, ∃ hk : k < blockCount (2^j) (2*(n+9)),
      areaSum (by positivity : 0 < 2^j) hk u = observable (2^j) (2*(n+9))
```

This yields `CofinalP3`, then the already verified
`goalNeg2_of_cofinalP3`. The unproved physical work is to identify the frozen
right-star flat-collar recurrence and a same-generator top-row `areaSum` with
such an observable, and to prove the normalized limit nonzero from an explicit
two-layer seed. The scalar formulas in Section 1 do not supply those physical
identities.

R1's exact `CofinalLaurentAreaSeed` and the nested unit area seed also remain
unproved alternatives.

### Original P3 — unchanged and still unproved

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

No unconditional `P3`, `CofinalP3`, `AreaSeedRightStar`,
`UnitAreaSeedRightStar`, `CofinalUnitAreaSeedRightStar`,
`CofinalDominantAreaSeed`, `CofinalUnitDominantAreaSeed`, or `GoalNeg2`
inhabitant is included.

## 5. Numerical evidence boundary

No new numerical solve was run. R1's retained right-star samples and its
held-out failure of the natural same-row three-term Laurent fit remain
non-interval evidence only. That failed fit is a reason not to assert the exact
ansatz, not a counterexample to P3 or to the more general dominant certificate.
Mixed cell signs and large cancellation ratios are unchanged; no common-sign
or definite-Hermitian argument is claimed here.

## Reproduction and scope

```sh
bb heavy run -- AHP/round3/lean1.sh AHP/round14/transfer/r2/Collar.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round14/shared/transfer/R2_Collar.lean
python3 AHP/round14/transfer/r2/audit.py
```

Only `AHP/round14/transfer/r2/` and
`AHP/round14/shared/transfer/R2_Collar.lean{,.log,.exit}` were written.
Earlier rounds, frozen modules, the lakefile, the integration checkout, and the
shared assembly ledger were not edited. No `lake build`, `REPRODUCE.sh`, large
historical join, numerical solve, deletion, git commit, or push was performed.
