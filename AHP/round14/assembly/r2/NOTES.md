# Round 14 assembly R2 — charged-line area join and held-out audits

## Verdict and audit boundary

**P3, CofinalP3, and GoalNeg2 remain open.** No track has published a physical
area-seed proof or a path-variant P1+P2+P3 proof. The new compiled result is a
strictly conditional integration of the R2 transfer and cancellation work: one
area-detected generator implies the *universal* mixed-colour area remainder,
directly at the level of `areaSum`. It is not a physical nonvanishing proof.

The required round-13 blueprint, GAPS, detection R1/R2 notes were read in full.
The round-14 transfer and cancellation R1/R2 NOTES were also read. Path-choice
R2 artifacts were inspected; its NOTES.md was not present when this report was
prepared, and no candidate-specific Lean certificate is available in its
published artifacts. The original right-star route therefore remains the only
assembled route.

## Compiled integration artifact

`AreaLine.lean` combines the final R2 `Collar.lean`, the final cancellation R2
charged-line declarations, and the new assembly join. It imports only frozen
`DrEquiv` and `ZXR2Flat6`, with no AHP module import. Local and published
sources are byte-identical and were compiled separately by

```sh
bb heavy run -- AHP/round3/lean1.sh AHP/round14/assembly/r2/AreaLine.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round14/shared/assembly/R2_AreaLine.lean
```

| File | Lines | Exit | Axiom records | Source SHA-256 |
|---|---:|---:|---:|---|
| `AHP/round14/assembly/r2/AreaLine.lean` | 5671 | 0 | 367 | `445296f28fa28e42994c9bb831f2aea9ca84c675548c9b7d6ffe16f5ddd8b8db` |
| `AHP/round14/shared/assembly/R2_AreaLine.lean` | 5671 | 0 | 367 | same |

Both logs have SHA-256
`acb027f10d8474fa1de9cdb312aa72d32092778b4ac388e63270453402463e58`.
They contain no warnings, errors, or `sorryAx`. `AUDIT.json` checks publication
identity, both zero exits, all 367 records per execution, the six new assembly
records, and absence of forbidden proof mechanisms. Every axiom record is a
subset of `{propext, Classical.choice, Quot.sound}`. There is no `sorry`,
`admit`, new `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or
`opaque`.

### New conditional theorems

The main new declaration is

```lean
theorem AdalyFormal.Round14.Assembly.areaNonvanishing_of_areaSeed
    (h : AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar) :
    AdalyFormal.Round14.Assembly.AreaNonvanishing
```

with permitted record at `AreaLine.lean.log:585`:

```text
'AdalyFormal.Round14.Assembly.areaNonvanishing_of_areaSeed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Its conclusion is exactly

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

The proof takes the generator and top row supplied by `AreaSeedRightStar`,
writes any other original `KernelLine` vector in the generator's charged real
span, and applies cancellation R2's exact
`areaSum_ne_zero_of_mem_charged_span`. Thus nonvanishing propagates with the
factor `a^2+b^2`; it does not depend on a common cell sign or on the numerical
response normalization.

Also compiled:

```lean
theorem areaNonvanishing_of_unitAreaSeed
    (h : AdalyFormal.Round14.Transfer.Physical.UnitAreaSeedRightStar) :
    AreaNonvanishing

theorem p3_of_areaNonvanishing (h : AreaNonvanishing) :
    AdalyFormal.Round13.Assembly.R1.P3

theorem p3_of_areaSeed_via_area
    (h : AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar) :
    AdalyFormal.Round13.Assembly.R1.P3

theorem p3_of_unitAreaSeed_via_area
    (h : AdalyFormal.Round14.Transfer.Physical.UnitAreaSeedRightStar) :
    AdalyFormal.Round13.Assembly.R1.P3
```

These are conditional reductions only. The unit norm is the full carrier norm,
not the nine-boundary-bond norm used by numerical Schur drives. No unconditional
`AreaSeedRightStar`, `AreaNonvanishing`, `P3`, `CofinalP3`, or `GoalNeg2`
inhabitant is included. Once a seed is supplied, the already independently
verified `AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3` applies unchanged;
the cofinal route uses `goalNeg2_of_cofinalP3`.

## Exact missing statements

### Original P3 — still unproved

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

### Preferred per-instance normalized seed — still unproved

`AdalyFormal.Round14.Transfer.Physical.UnitAreaSeedRightStar` is exactly:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧ ‖u‖ = 1 ∧
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

`unitAreaSeedRightStar_iff` proves this is equivalent to R1's
`AreaSeedRightStar`. Assembly's new theorem turns either form into the
universal area remainder above. The fixed value at one generator and one
physical top row is still not known to be nonzero.

### Preferred cofinal dominant seed — still unproved

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

where

```lean
RadiusDominantData observable q :=
  ∃ r K : ℝ, 0 < r ∧ K ≠ 0 ∧
    Tendsto (fun n => observable q (2*(n+9)) / r^n) atTop (𝓝 K)
```

The frozen right-star collar recurrence, the same-generator observable, and a
nonzero normalized limit are not identified. R1's exact Laurent seed and the
nested existential area seed remain open alternatives.

### Dominant-matrix physical identification — still unproved

Cancellation R2 proves sign preservation for a convergent normalized matrix,
but its physical leading model is missing. Its exact schematic remainder is:

```lean
∃ (r : ℝ) (K0 : ι → ι → ℝ) (z : ι → ℂ),
  0 < r ∧ 0 < chargedArea K0 z ∧
  Tendsto (fun n => (r^n)⁻¹ • K n) atTop (𝓝 K0)
```

One must additionally identify `K`, `K0`, and `z` with the actual aggregate
coefficients and crossing-generator coordinates, including a common finite
index type and all radius-dependent choices. `areaSum_eq_chargedArea` is only
the dictionary back to the genuine area. No such model or cofinal instance is
constructed.

## Independent held-out numerical audits

All numerical results are non-interval evidence only. Completed audit files are
`NUMERICS.json` and, for the final R2 claims, `HELD_OUT.json`; both audit scripts
exit zero. No numerical value is a Lean premise.

### Original right star q=1,R=32

This case was not used in cancellation R2's R=20,...,30 dominant-rate analysis.
All 16 Fourier characters were recomputed at 120 and 155 digits.

- The tangential physical top jets are positive, approximately
  `5.9702664573685409e-69` and `5.9702664573681616e-69` at 155 digits.
  Relative 120/155 discrepancies are `5.90e-105` and `6.24e-105`.
- At 155 digits, null/resolvent residuals relative to the tangential jet are
  approximately `1.25e-86` and `2.68e-83`. Charged-line scaling error is below
  `1e-100`, and peak RSS is below 2 GiB.
- The R=30→32 rate matches the R=28→30 rate within `1.26e-9` tangentially and
  `2.90e-9` in direction zero. This is consistent with cancellation's dominant
  numerical lead but supplies no exact rate, matrix limit, or nonzero leading
  coefficient.
- Cell/sum ratios are approximately `556891.70, 67575.896, 67575.897`, so a
  naive common-sign argument is unsupported. Doubling a physical aggregate is
  only the compiled numerical `areaSum` dictionary, not a nonzero Lean proof.

### Path-choice L3 candidate at q=2,R=30

The candidate `c2=-0.25,c3=-2.25` was independently replayed at 120 and 155
digits using the same double-precision Schur drive convention as path choice.
This instance was not used by path-choice R2.

- The last physical-row aggregate is positive,
  `4.7701350589925427e-112` at 155 digits, with 120/155 relative difference
  `1.44e-113`. The doubled value is numerical `areaSum` evidence only.
- `max |cell|/|sum| = 0.2966429803`, compared with `0.0410964394` at q=2,R=20.
  Thus the numerical lead survives but weakens with radius.
- The 155-digit resolvent residual/sum is `5.55e-40`; double/high aggregate
  agreement is about `1.60e-11` relative. Peak RSS is below 2 GiB.
- There are 31 negative and 33 positive cells, and no computed row has a common
  weak sign. The signed-row shortcut therefore remains unavailable. Sampled
  positive spectral diagnostics are not P1, P2, KernelLine, or detection proofs.

A separate original-star all-row profiling attempt at q=1,R=30 timed out after
row 96. Its `.exit` was absent when polled; it was not relaunched and no
conclusion uses the partial log. The completed independent R=30 and R=32
right-star runs and the completed L3 runs are unaffected.

## Scope and reproduction

```sh
python3 AHP/round14/assembly/r2/build.py --publish
bb heavy run -- AHP/round3/lean1.sh AHP/round14/assembly/r2/AreaLine.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round14/shared/assembly/R2_AreaLine.lean
python3 AHP/round14/assembly/r2/audit.py
python3 AHP/round14/assembly/r2/audit_numerics.py
python3 AHP/round14/assembly/r2/audit_held_out.py
```

Writes are confined to `AHP/round14/assembly/r2/` and
`AHP/round14/shared/assembly/`, plus the requested shared ledger
`AHP/round14/shared/GAPS.md`. No earlier round, frozen module, lakefile,
integration checkout, git commit, or push was changed. No `lake build` or
`REPRODUCE.sh` was run.
