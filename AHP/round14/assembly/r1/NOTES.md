# Round 14 assembly R1 — area bridges and held-out numerical audit

## Verdict

**P3, CofinalP3, and GoalNeg2 remain open.** This round compiles conditional
area-to-detection interfaces and independently tests the numerical nonvanishing
evidence on new radii. It supplies no physical area-seed proof and calls no
conditional result a proof of the pinned goal.

The required round-13 blueprint/GAPS/detection notes were read in full before
work. The round-14 transfer, cancellation, and path-choice NOTES were also
read. In particular, transfer's `p3_of_areaSeed` is sharper than the direct
universal area bridge below: one detected generator at each instance already
proves the universal original P3 by the round-12 charged-line response theorem.
Path choice found no easier detected path or candidate-specific P1/P2/kernel
certificate, so there is no path-variant join to assemble in this round.

## Compiled integration artifact

`AreaP3.lean` is a compact standalone join of the round-13 physical-area file,
the minimal right-star definitions, and the original P3/CofinalP3 predicates.
It imports only frozen `DrEquiv` and `ZXR2Flat6`. It contains no `sorry`,
`admit`, new `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or
`opaque`.

| File | Lines | Exit | Axiom records | SHA-256 |
|---|---:|---:|---:|---|
| `AHP/round14/assembly/r1/AreaP3.lean` | 4627 | 0 | 292 | `4dfb6a6fabb54f21bdeb0ff3e87765439b3aab05bf675d8c9ea8c6f6737cc116` |
| `AHP/round14/shared/assembly/R1_AreaP3.lean` | 4627 | 0 | 292 | same |

The local and published sources are byte-identical and were compiled separately
with `bb heavy run -- AHP/round3/lean1.sh <file>`. Both final logs have zero
warnings/errors and every record is contained in
`{propext, Classical.choice, Quot.sound}`. `build.py` regenerates the local file
without editing any historical source.

### New conditional theorems

The exact all-instance area predicate is

```lean
def AdalyFormal.Round14.Assembly.AreaNonvanishing : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
      ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

It remains **unproved**. The compiled implications are:

```lean
theorem AdalyFormal.Round14.Assembly.p3_of_areaNonvanishing
    (h : AreaNonvanishing) : AdalyFormal.Round13.Assembly.R1.P3

theorem AdalyFormal.Round14.Assembly.cofinalP3_of_areaNonvanishing
    (h : AreaNonvanishing) : AdalyFormal.Round13.Assembly.R2.CofinalP3

theorem AdalyFormal.Round14.Assembly.cofinalRightStarCurlLine_of_cofinalAreaNonvanishing
    (h : CofinalAreaNonvanishing) :
    AdalyFormal.Round13.Assembly.R1.CofinalRightStarCurlLine
```

The nested input `CofinalAreaNonvanishing` uses one actual generator and one
physical top row at each selected index, with no intersection of independently
chosen subsequences. It also remains unproved.

Once a suitable hypothesis is supplied, the already verified downstream
bridges apply without change:

```lean
AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3
AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3
AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_rightStar
AdalyFormal.Round10.Assembly.R4.goalNeg2_of_cofinalAnyPathNoResponseCancellation
```

No unconditional `GoalNeg2` declaration is included in this standalone file.

## Sharper published round-14 interface

The transfer track's compiled `AdalyFormal.Round14.Transfer.Physical` results
are the preferred current reductions:

```lean
theorem p3_of_areaSeed (h : AreaSeedRightStar) :
  AdalyFormal.Round13.Assembly.R1.P3

theorem cofinalP3_of_areaSeed (h : CofinalAreaSeedRightStar) :
  AdalyFormal.Round13.Assembly.R2.CofinalP3

theorem cofinalP3_of_laurentAreaSeed (h : CofinalLaurentAreaSeed) :
  AdalyFormal.Round13.Assembly.R2.CofinalP3
```

`AreaSeedRightStar` asks only for one crossing generator and one nonzero
`areaSum` per admissible instance. Its local and published `Generator.lean`
executions both have exit zero; its scalar `Transfer.lean` executions also have
exit zero. Cancellation's `chargedArea_real_imag` gives an equivalent
sesquilinear presentation but explicitly not a positivity argument.

## Held-out physical detection evidence, not a certificate

`right_star.py` generalizes the independent local-plaquette/full-flat-resolvent
computation. The main new case is **right star q=1,R=22**, absent from the
round-12/13 detection experiments and from the new transfer/cancellation
arguments. All 16 Fourier characters are included. Runs at 120 and 155 digits
both exited zero and used less than 350 MiB. `NUMERICS.json` and
`audit_numerics.py` record hashes and checks.

At 155 digits:

- crossing root: `1.207987856419019283043906137985632730100728948139...`;
- next charged Schur value: `0.932012806275816171530438663313173438450580...`;
- physical top-jet sums in directions 0,1,2:
  `-5.505913908061010103...e-49`,
  `2.607658103462613920...e-48`,
  `2.607658103265961717...e-48`;
- therefore the compiled factor-one-half dictionary gives the corresponding
  **numerical evidence** for nonzero `areaSum`, namely twice those values;
- relative 120/155 discrepancies of the three aggregates are
  `4.82e-109`, `4.47e-109`, `4.50e-109`;
- at 155 digits, null-residual/tangential-jet is `2.92e-107` and
  flat-resolvent-residual/tangential-jet is `2.06e-103`;
- `max |cell|/|sum|` is approximately
  `6099.8410`, `740.2955`, `740.2968` at both precisions.

Thus the held-out nonzero evidence is stable, but a naive common-cell-sign
argument is even more strongly unsupported. These are non-interval floating
point computations, not exact Lean nonvanishing statements, spectral
certificates, or cofinal evidence.

## Held-out test of the natural Laurent ansatz

To test transfer's conditional nonvanishing strategy rather than merely repeat
its algebra, the same first physical top-row observable was computed at 120
digits for **R=20,22,24,26,28** (`laurent_probe.py`, `LAURENT.json`). Every new
run exited zero. Both tangential aggregates remain nonzero at every radius;
successive absolute ratios are about `1.3429e4`.

A three-term sequence `A*r^n+B+C*r^(-n)` has characteristic roots
`r,1,r^-1`. Fitting its exact third-order recurrence on R=20,22,24,26 and
predicting R=28 fails dramatically in all three directions:

- direction 0 relative error approximately `2.0091e6`;
- direction 1 relative error approximately `8.77165e5`;
- direction 2 likewise approximately `8.77e5`.

Residuals remain tiny compared with the observations (at R=28,
null/tangential `7.66e-60`, resolvent/tangential `7.19e-61`), so the failed
prediction is not a roundoff artifact. **Do not use the natural same-row
three-term Laurent formula as a proof.** This does not refute P3, the general
`CofinalLaurentAreaSeed` predicate, another top row, another generator, or a
different physical recurrence. It only rejects the tested ansatz.

## Exact missing statements

The original P3 remains exactly:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

The sharper sufficient statement from transfer remains unproved:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

For the pinned cofinal route, `CofinalLaurentAreaSeed` is exactly:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∃ observable : ℕ → ℕ → ℝ,
  RadiusLaurentData observable (2^j) ∧
  ∀ n : ℕ, ∃ u : TwistSpace (2^j) (2*(n+9)),
    KernelLine (2^j) (2*(n+9)) (rightStar (by positivity) (2*(n+9))) u ∧
    ∃ k : ℕ, ∃ hk : k < blockCount (2^j) (2*(n+9)),
      areaSum (by positivity : 0 < 2^j) hk u = observable (2^j) (2*(n+9))
```

where

```lean
RadiusLaurentData observable q :=
  ∃ r A B C : ℝ, 0 < r ∧ r < 1 ∧ (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧
    ∀ n : ℕ, observable q (2*(n+9)) = A*r^n + B + C*(r⁻¹)^n
```

The original weaker `CofinalP3` and the pinned `GoalNeg2` have no inhabitants.
The shared ledger is in `AHP/round14/shared/GAPS.md`.

## Reproduction and scope

```sh
python3 AHP/round14/assembly/r1/build.py
bb heavy run -- AHP/round3/lean1.sh AHP/round14/assembly/r1/AreaP3.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round14/shared/assembly/R1_AreaP3.lean
python3 AHP/round14/assembly/r1/audit_numerics.py
python3 AHP/round14/assembly/r1/laurent_probe.py
```

The numerical runs used `right_star.py --side right --q 1 --R <radius> --dps
120` (and `--dps 155` for R=22). Only `AHP/round14/assembly/r1/` and
`AHP/round14/shared/assembly/` were written by this track; the shared ledger is
the requested assembly exception. No earlier round, frozen module, lakefile,
integration checkout, git commit or push was changed. No `lake build` or
`REPRODUCE.sh` was run, and no deletion was performed.
