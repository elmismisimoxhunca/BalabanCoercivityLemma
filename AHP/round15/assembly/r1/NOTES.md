# Round 15 assembly R1 — conditional goal chain and held-out R=34 audit

## Verdict and scope

**No unconditional physical seed or GoalNeg2 proof was found.**  Original P3,
CofinalP3, every displayed area/dominant/charged-leading input, and GoalNeg2
remain open.  This track assembled the existing area interfaces and seed R1's
charged-leading interface into complete conditional arrows to the pinned goal.
No numerical value is a Lean premise.

The round-14 blueprint/GAPS and all four R2 track notes were read in full before
work.  Seed R1 NOTES was read when published.  No other track NOTES was present
at the time of writing.  The current dictionary R1 prototype has exit 1 and a
`sorryAx` record; it is not used.

## Compiled integration

| Artifact | Lines | Exit | SHA-256 |
|---|---:|---:|---|
| `AHP/round15/assembly/r1/AreaGoal.lean` | 15475 | 0 | `4cfcd3b1b146a16405678dc04a097e50fe4e024e887f1da2beb0e0bd7f4c3aa9` |
| `AHP/round15/shared/assembly/R1_AreaGoal.lean` | 15475 | 0 | same |

The publication is byte-identical.  Both were compiled with

```sh
bb heavy run -- AHP/round3/lean1.sh <file>
```

The self-contained source uses only frozen `DrEquiv` and `DrPath3` imports.
`build.py` starts from the verified round-13 goal source, appends only missing
fully-qualified declarations from round-14 `R2_AreaLine` and round-15
`Seed.lean`, and appends the new assembly declarations.  Earlier rounds are not
modified and no AHP module is imported.  The retained declarations are copied
verbatim.  Initial deduplication parser errors involving `in` modifiers and a
doc comment were corrected; the final source was recompiled from scratch and
exits 0.

The final logs have no errors or `sorryAx`.  They contain 11 warnings inherited
from the round-13 base (one deprecated `push_neg`, and unused variable/simp
warnings).  No new warning is introduced by the assembly declarations.  All ten
new main declaration axiom records, in both logs, are exactly within
`{propext, Classical.choice, Quot.sound}`.  There is no `sorry`, `admit`, new
axiom, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`.
`audit.py` checks these facts, publication identity, current source hash,
statements, and the numerical audit; `AUDIT.json`, `AUDIT.log`, and
`AUDIT.exit=0` are included.

### New conditional arrows

```lean
AdalyFormal.Round15.Assembly.goalNeg2_of_areaSeed :
  AreaSeedRightStar → GoalNeg2

AdalyFormal.Round15.Assembly.goalNeg2_of_unitAreaSeed :
  UnitAreaSeedRightStar → GoalNeg2

AdalyFormal.Round15.Assembly.goalNeg2_of_cofinalAreaSeed :
  CofinalAreaSeedRightStar → GoalNeg2

AdalyFormal.Round15.Assembly.goalNeg2_of_laurentAreaSeed :
  CofinalLaurentAreaSeed → GoalNeg2

AdalyFormal.Round15.Assembly.goalNeg2_of_dominantAreaSeed :
  CofinalDominantAreaSeed → GoalNeg2

AdalyFormal.Round15.Assembly.goalNeg2_of_unitDominantAreaSeed :
  CofinalUnitDominantAreaSeed → GoalNeg2

AdalyFormal.Round15.Assembly.goalNeg2_of_chargedLeading :
  AdalyFormal.Round15.Seed.DyadicChargedLeadingCertificate → GoalNeg2
```

These are the compiled chains `AreaSeed → P3 → GoalNeg2` and
`Cofinal* → CofinalP3 → GoalNeg2`, not inhabitants of their premises.

The new nested charged-leading predicate and its two bridges are

```lean
def AdalyFormal.Round15.Assembly.CofinalChargedLeadingCertificate : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧
    AdalyFormal.Round15.Seed.ChargedLeadingData (2^j) (by positivity)

theorem cofinalUnitDominantAreaSeed_of_cofinalChargedLeading :
  CofinalChargedLeadingCertificate → CofinalUnitDominantAreaSeed

theorem goalNeg2_of_cofinalChargedLeading :
  CofinalChargedLeadingCertificate → GoalNeg2
```

Thus only cofinally many dyadic scales are required, rather than seed R1's
stronger certificate at every dyadic scale.  Every chosen scale still requires
the full even-radius progression and its common generator/matrix dictionary.

## Exact statements still missing

### Universal area seed

`AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar` remains exactly:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

No inhabitant is supplied.  Original P3 is likewise still

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

### Charged-leading physical dictionary

Seed R1's exact compiled physical input is:

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

The preferred nested input `CofinalChargedLeadingCertificate` displayed above
is still unproved.  The stronger seed predicate
`∀ j, ChargedLeadingData (2^j) (by positivity)` is also unproved.
`CofinalUnitDominantAreaSeed`, `CofinalLaurentAreaSeed`, and the nested
existential area seed remain open; their exact statements are retained in
`AHP/round15/shared/GAPS.md`.

The actual missing work is the frozen flat-collar recurrence, exceptional star
and `Omega_1` interface rows, common finite generator/area coordinates,
nonzero seed projection, normalized matrix limit, separate fixed-finite
`chargedArea K0 z ≠ 0`, and same-generator genuine `areaSum` identity.  No
scalar decoupling, common-sign, definite-Hermitian, spectral-gap, or invertible
naive-transfer assumption is made.

## Independent held-out numerical retest

The original right star was rerun at **q=1,R=34**, a case not used by the
round-14 cancellation analysis or its R=32 held-out assembly audit.  Both runs
used `right_star.py` (copied unchanged from round-14) at 120 and 155 digits and
exited 0.  Peak RSS was 477108/490028 KiB.

- Tangential top jets are positive and stable to maximum relative discrepancy
  `2.66e-104`; at 155 digits both are approximately `4.4457223974e-73`.
  Their doubles are only numerical `areaSum` evidence.
- Root relative difference is `2.93e-115`; null/resolvent residuals relative
  to the tangential jet are below `1e-40`; charged-line scaling errors are
  below `1e-100` at both precisions.
- R=32→34 rates match R=30→32 rates within `7.04e-10` relative change.
- Seed's candidate \(\rho^8=7.44643883080822\times10^{-5}\), where
  \(\rho=(5-\sqrt2-\sqrt{23-10\sqrt2})/2\), agrees with every held-out rate
  within `2.26e-10` relative error.  This is a useful independent test of the
  candidate on data its author did not use, not an exact rate or a proof of
  branch projection or nonzero leading charged area.
- Cell/sum ratios are about `1.37e6` and `1.67e5`; no common-sign shortcut is
  supported.

Artifacts are `star_right_q1_R34_p{120,155}.{json,log,exit}`,
`audit_held_out.py`, `HELD_OUT.json`, `HELD_OUT.log`, and `HELD_OUT.exit=0`.
All values are finite non-interval numerical evidence only.  They do not prove
any unbounded/cofinal statement and are not referenced by the Lean source.

## Remaining boundary

`AHP/round15/shared/GAPS.md` is the current shared ledger.  The complete arrows
are compiled, but the physical left-hand inputs and GoalNeg2 itself remain
open.  A future dictionary result must be compiled with permitted axioms
before it can be used to discharge `ChargedLeadingData`; the current failed
dictionary prototype is deliberately excluded.
