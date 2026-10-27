# Round 15 — exact current gaps and assembly status

## Run disposition — 2026-10-27

Workflow `wfr_5df3dc43-d69b-4118-bbde-2106f7836520` hit its 24-hour total timeout during Work: 7 calls succeeded, 2 earlier attempts failed and were retried, and dictionary R2 was cancelled. The workflow did not reach its Blueprint phase. The cancelled worker is idle; no relevant Lean process remained at the coordinator's check. Research is not being restarted. The promised evidence audit and blueprint are now complete: `AHP/round15/BLUEPRINT.md`, `AHP/round15/blueprint/content.tex`, and the coordinator's `AHP/round15/audit/BLUEPRINT_VALIDATION.json`. Further guarded proof search is paused; none of the open mathematical premises below is marked closed.

The first-inverse-only all-plaquette reading is **numerically strongly disfavoured / conjectured false**, not formally refuted. This evidential classification does not apply to the already-proved full-guard variant or to source-reading questions.

See `AHP/round15/audit/TIMEOUT_AUDIT.json` for the retained source/log audit. Late `dictionary/r2/KData.lean` has a clean builder record for explicit-matrix Schur identities only. `Stencil.lean` is **not accepted**: its current log has a syntax error and is incomplete, while its zero exit marker predates the current source and log. Earlier `Support.lean`, `DeepCollar.lean` and `Transport.lean` attempts are not promoted. No new physical dictionary or detection result is claimed.

## Verdict

**The physical seed, original P3, CofinalP3, and GoalNeg2 remain OPEN.** No
inhabitant of `AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar`,
`AdalyFormal.Round14.Transfer.Physical.CofinalUnitDominantAreaSeed`,
`AdalyFormal.Round15.Seed.CofinalChargedVectorCertificate`,
`AdalyFormal.Round15.Assembly.CofinalRadiusChargedLeadingCertificate`, or
`AdalyFormal.Round2.Guarded.Pin.GoalNeg2` is posted.

Assembly R1 compiled the conditional arrows from the universal area seed and
from dominant/charged-leading cofinal inputs. Assembly R2 adds a genuinely
weaker radius quantifier: only **cofinally many even radii** are required at
each selected dyadic scale, rather than every even radius. The main new
conditional declaration is

```lean
AdalyFormal.Round15.Assembly.goalNeg2_of_cofinalRadiusChargedLeading :
  AdalyFormal.Round15.Assembly.CofinalRadiusChargedLeadingCertificate →
    AdalyFormal.Round2.Guarded.Pin.GoalNeg2
```

Its route is

\[
  \text{charged matrix leading data}\to \text{CofinalAreaSeedRightStar}
  \to \text{CofinalP3}\to GoalNeg2.
\]

Only the arrow is proved. Its physical premise and the final goal are not
proved. The accepted source is `AHP/round15/assembly/r2/AreaGoal.lean`, with
SHA-256 `a6d141eb46842741e72e9b8dd758fa1203c0dfa53c6b07a64ef6d86bf1ced5dc`,
published byte-identically as `AHP/round15/shared/assembly/R2_AreaGoal.lean`.
The retained publication log and zero exit record the earlier successful
compilation of this identical source. The local log is a copy of that retained
record; no independent recompilation is claimed.

## 1. Original per-instance area seed — still unproved

The shortest universal physical input remains exactly

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

This is `AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar`.
`goalNeg2_of_areaSeed` compiles its conditional route through P3. The
unit-full-carrier-norm form `UnitAreaSeedRightStar` is equivalent by the
round-14 theorem `unitAreaSeedRightStar_iff`; the norm is not the numerical
nine-boundary-bond norm.

Original P3 also remains open in its exact form:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

## 2. Preferred dominant cofinal input — still unproved

`CofinalUnitDominantAreaSeed` remains exactly

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
def RadiusDominantData (observable : ℕ → ℕ → ℝ) (q : ℕ) : Prop :=
  ∃ r K : ℝ, 0 < r ∧ K ≠ 0 ∧
    Tendsto (fun n => observable q (2*(n+9)) / r^n) atTop (𝓝 K)
```

The nested existential `CofinalAreaSeedRightStar`, the exact
`CofinalLaurentAreaSeed`, and `CofinalDominantAreaSeed` are also still open.
Assembly compiles their conditional arrows to GoalNeg2, but no inhabitants.

## 3. Charged matrix data and the new radius-cofinal certificate

Seed R1's physical identification predicate is

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

with

```lean
def ChargedLeadingMatrix {ι : Type*} [Fintype ι]
    (r : ℝ) (K : ℕ → ι → ι → ℝ) (K0 : ι → ι → ℝ) (z : ι → ℂ) : Prop :=
  0 < r ∧ z ≠ 0 ∧ chargedArea K0 z ≠ 0 ∧
    Tendsto (fun n => (r^n)⁻¹ • K n) atTop (𝓝 K0)
```

The older nested certificate is

```lean
def CofinalChargedLeadingCertificate : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧
    AdalyFormal.Round15.Seed.ChargedLeadingData (2^j) (by positivity)
```

Assembly R2 retains that conditional route but also compiles the strictly
weaker physical predicate

```lean
def CofinalRadiusChargedLeadingData (q : ℕ) (hq : 0 < q) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (r : ℝ) (K : ℕ → ι → ι → ℝ)
    (K0 : ι → ι → ℝ) (z : ι → ℂ),
    AdalyFormal.Round15.Seed.ChargedLeadingMatrix r K K0 z ∧
    ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧
      ∃ u : TwistSpace q (2*(n+9)),
        KernelLine q (2*(n+9)) (rightStar hq (2*(n+9))) u ∧ ‖u‖ = 1 ∧
        ∃ k : ℕ, ∃ hk : k < blockCount q (2*(n+9)),
          areaSum hq hk u = AdalyFormal.Round14.Cancellation.chargedArea (K n) z
```

The matrix limit gives eventual nonvanishing; the displayed identification is
needed only on an unbounded set of indices. Their intersection proves the
fixed-scale family

```lean
def CofinalRadiusAreaSeed (q : ℕ) (hq : 0 < q) : Prop :=
  ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
      ∃ k : ℕ, ∃ hk : k < blockCount q R, areaSum hq hk u ≠ 0
```

The new nested certificate is exactly

```lean
def CofinalRadiusChargedLeadingCertificate : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧
    CofinalRadiusChargedLeadingData (2^j) (by positivity)
```

`cofinalRadiusChargedLeadingCertificate_of_cofinalChargedLeading` proves that
the older all-radius certificate is a strengthening. No inhabitant of either
certificate is supplied.

## 4. Seed R2 charged vector interface — exact physical input, not assembled

Seed R2 proves the exact two-layer formula and the arbitrary-remainder vector
limit. Its analytic predicate is

```lean
def ChargedVectorLeading {ι : Type*} [Fintype ι]
    (s : ℝ) (K : ℕ → ι → ι → ℝ) (K0 : ι → ι → ℝ)
    (z : ℕ → ι → ℂ) (z0 : ι → ℂ) : Prop :=
  0 < s ∧ z0 ≠ 0 ∧ chargedArea K0 z0 ≠ 0 ∧
    Tendsto (fun n => (s^n)⁻¹ • z n) atTop (𝓝 z0) ∧
    Tendsto K atTop (𝓝 K0)
```

The exact physical input is

```lean
def ChargedVectorData (q : ℕ) (hq : 0 < q) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (s : ℝ) (K : ℕ → ι → ι → ℝ)
    (K0 : ι → ι → ℝ) (z : ℕ → ι → ℂ) (z0 : ι → ℂ),
    ChargedVectorLeading s K K0 z z0 ∧
    ∀ n : ℕ, ∃ u : TwistSpace q (2*(n+9)),
      KernelLine q (2*(n+9)) (rightStar hq (2*(n+9))) u ∧ ‖u‖ = 1 ∧
      ∃ k : ℕ, ∃ hk : k < blockCount q (2*(n+9)),
        areaSum hq hk u = chargedArea (K n) (z n)
```

and its nested form is

```lean
def CofinalChargedVectorCertificate : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ChargedVectorData (2^j) (by positivity)
```

Seed R2 proves `CofinalChargedVectorCertificate → CofinalUnitDominantAreaSeed`
with permitted axioms. No inhabitant of the physical certificate is supplied.
The final assembly artifact uses the matrix route above; an additional vector
radius-cofinal goal arrow is **not claimed**. In particular,
`collarTestLeadingConstant = Real.sqrt 2` is only a fixed test matrix
computation, not the frozen physical leading matrix or amplitude.

## 5. Exact physical work still missing

Supplying any of these certificates requires the actual frozen right-star
identification, not merely a model recurrence:

1. the exact frozen flat-collar operator dictionary, including the constant
   blocks on every required row and Fourier character;
2. the exceptional star and `Omega_1` interface rows, not just a deep-collar
   recurrence;
3. a common finite coordinate system for the crossing generator, top-row area
   coefficients, and the seed, including proof of nonzero seed projection;
4. the normalized matrix/vector limits and the separate fixed-finite
   `chargedArea K0 z0 ≠ 0` computation; and
5. the same-generator identity with genuine `areaSum`, at the same physical
   top row and radius, with full-carrier normalization.

A nonzero `z` does not imply nonzero charged area. Scalar decoupling,
definiteness, common cell signs, a uniform spectral gap, and an invertible
naive transfer matrix are not assumed.

Dictionary R1's accepted model theorem `collar_dictionary` is only a model
certificate. Its exact physical gap remains the uninhabited predicate

```lean
def Q1C10PhysicalDictionary : Prop :=
  ∀ u : TwistSpace 1 20,
    KernelLine 1 20 (rightStar (q := 1) (by norm_num) 20) u →
    ∀ x : Fin (12*1*20+16), 213 ≤ x.val → x.val ≤ 250 →
      Matrix.mulVec collarC (physicalLayer u (x-1)) +
        Matrix.mulVec collarB (physicalLayer u x) +
        Matrix.mulVec collarA (physicalLayer u (x+1)) = 0
```

The exceptional interface, dressed-jet/top-row area identification, and a
proved nonzero physical leading constant remain open. Assembly does not use
unfinished dictionary R2 work. In particular, the stale zero marker for the
last interrupted Stencil attempt is not evidence of successful compilation.

## 6. Numerical evidence — exact matrix arithmetic is not a physical proof

Numerics R2 verifies exact characteristic factors for all 336 transcribed
character dictionaries and repairs four q=4 reduced-matrix packaging defects
in separate R2 files. It also gives explicit determinant fields. These are
exact computations on numerical transcriptions, not Lean identifications with
the frozen operator. No exact closed form for the physical area amplitude is
established; bounded PSLQ failures are not nonexistence proofs.

The retained direct normalized constants remain approximately

- q=1: `0.0133612068931633503479`;
- q=2: `0.0019184541381844317668645407795820`;
- q=4: `0.0001653700585858785228210904209427`.

The failed same-row three-term Laurent fit is still explained by omitted
subleading character rates, not promoted to an exact finite Laurent model.

### Assembly R2 independent held-out retest

The original right star was rerun at **q=1,R=42**, outside every direct
R=18,...,40 sweep used by numerics R1. Both 120- and 155-digit runs exited 0
and used less than 0.6 GiB.

- Both tangential top aggregates are positive and stable, with maximum
  120/155 relative discrepancy below `5e-101`. At 155 digits they are
  approximately `1.3669003225384349e-89`; doubling them is numerical
  `areaSum` evidence only.
- Null/resolvent residuals relative to the tangential aggregate are below
  `1e-62` at 155 digits (and below `5e-31` at 120 digits); charged-line
  scaling error is below `1e-104` at both precisions.
- The geometric mean R=36→42 rates match the candidate `rho^8` within
  `5.77e-12` in all three directions.
- The normalized full-area constants at both precisions are approximately
  `0.01336120689316480408`, agreeing with the direct R=40 constant within
  `1.09e-13` relative error.
- Cell/sum ratios remain very large (about `5.09e7` and `6.17e6`), so a naive
  common-sign argument remains unavailable.

A separate q=2,R=42 probe timed out after 31 of 64 sectors, left no JSON and no
`.exit`, was not retried, and is not used. All these results are finite
non-interval evidence, not Lean premises or proofs of an unbounded statement.

## 7. Current accepted conditional routes

- `AreaSeedRightStar → P3 → GoalNeg2`;
- `CofinalAreaSeedRightStar → CofinalP3 → GoalNeg2`;
- `CofinalLaurentAreaSeed → CofinalP3 → GoalNeg2`;
- `CofinalDominantAreaSeed → CofinalP3 → GoalNeg2`;
- `CofinalUnitDominantAreaSeed → CofinalP3 → GoalNeg2`;
- `DyadicChargedLeadingCertificate → CofinalUnitDominantAreaSeed →
  CofinalP3 → GoalNeg2`;
- `CofinalChargedLeadingCertificate → CofinalUnitDominantAreaSeed →
  CofinalP3 → GoalNeg2`; and
- `CofinalRadiusChargedLeadingCertificate → CofinalAreaSeedRightStar →
  CofinalP3 → GoalNeg2`.

Seed R2 separately proves
`CofinalChargedVectorCertificate → CofinalUnitDominantAreaSeed`; no additional
vector goal assembly is claimed here. Only the implications are proved. Their
left-hand physical inputs and GoalNeg2 itself remain open.
