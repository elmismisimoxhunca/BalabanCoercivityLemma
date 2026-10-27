# Round 15 assembly R2 — radius-cofinal charged-leading goal chain

## Verdict and audit boundary

**No unconditional physical seed or GoalNeg2 proof was found.** Original P3,
CofinalP3, every displayed area/dominant/charged-leading input, and GoalNeg2
remain open. This round weakens the radius requirement on the charged-leading
route: only cofinally many radii at each selected dyadic scale are required,
rather than every even radius. All implications below remain conditional on
their displayed physical inputs.

The round-14 blueprint, shared GAPS, and all four R2 track notes were read in
full before work. Round-15 R1 shared files and all R1 track notes were read.
Seed R2 and numerics R2 notes were read when published. Dictionary R2 was
unfinished and had exit-1 artifacts when last inspected; none of that work is
used. Dictionary R1's model certificate is not confused with its uninhabited
physical dictionary.

## Accepted compilation record and source reuse

`AreaGoal.lean` starts from the accepted assembly R1 source and appends the
new charged-leading declarations. No AHP file is imported as a Lean module.
The only imports are frozen `DrEquiv` and `DrPath3`. The local and shared
sources are byte-identical:

- `AHP/round15/assembly/r2/AreaGoal.lean`;
- `AHP/round15/shared/assembly/R2_AreaGoal.lean`.

They have 15591 lines and SHA-256
`a6d141eb46842741e72e9b8dd758fa1203c0dfa53c6b07a64ef6d86bf1ced5dc`.
The retained publication log has SHA-256
`8d9d20ba6b0647d5135310b4d2ea03cd2f9870999d4d40709c81f32b28ae142f` and exit
zero. It records the earlier successful compilation of this identical source.
The local log is a copy of that retained record. **No independent
recompilation is claimed.** Later attempts to enlarge the source with the
seed R2 vector interface exceeded the 8 GiB command cap and are not accepted.

The retained log contains inherited round-13 warnings and the separate
absolute publication path; its axiom records, not its path strings, are used
by the audit. `AUDIT.json` checks publication identity, the accepted source
and log hashes, both zero exits, all 18 assembly records, forbidden proof
mechanisms, and the numerical audit. Every new declaration has an individual
record contained in `{propext, Classical.choice, Quot.sound}`. No `sorry`,
`admit`, new axiom, `native_decide`, `unsafe`, `implemented_by`, `extern`, or
`opaque` occurs. `AUDIT.exit=0`.

## New conditional matrix chain

The main declaration is

```lean
theorem AdalyFormal.Round15.Assembly.goalNeg2_of_cofinalRadiusChargedLeading
    (h : CofinalRadiusChargedLeadingCertificate) : GoalNeg2
```

Its proof uses `cofinalAreaSeed_of_cofinalRadiusChargedLeading` and the
existing `CofinalAreaSeedRightStar → CofinalP3 → GoalNeg2` chain. The new
predicate keeps seed R1's `ChargedLeadingMatrix` but requires the
same-generator identification only on arbitrarily large indices:

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

The matrix limit supplies eventual nonvanishing. Intersecting that eventual
statement with the unbounded identification set proves the fixed-scale family

```lean
def CofinalRadiusAreaSeed (q : ℕ) (hq : 0 < q) : Prop :=
  ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
      ∃ k : ℕ, ∃ hk : k < blockCount q R, areaSum hq hk u ≠ 0
```

The nested certificate is

```lean
def CofinalRadiusChargedLeadingCertificate : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧
    CofinalRadiusChargedLeadingData (2^j) (by positivity)
```

The older `CofinalChargedLeadingCertificate` maps into this weaker certificate
by `cofinalRadiusChargedLeadingCertificate_of_cofinalChargedLeading`.
`cofinalRadiusChargedLeadingData_of_chargedLeading` proves the corresponding
per-scale weakening. No certificate is inhabited.

## Exact physical statements still missing

### Universal area seed and P3

`AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar` remains exactly:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

Original P3 is likewise still

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

The preferred all-radius `CofinalUnitDominantAreaSeed` is retained verbatim in
`AHP/round15/shared/GAPS.md`; it is not inhabited either.

### Physical collar/interface dictionary

Dictionary R1's model is accepted, but its physical statement remains the
uninhabited predicate

```lean
def Q1C10PhysicalDictionary : Prop :=
  ∀ u : TwistSpace 1 20,
    KernelLine 1 20 (rightStar (q := 1) (by norm_num) 20) u →
    ∀ x : Fin (12*1*20+16), 213 ≤ x.val → x.val ≤ 250 →
      Matrix.mulVec collarC (physicalLayer u (x-1)) +
        Matrix.mulVec collarB (physicalLayer u x) +
        Matrix.mulVec collarA (physicalLayer u (x+1)) = 0
```

The exceptional star/Omega_1 interface, common finite generator/area
coordinates, nonzero seed projection, normalized matrix/vector limits,
separate fixed-finite `chargedArea K0 z0 ≠ 0`, and same-generator genuine
`areaSum` identity remain missing. No scalar decoupling, common-sign,
definite-Hermitian, spectral-gap, or invertible naive-transfer assumption is
made.

### Seed R2 vector input — not assembled

Seed R2 independently compiles its vector-limit interface, but the following
physical certificate remains uninhabited and no additional vector goal arrow
is claimed in this artifact:

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

with

```lean
def ChargedVectorLeading {ι : Type*} [Fintype ι]
    (s : ℝ) (K : ℕ → ι → ι → ℝ) (K0 : ι → ι → ℝ)
    (z : ℕ → ι → ℂ) (z0 : ι → ℂ) : Prop :=
  0 < s ∧ z0 ≠ 0 ∧ chargedArea K0 z0 ≠ 0 ∧
    Tendsto (fun n => (s^n)⁻¹ • z n) atTop (𝓝 z0) ∧
    Tendsto K atTop (𝓝 K0)
```

and

```lean
def CofinalChargedVectorCertificate : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ChargedVectorData (2^j) (by positivity)
```

Seed R2 separately proves `CofinalChargedVectorCertificate →
CofinalUnitDominantAreaSeed` with permitted axioms. Its fixed test matrix
`collarTestLeadingConstant = Real.sqrt 2` is not the physical leading matrix.

## Independent held-out numerical retest

The original right star was rerun at **q=1,R=42**, outside every direct
R=18,...,40 sweep used by numerics R1. Both 120- and 155-digit runs exited 0.
Peak RSS was 578828/587568 KiB. `HELD_OUT.json`, `HELD_OUT.log`, and
`HELD_OUT.exit=0` record the passing audit.

- Tangential top jets are positive and stable to maximum relative discrepancy
  below `5e-101`; at 155 digits both are approximately
  `1.3669003225384349e-89`. Their doubles are numerical `areaSum` evidence
  only.
- Null/resolvent residuals relative to the tangential jet are below `1e-62`
  at 155 digits and below `5e-31` at 120 digits. Charged-line scaling errors
  are below `1e-104` at both precisions.
- The R=36→42 geometric-mean rates match candidate `rho^8` within `5.77e-12`
  in all directions.
- Both normalized full-area constants are approximately
  `0.01336120689316480408`, within `1.09e-13` relative error of the direct
  R=40 constant.
- Cell/sum ratios are about `5.09e7` and `6.17e6`; no common-sign shortcut is
  supported.

A separate q=2,R=42 attempt hit its shell timeout after 31 of 64 sectors. It
left no JSON and no `.exit`, was not retried, and is not used. All numerical
results are finite non-interval evidence only. They do not prove an exact
recurrence, normalized limit, nonzero leading coefficient, AreaSeedRightStar,
P3, CofinalP3, or GoalNeg2.

## Remaining boundary and scope

`AHP/round15/shared/GAPS.md` is the current shared ledger. The complete arrows
are conditional; the physical left-hand inputs and GoalNeg2 remain open.
Writes are confined to `AHP/round15/assembly/r2/` and
`AHP/round15/shared/assembly/`, plus the shared ledger. Earlier rounds, frozen
modules, the lakefile, integration checkout, and other tracks were not edited.
No `lake build`, `REPRODUCE.sh`, git commit, or push was performed.
