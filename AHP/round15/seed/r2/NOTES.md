# Round 15 seed R2 — charged two-layer algebra and a vector leading interface

## Verdict and audit boundary

**The physical area seed is still open.**  This round proves new exact algebra
and a conditional reduction to `CofinalUnitDominantAreaSeed`; it does not prove
`AreaSeedRightStar`, `CofinalUnitDominantAreaSeed`, P3, CofinalP3, or GoalNeg2.
The new physical predicate `CofinalChargedVectorCertificate` is not inhabited.

The main conditional declaration is

```lean
theorem AdalyFormal.Round15.Seed.cofinalUnitDominantAreaSeed_of_chargedVector
    (h : AdalyFormal.Round15.Seed.CofinalChargedVectorCertificate) :
    AdalyFormal.Round14.Transfer.Physical.CofinalUnitDominantAreaSeed
```

with the checked record

```text
'AdalyFormal.Round15.Seed.cofinalUnitDominantAreaSeed_of_chargedVector' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is not an unconditional proof of the conclusion.

## Compiled artifacts

| File | Lines | Exit | Evidence |
|---|---:|---:|---|
| `AHP/round15/seed/r2/Leading.lean` | 6311 | 0 | local main source and clean log |
| `AHP/round15/shared/seed/R2_Leading.lean` | 6311 | 0 | byte-identical publication and clean log |

Both were compiled separately using only

```sh
bb heavy run -- AHP/round3/lean1.sh <file>
```

The two sources are byte-identical, and the two logs are also byte-identical.
There are 419 axiom records (417 distinct printed names), including 25 new R2
records.  Every record is contained in
`{propext, Classical.choice, Quot.sound}`.  There are no warnings, errors, or
`sorryAx` records.  The appended source contains no `sorry`, `admit`, new
`axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`.
Only frozen `DrEquiv` and `ZXR2Flat6` are imported.  No AHP module is imported,
and no `lake build` or `REPRODUCE.sh` was run.  `AUDIT.json`, `audit.py`,
`audit.log`, and `audit.exit=0` check these facts and the source hash
`12074eaafe4107864fdc737bddb90001cc00d1ed554dba58fea07e460f9064d3`.

The source starts from the accepted seed R1 file and appends the new
declarations.  It also retains the previously compiled complex `chargedArea`
scaling theorem and dictionary R1's `phase`/`mode0` definitions.  No earlier
file was edited.  `R2Declarations.lean` is the appended source fragment used by
`build.py`; the compiled deliverable is `Leading.lean`.

## 1. Exact two-layer charged-seed formula

For a finite index type, `chargedTwoLayerMode r z w n` is

```lean
(r^n) • z + ((r⁻¹)^n) • w
```

where the vectors can include all transverse components and both interface
layers.  The new `chargedBilin` and `chargedMixed` retain the full matrix cross
term.  `chargedArea_twoLayerMode` proves

```lean
chargedArea K (chargedTwoLayerMode r z w n) =
  laurent (r^2) (chargedArea K z) (chargedMixed K z w) (chargedArea K w) n
```

for `r ≠ 0`.  Thus the growing leading coefficient is exactly
`chargedArea K w`; the mixed and decaying terms are explicit rather than being
hidden by a scalar-mode or common-sign assumption.  Complex scaling by `c`
multiplies the area by `Complex.normSq c`, and real scaling by `c` multiplies
it by `c^2`.

`radiusLaurentData_of_chargedTwoLayer` converts any nonzero one of these three
fixed finite coefficients to the already compiled Laurent interface when
`0 < r < 1`.  No claim is made that the actual physical observable has only
these branches; the retained numerical five-rate warning still applies.

## 2. Arbitrary-remainder vector limit

The new analytic predicate is exactly

```lean
def ChargedVectorLeading {ι : Type*} [Fintype ι]
    (s : ℝ) (K : ℕ → ι → ι → ℝ) (K0 : ι → ι → ℝ)
    (z : ℕ → ι → ℂ) (z0 : ι → ℂ) : Prop :=
  0 < s ∧ z0 ≠ 0 ∧ chargedArea K0 z0 ≠ 0 ∧
    Tendsto (fun n => (s^n)⁻¹ • z n) atTop (𝓝 z0) ∧
    Tendsto K atTop (𝓝 K0)
```

The vector and matrix remainders are arbitrary.  The new theorem
`tendsto_chargedArea_vector` proves

```lean
Tendsto (fun n => chargedArea (K n) (z n) / (s^2)^n) atTop
  (𝓝 (chargedArea K0 z0))
```

from the displayed vector and matrix limits and `s ≠ 0`.
`radiusDominantData_of_chargedVectorLeading` turns this into the existing
`RadiusDominantData`.  Nonzero `z0` and nonzero `chargedArea K0 z0` remain
separate hypotheses.

For the exact two-layer mode, `chargedVectorLeading_of_twoLayer` proves that
`0 < r < 1`, `w ≠ 0`, and `chargedArea K w ≠ 0` give a
`ChargedVectorLeading (r⁻¹) (fun _ => K) K` certificate.  Its normalized vector
is the original two-layer mode and its limit is `w`.  The other mode tends to
zero after normalization; no spectral gap is assumed beyond the displayed
single branch and its nonzero fixed area coefficient.

## 3. Exact physical input still missing

`ChargedVectorData` is the precise unproved physical dictionary for this route:

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

The required nested certificate is

```lean
def CofinalChargedVectorCertificate : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ChargedVectorData (2^j) (by positivity)
```

**No inhabitant of either predicate is supplied.**  In particular, the frozen
operator must still provide the exceptional star/Omega_1 interface, a common
finite coordinate dictionary, nonzero seed projection, the matrix/vector
limits, the genuine same-generator `areaSum` identity, and full-carrier
normalization.  Dictionary R2 was not an accepted shared publication when this
file was compiled, so no uncompiled deep-collar work is used.

The original shortest physical target also remains exactly

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

and the preferred cofinal target remains

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∃ observable : ℕ → ℕ → ℝ,
  RadiusDominantData observable (2^j) ∧
  ∀ n : ℕ, ∃ u : TwistSpace (2^j) (2*(n+9)),
    KernelLine (2^j) (2*(n+9)) (rightStar (by positivity) (2*(n+9))) u ∧
    ‖u‖ = 1 ∧
    ∃ k : ℕ, ∃ hk : k < blockCount (2^j) (2*(n+9)),
      areaSum (by positivity : 0 < 2^j) hk u = observable (2^j) (2*(n+9))
```

The new theorem proves only the arrow from
`CofinalChargedVectorCertificate` to the latter.

## 4. Fixed finite computation and its limitation

`collarTestMatrix` is an explicit real matrix on `Fin 8`, supported on the
`(0,1)` and `(1,0)` entries with values `-1` and `1`.  The computation

```lean
theorem collarTestLeadingConstant :
  chargedArea collarTestMatrix AdalyFormal.Round15.Dictionary.mode0 = Real.sqrt 2
```

is proved by exact finite simplification in `Q(sqrt 2)`, and
`collarTestLeadingConstant_ne_zero` discharges its nonvanishing.  The seed is
shown nonzero independently.  `collarModelLeading` packages these facts with
seed R1's `0 < dominantRho < 1` into a concrete `ChargedVectorLeading` model.

**This fixed matrix is a test model, not the frozen physical leading matrix.**
It is not asserted to be `aggregateCoefficient`, a dressed-jet restriction, or
an interface matrix, and `sqrt 2` is not claimed to be the numerical physical
area amplitude.  The actual fixed physical matrix and its nonzero charged area
remain open.  In particular, this computation does not close the physical
certificate or any goal.

## Reproduction and scope

```sh
python3 AHP/round15/seed/r2/build.py
bb heavy run -- AHP/round3/lean1.sh AHP/round15/seed/r2/Leading.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round15/shared/seed/R2_Leading.lean
python3 AHP/round15/seed/r2/audit.py
```

Writes were confined to `AHP/round15/seed/r2/` and
`AHP/round15/shared/seed/`.  Earlier rounds, frozen modules, the lakefile,
integration checkout, and other tracks were not edited.  No numerical solve,
git commit, or push was performed.
