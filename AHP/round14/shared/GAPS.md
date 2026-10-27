# Round 14 — current exact gaps and assembly status

**P3, CofinalP3, and GoalNeg2 remain OPEN.** P1, P2, the actual right-star
crossing, whole-kernel charged line, real nullity two, flat N-unit, physical
area dictionary, and all downstream response/goal bridges are already compiled.
No round-14 numerical result is a proof premise.

This ledger reflects the published assembly, transfer, cancellation, and
path-choice R1/R2 artifacts. Their conditional theorems are not physical seed
certificates. In particular, transfer R2 adds exact two-layer/dominant transfer
interfaces and unit-full-norm seeds; cancellation R2 adds exact charged-line
area scaling and a dominant-matrix sign theorem; neither supplies its physical
model. No path-variant proof is available.

The new assembly R2 `AreaLine.lean` compiles the additional area-level join

```lean
theorem AdalyFormal.Round14.Assembly.areaNonvanishing_of_areaSeed
    (h : AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar) :
    AdalyFormal.Round14.Assembly.AreaNonvanishing
```

and its unit-norm analogue. Thus one detected generator now yields the
universal area remainder directly by the exact charged-span area formula, not
merely curl detection by the older response-gradient route. The compiled
`p3_of_areaSeed_via_area` and `p3_of_unitAreaSeed_via_area` remain conditional;
no inhabitant of any seed is posted.

## 1. Original universal P3

With the original round-13 opens, the unproved statement is verbatim:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

The compiled implication `AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3`
turns any inhabitant into the pinned `GoalNeg2`. No such inhabitant is posted.

## 2. Sharpest current per-instance area seed

The preferred sufficient statement is transfer's **unproved**
`AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar`:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

`AdalyFormal.Round14.Transfer.Physical.p3_of_areaSeed` compiles this to the
original P3. It uses the exact round-12 response scaling: detection of one
whole-line generator detects every vector satisfying `KernelLine`.

Transfer R2's equivalent unit-full-carrier-norm input is also unproved:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧ ‖u‖ = 1 ∧
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

This is `UnitAreaSeedRightStar`; `unitAreaSeedRightStar_iff` proves its
equivalence to `AreaSeedRightStar`. The norm is the full carrier norm, not the
nine-boundary-bond norm printed by numerical probes. Assembly R2 proves both
`areaNonvanishing_of_areaSeed` and `areaNonvanishing_of_unitAreaSeed`, so either
existential seed yields the following universal remainder.

Assembly also compiles the stronger, still unproved universal remainder
`AdalyFormal.Round14.Assembly.AreaNonvanishing`:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

with `p3_of_areaNonvanishing` and `cofinalP3_of_areaNonvanishing` in
`shared/assembly/R1_AreaP3.lean`. The existential transfer seed is therefore
the shorter current target.

Cancellation's `chargedArea_real_imag` gives an exact sesquilinear rewrite of
the same area, not a sign or nonvanishing theorem. A common-phase field has zero
area; chargedness or one nonzero coordinate alone is insufficient.

## 3. Cofinal area alternatives

The nested existential seed, also unproved, is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    ∃ k : ℕ, ∃ hk : k < blockCount (2^j) R,
      areaSum (by positivity : 0 < 2^j) hk u ≠ 0
```

This is `AdalyFormal.Round14.Transfer.Physical.CofinalAreaSeedRightStar` (and
the equivalent assembly `CofinalAreaNonvanishing`). Transfer compiles it to
`AdalyFormal.Round13.Assembly.R2.CofinalP3`; assembly compiles it to the
original existential right-star detected-line family. The verified
`goalNeg2_of_cofinalP3` and response-hull bridges then apply.

The original `CofinalP3` itself remains unproved:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∀ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u →
      CurlDetected (2^j) R u
```

## 4. Laurent transfer certificate

Transfer's alternative sufficient `CofinalLaurentAreaSeed` is exactly:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∃ observable : ℕ → ℕ → ℝ,
  RadiusLaurentData observable (2^j) ∧
  ∀ n : ℕ, ∃ u : TwistSpace (2^j) (2*(n+9)),
    KernelLine (2^j) (2*(n+9)) (rightStar (by positivity) (2*(n+9))) u ∧
    ∃ k : ℕ, ∃ hk : k < blockCount (2^j) (2*(n+9)),
      areaSum (by positivity : 0 < 2^j) hk u = observable (2^j) (2*(n+9))
```

where the exact data definition is:

```lean
∃ r A B C : ℝ, 0 < r ∧ r < 1 ∧ (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧
  ∀ n : ℕ, observable q (2*(n+9)) = A*r^n + B + C*(r⁻¹)^n
```

No physical collar identification or nonzero Laurent certificate is supplied.
`cofinalP3_of_laurentAreaSeed` is conditional, not a proof of this input.

Transfer R2 weakens the required analytic input to a normalized limit with an
arbitrary remainder. `RadiusDominantData` is exactly

```lean
∃ r K : ℝ, 0 < r ∧ K ≠ 0 ∧
  Tendsto (fun n => observable q (2*(n+9)) / r^n) atTop (𝓝 K)
```

The preferred normalized cofinal input `CofinalUnitDominantAreaSeed` remains
unproved:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∃ observable : ℕ → ℕ → ℝ,
  RadiusDominantData observable (2^j) ∧
  ∀ n : ℕ, ∃ u : TwistSpace (2^j) (2*(n+9)),
    KernelLine (2^j) (2*(n+9)) (rightStar (by positivity) (2*(n+9))) u ∧
    ‖u‖ = 1 ∧
    ∃ k : ℕ, ∃ hk : k < blockCount (2^j) (2*(n+9)),
      areaSum (by positivity : 0 < 2^j) hk u = observable (2^j) (2*(n+9))
```

`cofinalP3_of_dominantAreaSeed` and
`cofinalP3_of_unitDominantAreaSeed` are conditional reductions only. The exact
two-layer quadratic formula has not been identified with the frozen carrier.

Cancellation R2 independently proves `areaSum_eq_chargedArea` and

```lean
(hr : 0 < r) (z : ι → ℂ) (hpos : 0 < chargedArea K0 z)
(hK : Tendsto (fun n => (r^n)⁻¹ • K n) atTop (𝓝 K0)) :
  ∀ᶠ n in atTop, 0 < chargedArea (K n) z
```

A still-missing physical leading model therefore has the exact schema

```lean
∃ (r : ℝ) (K0 : ι → ι → ℝ) (z : ι → ℂ),
  0 < r ∧ 0 < chargedArea K0 z ∧
  Tendsto (fun n => (r^n)⁻¹ • K n) atTop (𝓝 K0)
```

One must also identify `K`, `K0`, and `z` with the actual aggregate
coefficients and crossing-generator coordinates, with a common finite index
type and all radius-dependent choices. No such identification is proved.

**Assembly numerical caution:** on right-star q=1, the natural first-physical-
row three-term Laurent recurrence fitted at R=20,22,24,26 fails badly at the
held-out R=28 in every direction (120 digits; see
`assembly/r1/LAURENT.json`). This rejects that particular same-row ansatz, not
the general predicate above, another row, or P3 itself.

## 5. Numerical evidence boundary

Assembly R2 ran two independent held-out audits (`assembly/r2/HELD_OUT.json`).
Neither is a proof premise or an interval certificate.

* **Original right star q=1,R=32, unused by cancellation R2's R=20,...,30
  analysis.** All 16 Fourier characters were recomputed at 120 and 155 digits.
  The tangential physical top jets are positive and stable to relative
  discrepancies about `5.90e-105` and `6.24e-105`; at 155 digits they are
  approximately `5.9702664573685409e-69` and
  `5.9702664573681616e-69`. The doubled values are the corresponding
  numerical `areaSum` evidence. The R=30→32 ratios match the previous R=28→30
  ratios within `1.26e-9` (tangential) and `2.90e-9` (direction zero), which is
  consistent with, but does not prove, a dominant limit. At 155 digits the
  null/resolvent residuals relative to the tangential jet are about
  `1.25e-86` and `2.68e-83`. Cell/sum ratios are approximately
  `556891.70, 67575.896, 67575.897`, so common-sign reasoning remains
  unsupported.
* **Path-choice L3 candidate `c2=-0.25,c3=-2.25` at unused q=2,R=30.**
  Independent 120/155-digit dressed-solve replays give the same positive last
  physical-row aggregate to relative difference `1.44e-113`, namely
  `4.7701350589925427e-112` at 155 digits. The max-cell/sum ratio is
  `0.2966429803`, versus `0.0410964394` at q=2,R=20. The 155-digit
  resolvent residual/sum is `5.55e-40`, and double/high values agree to about
  `1.60e-11` relative. This supports the numerical nonvanishing lead while
  showing degradation with radius. There are 31 negative and 33 positive
  cells and no computed common-weak-sign row, so the signed-row shortcut is
  still unavailable. The sampled spectral diagnostics are not P1, P2, or a
  KernelLine proof.

A separate all-row original-star profiling attempt at q=1,R=30 timed out and is
not used in any conclusion. All reported audits above have exit zero and peak
RSS below 2 GiB.

## 6. Goal status

`AdalyFormal.Round2.Guarded.Pin.GoalNeg2` has no posted inhabitant. The shortest
currently compiled routes are:

- `AreaSeedRightStar → AreaNonvanishing → P3 → GoalNeg2` (the first two
  arrows are now also compiled directly at the area level in assembly R2);
- `UnitAreaSeedRightStar → AreaNonvanishing → P3 → GoalNeg2`;
- `CofinalAreaSeedRightStar → CofinalP3 → GoalNeg2`;
- `CofinalLaurentAreaSeed → CofinalP3 → GoalNeg2`;
- `CofinalUnitDominantAreaSeed → CofinalP3 → GoalNeg2`.

Only the implications are proved. Their left-hand physical inputs remain the
exact missing statements above.

## 7. Path-variant audit

No path supplies a compiled P1+P2+P3 route. The R2 length-three candidate
`c2=-0.25,c3=-2.25` has a much smaller numerical cancellation ratio than the
R1 families, but it remains a numerical candidate only: no candidate-specific
Lean path definition, half-pi P1, P2, whole KernelLine, or detection theorem is
published. Assembly's independent q=2,R=30 replay found mixed signs and a
larger ratio `0.2966429803`; it does not close those prerequisites. Signed arms,
arm subsets, odd placements, and equal left/right double stars remain
unrecommended. The R1 compiled weighted-arm path proves validity, masking, the
exact `vacA` identity, and negative pi only; negative pi does not discharge the
half-pi P1 used by the crossing proof. The L3 numerical family is not that
four-arm `weightedStarPath` and must not be conflated with it.

For a signed coefficient function `c`, the exact additional prerequisites are
as follows. They are parameterized statements, not claims for any accepted
candidate. Open `AdalyFormal.Round14.PathChoice` and
`AdalyFormal.Round12.Noncancel.Path` in addition to the original opens.

Half-pi P1 is unproved:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ),
  (∀ e ∈ starLinks (periodicLatticeShift (rightSite hq R) 0),
    c e = 1 ∨ c e = -1) →
  ∃ w : TwistSpace q R,
    ⟪w, vacA q R (weightedRightStar hq R c) 1 (Real.pi/2) w⟫ < 0
```

P2 on the original central-charged-zero subspace is unproved:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ),
  (∀ e ∈ starLinks (periodicLatticeShift (rightSite hq R) 0),
    c e = 1 ∨ c e = -1) →
  ∀ (t : ℝ), 0 < t → t < Real.pi/2 →
  ∀ x : TwistSpace q R, x ≠ 0 →
    AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
      (rightSite hq R, (0 : Fin 3)) x = 0 →
    0 < ⟪x, vacA q R (weightedRightStar hq R c) 1 t x⟫
```

The whole-kernel line and real nullity two are unproved for the modified path:

```lean
∀ {q R : ℕ} (hq : 0 < q), 2 ∣ R → 18 ≤ R →
  ∀ (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ),
  (∀ e ∈ starLinks (periodicLatticeShift (rightSite hq R) 0),
    c e = 1 ∨ c e = -1) →
  0 < vacEdge q R (weightedRightStar hq R c) ∧
  vacEdge q R (weightedRightStar hq R c) < Real.pi/2 ∧
  ∃ u : TwistSpace q R, KernelLine q R (weightedRightStar hq R c) u ∧
    Module.finrank ℝ (vacA q R (weightedRightStar hq R c) 1
      (vacEdge q R (weightedRightStar hq R c))).ker = 2
```

Even after those prerequisites, modified-path P3 remains exactly:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ),
  (∀ e ∈ starLinks (periodicLatticeShift (rightSite hq R) 0),
    c e = 1 ∨ c e = -1) →
  ∀ u : TwistSpace q R,
    KernelLine q R (weightedRightStar hq R c) u → CurlDetected q R u
```

No instance of these statements is offered as a current alternative to the
original area seed.
