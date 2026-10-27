# Round 13 — exact remaining gaps (final assembly R2)

**P1 and P2 are CLOSED and integrated. The actual whole-kernel KernelLine,
real nullity two, and crossing in (0,pi/2) are proved, including nested cofinal
quantifiers. Only P3 remains as a physical input. GoalNeg2 remains OPEN.**

There is no unconditional `CurlDetected` theorem for these crossing generators,
`CofinalAnyPathCurlLine`, or `CofinalAnyPathNoResponseCancellation` inhabitant.
The entire conditional implication **P3 → GoalNeg2** is now compiled with P3 as
the single explicit hypothesis. The old missing-helper join is repaired, not a
current blocker.

## 1. Clean final assembly certificates

- **`assembly/R2_P2Goal.lean`** (11120 lines), byte-identical local
  `../assembly/r2/P2Goal.lean`: both exit 0, twelve standard dependency records
  each, with explicit `#check @...` types. This source contains the complete
  physical P1/P2 proofs, first crossing, whole-kernel line, response bridge,
  proved regularity, and round-9 pinned-goal bridge. Imports only frozen
  `DrEquiv` and `DrPath3`.
- `assembly/R2_PhysicalGoal.lean` (9626 lines): retained earlier R2 conditional
  `P2 → P3 → GoalNeg2` / `CofinalP2P3 → GoalNeg2`, local/shared exit 0.
- `assembly/R1_P1Spine.lean` (6150 lines): retained unconditional canonical
  crossing with a nonzero kernel vector, local/shared exit 0. R2 strengthens
  that result to the whole `KernelLine` and nullity two using proved P2.
- `../assembly/r1/RepairedJoin.lean` (16844 lines): the requested **single**
  BB-terminal compile already succeeded in R1, exit 0, 1186 standard records.
  R2 rechecks the source/log and exact helper insertion without rerunning it.
  Earlier round-10 sources and their historical failed logs are unchanged.

`../assembly/r2/AUDIT.json` verifies all six assembly compilation artifacts,
763 verbatim final-source declaration chunks, 18 exact original interfaces,
final elaborated theorem types, publication identity, and fourteen current
sibling publications. All printed axioms are subsets of
`{propext, Classical.choice, Quot.sound}`. Assembly executions are builder and
publication checks, not a claimed independent reviewer acceptance.

## 2. Original physical statements and current status

Namespace openings for all statements below:

```lean
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round12.Noncancel.RightFamily (rightStar)
```

### P1 — CLOSED, independently accepted

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ w : TwistSpace q R,
    ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0
```

`AdalyFormal.Round13.Trial.rightStar_negative_halfpi`,
`trial/R1_Trial.lean:2180`. Exact physical six-bond energy is `-1/4`, not a
surrogate polynomial. Independent acceptance is in `../trial/r1/Trial.VERIFY.md`.
R2 trial supplies the combined cofinal path/half-pi handoff and exact trial
Rayleigh quotient `-4/21`; the latter is not a crossing eigenvalue. Assembly
rechecks the P1 proof inside the final complete join.

### P2 — CLOSED, builder/publication and assembly-integration checked

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (t : ℝ), 0 < t → t < Real.pi/2 →
  ∀ x : TwistSpace q R, x ≠ 0 →
    AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
      (rightSite hq R, (0 : Fin 3)) x = 0 →
    0 < ⟪x, vacA q R (rightStar hq R) 1 t x⟫
```

`AdalyFormal.Round13.Positivity.Physical.rightStar_P2`,
`positivity/R2_P2.lean:3490`, with nested cofinal theorem at :3502. All local/shared
P2 and geometry compiles exit 0 with standard dependencies. There is no omitted
sum, inverse-unit, positivity, simplicity, or numerical hypothesis.

The formerly open raw omitted-sum inequality is now proved by
`rightStar_raw_omitted_loss` (:2395): the four distinct actual star arms are paid
by exactly eight distinct physical leaf masses; every other omitted plaquette
is flat or has zero input even when its holonomy is curved. Central neutral
coordinates are retained. Consequently the actual full carrier dominates
`cos(t)` times the genuine strictly positive flat localized carrier on this
subspace. `rightStar_prefix_lower` (:3460) gives a positive scale/radius-independent
relative factor on every closed strict half-pi prefix. No strict endpoint
positivity or uniform ordinary-norm spectral gap is claimed.

### P3 — OPEN, the only remaining physical assertion

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

This remains exactly `AdalyFormal.Round13.Assembly.R1.P3`. The KernelLine premise
now has an actual witness at every admissible pair, but the detection conclusion
is not proved. Chargedness, a nonzero central trace, and nullity two do not imply
this quadratic noncancellation.

## 3. New unconditional whole-kernel theorem

`AdalyFormal.Round13.Assembly.R2.rightStar_kernelLine`,
`assembly/R2_P2Goal.lean:11050`, proves:

```lean
∀ {q R : ℕ} (hq : 0 < q), 2 ∣ R → 18 ≤ R →
  0 < vacEdge q R (rightStar hq R) ∧
  vacEdge q R (rightStar hq R) < Real.pi/2 ∧
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
    Module.finrank ℝ (vacA q R (rightStar hq R) 1
      (vacEdge q R (rightStar hq R))).ker = 2
```

The original first-crossing theorem consumes proved P1/P2, actual continuity and
full positive start, and the right-star quarter gauge. No isolation, selected
character, kernel witness, or detection hypothesis is present. The source/log
explicitly prints the full elaborated type.

`cofinal_rightStar_kernelLine` (:11061) provides the same result with
`∀ j₀, ∃ j≥j₀, ∀ R₀, ∃ R≥R₀`, even R≥18, at q=2^j. This is **not** a cofinal
curl-line theorem, since its detection conjunct is still missing.

## 4. Complete conditional response and pinned-goal reductions

Namespace `AdalyFormal.Round13.Assembly.R2`, final source:

```lean
-- :11075
theorem cofinalNoCancellation_of_P3 (h3 : P3) :
  AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation

-- :11077
theorem goalNeg2_of_P3 (h3 : P3) : AdalyFormal.Round2.Guarded.Pin.GoalNeg2

-- :11089
theorem cofinalNoCancellation_of_cofinalP3 (h : CofinalP3) :
  AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation

-- :11093
theorem goalNeg2_of_cofinalP3 (h : CofinalP3) :
  AdalyFormal.Round2.Guarded.Pin.GoalNeg2
```

Each displayed assumption remains an assumption. `#check @...` verifies no
other hypotheses. All four declarations print exactly
`[propext, Classical.choice, Quot.sound]`. The path, scale, radius, canonical edge
and generator are kept identical throughout the round-12 response arrow and
round-9/10 final-goal bridges. The all-plaquette pin and sole carrier guard are
unchanged. In particular, a proved P3 plugs directly into `goalNeg2_of_P3`.

The exact weaker sufficient `CofinalP3` (:11078), still OPEN, is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∀ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u → CurlDetected (2^j) R u
```

The stronger all-instance P1/P2 apply at whichever same indices this premise
selects. No intersection of separately chosen cofinal subsequences is used.
The original sufficient existential detected-line family remains OPEN too:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    CurlDetected (2^j) R u
```

The line conjunct alone is now proved. No finite sample supplies detection with
these unbounded nested quantifiers.

## 5. Detection R2 sharpens, but does not close, P3

Detection's full flat N-unit and the physical top-jet-to-curl handoff are proved.
Thus actual `TopJetDetected hq R u` suffices without an extra inverse guard.
`detection/R2_PhysicalArea.lean` (4436 lines, local/shared exit 0) additionally
proves for the original crossing generator:

```lean
physicalJetAggregate hq hj u = (1 / 2 : ℝ) * areaSum hq hj u
```

Its `crossing_topJet_iff_area` and `crossing_curlDetected_of_area` retain the
nonzero-area premise. With the `PhysicalArea` and original `DilatedFlux` opens,
the exact sufficient **unproved** all-instance remainder is:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

An exact nested sufficient version, also OPEN, is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    ∃ k : ℕ, ∃ hk : k < blockCount (2^j) R,
      areaSum (by positivity : 0 < 2^j) hk u ≠ 0
```

The area coefficients use the genuine masked carrier atoms and full interior
W/C2, not a guessed local stencil. The weighted determinant sum may cancel;
nonzero linear traces or one nonzero determinant do not settle its nonvanishing.
The exact dictionary is a compiled identity, not a P3 proof. All sibling R1/R2
NOTES were read before this final status update.
