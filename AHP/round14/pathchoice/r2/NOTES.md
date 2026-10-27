# Round 14 path choice R2 — a common-sign long-arm candidate, still conditional

## Verdict

**The original P3, CofinalP3 and GoalNeg2 remain OPEN.** The modified path's
negative-`pi` endpoint is now proved.  Its crossing positivity, whole kernel
line, and area seed are still not proved.

This round nevertheless finds a genuinely new candidate.  A three-level
transverse-arm path with coefficients `1`, `-1/4`, and `-9/4` has a
**common-sign physical top row** in the numerical experiments at `q=4`.
All 256 direction-1 cells are positive at `R=18` (also checked at 110 digits)
and at `R=20` (double precision).  This is a large structural improvement over
round 1, where every tested family had mixed signs and no dominant regime.

The Lean work proves the path infrastructure and two conditional reductions:
crossing positivity alone gives the complete charged kernel line, and an
area-detected generator gives universal/cofinal detection on that line.  The
negative-`pi` endpoint is unconditional; the other physical inputs remain open.

## Compiled artifacts

| Local source | Byte-identical shared publication | Lines | Exit each | Log status |
|---|---|---:|---:|---|
| `AHP/round14/pathchoice/r2/LongArm.lean` | `AHP/round14/shared/pathchoice/R2_LongArm.lean` | 5479 | 0 | 376 permitted records; 52 path-choice + 7 support records |
| `AHP/round14/pathchoice/r2/LongCrossing.lean` | `AHP/round14/shared/pathchoice/R2_LongCrossing.lean` | 11651 | 0 | 30 permitted records; 18 new crossing records |

Both publications were compiled separately with only
`AHP/round3/lean1.sh <file>`.  Every final log has zero warnings, zero errors,
and no `sorryAx`.  Every printed axiom set is a subset of
`{propext, Classical.choice, Quot.sound}`.  The sources contain no forbidden
proof mechanism.  `AUDIT.json` and `audit.py` check these facts, source identity,
hashes, and the numerical controls below.  These are builder/publication
executions, not independent mathematical review.

`LongArm.lean` reuses the compact transfer generator and appends the new path
and detection declarations.  `LongCrossing.lean` reuses the integrated round-13
crossing source, with only lint-option additions and the semantics-neutral
`push_neg` to `push Not` update.  No AHP file is imported as a Lean module.

### Path definitions

For every site `x`, `longStarLinks x N` contains the transverse bonds on the
two arms through level `N-1`.  Level zero is the original four-bond star; each
new level adds four bonds.  The candidate is exactly:

```lean
def tailCoeff (x : PeriodicLatticeSite L) (e : Bond L) : ℝ :=
  if e ∈ longStarLinks x 1 then 1
  else if e ∈ longStarLinks x 2 then -(1/4 : ℝ)
  else if e ∈ longStarLinks x 3 then -(9/4 : ℝ)
  else 0

def tailPath (x : PeriodicLatticeSite L) : ℝ → Cfg L :=
  longStarPath x 3 (tailCoeff x)

def tailRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  tailPath (periodicLatticeShift (rightSite hq R) 0)
```

The file proves exterior support in the actual `Zb`, zero/continuity/analyticity,
exterior masking, the exact `pathU`, `dilU`, and `vacA` identities, and invariance
under every constant diagonal gauge rotation.  The coefficient evaluation
lemmas identify the three levels precisely.

### Unconditional start facts

```lean
AdalyFormal.Round14.PathChoice.tailRightStar_vacA_cont
AdalyFormal.Round14.PathChoice.tailRightStar_vacA_pd_zero
```

These prove, respectively, continuity of the actual tail-path carrier and
strict positivity at angle zero.  They are not spectral statements at the
crossing.

### Conditional whole-kernel package

The main crossing theorem is now:

```lean
AdalyFormal.Round14.PathChoice.tailKernelLinePackage_of_crossingPositive :
  TailCrossingPositive → TailKernelLinePackage
```

The negative-`pi` endpoint is discharged by `tailEndpointNegative`.  Only
zero-coordinate positivity at the canonical crossing remains as a hypothesis,
not the stronger full-half-interval P2.  The conclusion is `0 < vacEdge < pi`,
a whole charged `KernelLine` generator, and real nullity two.  The more general
`tailKernelLinePackage_of_inputs` is also compiled.

### Conditional detection reductions

```lean
AdalyFormal.Round14.PathChoice.tailP3_of_areaSeed :
  TailAreaSeed → TailP3

AdalyFormal.Round14.PathChoice.cofinalTailP3_of_areaSeed :
  CofinalTailAreaSeed → CofinalTailP3
```

One nonzero physical `areaSum` on one whole-line generator detects every vector
on that charged line, using the already compiled response scaling and the
actual flat-unit/top-jet bridge.  The universal and nested quantifiers are not
interchanged.  These theorems do not prove the area seed or the original P3.

## Exact statements still missing

### Original right-star P3 — unchanged and unproved

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

The original nested alternative is also open:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∀ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u →
      CurlDetected (2^j) R u
```

The original sufficient area remainder remains:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

### Modified-path endpoint input — CLOSED

`AdalyFormal.Round14.PathChoice.tailEndpointNegative` proves the exact
compiled predicate:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ w : TwistSpace q R,
    ⟪w, vacA q R (tailRightStar hq R) 1 Real.pi w⟫ < 0
```

The proof uses the original central axial-bond trial.  Added arm levels do not
change the four plaquettes entering its local energy: original-arm and interior
identities give the same exact negative contribution as in the round-12 proof.
This is not a numerical inference.  Its supporting declarations
`tailPath_negative_endpoint` and `tailRightStar_negative_pi` also have clean
standard-axiom records.

### Modified-path crossing positivity — unproved

This is the exact compiled predicate `TailCrossingPositive`:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (x : TwistSpace q R), x ≠ 0 →
  AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
    (rightSite hq R, (0 : Fin 3)) x = 0 →
  0 < ⟪x, vacA q R (tailRightStar hq R) 1
    (vacEdge q R (tailRightStar hq R)) x⟫
```

At the numerical crossing the third-arm angle is about `-2.544`, beyond
`pi/2`, so its cosine is negative.  The original cosine-positive mass
absorption proof therefore does not routinely transfer.  The sampled positive
margin is evidence only.

Consequently `TailKernelLinePackage` itself remains unproved:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  0 < vacEdge q R (tailRightStar hq R) ∧
  vacEdge q R (tailRightStar hq R) < Real.pi ∧
  ∃ u : TwistSpace q R, KernelLine q R (tailRightStar hq R) u ∧
    Module.finrank ℝ (vacA q R (tailRightStar hq R) 1
      (vacEdge q R (tailRightStar hq R))).ker = 2
```

### Modified-path area seed — unproved

The exact compiled predicate `TailAreaSeed` is:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ u : TwistSpace q R, KernelLine q R (tailRightStar hq R) u ∧
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

`TailP3` therefore also remains open:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (tailRightStar hq R) u →
    CurlDetected q R u
```

The exact nested input `CofinalTailAreaSeed` is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (tailRightStar (by positivity) R) u ∧
    ∃ k : ℕ, ∃ hk : k < blockCount (2^j) R,
      areaSum (by positivity : 0 < 2^j) hk u ≠ 0
```

`CofinalTailP3` is the same nested form with `tailRightStar` in place of
`rightStar`.  Neither is inhabited here.  No response-hull or pinned-goal
inhabitant is claimed from these conditional reductions.

## Numerical evidence, never a proof premise

All screens use the full all-character flat augmented operator before Schur
restriction, the genuine four-edge local Hessian algebra, and exact Taylor
`rawjet` reconstruction.  Schur spectra are not full-carrier spectra.  Roots
and spectral margins in the JSON are double-precision diagnostics, not
interval enclosures or Lean facts.  High-precision runs replay the dressed
solve from the same double-precision drive; they do not independently certify
the root.

### q=4: common sign at two radii

For the exact coefficient family above:

- `q=4,R=18`, right row `j=303`, 110 digits:
  - all **256** direction-1 cells are strictly positive and none is zero;
  - sum `3.8636783516663492e-129`;
  - `max |cell| / |sum| = 0.00604231654413030`;
  - `|sum| / l1 = 1` to displayed precision;
  - residual `1.90217e-106`;
  - double-drive root `1.1308445374655998`, next charged value `0.27958754`;
  - central-zero diagnostics at zero/root/half-pi are
    `1.3667858`, `0.26234635`, `0.13318316`;
  - neutral minimum at the crossing is `0.69158711`.
- `q=4,R=20`, double precision: again all 256 cells are positive;
  the direction-1 ratio is `0.00579853366313165`.

By comparison, the original star at `q=4,R=18` has 117 negative direction-1
cells.  Thus the modified path, not merely the increased character count, is
responsible for the common-sign result.  A 54-variant coefficient sweep at
`q=4,R=18` found this exact common-sign family only once, so no simpler
cosine-positive alternative is claimed.

### q=2: strong but not exactly common-sign

- `q=2,R=20`, 110 digits, right row `j=167`:
  - 62 positive and two negative cells;
  - ratio `0.04109643939296284`;
  - `|sum| / l1 = 0.999582572218818`;
  - residual `1.68509e-106`.
- `q=2,R=22`, double precision: ratio `0.05515236589513498`, with positive
  sampled central-zero and charged margins.

The 110-digit row sweep found no exactly common-sign row, but the right row
has the best `l1` ratio and the adjacent row has a slightly smaller max/sum
ratio.  Detection permits any row; no row is promoted to a Lean certificate.

### q=1: no uniform all-q claim

At `q=1,R=20`, the same coefficients improve the original direction-1 ratio
from about 300 to `37.1400873`, but this remains heavy cancellation.  There is
no all-q common-sign assertion.  The dyadic cofinal sequence uses `q=2^j`, but
even the favorable `q=4` samples do not prove a result at every dyadic scale or
cofinally many radii.

### Other controls

The length-two alternating control reproduces round 1.  The new same-side
transverse double-star family does not improve cancellation: equal strength
has ratios about `1.756` and `2.310`, and unequal strength reverts to one-sided
behavior.  It is not recommended for further work.

## Reproduction and scope

```sh
python3 AHP/round14/pathchoice/r2/build_longarm.py
python3 AHP/round14/pathchoice/r2/build_longcrossing.py
AHP/round3/lean1.sh AHP/round14/pathchoice/r2/LongArm.lean
AHP/round3/lean1.sh AHP/round14/shared/pathchoice/R2_LongArm.lean
AHP/round3/lean1.sh AHP/round14/pathchoice/r2/LongCrossing.lean
AHP/round3/lean1.sh AHP/round14/shared/pathchoice/R2_LongCrossing.lean
python3 AHP/round14/pathchoice/r2/audit.py
```

Numerical drivers are `screen_cluster.py`, `screen_longer.py`,
`screen_tail_sweep.py`, `screen_tail_targeted.py`, `screen_tail_instance.py`,
`screen_tail_q4_sweep.py`, and `verify_tail_mp.py`.  Their successful logs,
JSON data, and zero exit files are retained.  The final high-precision replay
stores only the required right-row dressed values, avoiding the earlier memory
failure; no result from that failed run is used.

Only `AHP/round14/pathchoice/r2/` and `AHP/round14/shared/pathchoice/` were
written.  No earlier round, frozen module, lakefile, integration checkout,
commit, or push was changed.  No `lake build`, `REPRODUCE.sh`, or deletion was
run.
