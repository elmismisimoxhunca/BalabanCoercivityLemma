# Noncancel R2 — physical collar, full-color atoms, leaf mass, right-star family

## Verdict

**OPEN, not disproved.** No theorem of
`AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation`, no
unconditional instance of crossing `KernelLine`, and no crossing-specific
`CurlDetected` has been proved by this track. Consequently this is **not** a
proof of `GoalNeg2`. Conditional kernel criteria remain conditional.

R2 supplies 33 new independently checked declarations plus two copied geometry
certificates. The compact joined harness `Attempt.lean` is 1372 lines, imports
only frozen `DrEquiv`, exits 0, and has 78 printed dependency records, each a
subset of `propext`, `Classical.choice`, `Quot.sound`. Its independent shared
copy also exits 0. See `AUDIT.json` for hashes, declarations, and all ten
local/shared compilation results.

## Compiled deliveries

| Local certificate | Independently compiled shared certificate | New content |
|---|---|---|
| `Boundary.lean` | `AHP/round12/shared/noncancel/R2_Boundary.lean` | Six actual support/dressing lemmas |
| `FullPlaquette.lean` | `AHP/round12/shared/noncancel/R2_FullPlaquette.lean` | Eleven full-color local declarations |
| `Mass.lean` | `AHP/round12/shared/noncancel/R2_Mass.lean` | Six actual row-zero/mass declarations |
| `RightFamily.lean` | `AHP/round12/shared/noncancel/R2_RightFamily.lean` | Ten right-star/canonical-family declarations |
| `Attempt.lean` | `AHP/round12/shared/noncancel/R2_StarLocal.lean` | All four packages together |

Each listed file has its own `.lean.log` and `.lean.exit=0`. These are compact
source certificates, not importable `.olean` modules. The joined certificate
avoids duplicate namespaces from separately copied historical harnesses.

### 1. Actual boundary dressing — no inverse-unit assumption

Namespace `AdalyFormal.Round12.Noncancel.Boundary`:

- `potential_zero_off_om1`: `Gp ... (Rproj ... f)` vanishes outside `S.Om 1`.
- `Wop_eq_on_collar`: for **every** field `A`, `(Wop ... A) e = A e` when
  neither endpoint of `e` belongs to `S.Om 1`.
- `Wop_eq_on_omitted`: under `Admissible ell M R k S` and `4 ≤ R*M`, the
  preceding identity holds on **every edge** of every
  `p ∉ plaqIn (S.Om 0)`.
- `gradAdj_sing_support`: any-orientation single-bond divergence is supported
  at the endpoints.
- `Tfull_sing_zero_near`, `Wop_sing_near`: an exterior site within distance
  `d` of both endpoints, with `d+1 ≤ R*M`, kills `T` and makes `W` the identity
  on the single-bond field.

This removes a physical identification gap for arbitrary carrier fields. It
is stronger than a unit-conditional boundary-dressing lemma and does not
require assembling the historical flat inverse.

### 2. Neutral coordinates are not discarded

Namespace `AdalyFormal.Round12.Noncancel.FullPlaquette`:

`lieMat h z = !![(h:ℂ)*I,z; -star z,-(h:ℂ)*I]` represents **every** `SuTwo`,
with `h = Im X₀₀` and `z = X₀₁`. The actual squared inner product is
`Complex.normSq z + h^2` (`lieMat_coordinates`, `full_inner`).

`frozen_full_three_right` and `frozen_full_three_left` are identities for the
FROZEN `curlValueCovariant` and `bilPlaq`. Subject to their explicitly stated
atom and holonomy equalities, the form is

`tripleForm c s x y z + c*(h+k+l)^2`.

The right ordering is `(a1,a2,a3,a4)=(X,Y,Z,0)`; the left ordering is
`(X,0,Y,Z)`. No reflection identification is claimed. The mixed
neutral/charged terms vanish in the computed local algebra.

`full_pair_mass_lower` proves, for `0 ≤ c ≤ 1` and `c²+s²=1`,

`c*(normSq y+k² + normSq z+l²)`
`  ≤ normSq y+k² + normSq z+l² + pairForm c s y z + c*(h+k+l)²`.

`full_star_mass_lower` sums this estimate over any finite family with a
nonnegative remainder. **It is not a whole-carrier decomposition theorem.**
The charged central coordinate may vanish while its neutral coordinate does
not; the neutral square above is essential.

### 3. Physical leaf masses

Namespace `AdalyFormal.Round12.Noncancel.Mass`:

- `rowZero`, `Qfull_rowZero`: the true level-zero row of `QfullOf` reads `A e`.
- `collar_levelZero`: any touching bond whose endpoints avoid `S.Om 1` is a
  true level-zero row (admissibility and positive block scale required).
- `leaf_mass_le`, `carrier_leaf_mass_le`: for any finite set of **distinct**
  such bonds and `0 ≤ a`, the actual mass dominates
  `a * ∑ e ∈ leaves, ‖A e‖²`.
- `mass_split`: the exact physical mass equals that sum plus a nonnegative
  remainder.

The finite-set formulation forbids reusing a mass by listing one leaf twice.
What is still missing is the eight-leaf geometry/injectivity and matching of
those rows to all four curved plaquettes, together with a strictly positive
remaining form. A nonnegative mass remainder alone is insufficient.

### 4. One cofinal right-star family, with actual canonical equality

Namespace `AdalyFormal.Round12.Noncancel.RightFamily`:

`rightStar hq R = starPath (periodicLatticeShift (rightSite hq R) 0)`.

The historical `dilLu`, `dilTower`, `dilLam`, `dilU`, `maskedU`, `pathU`,
`pathP`, `pathA`, `vacA`, `rightSite` and required geometry proofs are copied
verbatim. `FAMILY_COPIES.json` records source spans/hashes.

- `rightStar_zero`, `rightStar_cont`, `rightStar_an` prove all path clauses.
- `rightStar_off_exterior`, `pathU_rightStar`, `dilU_rightStar` prove the
  exterior masking is exactly transparent, not numerically approximated.
- `vacA_rightStar` identifies the original vacuum carrier with the frozen
  all-plaquette carrier at this precise star background.
- `rightStar_negative` proves a negative direction at `π` for **every**
  `q>0`, even `R≥18`, with `a=1`.
- `cofinal_rightStar_paths` proves the full nested dyadic/even quantifiers
  and every path-validity clause of the requested target, **with the final
  `NoResponseCancellation` conjunct deliberately absent**.

The last theorem is not sufficient for the requested conclusion. It closes
path validity and the previous left/right endpoint mismatch only.

## Exact remaining propositions

The following are **unproved Lean statements**, not new assumptions or
certificates. Names use the original namespaces, opened as follows:

```lean
open scoped RealInnerProductSpace
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Assembly.R4 (NoResponseCancellation)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round12.Kernel.Actual (chargedCoordinate)
open AdalyFormal.Round12.Noncancel.RightFamily (rightStar)
```

### A. Direct sufficient remainder for our now-valid family

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  NoResponseCancellation (2^j) R (rightStar (by positivity) R)
```

`cofinal_rightStar_paths` discharges the other original target conjuncts.
This direct remainder concerns the entire kernel and cannot be replaced by
individual nonzero responses unless cancellation is separately excluded.

### B. Proposed one-line route, also still unproved

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    CurlDetected (2^j) R u
```

Both conjuncts still need actual witnesses. Kernel R2 has now independently
compiled `shared/kernel/R2_ResponseLine.lean`: its
`ResponseActual.noCancellation_iff_curlDetected_of_kernelLine` and
`cofinal_noCancellation_of_curlLine` give a DIRECT bridge, without
`RegularityFacts`. I checked the shared exit=0 and all 150 printed axiom
records; none is nonstandard. This does not discharge either physical
conjunct above and does not certify the old large assembly.

### C. Concrete physical estimates proposed to establish the line

The anticipated first-crossing-range theorem is:

```lean
∀ (q R : ℕ) (hq : 0 < q), 2 ∣ R → 18 ≤ R →
  vacEdge q R (rightStar hq R) < Real.pi / 2
```

The needed strict boundary-zero positivity at the actual crossing is:

```lean
∀ (q R : ℕ) (hq : 0 < q), 2 ∣ R → 18 ≤ R →
  ∀ u : TwistSpace q R, u ≠ 0 →
    chargedCoordinate q R (rightSite hq R, 0) u = 0 →
    0 < ⟪u, vacA q R (rightStar hq R) 1
      (vacEdge q R (rightStar hq R)) u⟫
```

A stronger useful intermediate assertion replaces the crossing by every
`t ∈ Set.Ioo 0 (Real.pi/2)`. This track proves neither version. The local lower
bounds and physical mass extraction do not prove strict positivity of the
remaining full carrier form.

Kernel R2's newly compiled `shared/kernel/R2_FirstCrossing.lean`, theorem
`CrossingActual.kernelLine_exists_before_halfpi`, now constructs the actual
crossing vector and complete `KernelLine`; no isolated-root input is needed.
Its explicit premises are operator continuity, symmetry, strict positivity at
zero, quarter-gauge invariance of the path, the above interval positivity,
and the physical half-pi trial:

```lean
∀ (q R : ℕ) (hq : 0 < q), 2 ∣ R → 18 ≤ R →
  ∃ w : TwistSpace q R,
    ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0
```

The two physical interval/half-pi premises remain unproved. The pi-negative
endpoint in our `rightStar_negative` is not a substitute. I checked the shared
first-crossing exit=0 and all 111 printed axiom records; none is nonstandard.

### D. Detection must use the actual crossing vector

Even after a line generator has been constructed, the missing assertion is:

```lean
∀ (q R : ℕ) (hq : 0 < q), 2 ∣ R → 18 ≤ R →
  ∀ u : TwistSpace q R,
    KernelLine q R (rightStar hq R) u → CurlDetected q R u
```

The weaker `TopJetDetected` route still needs its true crossing-specific
quadratic jet and the flat `N`-unit hypothesis of `curlDetected_of_topJet`.
Chargedness alone does not supply either. `exists_charged_invisible` remains
an obstruction to that shortcut, not a crossing counterexample.

## Reproduction and limitations

```bash
python3 AHP/round12/noncancel/r2/build.py --publish
# Run sequentially (or coordinate at most two Lean jobs globally):
systemd-run --user --scope --quiet -p MemoryMax=8G -p MemorySwapMax=0 -- \
  bb heavy run -- AHP/round3/lean1.sh AHP/round12/noncancel/r2/Attempt.lean
systemd-run --user --scope --quiet -p MemoryMax=8G -p MemorySwapMax=0 -- \
  bb heavy run -- AHP/round3/lean1.sh AHP/round12/shared/noncancel/R2_StarLocal.lean
python3 AHP/round12/noncancel/r2/audit.py
```

The audit additionally expects the separately compiled local/shared component
logs already delivered. No new numerical claims are made in this round; R1
spectral/top-jet computations remain evidence only. No large round-9 or
round-10 assembly was compiled. No `lake build` or `REPRODUCE.sh` was run. All
writes by this track are under its R2 directory or `shared/noncancel/`.
No goal/axiom placeholders are introduced into any source certificate.

## Late kernel-track evidence: concrete half-pi trial

After this track submitted its workflow result, kernel R2 supplied
`AHP/round12/kernel/r2/TRIAL_CHECKS.json` and `trial_crosscheck.py`. I inspected
both; I did not rerun the computation. The reported 130-digit checks use
`(q,R)=(2,20),(4,22),(8,24)` and the same RIGHT star. At `t=π/2`, in charged
coordinates, the proposed trial has:

- central normal bond `(rightSite,0)` equal to `1`;
- normal bonds displaced by `+e_d` equal to `-i/4`, and by `-e_d` equal to
  `+i/4`, for `d=1,2`;
- tangential bond `(rightSite,1)` equal to `-i/4`.

The local stencil has six supported bonds and nineteen touched plaquettes.
Reported contributions are mass `21/16`, untwisted plaquettes `15/16`, and
four curved star plaquettes `-5/2`, summing to `-1/4`. Removing the tangential
bond gives five bonds/sixteen plaquettes and contributions `5/4`, `3/4`,
`-2`, summing to zero. All listed endpoints avoid `Omega1`.

This is a useful finite trial candidate, **not a certificate of the actual
carrier energy**. The script enumerates an integer-coordinate local stencil,
not the periodic frozen Lean operator, and uses unit-weight local mass.
The periodic embedding/no-collision argument, higher-level mass exclusion,
finite plaquette enumeration, and frozen-operator identification still need
proof. Our generic collar lemmas help with `W=id` and `T=0`; lower mass
extraction alone cannot prove the trial's required upper/equal mass estimate.
The formal half-pi premise and the overall verdict therefore remain OPEN.
