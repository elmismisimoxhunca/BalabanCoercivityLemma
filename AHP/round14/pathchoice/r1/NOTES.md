# Round 14 path choice R1 — no easier detected path found

## Verdict

**P3, CofinalP3 and GoalNeg2 remain OPEN.** This round did not prove detection
for the original right star or for any modified star. It did not re-establish
the half-pi P1 input, P2, or the whole-kernel line for a modified path.

The numerical screens found no family with a dominant cell or a common cell
sign. The only modest improvement is a length-two alternating-arm family. Its
best tangential `max |cell| / |sum|` ratio is about **1.49351**, versus 1.62841
for the original star. This is only an 8.3% reduction, and its sampled
central-zero spectral margin is much smaller. It does **not** meet the requested
“no heavy cancellation” design criterion and is not promoted to a Lean P1/P2 or
kernel-line candidate.

A compact Lean artifact instead supplies reusable **weighted-arm path
infrastructure**. It proves validity, exterior masking, the exact original
`vacA` identity, and the old negative-pi endpoint for every signed-arm family.
The negative-pi result is strictly weaker than the half-pi P1 used in round 13;
it is not a crossing or P3 proof.

## Numerical evidence, not proof

All new screens use the full all-character flat augmented operator before Schur
restriction, the genuine four-edge local Hessian algebra, and the exact Taylor
`rawjet` reconstruction. They use `q=2, R=20` unless stated otherwise. Schur
spectra are not full-carrier spectra. “Candidate” in a JSON file is only a
screening label based on a sign-changing root, numerical gaps, and three sampled
central-zero restrictions. It is not a spectral enclosure or a proof of P1, P2,
`KernelLine`, or cofinality. No floating-point nonzero value is a Lean
certificate.

The original-star control in `shifts_q2_R20.json` has root relative error
`1.29e-15` against the retained 155-digit run. Its three cell ratios and three
jet sums agree with that run to better than `1e-9` relative. `AUDIT.json`
checks this and all controls below.

### 1. Signed arms, arm subsets, and real arm coefficients

Files: `signed_q2_R20_all.json`, `signed_q2_R20_subsets.json`, and
`signed_q2_R20_coefficients.json`; drivers `screen_signed.py` and
`screen_coefficients.py`.

- All 16 sign choices retain a numerically simple first crossing below half pi,
  but none improves the best tangential cancellation ratio. In particular the
  alternating `(+,-,+,-)` “site-gauge” choice has ratios about
  `3.59e9, 3.83e9, 8.52e9` and jets around `1e-90`, much worse than the
  original `1e-75` tangential scale.
- The best arm subset is `(1,0,1,0)`, with root `1.49530479533` and ratios
  `27.4772, 1.58367555, 1.58431530`. Its half-pi lowest Schur value is only
  `-0.0955059`, compared with `-1.06071934` for the original star.
- The broader 112-variant real-coefficient grid does not improve that best
  worst-tangential ratio. The best single tangential direction in the grid is
  still about 1.575, not close to a dominant-cell regime.

Thus the new weighted-star Lean infrastructure is reusable, but this numerical
class gives no reason to spend round 2 reproving P1/P2 for one of these paths.

### 2. Longer exterior arms

Files: `long_q2_R20_L2_extensions.json` and
`long_q2_R20_L2_second_coeffs.json`; drivers `screen_long.py` and
`screen_long_coefficients.py`.

Each added segment is an actual transverse bond in `Zb Omega0`. The enlarged
flat patch reproduces the original root and all three original cell ratios as a
control. Absolute jet magnitudes on an enlarged patch use a different numerical
kernel-vector normalization and must not be compared as physical normalized
amplitudes.

The best symmetric family has angle `+t` on each original arm segment and `-t`
on each of the four added length-two segments (`all_-1.0`):

| Quantity | Numerical value |
|---|---:|
| root | 1.07856980282654 |
| half-pi lowest Schur value | -1.3365 |
| next charged Schur value at root | 0.7205457 |
| ratios, directions 0/1/2 | 27.0647457, 1.49338884, 1.49350962 |
| minimum sampled central-zero diagnostic | 0.0921277 |

The last row is only the minimum at angles `0, root, pi/2`; it is not a P2
proof or even a full sampled interval check. The other 202 second-segment
variants give no dominant-cell alternative. The best one-direction ratio is
about 1.479, with the other tangential direction about 1.68.

`verify_long_mp.py` independently repeats the dressed solves and raw-cell
reconstruction at **110 decimal digits**, using the same double-precision Schur
drive. It gives ratios

```text
27.0647456995809676
1.49338883599268080
1.49350961681847676
```

with flat-solve residual `7.7813e-107`. Tangential sums agree with the double
run to about `2.3e-12` relative. The root is **not** independently replayed at
high precision. This validates response/cell stability only, not P1/P2,
`KernelLine`, nonvanishing, or cofinality.

### 3. Fine transverse placement

Files: `shifts_q2_R20.json` and `screen_shift.py`.

The original star, crossing vector, and drive are translated by fine transverse
shifts. Even shifts are exact numerical permutation controls: their aggregate
sums, maxima, and ratios coincide with the unshifted run (`AUDIT.json` reports
zero error). Odd shifts are genuinely different because the physical `topIdx`
cells have even transverse coordinates.

Every odd parity is worse for the tangential observable. The best odd result is
shift `(0,1)`, direction 1, ratio `1.97438538`; the original best is
`1.62827661`. The doubly odd shift `(1,1)` has tangential ratios about 2.57.
No placement improvement was found.

### 4. Left/right double star

Files: `double_q2_R20.json` and `screen_double.py`.

The screen uses the union of the two nine-bond boundary patches. With equal
left/right strength, the second charged eigenvalue at the first crossing is
numerically about `1.53e-14`; this is not a numerically simple kernel and is
rejected for the `KernelLine` route. With unequal strengths, the first crossing
selects one side and the observed response is the unchanged one-sided response,
not a useful hybrid.

The double-star script evaluates the common right physical top row. Its tiny
left-star values at that distant row are not a claim about the separate left
row. They are irrelevant to the conclusion that the tested left/right coupling
did not improve the common-row response.

## Compiled Lean artifact

| Local | Published shared copy | Lines | Exit each | New axiom records each |
|---|---|---:|---:|---:|
| `AHP/round14/pathchoice/r1/PathChoice.lean` | `AHP/round14/shared/pathchoice/R1_WeightedStar.lean` | 864 | 0 | 16 |

The sources are byte-identical, SHA-256
`672250dab629a34f6f5f058b84e8b18d2372126cd0b81eee6160593fe7a28748`.
They import only frozen `DrEquiv`. The first 693 lines are copied verbatim from
round-13 `shared/trial/R1_Trial.lean`; the appended definitions and proofs are
in namespace `AdalyFormal.Round14.PathChoice`.

For `c : Bond L -> ℝ`, the new path is

```lean
def weightedStarPath (x : PeriodicLatticeSite L) (c : Bond L → ℝ) (t : ℝ) : Cfg L :=
  fun e => if e ∈ starLinks x then uθ (c e * t) else 1
```

The file proves:

- `weightedStarPath_zero`, `weightedStarPath_cont`, `weightedStarPath_an`;
- `weightedStarPath_off_exterior` and its right-placed specialization;
- `pathU_weightedRightStar`, `dilU_weightedRightStar`, and
  `vacA_weightedRightStar`, so the original masking and vacuum carrier apply
  exactly, not merely up to a numerical stencil;
- `weightedStarPath_pi_of_sign`: if every arm coefficient is `1` or `-1`, the
  weighted and original star configurations agree at `pi`;
- `weightedRightStar_negative_pi`, with exactly the following elaborated
  conclusion after its sign hypothesis:

```lean
∃ w, ⟪w, vacA q R (weightedRightStar hq R c) 1 Real.pi w⟫ < 0
```

Every new `#print axioms` record is a subset of
`{propext, Classical.choice, Quot.sound}`. There are no errors, warnings,
`admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`,
or `opaque` declarations in the source. The audit checks both executions and
source identity. These are builder/publication checks, not independent review.

**No theorem in this file asserts half-pi negativity, P2, a crossing,
`KernelLine`, `CurlDetected`, nonzero `areaSum`, CofinalP3, or GoalNeg2.**

## Exact remaining statements

### Original pinned P3 — unchanged and unproved

With the original round-13 opens, the exact statement is:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

The compiled sufficient area remainder is also still unproved (add the
round-13 `AdalyFormal.Round13.Detection.PhysicalArea` and
`AdalyFormal.Round10.Nonvanishing.DilatedFlux` opens for `areaSum`):

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

The nested alternative is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∀ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u →
      CurlDetected (2^j) R u
```

### Missing prerequisites for any chosen weighted-arm path

The following are parameterized statements, not claims about every possible
coefficient function. A chosen candidate must prove its instance with its own
`c` and sign proof. Open `AdalyFormal.Round14.PathChoice` and
`AdalyFormal.Round12.Noncancel.Path` in addition to the original opens.

Half-pi P1, which is **not** supplied by `weightedRightStar_negative_pi`:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ),
  (∀ e ∈ starLinks (periodicLatticeShift (rightSite hq R) 0),
    c e = 1 ∨ c e = -1) →
  ∃ w : TwistSpace q R,
    ⟪w, vacA q R (weightedRightStar hq R c) 1 (Real.pi/2) w⟫ < 0
```

P2 on the original central-charged-zero subspace:

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

The whole-kernel line and real nullity two for the modified path:

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

Modified-path detection, still open even if all preceding inputs are supplied:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ),
  (∀ e ∈ starLinks (periodicLatticeShift (rightSite hq R) 0),
    c e = 1 ∨ c e = -1) →
  ∀ u : TwistSpace q R,
    KernelLine q R (weightedRightStar hq R c) u → CurlDetected q R u
```

The length-two and double-star numerical families have no Lean definition or
candidate-specific physical theorem in this round. They are not available for
assembly. In particular, the alternating length-two numerical result must not
be confused with the compiled `weightedStarPath`, whose support is only the
original four arms.

## Reproduction and round-2 recommendation

```sh
python3 AHP/round14/pathchoice/r1/build_pathchoice.py
AHP/round3/lean1.sh AHP/round14/pathchoice/r1/PathChoice.lean
AHP/round3/lean1.sh AHP/round14/shared/pathchoice/R1_WeightedStar.lean
python3 AHP/round14/pathchoice/r1/audit.py
```

Numerical drivers are `screen_signed.py`, `screen_coefficients.py`,
`screen_long.py`, `screen_long_coefficients.py`, `screen_shift.py`,
`screen_double.py`, and `verify_long_mp.py`. Their raw JSON, successful logs and
zero exit files are retained. Reusable flat caches are retained to avoid
repeating identical solves. The erroneous first long-arm coordinate cache and
cache-check diagnostics were removed; the corrected original control was
required before any long-arm result was read.

**Recommendation:** do not spend round 2 re-establishing P1/P2 for signed arms,
arm subsets, odd placements, or equal left/right double stars. The alternating
length-two family is the only surviving numerical lead, but its improvement is
small and its P2 diagnostic margin is weak. A round-2 continuation should first
seek an exact symmetry/Fourier reorganization of the original area sum, or a
genuinely new path with a structurally dominant observable, rather than calling
the 1.49351 ratio easy detection.
