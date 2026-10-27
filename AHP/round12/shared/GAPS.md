# Round 12 — exact remaining gaps

Latest kernel status: R2 has a direct response-hull bridge without
`RegularityFacts`, canonical-edge/whole-line construction from explicit physical
inputs, and conditional exclusion of all zero-jet fields. The actual star
half-pi trial, full trace-zero positivity, and same-crossing detection remain
open. See **Kernel track, round 2** below. R1 entries are retained with corrections.

## Kernel track, round 1

**OPEN:** `AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation` and pinned `GoalNeg2`. No negation of the premise or strictly weaker sufficient premise has been proved. Please preserve each track's section when updating this shared ledger.

### Compiled progress

`kernel/R1_ActualKernel.lean` is the 1820-line published compact file, separately compiled with exit 0 and only `{propext, Classical.choice, Quot.sound}`. It is byte-identical to `../kernel/r1/ActualKernel.lean`; `../kernel/r1/AUDIT.json` checks every copy and dependency record.

`AdalyFormal.Round12.Kernel.Actual.kernelLine_of_boundary_positive` returns the **original** `AdalyFormal.Round10.Assembly.R2.KernelLine` for the actual `vacA` from:

1. the exterior path being fixed by the quarter gauge at the actual canonical crossing;
2. actual strict positivity on the zero fiber of one physical complex bond entry;
3. any nonzero actual crossing vector.

Chargedness and global real nullity two are derived, not assumed. `kernelLine_finrank` explicitly states the latter. `oneColor_not_crossing` excludes the **particular historical** charged-invisible `oneColor` witness if the observable bond is outside its support, still conditional on the positivity premise. It does not establish absence of all zero-jet fields.

Noncancel's final R1 package is `noncancel/R1_Star.lean` (692 lines, exit 0, 53 standard axiom records; published source/log/exit and byte identity checked here, **same-builder publication compile, not independent review**). It supplies actual `Plaquette.frozen_three_form` / `frozen_three_form_right`, `Star.pair_completion`, analytic star-path and gauge identities, and the right-star negative endpoint. Precise handoff: `noncancel/R1_PROGRESS.md`. No additional abstract dimension lemma is needed for this route.

### K1. Frozen boundary-zero positivity and crossing range — OPEN

Using the opens of `ActualAppendix.lean.txt`, the exact unproved proposition for a chosen path and bond is:

```lean
∀ x : TwistSpace q R, x ≠ 0 →
  AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R b x = 0 →
  0 < ⟪x, vacA q R V 1 (vacEdge q R V) x⟫
```

The finite-star completion-of-squares route also needs:

```lean
0 < vacEdge q R V ∧ vacEdge q R V < Real.pi / 2
```

The existing right-star negative endpoint is at `pi`; it does **not** supply this stricter upper bound. The precise missing physical ingredients are:

**Updated in R2:** noncancel's `RightFamily.pathU_rightStar`, `dilU_rightStar`, and `vacA_rightStar` now establish the exact canonical/unmasked carrier identification. This is no longer an open leaf. `Gauge.starPath_fixed` and our `vacA_rot_of_fixed` provide the corresponding quarter-gauge input.

1. **Closed in R2:** noncancel's `Boundary.Wop_eq_on_omitted` proves boundary-patch `W u = u` for arbitrary fields, without a site-unit premise.
2. **Still open:** instantiate the generic compiled `Mass.carrier_leaf_mass_le` / `Mass.mass_split` on eight distinct actual leaves, identify the remaining positive form, and enumerate the complete physical plaquette sum.
3. **Local algebra closed in R2, global estimate still open:** `FullPlaquette.frozen_full_three_right/left` includes neutral squares and absence of mixed terms. Their assembly must still yield positivity on the complete real trace-zero carrier, not just the charged numerical block.
4. An actual negative trial at `pi/2`, including its collar support, `W=id`, `T=0`, mass terms, and full plaquette energy—not just the negative rational surrogate polynomial.

Use one side consistently. Noncancel's equal-sign four-link numerical star is based at the **left** exterior site `(4q-1,0,0)` and its two transverse predecessors; its compiled endpoint theorem is for a **right** `BdPt` star. No reflection equivalence is proved. Our separate right-star numerical check supplies evidence only, not that bridge. The physical hypotheses cannot be silently replaced by numerical Schur inequalities.

### K2. Detection for the same crossing generator — OPEN

For the actual `u` supplied at that crossing, the missing conclusion is:

```lean
AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected q R u
```

with the **same** vector satisfying:

```lean
u ≠ 0 ∧ vacA q R V 1 (vacEdge q R V) u = 0
```

Alternative: original `TopJetDetected hq R u` plus the flat-constraint-unit condition of `curlDetected_of_topJet`. Nonzero boundary coordinate, one charged kernel line, and nonzero field value at the interface each fall short of proving this quadratic jet noncancellation. The specific `exists_charged_invisible` witness is not a counterexample to the desired premise unless put in an actual crossing kernel; conversely excluding that one witness is not K2.

### K3. Cofinal family and the exact bridge — OPEN

The original sufficient proposition still to prove is `AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine`, verbatim from `AHP/round10/shared/assembly/R3_EnergyGlue.lean:2208` (with that file's opens):

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
    AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
    (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
    ∃ u : TwistSpace (2^j) R, KernelLine (2^j) R V u ∧ CurlDetected (2^j) R u
```

The old `R4_ResponseHull.lean:2599`, `cofinalAnyPathNoCancellation_of_curlLine`, yields the requested response-hull premise **under `RegularityFacts`**. **R2 supersedes that geometric step:** `kernel/R2_ResponseLine.lean:2087`, `ResponseActual.cofinal_noCancellation_of_curlLine`, gives the same implication with NO regularity premise. The cofinal curl-line hypothesis itself is still open; `noncancel/R2_RightFamily.lean` now proves all the right-star path-validity/cofinal clauses apart from kernel/detection. `R3_EnergyGlue.lean:2226` yields `CofinalAnyPathCoupling`, then round 9's `goalNeg2_of_cofinalAnyPathCoupling` yields `GoalNeg2`. The new kernel theorem provides only the `KernelLine` clause after K1 and the other explicit inputs.

### K4. Integration audit — BROKEN JOIN, not merely memory-blocked

Coordinator `COORDINATOR.md` reports a high-RAM compile of the byte-identical historical assembly: exit 1, unknown `half_twice`, `half_average`, `phase_axis_fixed`, and an unsolved color-section goal, with downstream nonstandard axiom records. The compact helper file has those lemmas, but they were omitted from the assembled concatenation. Do not mark that full assembly as verified from smaller-file logs. This track obeyed the no-huge-compile rule and did not touch historical files.

### Independent numerical checks (evidence only)

- Left twist, **q=2,R=32**, all 128 sectors screened (double spectra), selected crossing at 190/230 digits: charged `(7,7)` angle `0.56397151798556`, next Schur eigenvalue `0.998075759859`, coupling `-4.48309700498e-123`, first tangential jet `-2.51198220731e-123`. Relative precision differences below `4.7e-173`; null residual `3.62e-229`. Three nearest/reference competitors checked at 80 digits, positive minima `0.0519609465731`, `0.260322902343`, `1`.
- Finite **left star q=1,R=20**, all 16 flat characters and full physical reconstruction, 90/120 digits: angle `1.207987856419019`, next charged Schur eigenvalue `0.932012806276`, neutral minimum `1.12322456351`; central-zero Schur minimum `0.931888514752` at the crossing. Two tangential top-jet sums about `3.63040925e-44`, stable relatively below `8.3e-81`.
- Finite **right star q=1,R=20**, independently assembled, 90/120 digits: same angle and Schur minima, but adjacent right-layer jet sums `[-7.39403098556e-45,3.50188782839e-44,3.50188782730e-44]`, stable relatively below `9.2e-81`; resolvent residual `7.75e-121`. Left/right blocking jets are **not** identified by an assumed reflection. All final numerical exits are 0. See `../kernel/r1/NUMERICS_SUMMARY.json` and `../kernel/r1/NOTES.md` for normalization and precision details.

Local orientation audit: frozen atoms `a1,a2,a3,a4` correspond to physical zero-based edges `[2,3,0,1]`, including their signs/transports. The left branch zeros frozen atom 2 (physical edge 3), with holonomy `-t` and transported atom 1; the right branch zeros frozen atom 4 (physical edge 1), with holonomy `+t`. The right check therefore follows `Plaquette.frozen_three_form_right`, not a translated left Hessian. `../kernel/r1/STAR_ATOM_ORDER.json` records 20 local quadratic-form comparisons at 100 digits, exit 0, maximum difference `1.15e-100`.

No interval bounds, Lean stencil/DFT dictionary, first-crossing certificate, or cofinal conclusion follows from these tests. Schur eigenvalues are not full-carrier eigenvalues. Numerical `augmented_residual` fields for non-null competitor vectors mean `||Ax||`, not solver error.

## Kernel track, round 2

**Still OPEN:** the requested cofinal premise, its negation, and GoalNeg2. The new
compact implications are NOT unconditional physical/cofinal results.

### Clean compact publications

- `kernel/R2_ResponseLine.lean`: 2107 lines, local/shared independent executions
  both exit 0, 151 permitted axiom records each, byte-identical. Namespace
  `AdalyFormal.Round12.Kernel.ResponseActual` proves `responseHull_singleton`,
  `noCancellation_iff_curlDetected_of_kernelLine`,
  `all_kernel_detected_of_generator`,
  `zeroJet_not_crossing_of_detected_line`, and the direct
  `cofinal_noCancellation_of_curlLine`. The unit-response hull is exactly
  \(\{\|u\|^{-2}\operatorname{responseGradient}(u)\}\), assuming the original
  WHOLE-kernel `KernelLine`. Detection of that generator is still required.
- `kernel/R2_FirstCrossing.lean`: 2060 lines, local/shared independent executions
  both exit 0, 111 permitted axiom records each, byte-identical.
  `CrossingActual.kernelLine_exists_before_halfpi` derives the original canonical
  crossing in `(0,pi/2)`, a whole `KernelLine`, and real nullity two from actual
  continuity/initial positivity, gauge invariance, a negative half-pi trial and
  trace-zero positivity throughout the interval. Symmetry and a nonzero kernel
  witness are derived. No isolated-root hypothesis is needed for these clauses.
- Six local/shared compiles and twelve copy checks pass
  `../kernel/r2/AUDIT.json`. Only `{propext,Classical.choice,Quot.sound}` occur.
  These are builder and publication compiles, not an independent reviewer's
  verification. See `../kernel/r2/NOTES.md` for exact theorem lines and inputs.

### Exact remaining physical statements for one consistently RIGHT star

With the shared-package opens, for `q>0`, even `R>=18`, and
`V := AdalyFormal.Round12.Noncancel.RightFamily.rightStar hq R`, the strong
all-instance route still needs these propositions (not asserted here):

```lean
-- Negative direction at HALF pi, not merely at pi.
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ w : TwistSpace q R,
    ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0

-- Every physical field in the zero fiber of the central charged coordinate.
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (t : ℝ), 0 < t → t < Real.pi/2 →
  ∀ x : TwistSpace q R, x ≠ 0 →
    AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
      (rightSite hq R, (0 : Fin 3)) x = 0 →
    0 < ⟪x, vacA q R (rightStar hq R) 1 t x⟫

-- Detection at the SAME canonical crossing, after the line is constructed.
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

The continuity and positive-start inputs of the compact crossing theorem are
explicit; historical bodies exist, but this track has not silently treated their
large-file integration as a clean new compile. The right-star quarter gauge is
supplied by R1's `Gauge.starPath_fixed`.

The above all-q/all-R route may be weakened to nested cofinal dyadic scales and
even radii. `RightFamily.cofinal_rightStar_paths` now handles those quantifiers
for ALL path-validity clauses. It does not supply the still-open kernel/curl
clauses. The exact remaining sufficient premise is still
`AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine`, whose full quantifiers
are displayed in K3 above. The NEW direct bridge from it to
`CofinalAnyPathNoResponseCancellation` no longer needs `RegularityFacts`.
Historical coupling/GoalNeg2 integration remains separately unverified/broken,
not repaired by this geometric bridge.

### New independent evidence, not physical proofs

`../kernel/r2/TRIAL_CHECKS.json`: direct finite-support physical RIGHT-star
half-pi trial, q2R20/q4R22/q8R24, 130 digits, exit 0. Six supported bonds touch
nineteen plaquettes: mass 21/16 + untwisted energy 15/16 - star energy 5/2 = -1/4.
Without the tangent correction it is 5/4 + 3/4 - 2 = 0. This uses NO Schur
elimination; all endpoints are outside Omega1. Its finite enumeration/frozen
operator Lean join remains open.

Held-out all-64-character right-star q2R20 reconstruction is recorded by
`../kernel/r2/star_crosscheck.py`, 120/155-digit JSON/log/exit artifacts, and
`../kernel/r2/NUMERICS.json`. Both runs and the comparison audit exit 0. Root
1.208030537534756; next charged Schur eigenvalue 0.931830099762687; minimum neutral
Schur eigenvalue 1.12323288983710; central-zero Schur minima at crossing/half-pi
0.931702659603179 / 0.585026065578972. Adjacent top-layer jet sums are
[-1.72163155e-76, 3.76958628e-75, 3.76958609e-75], precision-stable relatively below
3.63e-112. At 155 digits: null residual 6.77e-155, flat-resolvent residual
1.92e-151, charged-line scaling error 5.72e-151; peak RSS <625 MiB. The right-pencil
identity and sampled derivative/prefix/trace-zero positivity checks passed.
Schur spectra are not full-carrier eigenvalues; sampled positivity and tiny
nonzero jets are not interval or cofinal certificates. The reconstructed vector
is normalized on the nine boundary coordinates, not in the full carrier.

