# Kernel R2 — canonical edge, whole-line response, held-out cross-check

**Status: partial progress only. Neither the requested cofinal premise nor its
negation, and not GoalNeg2, has been proved.** All mathematical claims below are
limited to the displayed hypotheses. No giant historical join was compiled.

## Compiled deliverables

All commands used `bb heavy run -- AHP/round3/lean1.sh <file>`, sequentially,
with the wrapper's 8 GiB cap. Each file has its own `.lean.log` and `.lean.exit`.

| Local file | Shared file | Lines | Axiom records | Exit |
|---|---|---:|---:|---:|
| `LineResponse.lean` | included verbatim in response package | 94 | 5 | 0 |
| `ActualResponse.lean` | `shared/kernel/R2_ResponseLine.lean` | 2107 | 151 each | 0 each |
| `ActualCrossing.lean` | `shared/kernel/R2_FirstCrossing.lean` | 2060 | 111 each | 0 each |
| `BoundaryDressing.lean` | not promoted: superseded | 91 | 6 | 0 |

Shared paths are relative to `AHP/round12/`. Both promoted shared files were
compiled separately, are byte-identical to their local copies, and import only
frozen `DrEquiv`. Every printed record uses only `propext`, `Classical.choice`,
`Quot.sound`. `AUDIT.json` contains source/log hashes, all records, forbidden-token
checks, and twelve verbatim-copy checks. `audit.py` passes.

### 1. Exact response hull on the complete original kernel line

Namespace `AdalyFormal.Round12.Kernel.ResponseActual`, shared response file:

- `profileCoupling_quad` (line 1985): actual explicit profile coupling is a
  quadratic map. This uses frozen `C2fullOf_quad` and actual H, not a surrogate.
- `responseGradient_on_line` (2003): for every vector in the charged span,
  \(g(v)=\|v\|^2\|u\|^{-2}g(u)\).
- `responseHull_singleton` (2021): under the ORIGINAL `KernelLine q R V u`,
  the closed convex hull of ALL unit crossing-kernel responses is exactly
  \(\{\|u\|^{-2}g(u)\}\).
- `noCancellation_iff_curlDetected_of_kernelLine` (2046):

```lean
    (hline : KernelLine q R V u) :
    NoResponseCancellation q R V ↔ CurlDetected q R u
```

- `all_kernel_detected_of_generator` (2058): if that generator is detected,
  EVERY nonzero vector of the complete crossing kernel is detected.
- `zeroJet_not_crossing_of_detected_line` (2072): conditional on that line and
  generator detection, EVERY nonzero zero-full-jet field is excluded from the
  crossing kernel. This is not restricted to oneColor or a support template.
- `cofinal_noCancellation_of_curlLine` (2087):

```lean
    (h : AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation
```

**There is no `RegularityFacts` assumption in this new direct geometric bridge.**
It does not prove its `h`, and does not remove the later historical
regularity/final-goal verification boundary. Generic support is in namespace
`AdalyFormal.Round12.Kernel.Response`, `LineResponse.lean`: quarter-turn-invariant
quadratic maps are radial on a charged complex line, with exact norm scaling.

### 2. Same canonical crossing, without assuming an isolated root or a witness

`AdalyFormal.Round9.Guarded.QualitativeR2.psdEdge_singular_without_isolation`
(shared crossing file, line 1887) reuses the valid part of the historical
`psdEdge_spec` proof: continuous symmetric path, positive initial operator and a
negative endpoint direction already imply a PSD singular canonical edge strictly
between endpoints. No isolated-nonunit hypothesis is used for those clauses.

`AdalyFormal.Round12.Kernel.Crossing.psdEdge_same_after_negative` (1981)
proves that once a negative direction occurs at T, increasing the endpoint from T
to pi does not change `psdEdge`. This part needs no continuity.

`AdalyFormal.Round12.Kernel.CrossingActual.kernelLine_exists_before_halfpi`
(line 2032) then gives

```lean
    0 < vacEdge q R V ∧ vacEdge q R V < Real.pi/2 ∧
      ∃ u : TwistSpace q R, KernelLine q R V u ∧
        Module.finrank ℝ (vacA q R V 1 (vacEdge q R V)).ker = 2
```

from these explicit inputs:

```lean
    (hc : Continuous (vacA q R V 1))
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x,vacA q R V 1 0 x⟫)
    (hw : ∃ w, ⟪w,vacA q R V 1 (Real.pi/2) w⟫ < 0)
    (hV : ∀ t, periodicGaugeTransform (rotGauge (Real.pi/4)) (V t) = V t)
    (hp : ∀ t, 0 < t → t < Real.pi/2 → ∀ x : TwistSpace q R,
      x ≠ 0 → chargedCoordinate q R b x = 0 → 0 < ⟪x,vacA q R V 1 t x⟫)
```

Operator symmetry is discharged from frozen `dataS_laws`. A nonzero kernel
witness is derived from non-unitness. R1's compiled actual trace-coordinate theorem
then derives chargedness, containment of the WHOLE kernel in the charged span,
and real nullity two. Thus no simplicity, chargedness, nonzero crossing witness,
or isolated-root assumption is hidden in the conclusion. **The physical `hw`
and `hp` inputs remain open.** Carrier continuity and initial positivity remain
explicit in this compact package; their historical bodies are not silently
asserted to be independently recompiled here.

### 3. Boundary work intentionally not double-counted

The 91-line `BoundaryDressing.lean` proves the collar identity with an explicit
site-unit hypothesis. The concurrent noncancellation track proved a stronger
arbitrary-field identity without that hypothesis in
`shared/noncancel/R2_Boundary.lean` and its joined `R2_StarLocal.lean`:
`Boundary.Wop_eq_on_omitted`, `Tfull_sing_zero_near`, `Wop_sing_near`.
It also published full neutral+charged local forms, distinct physical leaf-mass
extraction, exact `vacA_rightStar`, and `cofinal_rightStar_paths` (all original
path-validity clauses, including the negative pi endpoint). Therefore arbitrary
boundary W locality and right-star path cofinality are no longer missing leaves.
The finite full-plaquette enumeration/trace-zero estimate still is.

## Independent numerical evidence

### Direct physical finite-support half-pi trial, without Schur elimination

`trial_crosscheck.py`, 130 digits, tested held-out right-star cases q2R20, q4R22,
q8R24. Each has the same exact rational stencil values:

- central normal bond: 1;
- normal neighbors in directions 1,2: +neighbor = -i/4, -neighbor = +i/4;
- the positive direction-1 tangent at the central site: -i/4.

The six supported bonds touch nineteen plaquettes. Mass = 21/16, untouched
plaquette energy = 15/16, four twisted plaquette contribution = -5/2, total = -1/4.
Without the tangent: five bonds/sixteen plaquettes, 5/4 + 3/4 - 2 = 0.
All endpoints lie outside Omega1. See `TRIAL_CHECKS.json`, `trial_checks.log`,
`trial_checks.exit` (0). Peak RSS 28 MiB. This independently checks the intended
trial sign and right orientation; **its finite enumeration/frozen-operator Lean
join is still unproved.**

### All-character right-star reconstruction

`star_crosscheck.py` / `run_numerics.sh`: held-out q=2,R=20, all 64 physical
characters, 120 and 155 decimal digits, at most 2 GiB per process, one BLAS thread.
The full flat constrained inverse is formed BEFORE the boundary Schur reduction.
Charged and neutral sectors, central-coordinate-zero restrictions, physical top
jets, quadratic phase/scale response, and right-star affine-pencil/derivative
identities are checked. The tiny jet is not inferred from the matrix gap.

Both runs and the comparison audit finished with exit 0. `NUMERICS.json`
records all checks, hashes and precision differences. At 155 digits:

| Quantity | Value |
|---|---:|
| crossing angle | 1.20803053753475603036 |
| next charged Schur eigenvalue | 0.9318300997626865 |
| minimum neutral Schur eigenvalue at crossing | 1.123232889837102 |
| central-zero Schur minimum at crossing | 0.9317026596031793 |
| central-zero Schur minimum at half pi | 0.5850260655789722 |
| right-pencil B minimum | 1 |
| sampled minimum of negative scaled derivative | 0.1113891477900400 |
| adjacent top-layer jet sums, directions 0/1/2 | -1.72163155e-76 / 3.76958628e-75 / 3.76958609e-75 |
| boundary null residual | 6.76444e-155 |
| maximum flat-resolvent residual | 1.91375e-151 |
| charged-line phase/scale jet relative error | 5.71847e-151 |

The top-jet sums agree across precisions relatively below 3.63e-112 (tangential
ones below 3.66e-113); the root difference is below 2.64e-115 relatively. At 155
digits the null residual / smallest tangential jet is 1.80e-80 and the flat solve
residual / smallest tangential jet is 5.08e-77. Peak RSS was 639072 KiB (<625 MiB).
The affine-pencil identity and sampled prefix/trace-zero/derivative positivity
checks all passed. The almost-zero eigenvalue is compared ABSOLUTELY, not by a
meaningless relative quotient of two roundoff-sized numbers.

No interval enclosure, exact cofinality, full frozen-operator identification, or
unit-full-carrier jet normalization is claimed. Schur eigenvalues are NOT full
carrier eigenvalues. The reconstructed vector has unit NINE-BOND BOUNDARY norm,
not unit full-carrier norm. The nonzero jet is evidence only; no exact q=1 dilation
was assumed (the q=2 root does differ from q=1). The startup PATH failure is
preserved separately as `initial_path_failure.*`; it was not a failed numerical
computation.

## Exact remaining Lean statements

All the following are **unproved**, not new declarations with proof holes.
Open the namespaces used by the shared files. Let
`V := AdalyFormal.Round12.Noncancel.RightFamily.rightStar hq R` and
`b := (AdalyFormal.Round5.Guarded.IVTR2.rightSite hq R, (0 : Fin 3))`.
For q>0 and even R>=18, a strong sufficient route is:

```lean
-- (K1) actual half-pi trial, not the already-proved pi endpoint
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ w : TwistSpace q R,
    ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0

-- (K2) positivity on the actual trace-zero hyperplane for ALL carrier fields
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (t : ℝ), 0 < t → t < Real.pi/2 →
  ∀ x : TwistSpace q R, x ≠ 0 →
    AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
      (rightSite hq R, (0 : Fin 3)) x = 0 →
    0 < ⟪x, vacA q R (rightStar hq R) 1 t x⟫

-- (K3) actual detection at that SAME canonical crossing
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

K2 must be obtained from the full physical sum and actual eight distinct leaves,
not by assuming a three-variable local form is the whole operator. K3 may instead
come from an actual nonzero `TopJetDetected` and the known flat-N unit through
`curlDetected_of_topJet`; the old `oneColor` exclusion, nonzero vector, or a
nonzero toy jet does not prove it. One may weaken these all-q/all-R statements to
the original nested cofinal dyadic/even quantifiers; no finite sample suffices.

The **exact minimal old sufficient premise**, still missing, is

```lean
AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine
```

whose operative definition was copied verbatim at response-file line 1949.
The requested target is the verbatim
`AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation`
(response-file line 1917). Our compiled implication connects them directly.

Finally, do not label the historical giant join merely memory-blocked. The
coordinator identified actual missing `half_twice`, `half_average`, and
`phase_axis_fixed` errors in that historical source. The compact files above are
clean, but they do not certify that full join or its final GoalNeg2 specialization.

## Focused reproduction

Generate only this track's compact files:

```sh
python3 AHP/round12/kernel/r2/build.py
python3 AHP/round12/kernel/r2/build_crossing.py
bb heavy run -- AHP/round3/lean1.sh AHP/round12/kernel/r2/ActualResponse.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round12/kernel/r2/ActualCrossing.lean
python3 AHP/round12/kernel/r2/audit.py
```

Do not run `REPRODUCE.sh`, `lake build`, or either giant historical assembly here.
Do not relaunch an active or timed-out compilation: inspect its `.exit` first.
No git commit/push and no writes outside the kernel/shared allowed directories.
