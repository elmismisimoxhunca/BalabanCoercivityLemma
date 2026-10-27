# Round 12 — kernel track, round 1

**Status: OPEN.** Neither `CofinalAnyPathNoResponseCancellation`, its negation, a strictly weaker sufficient premise, nor `GoalNeg2` is proved. The new results are conditional whole-kernel structure theorems for the actual carrier, plus numerical cross-checks. No conditional theorem below closes its positivity hypothesis.

## 1. Compiled deliverables

- `KernelStructure.lean` (208 lines): abstract kernel exclusion, charged planes, boundary restriction, and reconstruction. Import: frozen `D1IVT`.
- `ActualKernel.lean` (1820 lines): the actual operators and the **original** `KernelLine`, with a physical complex boundary coordinate. Import: frozen `DrEquiv`.
- `../../shared/kernel/R1_ActualKernel.lean`: byte-identical published copy, separately compiled.
- Every file has current `.lean.log` and `.lean.exit` with exit **0**. `AUDIT.json` checks source/log/exit freshness, verbatim copies, shared-file equality, forbidden tokens, and every printed dependency set. Audit passes. Only `propext`, `Classical.choice`, `Quot.sound` occur.
- `build.py` produces the actual file; `COPIES.json` identifies every historical slice. The complete round-10 `R1_Dictionary.lean` is the byte prefix; original `PSD`, `vacEdge`, `KernelLine`, and the particular `oneColor` witness definitions are copied verbatim. Nothing is redefined as a toy operator.

Main axiom record (line-wrapped in the log):

```text
'AdalyFormal.Round12.Kernel.Actual.kernelLine_of_boundary_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Main exact statement

Within the opens in `ActualAppendix.lean.txt`:

```lean
theorem kernelLine_of_boundary_positive (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (b : Bond (scaleUp 2 1 (dilLu q R)))
    (hV : periodicGaugeTransform (rotGauge (Real.pi / 4))
      (V (vacEdge q R V)) = V (vacEdge q R V))
    (hpos : ∀ x : TwistSpace q R, x ≠ 0 →
      chargedCoordinate q R b x = 0 →
      0 < ⟪x, vacA q R V 1 (vacEdge q R V) x⟫)
    (u : TwistSpace q R) (hu : u ≠ 0)
    (hAu : vacA q R V 1 (vacEdge q R V) u = 0) :
    KernelLine q R V u
```

Here `chargedCoordinate q R b u` is precisely the upper-right complex entry of the physical matrix field at bond `b`. The result requires **no separate chargedness hypothesis**, no Fourier character, and no prior dimension bound.

### Why this controls the whole kernel

Write \(A=A(t_*)\), \(r(u)=u(b)_{01}\), and let \(J\) be the actual quarter gauge rotation.

1. Strict positivity on \(r=0\) makes \(r:\ker A\to\mathbb C\) injective (`boundary_observable_injective`). Hence the **whole** real nullity is at most two (`kernel_finrank_le_two_of_boundary`).
2. `vacA_rot_of_fixed` proves actual commutation with \(J\) whenever the exterior path is fixed by that gauge at the crossing.
3. `chargedCoordinate_quarter_twice` proves \(r(J^2u)=-r(u)\) for every actual field. Injectivity on the kernel yields \(J^2u=-u\) there (`charged_of_boundary`). Thus neutral exclusion is derived, not assumed.
4. A nonzero \(u\) and \(Ju\) span a real plane (`charged_span_finrank`). That plane is the whole kernel. `kernelLine_finrank` also explicitly proves real nullity exactly two from the original line predicate and commutation.

This replaces the proposed all-character simplicity proof by one physical quadratic-form estimate. It does not prove that estimate.

### The charged-invisible obstruction is handled narrowly, not erased

`crossing_coordinate_ne_zero` shows every nonzero kernel vector has a nonzero central charged entry, conditional on `hpos`.

`oneColor_not_crossing` conditionally excludes the **specific** `ColorObstruction.oneColor hq R` used by historical `exists_charged_invisible`, whenever `b` differs from its support bond `(interiorSite hq R, 0)`. That witness is supported at fine longitudinal coordinate `4*q`; either exterior-star central normal bond is different. This uses verbatim witness definitions and `oneColor_ne_zero`.

This is **not** a proof that all charged zero-jet fields are absent from the kernel. A different zero-jet charged line can still satisfy the boundary criterion. `CurlDetected` remains a separate open requirement.

The abstract `no_flip_eigenvector` is another conditional exclusion: a non-real spatial character contains no nonzero flip eigenvector when the stated translation/flip/quarter-turn identities hold. Actual full-kernel membership in such a character has not been proved. The local-star path deliberately avoids needing that decomposition.

`kernelBoundaryEquiv` and `kernel_finrank_eq_boundary` make precise the restriction/reconstruction obligations for any proposed numerical Schur reduction. Their hypotheses have **not** been instantiated for the frozen operators.

## 2. Held-out numerical evidence

All jobs enforce a 2 GiB address-space limit; observed peak RSS is below 0.8 GiB. These are **non-interval computations**, not certificates or Lean operator identifications. Every quoted eigenvalue is a **boundary Schur eigenvalue**, not a full-carrier eigenvalue. `NUMERICS_SUMMARY.json` is generated by `summarize.py` from the raw records.

### 2.1 Left twist, q=2, R=32

This radius was held out from the other track. `crosscheck.py` uses the historical round-6 full augmented-system transcription read-only, with inverse-before-restriction.

- All 128 charged/neutral character sectors screened at the candidate crossing. Assembly used 25 digits; the screen spectra used double precision.
- Charged `(7,7)` refined at **190 and 230 digits**:
  - angle \(0.563971517985560942179715334361727\ldots\);
  - next Schur eigenvalue \(0.998075759859083\ldots\);
  - reconstructed unit-vector angle derivative form \(-3.12652935690615\ldots\);
  - canonical coupling \(-4.48309700497806\times10^{-123}\);
  - first tangential jet \(-2.51198220730815\times10^{-123}\).
- Root disagreement between the precisions: \(6.31\times10^{-187}\); relative coupling disagreement: \(4.61\times10^{-173}\); relative jet disagreement: \(3.85\times10^{-173}\).
- At 230 digits, augmented null residual is \(3.62\times10^{-229}\), or \(8.07\times10^{-107}\) times the coupling magnitude. Full-torus charged-color anisotropy diagnostic is \(7.56\times10^{-233}\), compatible with a non-real-character circularly polarized mode, not a one-real-color field.
- Competitors recomputed at **80 digits** at the same angle: charged `(0,0)` minimum \(0.0519609465731\), charged `(1,1)` minimum \(0.260322902343\), neutral `(0,0)` minimum \(1\).

**Residual naming caveat:** in the competitor JSON, `augmented_residual` is \(\|Ax\|_\infty\) for a reconstructed **non-null** vector. Its nonzero values are not solver errors. The summary labels this explicitly. The same field is an actual null residual only for the solved crossing block.

The all-sector screen supports an isolated candidate crossing; it does not certify that no earlier crossing/re-crossing occurred. Nor does it prove a cofinal statement.

Files: `screen_q2_R32.json`; `precise_q2_R32_s7_7_c1_p190.json`, `...p230.json`; three competitor JSON files; corresponding logs/exits. All final execution exits are 0. `terminal_path_failure.*` records an initial PATH-only launcher failure, repaired before any numerical run.

### 2.2 Finite exterior star, held-out q=1, R=20

`star_crosscheck.py` assembles the local Hessian independently in the standard four-edge plaquette order (rather than importing the other track's local patch formula), retains all 16 flat Fourier sectors, solves the **full** augmented inverses before restricting to the nine physical boundary bonds, and reconstructs the physical top jets before taking quadratic forms.

Left-star 90/120-digit checks:

- angle \(1.20798785641901928304390613798563\ldots\);
- next charged Schur eigenvalue \(0.932012806275816\ldots\);
- neutral minimum at that angle \(1.12322456351321\ldots\);
- central-coordinate-zero Schur minima at \(0,t_*,\pi/2\): \(1.50062137035,0.931888514752,0.585118794375\);
- central charged coordinate modulus of the normalized nine-bond null vector: \(0.727415743683\);
- physical first top-layer jet sums, longitudinal and two tangential directions:
  \((7.51140822786\times10^{-46},3.63040925187\times10^{-44},3.63040925515\times10^{-44})\).
- Relative 90/120-digit disagreement of all three sums is below \(4.6\times10^{-80}\); maximum flat-resolvent absolute residual at 120 digits is \(6.78\times10^{-121}\).

The positivity checks are only at three sample angles, not a proof throughout an interval. The all-character physical resolvent does test the complete finite-star Schur kernel, unlike a single-character check.

**Orientation matters:** noncancel's compiled `star_negative_endpoint` uses a right-boundary star, while its original probes use a left star. No reflection symmetry of the blocking jet is assumed. The **right-star 90/120-digit** cross-check is now complete (all exits 0): the angle and Schur minima agree with the left-star values, but the adjacent right top layer `s-2=210` gives jet sums
\((-7.39403098556\times10^{-45},3.50188782839\times10^{-44},3.50188782730\times10^{-44})\).
Their relative precision disagreements are at most \(9.2\times10^{-81}\), and the flat-resolvent absolute residual at 120 digits is \(7.75\times10^{-121}\). This supports nonvanishing for the formally relevant orientation without pretending the left/right jets are equal.

**Stencil-order cross-check:** frozen `a1,a2,a3,a4` use physical zero-based edge order `[2,3,0,1]`, not `[0,1,2,3]` (`DeltaPrimeOperator.lean:280–306`). Our left branch has physical edge 3 zero, hence frozen atom 2 zero; its holonomy is `-t` and atom 1 carries `-exp(2*i*t)`. Our right branch has physical edge 1 zero, hence frozen atom 4 zero; its holonomy is `+t` and the remaining atoms are `[-edge2,-edge3,edge0]`. Thus the right calculation uses the ordering of compiled `Plaquette.frozen_three_form_right`, not a translated left Hessian. `check_star_atom_order.py` compares both patch quadratic forms with the corresponding frozen three-atom formula at five angles, with and without zero central coordinate: 20 checks at 100 digits, exit 0, maximum absolute difference `1.15e-100`. See `STAR_ATOM_ORDER.json`. This is an additional local transcription test, not a global Lean operator identification.

Star jets are normalized by a unit **nine-bond boundary** null vector, not a unit full-carrier vector. Both orientations have a negative Schur minimum at `pi` (about `-4.80371554579`). The star JSON files, logs, and exits are all retained; the complete comparisons are in `NUMERICS_SUMMARY.json`.

## 3. Exact remaining Lean obligations

Use the namespace opens of the actual file and, where needed, `AdalyFormal.Round10.Assembly.R3` and `AdalyFormal.Round10.Dictionary.FreeSource`.

### K1 — physical positivity (OPEN)

For the **same** chosen path, central bond, and cofinal scale/radius family, prove the following proposition, not merely assume it:

```lean
∀ x : TwistSpace q R, x ≠ 0 →
  AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R b x = 0 →
  0 < ⟪x, vacA q R V 1 (vacEdge q R V) x⟫
```

The local-star route can establish this from positivity on that hyperplane for all `0 < t < Real.pi / 2`, plus the **actual canonical** crossing bound:

```lean
0 < vacEdge q R V ∧ vacEdge q R V < Real.pi / 2
```

The other track has local pair completion of squares, a finite-star mass lower bound, actual star path/gauge identities, and a negative endpoint at `pi`. What is still required is the frozen form identity with the eight distinct leaf masses, proof that the remaining base form is strictly positive, and an actual negative trial at `pi/2` to put the canonical crossing in the interval. Its rational trial polynomial alone is not that physical identification.

### K2 — a detected crossing generator (OPEN)

Once K1 and the existing crossing-existence facts give a nonzero `u`, prove:

```lean
CurlDetected q R u
```

where `u` is the **same** actual vector satisfying:

```lean
u ≠ 0 ∧ vacA q R V 1 (vacEdge q R V) u = 0
```

Alternatively prove `TopJetDetected hq R u` in the original `JetDetection` namespace and discharge the flat-constraint-unit hypothesis of `curlDetected_of_topJet`. A boundary entry being nonzero does not imply a level-1 quadratic jet is nonzero. A unique-continuation theorem merely for the field's value would also not by itself exclude quadratic jet cancellation.

### K3 — cofinal assembly (OPEN)

The exact existing sufficient premise is:

```lean
AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine
```

Expanded verbatim in `R3_EnergyGlue.lean:2208`:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
    AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
    (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
    ∃ u : TwistSpace (2^j) R, KernelLine (2^j) R V u ∧ CurlDetected (2^j) R u
```

The new theorem supplies its `KernelLine` clause **if** K1, quarter-gauge invariance, and the nonzero kernel witness are proved. The other clauses must concern that same path and witness; unrelated numerical or formal examples cannot be joined.

`R4_ResponseHull.lean:2599`, `cofinalAnyPathNoCancellation_of_curlLine`, sends this premise and `RegularityFacts` to the requested response-hull premise. `R3_EnergyGlue.lean:2226` sends it to `CofinalAnyPathCoupling`; the round-9 bridge then gives `GoalNeg2`. These are existing conditional implications, not new premise proofs.

### K4 — historical integration status (separate from K1–K3)

Coordinator `shared/COORDINATOR.md` reports that the byte-identical historical large assembly was actually tried with ample temporary RAM and **failed**, rather than being merely memory-blocked: unknown `half_twice`, `half_average`, `phase_axis_fixed` and one unsolved goal in the appended color section, with downstream bad axiom records. The helpers exist in the compact dictionary but were omitted from the concatenation. This track did not compile or edit that huge file. Do not mark that full joined proof as verified from the compact successes here.

## 4. Reproduction and scope

From the repository root, compile only the compact files through the mandated wrapper:

```bash
python3 AHP/round12/kernel/r1/build.py
bb heavy run -- AHP/round3/lean1.sh AHP/round12/kernel/r1/KernelStructure.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round12/kernel/r1/ActualKernel.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round12/shared/kernel/R1_ActualKernel.lean
python3 AHP/round12/kernel/r1/audit.py
```

Numerics: `run_numerics.sh`, `run_star.sh`, `run_star_right.sh`; `summarize.py` compares precision runs. Initial left-star filenames omit `left`; subsequent script invocations explicitly include the side. The summary accepts either naming convention.

All writes are under `AHP/round12/kernel/` or `AHP/round12/shared/`. No earlier rounds, `lean/`, paper, notes, lakefile, integration checkout, commits, pushes, or worktrees were changed. No huge historical assembly, `lake build`, or `REPRODUCE.sh` was run. All new formal assertions were compiled; no floating-point evidence enters Lean.
