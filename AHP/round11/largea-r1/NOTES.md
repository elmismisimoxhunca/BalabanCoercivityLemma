# Round 11 / large-a / round 1

## Verdict

**closedGoal: none.** Neither `Round11.GoalLargeA`, its negation, nor an unguarded fixed-large-mass slice is proved. A substantial part of the proposed mass-domination route **is** now compiled: for every admissible tower with `R*M >= 4`, arbitrary background, and **a >= 272**, half the actual weighted mass absorbs all extra plaquettes beyond `plaqIn`. This is not an assertion that the full final form is positive.

Final source: `AHP/round11/largea-r1/Attempt.lean` (993 lines, approximately 46 KiB). The complete 8,342-byte `AHP/round11/pin/Statement.lean` occurs verbatim, after a short frozen-import preamble and before all new proofs. No pin statement was changed. All additional imports are frozen `lean/src` modules.

## Compiled results

All names below are in `Round11.LargeA`.

1. **`delta_lower_uniform` (line 289):** for every extent, SU(2) background, plaquette selector set and fine field,
   \[
   \langle A,\Delta_P A\rangle\ge -136\|A\|^2.
   \]
   This is a conservative kernel-checked bound, not the sharper analytical -16 estimate in the probe. The proof combines the frozen per-plaquette curvature estimate with the SU(2) diameter bound and a new **exact fourfold bond-incidence identity**, `pbs_sum_eq`. Thus volume, blocking factor and adding exterior links cannot produce unbounded bare-Delta negativity.

2. **`mass_level0_lower` (line 333):** the actual weighted mass satisfies
   \[
   \langle A,\operatorname{Mass}_a A\rangle
     \ge a\sum_{b\in\operatorname{bondsLam}(G,0)}\|A_b\|^2
   \quad(a\ge0).
   \]
   It uses the real `QfullOf`, `QlinB_zero`, and nonnegativity of the other weighted rows. `mass_on_level0_support` derives domination by scalar mass **only on fields supported on those rows**. No global scalar-mass substitution is made.

3. **`Wop_on_notIn` (line 429):** for an admissible tower with `R*M >= 4`, W is exactly identity on every edge of every plaquette outside `plaqIn`. This holds for arbitrary background, mass and fine field, without inverse guards. It follows from the frozen fact that `Gp R f` lies in `NQp`, together with collar geometry.

4. **`extra_Dpi_lower` (line 480):** writing \(A_0\) for the level-zero mask of the included carrier field,
   \[
   \langle WA,\Delta_{P\setminus\mathrm{plaqIn}}WA\rangle
      \ge -136\|A_0\|^2.
   \]
   This proves shell locality and mass coverage together, not merely a bound involving the potentially large norm of W. No slab or flat-background assumption is present.

5. **`extra_plaquettes_absorbed` (line 496):** for **a >= 272**,
   \[
   0\le \langle WA,\Delta_{P\setminus\mathrm{plaqIn}}WA\rangle
         +\tfrac12\langle A,\operatorname{Mass}_a A\rangle.
   \]
   The constant 272 is sufficient for this absorption estimate; it is **not** a proven transition mass of the headline.

6. **`corner_carrier_half_mass` (line 852), main unconditional partial result:** at the actual pinned corner selector,
   \[
   \langle A,G^{-1}_{\rm corner}(a)A\rangle
   \ge \langle A,D_{\pi,\rm in}(a)A\rangle
      +\|TA\|^2+\tfrac12\langle A,\operatorname{Mass}_a A\rangle.
   \]
   The only premises are admissibility, positive blocking factor, `R*M >= 4`, and `a >= 272`. It applies to every `ClassCoupledFour` member because it does not need class regularity at all.

7. **`ClassCoupledFour.toFrozen` (line 797):** copied the already-audited S-2 geometry/regularity proof, using the unchanged pin definitions. One call site uses explicit theorem application instead of field notation because the definitions now live in the pin's namespace.

8. **`guarded_touch_slice` (line 881):** the complete all-threshold slice with the actual corner Delta **and** J follows from frozen `M2RightInv.p428Target8`, class inclusion, and `InstIneqSG2_general`, **provided `WellDefAt selCorner selCorner` is supplied per instance**. This theorem holds for every positive mass. It is explicitly named guarded and is not counted as the unguarded pinned target.

9. **`Wop_mass_independent` (line 923):** W(a) = W(b) if both genuine padded site operators are units. The proof uses the same `NQp` minimizer and the frozen `Gp_lapDir_of_NQp`. **No unconditional mass-independence claim** is made.

10. **`corner_ge_local_half` / `corner_base_unit_of_local_half` (lines 951 / 977):** with site units at a and a/2, the corner base carrier dominates the actual frozen localized base carrier at a/2. If that localized carrier is also PSD and a unit, then the corner base carrier is a unit. Every extra premise remains visible in the compiled theorem.

## Exact remaining gap

To prove `GoalLargeA` (272 is now a plausible nonoptimal candidate), the following has **not** been closed:

- Uniformly extract the padded site units at a and a/2 and localized **base-carrier PSD plus invertibility** at a/2 from the frozen analytic pipeline, for all sufficiently large m, then all sufficiently large R, all k, all tori/admissible towers, and small-cap `ClassCoupledFour` backgrounds. The headline inequality alone is not this stronger carrier theorem. The comparison above is ready to consume it.
- Establish the **corrected** inverse and constrained inverse guards after changing selectors and mass. `WellDefAt` contains units of `dataS.Ginv`, `G1invS`, and `NmatS`. Proving the first does not prove the second. The source correction uses `H`, itself defined through inverses. Frozen `TwoData.Delta2_eq` additionally needs the base constrained inverse units; it cannot be invoked circularly to obtain them.
- Feed those guards into `guarded_touch_slice` with their genuine uniform thresholds, rather than assuming them or checking a numerical slab.

An attractive next adapter is mass-shift invariance of the constrained minimizer H under adding `Q* diag Q`, followed by the corresponding corrected-carrier comparison. That adapter is **not proved here**. Frozen `GdGen5.genFormS_eq_loc` already handles the final mass subtraction and both source terms once all guards exist; no separate monotonicity of the final form should be presumed.

This leaves the all-positive-mass refutation question open. The compiled shell estimate does rule out the suggested strategy of making the bare exterior negative direction arbitrarily large by using more plaquettes/bonds. It does not rule out corrected-guard failure or a different mechanism.

## Validation and hygiene

Only `AHP/round3/lean1.sh <file>` was used to compile, directly with a 1,200-second timeout. No compile timed out; no duplicate timeout relaunch occurred. The wrapper enforces the two-job machine-wide limit. Final `Attempt.lean.exit` is 0 and all printed dependencies are subsets of `propext`, `Classical.choice`, `Quot.sound`. Every explicit declaration in the assembled source has a `#print axioms` command.

`AUDIT.json` records the final pin-byte check, declaration/print coverage, forbidden-token scan and axiom audit. An independently copied `Attempt.verify.lean` is compiled through the same wrapper; its log/exit are retained. No numerical experiment, `lake build`, reproduction script, git commit/push, protected-source edit, integration-checkout edit, or worktree operation was performed. Scratch fragments were removed only from `AHP/round11/largea-r1/`; final source and verification evidence remain there.
