# Placement round 6, pass 2 — hybrid source reduction

**closedGoal: `none`. No pinned goal is proved.**

**Compilation distinction:** the two focused proof files compile successfully. The complete `Attempt.lean` compilation timed out after 600 seconds, produced no `.exit`, and was **not relaunched**. Its interrupted source and partial log are retained under `Interrupted.Attempt.lean*`. The final `Attempt.lean` is assembled from the entire first-pass file and verbatim new sections from the successful focused compilation. **That concatenation has not been compiled as a whole.** `exitCode: -1` denotes absent final-file completion evidence, not an observed Lean exit code.

## 1. Furthest compiled partial result

`AdalyFormal.Round6.Guarded.PlacementR2.hybrid_correction_formula`

- Successful compilation: `HybridCertificate.lean:2509`, exit **0**, no warnings/errors.
- Identical declaration in final `Attempt.lean:3193`.
- Normalized dependency record from the successful focused file:

```text
'AdalyFormal.Round6.Guarded.PlacementR2.hybrid_correction_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is an actual-operator identity, **not a positive sign theorem or a conditional assertion relabelled as GoalNeg2**. It proves that adding distant boundary curvature leaves the effective source unchanged, although the inverse propagation and dressed second jet in the correction still belong to the modified background.

The generic source reduction also compiles independently in `SourceReduction.lean`: exit **0**, no warnings/errors, all 51 declarations individually printed with permitted dependencies. The focused hybrid file has **147 local declarations** and **167 dependency records**, all permitted. The final concatenation has **180 local declarations**, each with an individual print command. Its new sections are byte-identical to successful focused source; inherited whole-file evidence is the first-pass file's prior successful log, not a new final-file check. `CHECKS.json` separates these facts explicitly.

## 2. The hybrid family and exact class obligations

The first pass proved that moving all curvature to the outer boundary makes the genuine correction zero. This pass retains a core defect instead of repeating that failed boundary-only construction.

Keep the original `dilLu`, `dilTower`, `dilLam`, and positive-energy `dilBt` competitor. Fine sides are

\[
(q(12R+16),8q,8q),\qquad
\Omega_0=[4q,(12R+12)q),\quad
\Omega_1=[(2R+4)q,(10R+12)q).
\]

`hybridMask` assigns independent amplitudes:

- boundary amplitude \(\beta\) at direction-1 bonds with \(x_0=4q+2\) and both transverse coordinates even;
- core amplitude \(\varepsilon\) at the original direction-1 pattern \(x_0=(2R+4)q\), again transverse-even;
- zero on remaining interior links.

`hybridU` uses `Ug` of this mask on non-exterior bonds and arbitrary V on exterior bonds. Thus the new boundary defect is two fine sites from the outer face, but the nonlinear-constraint core is retained. The numerical subfamily takes **\(\beta=h,\ \varepsilon=-h\)** with \(h>0\). Both signs are allowed by the exact mask bound.

New declarations, line numbers in final `Attempt.lean`:

| Declaration | Line | Exact content |
|---|---:|---|
| `hybridMask_bound` | 3050 | Both amplitude bounds imply the required pointwise mask bound; no sum-of-amplitudes loss. |
| `hybrid_regular` | 3057 | Genuine per-cube regularity, with both absolute amplitudes at most alpha/80. |
| `hybrid_agrees_near_top` | 3065 | Hybrid and original core agree on every bond based within distance three of Omega1. Allows arbitrary exterior fields on either side. |
| `hybrid_boundary_holonomy` | 3089 | Boundary plaquette word is exactly `(Ug beta)^(-1)`. |
| `hybrid_core_holonomy` | 3115 | Original core plaquette word is exactly `(Ug epsilon)^(-1)`. |
| `uniform_hybrid_class_family` | 3143 | Full TorusOK, Admissible, LambdaOK2, ClassCoupled, capped alpha, both competitor restrictions and strictly positive competitor energy. One allocation works for all sufficiently small independent signed amplitudes and every V. Positive beta gives actual nonidentity boundary holonomy. |
| `cofinal_hybrid_class_family` | 3220 | Cofinal scale/radius bookkeeping for these actual hybrid configurations. |

The cofinal theorem chooses

\[
m=m_0+1,\quad q=2^{m_0},\quad R=2(R_0+18)
\]

**before receiving the cap**. It then obtains positive alpha and delta, with delta<1, satisfying the cap, all class/geometry conditions, the fixed positive-energy competitor and nontrivial boundary holonomy for beta=delta and **every signed core amplitude** with absolute value at most delta. In particular the negative-core choice is allowed. The uniform theorem additionally permits smaller independent boundary amplitudes.

The original `cofinal_in_class_curved_competitor`, `dil_in_class_nonflat_competitor` and their geometry proofs remain verbatim in both the final prefix and the focused hybrid file. No class, coverage, cap, torus, Lambda or competitor condition is omitted. The cofinal theorem asserts no carrier unit, corrected nonunit, or spectral scaling law.

## 3. Exact source cancellation, including non-Abelian distant modifications

Define `activeField` by retaining the selected source on carrier bonds that are **not level-zero constraints**, and zeroing it elsewhere. `activeSource` is its carrier projection.

`source_split` (`:2833`) proves the exact identity

\[
J=Q^*j_0+J_{\mathrm{active}},
\]

where j0 is the actual level-zero part of the original source. The frozen level-zero second-jet identity and the totalized-inverse-aware `inner_H_Qs` theorem then give, **without any unit or smallness assumption**,

\[
\langle v,Dv\rangle
 =2\langle H C^{(2)}(v),J_{\mathrm{active}}\rangle.
\]

Here C2 is the actual assembled, W-dressed second jet, not an undressed surrogate. This is `correction_uses_active_source` (`:2861`). `nonzero_correction_requires_active_source` (`:2874`) gives the corresponding necessary condition, not a sufficient sign condition.

`activeSource_congr_near_top` (`:2962`) is a general actual-lattice theorem: if two configurations agree on every bond whose base is within periodic distance three of Omega1, their active sources are exactly equal. It allows arbitrary link configurations, not merely Abelian masks. The proof tracks the two-site localized source stencil plus the one-site endpoint shift of a non-level-zero carrier bond. It does **not** use a numerical operator dictionary.

`boundary_modification_correction_formula` (`:2997`) consequently gives

\[
\langle v,D_Uv\rangle
 =2\langle H_U C^{(2)}_U(v),J_{\mathrm{active},V}\rangle
\]

for such U,V. The operators H and C2 on the right still belong to U. **This does not assert \(D_U=D_V\), locality of an inverse, or a correction decay bound.**

`hybrid_activeSource_independent` (`:3181`) specializes the equality to the new family: its active source is exactly the original core family's active source, independent of beta and both arbitrary exterior fields. The main `hybrid_correction_formula` specializes the full pairing identity. Finally `hybrid_zero_core_correction_zero` (`:3207`) recovers D=0 for every beta, mass and exterior field when epsilon=0.

Thus boundary curvature cannot directly supply a new nearby effective source, even with a retained core. Any advantage must come from its effect on the response/dressing or on which carrier mode crosses. No theorem here excludes that possibility.

## 4. High-precision hybrid diagnostics

`hybrid_probe.py` imports the supplied probe transcription **read-only**, disables bytecode writes, and changes only the angle mask. `SOURCES.md` gives the Lean file/line provenance for every modeled operator. The source, raw Taylor jets, full localized augmented inverse, neutral KKT solve, and physical character normalization are unchanged. D is not replaced by a curvature mask.

All samples use R=18 and beta=h, epsilon=-h. The table records the **selected charged character**, not a certified first full-carrier crossing:

| q | h | character | independent precisions | computed unit-kernel pairing |
|---:|---:|---|---|---:|
| 1 | 1e-3 | (0,0) | 100 / 180 | +1.5180746767660055662e-38 |
| 2 | 1e-100 | (7,7) | 400 / 500 | **-2.7178923242798243994e-285** |
| 2 | 1e-220 | (7,7) | 500 / 600 | **+1.8124681040894913682e-290** |

Relative precision agreement is respectively **85.32**, **296.32** and **283.08** decimal digits. At the higher precisions, augmented-kernel residual divided by absolute pairing is respectively about 5.96e-143, 3.63e-215 and 8.06e-311. These are stability diagnostics, **not validated error enclosures**.

For q=2,h=1e-100, the selected mode is overwhelmingly right-localized: left-half mass approximately 1.21e-117. The next boundary Schur eigenvalue is about 3.04e-103. At h=1e-220 the mode is balanced, left-half mass approximately 1/2, and the second Schur eigenvalue is about 2.11e-161. The latter pairing divided by h is about **+1.8124681040894913682e-70**, numerically the opposite of the original positive-core vacuum coefficient reported in the supplied probe.

This is a further noncommuting-small-limit warning. The negative 1e-100 sample does **not** rule out an arbitrarily-small-amplitude existence premise: the sign becomes positive again at 1e-220. Conversely, that positive ultratiny sample supplies neither an all-q,R leading coefficient nor a formal arbitrary-cap construction.

At the supplied kernel-based pre-crossing offset, the corrected test forms are approximately -7.59e-39, +4.08e-285 and -9.06e-291 respectively. No full-carrier guard is inferred: **other characters and localized initial positivity were not screened in this pass**. The selected character agrees with the original family's first-character choice, but a changed background does not inherit that full-carrier conclusion automatically. No exact kernel, interval enclosure or Fourier dictionary is supplied by these numbers.

Maximum recorded RSS is **791424 KiB**, about 773 MiB. Each numerical process imposes the imported 7 GiB address-space ceiling, below 8 GB. All six runs used the heavy scheduler and single-threaded BLAS. No finite sample is used as a Lean premise.

## 5. What remains open

No R-independent positive overlap constant was obtained. The exact effective source remains near the nonlinear core rather than moving to the boundary. The ultratiny q=2 value still exhibits the extremely small original vacuum coefficient, not an R-independent improvement.

To close GoalNeg2 for this hybrid, one still needs a parametric analysis for cofinal q,R and arbitrarily small amplitudes: initial actual-carrier positivity/unit, initial corrected positivity, an exact full-carrier crossing/guard, and a positive genuine correction on its kernel (or an independently proved alternative separation premise). None is established by the class certificate, the source identity, or the selected-sector signs. No new bridge is asserted with an unproved hypothesis hidden as a theorem. The original bridge is copied unchanged.

There is also the explicit **final-file compilation gap**. The focused results are verified, but their concatenation with the whole inherited IVT bridge has no fresh completion evidence. This is not hidden behind the successful focused compilations.

## 6. Verification, commands and hygiene

Required round-5 RESULTS and all five route NOTES, the complete round-6 probe report/dictionary, the first-pass notes, the pin and relevant actual source definitions were read.

Compilation used only the supplied wrapper directly in the bash tool:

```sh
AHP/round3/lean1.sh AHP/round6/placement-r2/Attempt.lean
# timed out after 600 s; polled, no exit file, not relaunched
AHP/round3/lean1.sh AHP/round6/placement-r2/SourceReduction.lean
AHP/round3/lean1.sh AHP/round6/placement-r2/HybridCertificate.lean
```

The latter two are separately focused targets, not byte-identical replays of the interrupted full file. Their completed exit-1 elaboration failures were repaired locally before the final successful exit-0 runs. No timed-out focused call was retried. The interrupted full source/log hashes are in `INTERRUPTED.json`; the final combined source is a distinct, explicitly uncompiled assembly.

Numerics, with `PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1`, used:

```sh
"$BB_CLI" heavy run -- python3 AHP/round6/placement-r2/hybrid_probe.py --q 1 --R 18 --eps 1e-3 --dps 100 --bsign 1 --csign -1
# independently repeated at 180 digits
"$BB_CLI" heavy run -- python3 AHP/round6/placement-r2/hybrid_probe.py --q 2 --R 18 --eps 1e-100 --dps 400 --iy 7 --iz 7 --bsign 1 --csign -1
# independently repeated at 500 digits
"$BB_CLI" heavy run -- python3 AHP/round6/placement-r2/hybrid_probe.py --q 2 --R 18 --eps 1e-220 --dps 500 --iy 7 --iz 7 --bsign 1 --csign -1
# independently repeated at 600 digits
PYTHONDONTWRITEBYTECODE=1 python3 AHP/round6/placement-r2/audit.py
```

All authored files and cleanup are under `AHP/round6/placement-r2/`. No protected file, earlier round, lakefile, olean, paper, notes directory, expected, extras, commit or push was touched. No direct compiler/build/update/reproduction command or BB terminal was used. Superseded assembly fragments were removed only within this track; the interrupted source/log remain as audit evidence.
