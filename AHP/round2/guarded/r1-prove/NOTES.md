# Guarded, positive direction, round 1

## Result

**closedGoal: `none`.** Neither pinned positive goal is proved. No negative goal is proved either.

Final Lean file: `Attempt.lean`. Furthest compiled partial declaration:

`AdalyFormal.Round2.Guarded.R1Prove.goalPos2_iff_boundary_kernel`

at **Attempt.lean:441**. Its type is an equivalence between the unchanged pinned headline and an eventual kernel-location condition. It is **not** a proof of either side. The pointwise obstruction theorem at **:376** is the main supporting mathematical result.

The entire `pin/Statement.lean` is an exact byte prefix of `Attempt.lean`, including all operative definitions, both positive goals, and identity checks. The only import is frozen `DrEquiv`; there are no AHP imports. No hypothesis was added to a pinned goal. New declarations are in the separate namespace `AdalyFormal.Round2.Guarded.R1Prove`.

## Starting point and attempted proof

Read HANDOFF.md, OPEN_ITEMS B/K–N/R/S, STAGE_B_RESULTS, the guarded design/attack/decision, the Stage-B source and verification records, the numerical source scripts, and the round-2 pin. No numerical script was executed; no stored numerical observation is promoted to a theorem.

Started from the frozen nearest positive results and their proof bodies:

- `lean/src/SolR345Audit.lean:68`, `full_guard_literal`: proves the **full**-guard headline. It consumes corrected invertibility and cannot supply that missing premise.
- `lean/src/GdR5a.lean:65,114` and `DrEquiv.lean:60,101,116`: the residual/headline equivalences and the threshold-combining argument. These already supply localized well-definedness at sufficiently strong thresholds when a positive-energy admissible test exists.
- `lean/src/GdGen4.lean:58`, `unit_transfer`: reused its finite-dimensional injectivity-to-unit proof pattern. This theorem transfers a compressed inverse after assuming both carrier operators are units; applying it to the corrected operator would assume the missing conclusion.
- `lean/src/GdGen3.lean:66`, `Ginv_eq_on_V`, and `R2Algebra.lean:230`, `isG1inv_sub`: reused to compare the actual pencil to the already-controlled localized corrected operator on `V0`.

Let, purely as notation in this note,
\[
A=(\mathrm{dataS}\;\mathrm{selAll}\;\mathrm{selAll}\;P).\mathrm{Ginv},\qquad
D=(\mathrm{dataS}\;\mathrm{selIn}\;\mathrm{selIn}\;P).\mathrm{Delta2}.
\]
Both are the real frozen lattice assemblies. `V0 P.G` means fields zero on **every level-zero bond** (`GdGen2.lean:46`), not merely fields zero on a geometric exterior boundary or on the shell.

## Compiled partial results

All following line numbers are in `Attempt.lean`.

1. **:282, `pencil_eq_local_on_V`.** Under admissibility, positive ell, and the existing room condition, for every \(x\in V_0\),
   \[
   (A-D)x=G_{1,\mathrm{in}}^{-1}x.
   \]
   No flatness, literal guard, class bound, or inverse premise is needed for this equality.

2. **:301, `pencil_kernel_in_V_zero`.** If the actual localized corrected operator is a unit, a pencil null vector in \(V_0\) is zero. **:315, `pencil_isUnit_of_kernel_mem_V`** consequently proves the pencil is a unit if its entire kernel lies in \(V_0\). The kernel-location premise is not discharged.

3. **:329, `pencil_kernel_iff_feedback_fixed`.** With the literal unit guard,
   \[
   (A-D)x=0\quad\Longleftrightarrow\quad A^{-1}Dx=x.
   \]
   **:355, `pencil_isUnit_of_feedback_norm_lt_one`** gives the sufficient condition \(\lVert A^{-1}D\rVert<1\). This needs no positive quadratic-form bound, so it is usable for indefinite carriers too. It does not assert that any particular indefinite lattice configuration satisfies the bound.

4. **:376, `guarded_kernel_obstruction`.** Under the same geometry, literal carrier invertibility, and localized corrected invertibility, if the pencil is non-unit then there exists \(x\ne0\) with:
   - \((A-D)x=0\);
   - some level-zero bond coordinate of \(x\) nonzero;
   - \(Dx\ne0\).

   In addition, \(\lVert A^{-1}D\rVert\ge1\). This is a necessary condition for a separation, not its existence or exclusion. In particular it does not infer a nonzero quadratic matrix element from nonzero operator action.

5. **:416, `CBoundary`; :426/:441, `goalPos1_iff_boundary_kernel` / `goalPos2_iff_boundary_kernel`.** The pinned positive goals are equivalent to `GShape CBoundary`, where `CBoundary` says every corrected null vector belongs to \(V_0\). The full original eventual-scale, radius, smallness, class, and positive-test-field quantifiers remain in `GShape`. The proof uses frozen `GShape_imp` to obtain localized well-definedness; as in that theorem, thresholds can enlarge and the smallness bound can shrink. This is not a constant-preserving pointwise equivalence without those conditions.

6. **:445/:454, `CFeedbackSmall` / `goalPos2_of_feedback_smallness`.** Proves the conditional route `GShape CFeedbackSmall → GoalPos2`, using the inverse-relative norm bound above at the exact instance prefix. The premise is explicitly unproved. This declaration is not a solution of the pinned positive goal.

## Concrete stopping point

The frozen localized theorem controls the pencil on `V0`, not its whole carrier. The missing positive lemma is:

> At the pinned eventual thresholds and on the entire class, every corrected null vector has zero level-zero trace.

Equivalently, prove `GShape CBoundary`. No argument found forces the level-zero coordinates of a hypothetical null vector to vanish. The literal guard controls the kernel of \(A\), whereas a corrected null vector satisfies \(Ax=Dx\), not \(Ax=0\).

A sufficient quantitative route is `GShape CFeedbackSmall`, but no uniform estimate on \(\lVert A^{-1}D\rVert\) was obtained from the frozen class. Smallness of the localized correction alone does not supply the missing estimate on its product with the literal inverse. The existing `DrMargin` proof additionally requires positive coercivity of the literal carrier; `GdR6a.domination_fails_pi` prevents simply assuming such coercivity throughout the class. This does **not** disprove the inverse-relative bound: a source-specific correlation could still establish it.

The flat-interior path has zero correction and cannot decide this step. Nothing here extends its zero-correction identity to non-flat interiors, constructs a separating configuration, or changes the cofinal quantifier requirements for a negative result. No conclusion about the printed lemma follows.

## Verification

Final serial command:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/round2/guarded/r1-prove/Attempt.lean > ../AHP/round2/guarded/r1-prove/Attempt.lean.log 2>&1
echo $? > ../AHP/round2/guarded/r1-prove/Attempt.lean.exit
```

Final exit **0**, no errors or warnings. All **56** requested dependency records were emitted: all **49** locally named declarations (including copied definitions) and seven frozen helpers. Every record has only `propext`, `Classical.choice`, `Quot.sound`, or the empty set. Every added helper has an individual print.

An initial compilation exhausted heartbeats in a broad `congr` tactic. Replacing it with a specific `congrArg` avoided unfolding the operator assembly; subsequent compilation passed. The retained log/exit are from the final file, not that failed intermediate run.

`VALIDATION.json` records the byte-prefix identity, import check, whole-source prohibited-token scan (zero hits), print coverage, final exit, and SHA-256:

```text
14c828bc6495118756f962e1f19821e6269ee434bddd4bb12bf67a90bbe9983d
```

No independent second-agent verification or whole-project rebuild is claimed. No build, reproduction, dependency update, deletion, commit, or push was run. All writes are under `AHP/round2/guarded/r1-prove/`. The pre-existing changes in `lean/lakefile.toml`, `lean/src/BalabanCompact/`, and `lean/src/CompactDictionary/` were left alone.
