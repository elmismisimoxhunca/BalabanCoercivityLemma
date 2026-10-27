# Guarded positive attempt — round 3, pass 2

## Disposition

**closedGoal: `none`. Neither positive pin is proved.** The final source compiles, but its headline-facing result has an unproved propagation premise:

- `Attempt.lean:976`, `AdalyFormal.Round3.Guarded.R2Prove.goalPos2_of_inverse_boundary_jetInputZero`:
  `GShape CInverseBoundaryJetInputZero → GoalPos2`.

This is a sufficient route to the **unchanged** goal, not a replacement goal and not closure. The missing premise is explicitly identified below. No negative pin is proved either.

The entire `AHP/round3/guarded/pin/Statement.lean` is the exact byte prefix of `Attempt.lean`. Its namespace, all four goals, five boundary-response definitions and threshold order are unchanged. Only frozen `DrEquiv` is imported. Necessary round-2 proofs are copied after the pin; no AHP module is imported.

## Starting points and attempted reduction

Read `HANDOFF.md`, the requested OPEN_ITEMS sections, Stage-B and round-2 results, guarded round-2 JUDGEMENT in full, the pin, round-2 response proof and notes, the earlier feedback and second-jet/nonflat results, and the preceding round-3 positive attempt and notes.

The closest frozen proof is `lean/src/ZR8DataA.lean:83`, `C2fullOf_congr_in`. Its row proof actually uses `C2CompL_congr_in` (`lean/src/ZR8Jet.lean:79`) on the ball of radius `rhoT ell j`, then enlarges that ball into the base domain. I reused that proof before attempting new estimates. This yields an exact nullspace for the real correction, with **Wop retained**.

Other frozen roots inspected/reused:

- `R2Algebra.lean:220,222`: actual `Delta2` and its symmetric quadratic-form characterization.
- `GdR6b.lean:40,82`: vanishing correction under source orthogonality/base-point identity. These do not cover the full class.
- `DrRed1.lean`: actual literal/localized correction equality and pencil identity under the carrier guard and localized well-definedness.
- `DrEquiv.lean:60,116`: combination of eventual thresholds/localized well-definedness and equivalence of the pinned headlines.
- `RI6.lean`: the frozen positive theorem controls localized assemblies. It does not supply a gap for arbitrary exterior-dependent literal units.
- `GdGap2.lean`: positivity/monotonicity at the flat point does not provide the missing implication at every nonflat class instance.

The round-2 `pencil_isUnit_of_no_boundary_return` is reused. The new route asks whether the return already vanishes **before applying the corrected localized inverse**, instead of assuming support preservation through both inverses.

## New compiled source-specific results

Write, only as notation,
\[
A=G^{-1}_{\rm all},\quad B=G^{-1}_{\rm in},\quad
D=\Delta^{(2)}_{\rm in},\quad C=B-D,\quad\Theta=A-B,
\quad W=\operatorname{range}\Theta.
\]
These are the actual pinned assemblies, not independent model matrices.

### Precise row-ball input nullspace

`jetInputZero P` (`Attempt.lean:746`) consists of carrier fields \(x\) for which the actual dressed input
\[
W_{\rm op}\,i_E x
\]
vanishes on every fine bond based in the `rhoT ell j` ball about every active row bond at every positive level \(1\le j\le k\). Level zero is omitted because its genuine raw second jet is zero. This is a sufficient input-locality mask, not a claim that these balls are minimal or that the correction itself is a plaquette-diagonal operator.

- **:762**, `jet_translation_of_jetInputZero`: for \(x\) in this submodule and every carrier field \(z\), the genuine assembled second jet satisfies \(C_2(z+x)=C_2(z)\). The proof copies the frozen row-locality argument, using the exact row balls without enlarging to all BothIn bonds. It needs no added geometry premise: positive ell is part of `IngrBParams`.
- **:719**, `correction_kills_of_jet_translation`: symmetry and the genuine quadratic-form identity imply that such translation invisibility kills the **entire correction vector**, not merely its diagonal pairing.
- **:789**, `correction_kills_jetInputZero`: consequently \(Dx=0\) for every \(x\) in the new submodule.

A separate coarser mask, `interiorInputZero` (**:796**), requires the dressed input to vanish on all both-endpoints-inside bonds. With admissibility, ell at least two, and the frozen room condition, **:808/:821** prove jet translation invariance and correction annihilation. **:831** puts the correction range in the orthogonal complement of that dressed-input nullspace. No assertion that an inverse preserves either mask is made.

### Positive consequence using one localized inverse

- **:845**, `pencil_isUnit_of_inverse_boundary_jet_invisible`: if every \(B^{-1}y\), \(y\in W\), is invisible to all translated second-jet evaluations, then the corrected pencil is a unit under the original carrier guard and localized well-definedness.
- **:860**, `pencil_isUnit_of_inverse_boundary_jetInputZero`: the concrete sufficient premise is
  \[
  B^{-1}W\subseteq\texttt{jetInputZero P}.
  \]
  Then \(DB^{-1}y=0\), hence the previously established return
  \(\Theta C^{-1}DB^{-1}y\) vanishes. The added premise contains only the **uncorrected localized inverse**. The proof still uses the known localized corrected unit through `WellDefAt`; it does not assume the missing literal corrected unit.
- **:976**, `goalPos2_of_inverse_boundary_jetInputZero`: frozen `GShape_imp` lifts this sufficient condition to the untouched pinned headline, with all its quantifiers retained. This may enlarge thresholds and shrink the cap, as in the frozen theorem. The premise `GShape CInverseBoundaryJetInputZero` is **not proved**.

The coarser all-BothIn alternative is recorded at **:902/:957**, also conditionally. Neither criterion is asserted necessary, nor is a new nontrivial in-class family satisfying it supplied.

### Necessary obstruction to the attempted positive route

**:873**, `guarded_failure_forces_jet_ball_response`, proves that any guarded failure under localized well-definedness has a nonzero \(y\in W\) with
\[
K_Cy=0,\qquad DB^{-1}y\ne0,
\]
and a specific positive-level active row and bond in its `rhoT` ball where
\(W_{\rm op}i_EB^{-1}y\ne0\). It combines the genuine round-2 boundary-return obstruction with the new correction nullspace theorem. **:917** gives the analogous inside-bond conclusion under the stated geometry. These are necessary consequences of failure, not constructed failing instances.

## Concrete stopping point

The class hypotheses and capped alpha0 were **not shown to imply**
\[
B^{-1}(\operatorname{range}\Theta)\subseteq\texttt{jetInputZero P}.
\]
The frozen locality theorem controls the jet **given its input**. It does not control that input after applying the full localized Green operator. Even exact shell localization of Theta from pass 1 does not establish this propagation statement. In particular, replacing `Wop iE (B inverse y)` with `y`, or treating the inverse as a local finite-stencil map, is not justified.

The alternative weaker cancellation \(\Theta C^{-1}DB^{-1}|_W=0\) also remains unproved. The quantitative route still needs an eventual inverse-relative bound, for example
\(\|K_B^{-1}(K_C-K_B)\|<1\). A carrier unit guard is not a uniform inverse-response estimate; no such estimate was derived here from smallness. These are missing proofs, not proofs that no positive argument can exist.

Thus no reduction to an **already settled** theorem closes either positive pin. The new work identifies a source-specific nullspace and a sharper sufficient propagation condition; it does not settle the remaining analytic step.

## Verification

Final command, executed only via the shared-lock wrapper:

```sh
AHP/round3/lean1.sh AHP/round3/guarded/r2-prove/Attempt.lean
```

Final `Attempt.lean.exit`: **0**. Final log: `Attempt.lean.log`, **no errors or warnings**. All **79 local declarations**, plus **17 distinct frozen roots**, have dependency records; all **96 distinct records** are subsets of `propext`, `Classical.choice`, `Quot.sound`. Some inherited prints repeat; 96 is the distinct-name count. Every new helper is printed individually.

Main dependency line, normalized:

```text
'AdalyFormal.Round3.Guarded.R2Prove.goalPos2_of_inverse_boundary_jetInputZero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`python3 AHP/round3/guarded/r2-prove/validate.py` passed and saved `VALIDATION.json`. Checks include the exact complete pin prefix, sole frozen import, raw forbidden-token scan, source/log/exit timestamp order, exit 0, absence of diagnostics, and complete permitted dependency coverage. Source SHA-256:

```text
6599414900d3995ec0eb6194cc1fa96488fac4e355bd9634b88d5a0e2ed3779e
```

Two wrapper invocations ran serially in persistent terminals. The first found an incorrect explicit namespace opening and a missing zero-inner-product simplification; both were repaired. The second compiled the final row-ball and interior-mask results successfully. The failed run is not counted as proof evidence. No direct Lean/Lake invocation, build, reproduction, dependency update, or numerical script was run. No independent second-agent or whole-project check is claimed.

All authored workspace files are under `AHP/round3/guarded/r2-prove/`. A temporary draft fragment was removed there. No protected file, other item, lakefile, repository history, or remote was changed.
