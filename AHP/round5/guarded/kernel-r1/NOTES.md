# Guarded exact-kernel route, round 5 / pass 1

**closedGoal: `none`. No actual separating lattice instance was constructed.**

The deliverable `Attempt.lean` is a **byte-for-byte copy of the successfully compiled `DecayModel.lean`**. Its main accepted declaration is

`AdalyFormal.Round4.Guarded.DecayR2.Diagnostic.arbitrarily_small_separated_model`

at `Attempt.lean:470`. It is an exact matrix diagnostic, not a pinned goal, a lattice construction, or a cofinal failure certificate. The retained round-4 namespace identifies its provenance; these are repaired/recompiled inherited results, not newly discovered matrix counterexamples.

The more ambitious combined lattice lift is preserved separately as **`KernelDraft.lean`, unverified**. The final interrupted compilation was not relaunched. This separation keeps an unverified extension out of the accepted final file.

## 1. What was actually verified

Both previously uncompiled model drafts were copied into this directory and compiled through the supplied wrapper. Original rounds were not edited.

### Decay model — accepted final file

The copied definitions are

\[
 B=\begin{pmatrix}1&t\\t&1+d\end{pmatrix},\quad
 D=\begin{pmatrix}0&0\\0&d\end{pmatrix},\quad
 \Theta=\begin{pmatrix}t^2-1&0\\0&0\end{pmatrix}.
\]

For every positive correction cap and transmission bound, the main theorem chooses positive \(t,d\), each at most \(1/4\), below the respective bounds, and proves:

- exact disjoint direct supports: \(D\Theta=\Theta D=0\);
- units of \(B,C=B-D,A=B+\Theta\), but non-unit \(A-D\);
- localized inverse boundary columns with interior coordinates bounded by \(2t\);
- inverse-relative response change of absolute value exactly one.

The accompanying theorems prove fixed localized energy gaps, exact Green columns, actual scalar boundary responses, and correction-visible amplification. The model determinants are

\[
 \det B=1+d-t^2,\quad \det C=1-t^2,\quad
 \det A=t^2d,\quad \det(A-D)=0.
\]

The algebraic corrected kernel direction is \((1,-t)\). It is **not** a lattice bond field.

The only proof repair needed in the inherited decay draft was removal of a redundant `dsimp` after the division inequality had already unfolded the coefficient. Unused simplifier arguments were removed as well. Definitions and theorem statements were retained.

Actual command:

```sh
AHP/round3/lean1.sh AHP/round5/guarded/kernel-r1/DecayModel.lean
```

**Exit 0**, no warnings/errors. Evidence is `DecayModel.lean.log` and `DecayModel.lean.exit`, not a manufactured final-path log. All **56 local declarations** have dependency records, including all 42 pin declarations and the 14 model declarations. Every dependency set is permitted.

```text
'AdalyFormal.Round4.Guarded.DecayR2.Diagnostic.arbitrarily_small_separated_model' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Final/compiled-copy SHA-256:

```text
d2155bede9ab6340e8fb5b3dd1bf73e6fd961ce20e700128cf4cb32baa6f3c67
```

`python3 AHP/round5/guarded/kernel-r1/audit.py` passes and writes `CHECKS.json`. It checks exact final/compiled-copy equality, the entire pin prefix, sole frozen import, source/log/exit chronology **for the actual compiled copy**, all local dependency records, allowed dependencies and forbidden-token absence. It does not pretend that `Attempt.lean` was compiled again after the timeout.

### Gap model — successful repaired replay, secondary evidence

`GapModel.lean` is the full copied `gap-r2/Work.lean`, with local proof repairs. It reached wrapper **exit 0**. Its accepted main diagnostic is `AdalyFormal.Round4.Guarded.GapR2.localized_gap_and_direct_locality_insufficient`: fixed positive localized gaps, arbitrarily small correction and direct mixing, annihilation of the boundary range by the correction, carrier unit and corrected non-unit, using the pin's continuous-linear-map response.

Repairs addressed simplification of zero products, a missing nonzero denominator, rewriting only the inverse argument rather than the entire target, and the continuous-linear-map operator-norm scalar inequality. No model definition or theorem statement was changed. The successful version has one tactic-style warning; it has no errors or forbidden dependencies. A subsequent warning-only edit was reverted exactly to the successful version. Its source timestamp therefore records restoration, not a new compile. The clean, unchanged decay-model run above is the primary final evidence.

## 2. The attempted lift — NOT accepted as compiled

`KernelDraft.lean` starts with the complete refute-r1 attempt verbatim, hence the complete pin verbatim. It then includes both models and the new conditional work. It imports only `DrEquiv`.

The new obligation `ExactModes P` (`:2313`) uses the **actual** pinned assemblies. It asks for normalized orthogonal carrier vectors \(u,v\) and positive \(t,d\) satisfying the full-vector identities

\[
 Bu=u+tv,\qquad Bv=tu+(1+d)v,
\]
\[
 Du=0,\qquad Dv=dv,
\]
\[
 \Theta u=(t^2-1)u,\qquad \Theta v=0.
\]

It also retains the full-complement condition

\[
 \langle u,x\rangle=\langle v,x\rangle=0,\quad Ax=0
 \quad\Longrightarrow\quad x=0.
\]

This last clause is essential: a nonsingular two-dimensional restriction alone says nothing about other lattice modes. The six action equations must be full-vector equalities, **not just entries of a compression**, or the proposed kernel may have nonzero leakage into other coordinates.

Draft declarations:

| Declaration (prefix `AdalyFormal.Round5.Guarded.KernelR1`) | Line | Intended scope |
|---|---:|---|
| `two_mode_unit` | 2247 | Symmetry, two mode equations and complement injectivity imply full unit. |
| `two_mode_kernel` | 2277 | Explicit nonzero full-space kernel `u - t • v` from the action equations. |
| `direct_mixing_required` | 2293 | The literal ansatz requires `D (B u) ≠ 0`; inverse-mediated transmission does not prove it. |
| `actual_two_mode_separation` | 2326 | Conditional unit/kernel certificate on the actual pinned lattice carrier. |
| `mode_requires_positive_source_pairing` | 2349 | The proposed positive correction eigenvalue requires a positive genuine source pairing. |
| `dil_class_exterior_independent` | 2362 | Class membership for refute-r1's family transfers between arbitrary exterior fields with alpha/epsilon fixed. |
| `cofinalPencilFailure_of_dil_modes` | 2387 | Conditional assembly of all class, geometry, cap and competitor obligations using the copied family. |
| `goalNeg2_of_dil_modes` | 2415 | Conditional implication to the unchanged negative goal. The realization premise is unproved. |

The cofinal draft fixes `a` first, uses `m=m0+1`, `q=2^m0`, `R=2*(R0+18)`, and chooses the cap-dependent interior curvature before the exterior witness. `dil_class_exterior_independent` is designed to justify that order without wrongly assuming the class theorem's existential epsilon is uniform in V. **None of these draft results counts as a new verified result in this report.**

### Interrupted compile and provenance

A first combined compile completed with exit **1**: the concrete source-pairing lemma failed to rewrite its scalar inner product. Other new declaration records printed permitted dependencies during that failed run, but a failed file is not accepted as a successful compilation.

The revised source factors the scalar identity into generic helper `eigen_inner` and removes new linter warnings. Its direct wrapper invocation timed out after 200 seconds while another worker held the shared Lean lock. The new log was empty. Process inspection showed no surviving kernel-route wrapper/compiler. The old exit file had value 1 and a timestamp **before the revised source**; it was not mistaken for completion of the revised invocation.

**No relaunch occurred after the timeout.** The files were preserved as:

- `KernelDraft.lean`: revised, unverified combined source;
- `KernelDraft.interrupted.log`: empty interrupted-run log;
- `KernelDraft.previous-failed.exit`: explicitly labelled stale exit from the earlier failed source.

The accepted final `Attempt.lean` was then copied from the already successful `DecayModel.lean`. No `.log` or `.exit` was fabricated for that final path. The structured report's exit 0 refers to its **exact compiled copy**. A future authorized fresh compile of the draft is still required before using any of its new lemmas; even success would not provide a realization of `ExactModes`.

## 3. Concrete mathematical obstacle

No actual lattice vectors \(u,v\), no exterior field V realizing their action equations, and no proof of complement injectivity were found, even for one admissible instance.

The two coordinates of the matrix models are respectively a boundary-response coordinate and a correction-visible interior coordinate. These descriptions are **not a dictionary to lattice modes**. The required dictionary must accommodate all of `Wop`, the site projection, mass/constraint operators, positive-level raw jets and the assembled localized source pairing. Geometric dilation of refute-r1's family is not an operator intertwiner. Raw point support or a two-coordinate compression is not an invariant subspace theorem. Direct two-site mixing is particularly restrictive: the ansatz forces

\[
 D B u = td\,v\ne0,
\]

whereas the useful long-distance coupling in a lattice may occur through eliminated modes or full inverses instead. A Schur-complement construction would need to reconstruct those eliminated components, not omit them.

There is a separate unproved nonlinear condition. With \(\|v\|=1\), the identity \(Dv=dv\), \(d>0\), would force

\[
 \langle H_{\rm in} C^{(2)}_{\rm in}(v),J_{\rm in}\rangle=d/2>0.
\]

The cofinal family's exact interior plaquette holonomy proves neither this positivity nor even nonzero assembled D. Curvature cannot be substituted for this calculation. Likewise, the flat-interior exterior crossing has D=0 and cannot supply the required separation.

Finally, any successful instance must persist cofinally with a fixed positive `a`, arbitrarily large m and R, **R chosen before every cap**. The inherited geometric family settles those nonspectral obligations, not the operator equations. None of the repaired matrix models supplies them.

## 4. Scope and hygiene

The complete pin is unchanged. No positive or negative goal is weakened; `ExactModes` and `DilModeRealisation` are separately labelled, unproved sufficient obligations in an unverified draft. No completion is claimed from an implication, a determinant model, a definition's dependency print, or the failed/interrupted combined run.

The requested judgement, PIN, mining material, and all available round-4 route notes/obstacle text were inspected. The 419-entry mining inventory was not independently re-proved. Relevant frozen operator, jet and class definitions were inspected; no new source-reading conclusion is claimed.

All writes and the one scratch-file removal stayed inside `AHP/round5/guarded/kernel-r1/`. Only direct calls to the shared wrapper were used for Lean. No terminal, numerical script, direct Lean/Lake command, reproduction, build, dependency update, protected-source edit, commit or push was used.
