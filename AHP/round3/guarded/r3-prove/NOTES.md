# Guarded positive attempt — round 3, pass 3

## Disposition

**closedGoal: `none`. Neither pinned positive goal is proved.**

The furthest headline-facing compiled declaration is
`AdalyFormal.Round3.Guarded.R3Prove.goalPos2_of_diagonal_mixed_boundary_source_zero`,
`Attempt.lean:981`. Its type is

```text
GShape CDiagonalMixedBoundarySourceZero → GoalPos2
```

The premise is **unproved**. This is a sufficient route to the unchanged headline, not a replacement completion target. The genuine-operator identities below are partial results; neither negative goal is proved either.

## Contract and starting point

The complete 352-line `AHP/round3/guarded/pin/Statement.lean` remains the exact byte prefix of `Attempt.lean`. All definitions, four goals, namespaces, guards, and quantifier order are unchanged. The only import is frozen `DrEquiv`; no AHP import is used. The boundary-response proof prefix from the preceding positive attempt is also copied byte-for-byte, through its closing namespace, rather than reconstructed with replacement operators.

Read the handoff, requested OPEN_ITEMS sections, Stage-B and round-2 results, the complete guarded round-2 judgement, pin, original boundary-response proofs/notes, feedback and second-jet/nonflat results, and the preceding pass's positive proof/notes and negative notes. No numerical results were rerun or promoted to proof.

The nearest frozen proofs inspected and reused were:

- `lean/src/R2Algebra.lean:222`, `BaseDataS.Delta2_spec`: the actual symmetric correction and its quadratic form. The new polarization argument is the same argument already used in `AHP/round2/guarded/r1-refute/Attempt.lean:269`, with the three source pairings collected through linearity of H.
- `lean/src/R2Algebra.lean:258` onward, `isUnit_Q_inv_Qs`: its inverse-symmetry calculation is reused directly in `inverse_pairing` at `Attempt.lean:715`.
- `lean/src/GdGen4.lean:58`, `unit_transfer`: its kernel-to-unit pattern underlies the copied boundary-response reduction. It assumes the relevant carrier units and cannot furnish the missing corrected unit circularly.
- `lean/src/DrEquiv.lean:60`, `GShape_imp`: combines eventual thresholds and supplies localized well-definedness, retaining the original class, cap and competitor conditions.
- `lean/src/GdStat.lean:29,73,83`: constrained-solution and correction comparisons already require their unit premises. They do not identify the two unconstrained boundary Green extensions used below.

I also inspected `lean/src/DLR100.lean:54,96`: its genuine correction norm bound and M0/full-tower class theorem are absolute/localized estimates under their stated regime hypotheses. They are neither a zero-cancellation theorem nor a uniform inverse-response gap for this all-plaquette guard. I did not silently extend their full-tower scope to arbitrary pinned towers.

## New exact mixed-jet formulation

Use notation only for the actual pinned assemblies:

\[
A=G^{-1}_{\rm all},\quad B=G^{-1}_{\rm in},\quad
D=\Delta^{(2)}_{\rm in},\quad C=B-D,\quad
\Theta=A-B,\quad W=\operatorname{range}\Theta.
\]

Let H, C2 and J below be **localized data's actual** `H`, `C2`, `J`. Define

\[
q(u,v)=\langle H(C2(u+v)-C2(u)-C2(v)),J\rangle.
\]

`mixedJetSource` (`Attempt.lean:762`) implements precisely this expression. It retains the real dressing, jets, constrained solution and source through the frozen base-data assembly; it is not an arbitrarily chosen bilinear correction.

### Compiled identities

| Declaration | Line | Exact content |
|---|---:|---|
| `correction_pairing` | 769 | \(q(u,v)=\langle u,Dv\rangle\), by the genuine quadratic-form identity and symmetry. |
| `resolvent_pairing_eq_mixed_jet` | 804 | Under localized `WellDefAt`, \(\langle z,(C^{-1}-B^{-1})y\rangle=q(C^{-1}z,B^{-1}y)\), for all full-carrier y,z. |
| `no_return_iff_mixed_boundary_source_zero` | 826 | Exact zero return on W iff \(q(C^{-1}z,B^{-1}y)=0\) for every y,z in W. |
| `mixed_boundary_zero_iff_diagonal` | 858 | The preceding scalar cancellation holds iff \(q(C^{-1}y,B^{-1}y)=0\) for every y in W. Symmetry of the resolvent difference supplies the polarization; the mixed expression is not assumed symmetric without proof. |
| `return_norm_sq_eq_mixed_jet` | 892 | For \(v=C^{-1}DB^{-1}y\), \(\|\Theta v\|^2=q(C^{-1}\Theta^2v,B^{-1}y)\). |
| `pencil_isUnit_of_mixed_boundary_source_zero` | 909 | Localized well-definedness, the original literal guard, and the scalar cancellation imply the actual pencil is a unit. |
| `guarded_failure_forces_positive_mixed_source` | 922 | Any guarded failure has nonzero y,z in W, \(K_Cy=0\), and \(q(C^{-1}z,B^{-1}y)>0\). This is a necessary obstruction, not a failing instance. |
| `goalPos2_of_diagonal_mixed_boundary_source_zero` | 981 | The eventual diagonal cancellation premise implies the untouched positive headline. The premise remains open. |

The inverse operations are on the **entire carrier** before evaluating at boundary sources. No compression/inversion interchange is used. No fixed torus, flatness, positivity of the literal carrier, or new class condition is inserted into either pin.

### What changed relative to the previous pass

The previous route required the entire vector \(DB^{-1}y\) to vanish, using a stronger input-ball invisibility condition. This pass tests only a source-weighted mixed pairing against corrected boundary Green extensions. It is enough for that scalar pairing to cancel; neither extension nor \(DB^{-1}y\) is required to vanish. This is an exact characterization of the existing no-return condition, **not** a claimed new characterization of the positive goal itself, nor a proof of strictness on an inhabited class family.

The positive mixed-source obstruction is also more specific than merely finding a nonzero input on a jet ball. The proof chooses a boundary test from the nonzero return and obtains its squared norm exactly. It supplies no class instance where that return is nonzero.

## Why this still stops short

The missing sufficient statement is

\[
\texttt{GShape CDiagonalMixedBoundarySourceZero}:
\qquad q(C^{-1}y,B^{-1}y)=0\quad(y\in W)
\]

throughout the eventual pinned class. Neither capped alpha0 nor admissibility was shown to imply it. The cancellation criterion avoids demanding support preservation, but still involves the two full localized Green extensions. Raw jet locality only describes the jet given its input; it does not make these inverse-propagated inputs vanish or make their source pairing cancel.

The quantitative alternative remains unclosed too. Small absolute correction or return does not itself prove
\(\|K_B^{-1}(K_C-K_B)\|<1\). The carrier guard gives a unit of \(K_B\), not a class-uniform bound on its inverse. No additional gap or cancellation estimate was derived here, and the already-proved full-guard theorem assumes the missing corrected invertibility.

Consequently no reduction to an **already settled theorem** closes either positive pin. These obstacles do not prove that the positive goal is false or that all possible positive routes fail. The other worker's finite-radius floating-point candidates remain outside any exact conclusion of this file.

## Verification

Final compilation, exclusively through the required shared-lock wrapper:

```sh
LEAN_NUM_THREADS=1 AHP/round3/lean1.sh AHP/round3/guarded/r3-prove/Attempt.lean
```

Final `Attempt.lean.exit`: **0**. Final log: **no errors or warnings**. All **79 local declarations**, plus **10 distinct frozen roots**, have individual permitted dependency records, **89 distinct records** total. The main record, normalized, is:

```text
'AdalyFormal.Round3.Guarded.R3Prove.goalPos2_of_diagonal_mixed_boundary_source_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`python3 AHP/round3/guarded/r3-prove/validate.py` passed and saved `VALIDATION.json`. It verifies exact complete pin and reused-proof prefixes, sole frozen import, clean raw prohibited-token scan, fresh source/log/exit ordering, final exit 0, no diagnostics, complete local dependency coverage, and allowed dependencies.

Source SHA-256:

```text
0784988b5252fe245c8b1773218d21b2a96b324ed4d8234ac878eca10357ae3f
```

Three serial wrapper invocations were made. Initial failures were definitional-equality/rewrite elaboration issues between pinned and frozen assemblies and a linear-map coercion; these were corrected without changing any statement. Only the final successful run counts as evidence. No independent second-agent check or whole-project rebuild is claimed.

No numerical scripts, direct Lean/Lake invocation, build, reproduction, dependency update, commit or push was run. All authored files are under `AHP/round3/guarded/r3-prove/`. The temporary draft fragment was removed there. No protected file or other AHP path was edited.
