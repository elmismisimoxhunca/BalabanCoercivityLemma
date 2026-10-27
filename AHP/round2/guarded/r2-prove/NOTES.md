# Guarded all-plaquette reading — positive attempt, round 2

## Disposition

**closedGoal: `none`.** Neither pinned positive goal is proved. The new work is an exact boundary-response reduction of the actual operators, a resolvent identity, a conditional positive route, and a necessary obstruction to that route. These do not establish a uniform unit-transfer theorem.

Final source: `Attempt.lean`. Furthest compiled partial declaration at **line 554**:

`AdalyFormal.Round2.Guarded.R2Prove.goalPos2_iff_boundary_response`.

Its type is an equivalence, not a proof of either pinned positive goal.

The entire pinned `pin/Statement.lean` is copied verbatim as the file's prefix. The sole import is frozen `DrEquiv`. All later declarations are in the separate namespace `AdalyFormal.Round2.Guarded.R2Prove`. None of the goal statements, class hypotheses, operators, or threshold orders is changed.

## Starting point

Read the requested handoff and OPEN_ITEMS sections, STAGE_B_RESULTS, guarded design/attack/decision and Stage-B source/verification records, prior residual prosecution/review, both round-1 attempts, and the pin. The old small-box numerical scripts were read for scope; no numerical script was run in this attempt.

Started from these frozen proofs, not from a new positivity assumption:

- `lean/src/GdGen4.lean:58`, `unit_transfer`: reused its finite-dimensional kernel-to-unit argument. Its original statement assumes both carrier units, so it cannot itself supply corrected invertibility.
- `lean/src/GdGen3.lean:66`, `Ginv_eq_on_V`: proves actual literal/localized agreement on fields with zero level-zero trace. Symmetry now also identifies the range of their difference as orthogonal to that subspace.
- `lean/src/R2Algebra.lean:230`, `isG1inv_sub`, and `G1inv_unique`: identify the corrected localized operator with the already-controlled localized `G1invS`.
- `lean/src/DrEquiv.lean:60`, `GShape_imp`: supplies the unchanged eventual threshold combination and localized well-definedness. The final headline equivalence reuses `P428Target8SG_iff_pencilT`.
- `lean/src/SolR345Audit.lean:68`, `full_guard_literal`: inspected, but unusable for closing this goal because its guard already assumes corrected invertibility.

The round-1 reduction required a bound on the product of the **literal inverse** and the correction, or a kernel-location theorem. The new reduction removes the literal inverse from the auxiliary operators: only the two localized inverses occur.

## Exact boundary response

For notation in this note only, let

\[
A=(\mathrm{dataS}_{\rm all}).Ginv,\qquad
B=(\mathrm{dataS}_{\rm in}).Ginv,\qquad
D=(\mathrm{dataS}_{\rm in}).Delta2,\qquad
\Theta=A-B,\quad C=B-D.
\]

These are the actual pinned assemblies at one `IngrBParams`, not independent matrices. The Lean definitions `boundaryShift` and `localCorrected` implement exactly \(\Theta\) and \(C\).

Set \(W=\operatorname{range}\Theta\). On this genuine subspace define

\[
K_B y=y+\Theta B^{-1}y,\qquad K_C y=y+\Theta C^{-1}y.
\]

`response` constructs these as continuous linear endomorphisms of \(W\). This is **not** the inverse of a compressed operator. No equality between compression/inversion is asserted. The range can be zero, and no claim is made that it is a proper subspace in every geometry.

### Compiled partial statements (line numbers in `Attempt.lean`)

1. **:300**, `unit_add_iff_response`: whenever the reference operator is a unit, its sum with \(\Theta\) is a unit iff its response on \(W\) is a unit. The proof constructs the kernel correspondence directly, then uses finite dimension.
2. **:435/:444**, `boundaryShift_kills_V` and `boundaryShift_range_le_orthogonal`: under the frozen admissibility/room assumptions, \(\Theta V_0=0\) and \(W\subseteq V_0^\perp\). Here \(V_0\) means zero on **every** level-zero bond, not merely a geometric shell.
3. **:459/:467**, `carrier_isUnit_iff_response` and `pencil_isUnit_iff_response`: with the corresponding localized units, the literal guard is equivalent to `IsUnit K_B`, and the target pencil condition is equivalent to `IsUnit K_C`.
4. **:341/:362**, `inverse_sub_apply` and `response_sub_apply`: when \(B,C\) are units,
   \[
   C^{-1}-B^{-1}=C^{-1}DB^{-1},\qquad
   (K_C-K_B)y=\Theta C^{-1}DB^{-1}y.
   \]
5. **:475**, `pencil_isUnit_of_no_boundary_return`: localized well-definedness, the literal guard, and vanishing of the displayed return for every \(y\in W\) imply the actual pencil is a unit. This permits nonzero \(D\) as a conditional algebraic statement; it supplies no new non-flat in-class witness satisfying the premise.
6. **:496**, `guarded_failure_forces_boundary_return`: localized well-definedness and a genuine unit/non-unit separation force a nonzero \(y\in W\) with \(K_Cy=0\) and \(\Theta C^{-1}DB^{-1}y\ne0\). This proves neither existence nor exclusion of that boundary mode.
7. **:554**, `goalPos2_iff_boundary_response`: the exact pinned `GoalPos2` is equivalent to `GShape CBoundaryResponse`, which asks for `IsUnit K_C` at the unchanged eventual/class/test-field prefix. The equivalence is not a proof of either side and need not preserve chosen constants. `goalPos2_of_no_boundary_return` at **:569** separately proves a sufficient implication with the same prefix; its premise is not discharged.

## Why the positive proof stops

The literal guard supplies invertibility of \(K_B\), not of \(K_C\). Their difference is the actual return

\[
\Theta C^{-1}DB^{-1}\big|_W.
\]

The frozen agreement \(\Theta V_0=0\) does not show that \(C^{-1}DB^{-1}W\subseteq V_0\), and no such theorem was found. Locality of the raw correction alone would not imply locality after the two Green operators. The class and long collar do not currently give an exact zero-return identity.

A small return estimate alone would also need an inverse-relative gap for \(K_B\). `IsUnit K_B` at each point supplies no uniform positive lower gap as the exterior configuration varies. The old failure of literal positive domination therefore is not repaired merely by using localized inverse estimates. This is a specific missing analytic statement, **not** a proof that positive transfer is impossible.

The exact remaining positive obligation is `GShape CBoundaryResponse`: exclude a nonzero boundary vector satisfying \(y+\Theta C^{-1}y=0\) whenever \(K_B\) is a unit, uniformly through every pinned parameter/class quantifier. A sufficient stronger route is `GShape CNoBoundaryReturn`; it is not claimed necessary and remains unproved. Base-flat paths have \(D=0\), but that does not cover non-flat interiors. Neither this attempt nor a finite-torus numerical candidate settles the cofinal negative question.

## Verification

Final serial compilation exited **0**, with no errors or warnings. The retained `Attempt.lean.log` and `Attempt.lean.exit` belong to the final source; the exit record is newer than the log, which is newer than the source. No earlier interrupted invocation is counted.

All **71** requested dependency records were emitted: **62** locally declared definitions/theorems (37 copied pin declarations and 25 appended declarations), plus nine directly reused frozen roots. Every record lists only `propext`, `Classical.choice`, `Quot.sound`, or the empty set. Every helper has an individual print. The main record is:

```text
'AdalyFormal.Round2.Guarded.R2Prove.goalPos2_iff_boundary_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`validate.py` passed and wrote `VALIDATION.json`: exact pin byte prefix, sole frozen import, zero whole-source prohibited-token hits, complete print coverage, permitted dependencies, final exit, timestamps, and declaration line numbers. Source SHA-256:

```text
183d253712e04e4ccbfd13a0a367e4d6ba368bfd840230e7a4f595a0b2c4f949
```

No independent second-agent verification or whole-project rebuild is claimed.

Exact serial command, from the frozen project:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/round2/guarded/r2-prove/Attempt.lean > ../AHP/round2/guarded/r2-prove/Attempt.lean.log 2>&1
echo $? > ../AHP/round2/guarded/r2-prove/Attempt.lean.exit
```

Intermediate tactic/coercion errors were repaired. A concrete nested-subspace typeclass problem was resolved by proving the kernel extraction and injectivity helpers in the generic algebra section and specializing them, without changing any statement. Foreground heavy-slot waits and a later persistent-terminal invocation were interrupted; the latter's terminal reported `daemon-disconnect`, leaving a stale exit record despite its clean printed output. That run was rejected as compilation evidence. The final **foreground** invocation of the exact command above completed and freshly wrote exit 0. No two Lean files were compiled by this attempt concurrently.

All writes by this attempt are under `AHP/round2/guarded/r2-prove/`. No build, reproduction, dependency update, deletion, commit, push, or protected-file edit was performed. Other threads' work in the shared checkout was left untouched.
