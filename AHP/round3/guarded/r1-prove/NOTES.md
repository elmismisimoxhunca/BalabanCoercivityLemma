# Guarded all-plaquette reading — round-3 positive attempt, pass 1

## Disposition

**closedGoal: `none`.** Neither pinned positive goal has been closed. The compiled partial results are a sharper selector-shell locality statement, a conditional support-propagation route, and an inverse-relative boundary-response criterion. Final shared-wrapper compilation exited **0**, with no errors or warnings and only permitted dependency lists.

Furthest compiled partial declaration: `AdalyFormal.Round3.Guarded.R1Prove.goalPos2_of_return_offSelectorShell`, **`Attempt.lean:835`**. Its type is `GShape CReturnOffSelectorShell -> GoalPos2`; the premise is unproved. It is **not** a proof of the pinned goal. The independent quantitative route is at **:817**.

The complete round-3 `pin/Statement.lean` is copied byte-for-byte at the beginning of `Attempt.lean`, including its retained round-2 namespaces, all four goal definitions, and its boundary-response appendix. No goal, class, operator, quantifier, or guard is changed. Only frozen `DrEquiv` is imported; no AHP module is imported.

## Starting points inspected and reused

Read the handoff, OPEN_ITEMS (including B, K–N, R and S), Stage-B results, round-2 results, guarded JUDGEMENT in full, both round-2 positive and both negative attempts and their notes, and the round-3 pin.

Frozen proofs inspected:

- `lean/src/GdGen1.lean`, `Wop_zero_on_notIn`, and `GdV.lean`: the gauge-fixing potential is zero outside Omega1 on omitted-plaquette edges. Its proof contains a stronger intermediate observation that does not require the input field to vanish on all level-zero bonds.
- `lean/src/GdGen3.lean:66`, `Ginv_eq_on_V`: actual localized/all-selector agreement on V0. The new support argument follows this proof but requires zero input only on omitted-plaquette edges.
- `lean/src/GdGen4.lean:58`, `unit_transfer`: reuse its finite-dimensional kernel-to-unit method; the theorem itself assumes carrier units and cannot provide the missing corrected unit.
- `lean/src/R2Algebra.lean:145,149,220,222,230`: actual carrier, constraint solution, correction, its quadratic identity, and corrected-operator identity.
- `lean/src/DrEquiv.lean:60,116`: eventual threshold combination with localized well-definedness, and equivalence of the two pinned positives.
- `lean/src/DrMargin.lean:33`: existing positive-coercivity margin, insufficient for arbitrary indefinite literal units.
- `lean/src/GdR6b.lean:40,82`: zero correction for a source orthogonal to V0 and for the base-point-identity family. Those hypotheses are not consequences of the entire class.
- `lean/src/SolR345Audit.lean:68`: the full-guard theorem consumes corrected invertibility; using it to obtain that missing premise would be circular.
- `lean/src/ZR8DataA.lean:83`, `C2fullOf_congr_in`: raw second-jet input locality. It does not establish locality of the two inverses in the boundary return.
- `lean/src/DS1.lean:77` and `DLR100.lean:54`: genuine correction estimates, with their hypotheses retained. The latter is an M0/full-domain statement. Neither supplies the inverse boundary-response gap required here.

The necessary round-2 response algebra and proof bodies are copied verbatim after the pin, without redeclaring its five appendix definitions. In particular the equivalence with `GShape CBoundaryResponse` is reused, not counted as new closure.

## New source-specific locality route

Write
\[
A=G^{-1}_{\rm all},\quad B=G^{-1}_{\rm in},\quad
D=\Delta^{(2)}_{\rm in},\quad C=B-D,\quad\Theta=A-B.
\]
All are the genuine pinned assemblies at the same `IngrBParams`.

`offSelectorShell P` consists of carrier fields zero on every edge of every plaquette omitted by `plaqIn Omega0`. Since the carrier itself is supported on touching bonds, the exterior coordinates outside that carrier are already zero. No identification with a printed domain convention is asserted.

The compiled `Wop_eq_on_selector_shell` (**:562**) strengthens an intermediate step of frozen `Wop_zero_on_notIn`: under admissibility and `4 <= R*M`, for **every** input field, `Wop` equals the input on these edges. Indeed the gauge potential vanishes at both endpoints there. The old proof additionally used zero level-zero trace only to make the input itself zero; that assumption is unnecessary for the equality.

Consequently `boundaryShift_kills_offSelectorShell` (**:591**) proves that Theta kills fields zero on this shell. Symmetry yields `boundaryShift_range_le_selector_shell` (**:627**), putting its entire range in the orthogonal complement of this submodule. `V0_le_offSelectorShell` (**:639**) proves that the old all-level-zero vanishing space is contained in the new one; no strict inclusion is claimed. This is actual operator locality, not a statement that either localized Green operator preserves shell support.

The attempted zero-return proof still needs the propagation statement
\[
 C^{-1}DB^{-1}(\operatorname{range}\Theta)
 \subseteq\texttt{offSelectorShell P},
\]
or a weaker cancellation sufficient for Theta to annihilate that image. `pencil_isUnit_of_return_offSelectorShell` (**:780**) proves that this propagation statement suffices pointwise under localized well-definedness and the literal guard. `goalPos2_of_return_offSelectorShell` (**:835**) supplies the unchanged eventual/headline implication using frozen `GShape_imp`. Raw locality does not prove the propagation after inversion. This is the precise point at which the support route stops.

## Inverse-relative quantitative route

On \(W=\operatorname{range}\Theta\), use the pinned responses
\[
K_B=I+\Theta B^{-1},\qquad K_C=I+\Theta C^{-1}.
\]
Define the actual inverse-relative return
\[
F=K_B^{-1}(K_C-K_B).
\]
No compressed inverse is substituted for an inverse on the full carrier. The literal guard and localized carrier unit make \(K_B\) a unit by the reused exact response equivalence.

The compiled `kernel_iff_relative_neg` (**:658**) gives the exact equivalence
\[
K_Cy=0\quad\Longleftrightarrow\quad Fy=-y.
\]
Thus \(\|F\|<1\) suffices for corrected invertibility, including when the literal carrier is indefinite (`pencil_isUnit_of_relative_boundary_smallness`, **:751**). A guarded failure forces a nonzero minus-one mode and \(\|F\|\ge1\) (`guarded_failure_has_relative_boundary_mode`, **:763**). These results neither exhibit nor exclude that mode on the entire class.

The norm estimate explicitly retains the previously missing inverse-response factor:
\[
\|F\|\le
\|K_B^{-1}\|\,\|\Theta\|\,\|C^{-1}\|\,\|D\|\,\|B^{-1}\|.
\]
An absolute smallness estimate on the return or on D alone is not the sufficient condition established here. No uniform bound on \(K_B^{-1}\), or on its product with the actual return, is obtained from capped alpha0. A unit guard is not a quantitative lower gap.

`goalPos2_of_relative_boundary_smallness` is only the conditional implication
`GShape CRelativeBoundarySmall -> GoalPos2`, with the full pinned eventual, class, and positive-test-field prefix. Its premise is unproved. The thresholds in `GShape_imp` may enlarge and its smallness cap may shrink; no fixed-instance constant-preserving claim is made.

## Verification and scope

Final source: `Attempt.lean`. Final compile evidence: `Attempt.lean.log`, `Attempt.lean.exit` (**0**). The final log has no errors or warnings. All **75** local declarations have individual dependency prints; **14** directly reused frozen roots are printed too, for **89** records. Every record contains a subset of `propext`, `Classical.choice`, `Quot.sound`. The main dependency record, normalized to one line, is:

```text
'AdalyFormal.Round3.Guarded.R1Prove.goalPos2_of_return_offSelectorShell' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`python3 AHP/round3/guarded/r1-prove/validate.py` passed and saved `VALIDATION.json`. It checks the exact complete pin prefix, sole frozen import, raw prohibited-token scan (including comments), all local dependency records, permitted dependency sets, exit code and source/log/exit timestamp order.

Final source SHA-256:

```text
13fbbd1fbf0745cca23449239d9112c2acc689fdcc61ae3fd642f72e29e3205f
```

All Lean invocations were exclusively through

```sh
AHP/round3/lean1.sh AHP/round3/guarded/r1-prove/Attempt.lean
```

The shared lock and heavy-slot queue delayed compilation. The first foreground invocation timed out while waiting; another foreground invocation ended without an exit record. Neither is counted as compilation evidence. Persistent bb terminals then ran the same wrapper to survive command transport interruptions. The first completed compilation exposed two nested-subspace instance-resolution errors; these were repaired by specializing the generic criterion to the response range before substituting the concrete carrier. The last terminal finished normally and freshly wrote exit 0. The retained log/exit are from that final successful source. No two Lean compilations from this attempt ran concurrently.

No independent second-agent recheck, source-page image review, numerical operator dictionary, or whole-project rebuild is claimed. Proposition-definition dependency prints do not prove their bodies. The acceptance boundary is the compiled partial results above; `GoalPos1` and `GoalPos2` remain open.

No numerical script was run. No build, reproduction, dependency update, deletion, commit, push, or protected-file edit was performed. Every authored workspace file is under `AHP/round3/guarded/r1-prove/`. Other workers' changes were left untouched.
