# Guarded gap route, round 1

**Status: open. Closed goal: none.** The full 352-line round-3 pin is the byte-for-byte prefix of `Attempt.lean`. No goal, selector, class, quantifier or assembly was changed. New declarations are in `AdalyFormal.Round4.Guarded.GapR1`.

## What the Total route actually yields

Read the three requested judgement/pin documents in full, the mining report's conclusions and relevant catalogue index, and the actual frozen declarations in `TT_F`, the coercivity/unit portion of `TT_C`, `MI21`, `DLR1`, `DS1`, `UMC`, `GdGen3`, `D1Lit`, and `R2Algebra`.

`TT_F.lean:29` defines Total; its proved theorem is at line 43. The `hcoer` at `TT_C.lean:246` estimates **localized** `P.data.Ginv`. The localized D-layer is subtracted at `MI21.G1inv_coercive_strat`; `MI21.G1inv_coercive_plain` has ordinary-norm coefficient

\[
(c_w-\varepsilon)\ell^{-2k}.
\]

The positive numerical constant chosen before the instance is a **weighted** constant. The final uniform coercivity constant of Total controls the pulled-back final form; it is not a singular-value bound for the all-plaquette carrier or its boundary response. The total theorem exports localized units, not a quantitative all-plaquette gap. Its later localization and torus descent do not silently export `hcoer` as a new all-plaquette theorem.

`DS1.delta2_strat` is the reusable small-correction estimate. The correction is small through its source pairing. The raw second jet is quadratic in its input, not asserted quadratic in the background smallness. Accordingly this attempt proves a **linear** source-smallness bound, not an unsupported quadratic bound.

## New formal content

All operators below are the pinned assemblies, except the explicitly labelled scalar diagnostic. Write \(A=G^{-1}_{\rm all}\), \(B=G^{-1}_{\rm in}\), \(D=\Delta^{(2)}_{\rm in}\), \(\Theta=A-B\), and \(w(x)=\texttt{wnormSq}(x)\).

1. `weighted_norm_le` proves \(w(x)\le\|x\|^2\), uniformly in depth. `weighted_norm_pos` proves strict positivity at every nonzero carrier vector using the actual depth-dependent lower comparison.
2. `delta2_norm_le_weighted` converts \(|\langle x,Dx\rangle|\le\varepsilon w(x)\) into \(\|D\|\le\varepsilon\), using the genuine symmetry theorem. Thus the **upper** ordinary operator bound has no depth loss.
3. `delta2_norm_le_source` uses the frozen `DS1.delta2_strat` to prove
   \[
   \|D\|\le (2L K_2 C_W)t
   \]
   when the actual source field satisfies \(\|\psi_D(p)\|\le Lt\), with the displayed raw-jet and weighted Wop bounds. `correction_cap` chooses a positive cap before P and t, namely \(\varepsilon/[2(2LK_2C_W+1)]\), sufficient for \(\|D\|<\varepsilon\) under those hypotheses. These hypotheses are retained; this is not an assertion that the entire class has already been discharged in this file.
4. `pencil_weighted_lower` gives the exact accounting
   \[
   \langle x,(A-D)x\rangle\ge(c_w-\varepsilon-\beta)w(x)
   \]
   from the localized lower bound, the D-layer bound, and **the additional explicit boundary-shift bound** \(\langle x,\Theta x\rangle\ge-\beta w(x)\). `pencil_isUnit_of_weighted_boundary_gap` proves the actual corrected carrier is a unit if \(\varepsilon+\beta<c_w\). That last boundary premise is not inferred from Total or the guard.
5. `pencil_failure_forces_negative_boundary_energy` is the strongest concrete obstruction produced here. Given the localized bounds and \(\varepsilon<c_w\), failure of the actual corrected unit forces a nonzero actual carrier kernel vector x with
   \[
   \langle x,\Theta x\rangle\le-(c_w-\varepsilon)w(x)<0.
   \]
   This does not assert such a vector exists on the class: failure remains a premise. It does not need the carrier guard, so in particular it applies to a guarded failure with the same localized estimates.
6. `pencil_lower_on_V0` transfers the localized lower bound to the actual all-plaquette corrected pencil on the **known agreement subspace** V0, using `GdGen3.Ginv_eq_on_V` and its genuine geometry/room hypotheses. It does not transfer that bound to the complementary boundary range W.
7. `response_lower_of_carrier_lower` proves the useful correct response estimate
   \[
   g\|y\|\le\|B\|\|K_By\|
   \]
   assuming a singular-value lower bound \(g\|x\|\le\|(B+\Theta)x\|\) on the full carrier and a unit of B. `inverse_response_norm_of_carrier_lower` gives \(\|K_B^{-1}\|\le\|B\|/g\) when \(g>0\) and K_B is a unit. The lower bound is explicitly for **A=B+Theta**, not B. This identifies precisely the missing input to the existing inverse-relative perturbation criterion.

## Why the naive gap transfer is invalid

`scalar_gap_obstruction` is an exact real-scalar diagnostic, **not a lattice configuration, not a cofinal certificate, and not a proof of either negative pinned goal**. For every positive cap choose

\[
d=\min(\mathrm{cap}/2,1/4),\quad B=1,\quad D=d,\quad\Theta=d-1.
\]

The theorem proves: B, C=B-D and A=B+Theta are units; \(C\ge3/4\); \(0<|D|<\mathrm{cap}\); \(A-D=0\) is not a unit; \(\Theta\ne0\); and the scalar response formulae satisfy

\[
0<|K_B|=d<\mathrm{cap},\qquad K_C=0.
\]

Thus even a fixed strictly positive localized gap, an arbitrarily small correction, and the carrier unit guard together do not imply a response gap or corrected invertibility in abstract algebra. Here the absolute response difference tends to zero, while its inverse-relative value is minus one. The diagnostic does **not** exclude a proof using additional actual lattice structure.

## Concrete remaining obstacle

The missing theorem must control the all-plaquette boundary directions, for example a class-uniform inverse-relative gap for K_B, a sufficiently small weighted negative part of Theta, or an exact propagation/cancellation property. Total's localized coercivity and D-layer estimate do not themselves furnish it. An ordinary localized inverse estimate obtained by forgetting the weights would additionally grow like \(\ell^{2k}\); the pinned cap is chosen before arbitrary depth, so a cap depending on k is invalid. A weighted or boundary-specific estimate could avoid this loss, but is not proved here.

Changing the permissible order to m, then R, then cap does not fix the missing boundary estimate: no all-plaquette gap has been established at a fixed m,R over all permitted exterior backgrounds. In particular this file does not prove `GShape CBoundaryResponse`, `GoalPos1`, `GoalPos2`, or either negation.

## Verification status

Compilation was exclusively through the supplied `AHP/round3/lean1.sh`. The initial foreground invocation for `Attempt.lean` ended without an exit file and with an empty log. Subsequent process inspections found no remaining invocation for that path. It was not relaunched. Verification proceeded on separately named copies in persistent BB terminals; no concurrent duplicate compile was launched.

| Invocation | Result |
| --- | --- |
| `AHP/round3/lean1.sh AHP/round4/guarded/gap-r1/Attempt.lean` | Interrupted before an exit record; empty log, not accepted as compilation evidence. |
| `AHP/round3/lean1.sh AHP/round4/guarded/gap-r1/Check1.lean` | Exit 1: an unresolved namespace in the weighted-norm lemma; not accepted. |
| `AHP/round3/lean1.sh AHP/round4/guarded/gap-r1/Check2.lean` | Exit 1: a final algebraic tactic in the inverse-response bound; not accepted. |
| `AHP/round3/lean1.sh AHP/round4/guarded/gap-r1/Check3.lean` | **Exit 0**, no warnings/errors, final byte-identical copy of `Attempt.lean`. |

`Check3.lean.exit` and `Check3.lean.log` are the actual final wrapper records. No successful `Attempt.lean.exit` or replacement log has been manufactured. The reported exit 0 refers to compilation of its exact copy `Check3.lean`.

`python3 AHP/round4/guarded/gap-r1/audit.py` passed. `CHECKS.json` records the unchanged pin prefix, byte identity with the successfully compiled copy, the sole frozen import, a clean forbidden-token scan, source/log/exit timestamp order, complete local dependency-print coverage, and **54** accepted dependency records (**42** pin declarations plus **12** new theorems), all subsets of the permitted three. Earlier failed logs are historical diagnostics only.

Final source SHA-256:

```text
efa8a63101212eaedb1f771224ee8fe795e39000f8bf2b86bd7d5781784784c6
```

Main partial declaration at `Attempt.lean:505`:

```text
'AdalyFormal.Round4.Guarded.GapR1.pencil_failure_forces_negative_boundary_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The sufficient actual-pencil criterion is at line 476, the source/cap bounds at lines 412/431, the exact scalar obstruction at line 550, and the inverse-response estimate with its explicit all-carrier gap premise at line 623. Every new helper has its own dependency record. This is a successful partial-result compilation, **not** completion of any pinned goal.

The final file imports only frozen `DrEquiv`; its transitive imports provide `DS1`, `MI21`, and `DLR1`. There is no AHP import. All authored files stay in `AHP/round4/guarded/gap-r1/`. No numerical experiment, reproduction, build, direct compiler invocation, dependency update, protected-source edit, deletion, commit or push was performed.
