# Round 6 adversarial limits — pass 2

**closedGoal: `none`. No positive-amplitude crossing-kernel sign or cofinal obstruction was proved.**

There is now a **fresh successful final-path compile and complete dependency audit**. This repairs pass 1's missing retained verification. The new exact results prove invisibility of the bare outgoing boundary vector, and more generally of every input whose **W-dressed** field vanishes on all both-endpoint interior bonds. They do **not** identify that subspace with the crossing kernel.

## 1. Final verification

Final file: `AHP/round6/limits-r2/Attempt.lean`.

Commands, directly in the bash tool:

```sh
AHP/round3/lean1.sh AHP/round6/limits-r2/Attempt.lean
python3 AHP/round6/limits-r2/audit.py
```

- Wrapper exit **0**; no errors.
- One harmless deprecation warning at line 2828: `push_neg` prefers the spelling `push Not`.
- **158 local declarations**, each matched to a dependency print; **178 total dependency records**, all subsets of `propext`, `Classical.choice`, `Quot.sound`.
- Complete round-3 pin, round-5 IVT bridge, and pass-1 final attempt are unchanged byte prefixes. The copied polarization helper is also verbatim.
- Only frozen `DrEquiv` is imported; no AHP imports or forbidden proof constructs.
- Source/log/exit timestamp order and hashes are checked by `audit.py`; detailed results are in `CHECKS.json`.
- Final source SHA-256: `43c3bd051cf4ec664e8ba2d21d0bc0b7740f35ddf30a941e0fcc73eba258f34a`.

Main new partial declaration, line **2713**:

```text
'AdalyFormal.Round6.Guarded.LimitsR2.twistD_kills_interiorInvisible' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The final log was not overwritten by a later invocation. This is builder verification, not an independent replay.

## 2. What is newly proved

Write \(E=\operatorname{bondSupp}(\operatorname{geomOf}(2,1,\operatorname{dilTower}(q,R)))\), and let \(A,D,W\) be the actual copied `twistA`, `twistD`, and frozen `Wop`. All results below retain positive q, even R, and the room condition \(34\le R(2q)\). They allow **every real amplitude, mass, and exterior angle**, including positive amplitudes. No inverse or numerical hypothesis is used in the invisibility results.

### A. The formerly unverified bare-boundary lemma now compiles

The old draft's `rightVector` is the actual outgoing bond vector

\[
x_X=X\delta_{(\mathrm{rightSite},0)}\in E.
\]

At lines **2632** and **2663**:

\[
D x_X=0,\qquad \langle x_X,Dy\rangle=0\quad\text{for every }y\in E.
\]

Names retain namespace `AdalyFormal.Round6.Guarded.LimitsR1` because this is the recovered draft. The proof needs two elaboration repairs: explicitly supply the input vector to the polarization lemma and normalize the dependent carrier type of its bound variable before adding vectors. No mathematical premise was changed. The new appendix also lowers its local heartbeat limit to obtain bounded diagnostics.

The proof uses:

- `lean/src/D1Geo2.lean:74`, `Wop_sing`: W fixes this boundary vector for arbitrary background and mass;
- `lean/src/ZR8DataA.lean:83`, `C2fullOf_congr_in`: the actual second jet reads its argument only on bonds with both endpoints in Omega0;
- `Attempt.lean:2580`, the verbatim polarization lemma: translation invariance of the genuine quadratic jet kills the **full correction vector**, not merely its diagonal form;
- symmetry of the assembled correction to obtain orthogonality to its whole range.

The outgoing bond's second endpoint is outside Omega0. Thus its dressed input is zero on every bond the locality lemma reads.

### B. A whole invisible subspace, not only one vector

`LimitsR2.interiorInvisible` at line **2700** is the submodule

\[
N_{q,R,\varepsilon,a,t}
 =\{x\in E:(W_{q,R,\varepsilon,a,t}i_E x)(e)=0
       \text{ for every }e\text{ with both endpoints in }\Omega_0\}.
\]

This is an actual W-dressed input condition, **not** a coordinate curvature mask or a substitute operator. It is only a sufficient invisible subspace, not an asserted maximal kernel of D.

The main theorem `twistD_kills_interiorInvisible` proves

\[
x\in N\Longrightarrow Dx=0.
\]

`rightVector_mem_interiorInvisible` (**2732**) places every bare outgoing boundary vector in N. `interiorInvisible_orthogonal_correction_range` (**2748**) proves

\[
x\in N\Longrightarrow\langle x,Dy\rangle=0\quad(\forall y).
\]

`correction_pairing_remove_invisible` (**2760**) and `correction_pairing_tail_bound` (**2771**) give, for every \(x\in N\),

\[
\langle v,Dv\rangle=\langle v-x,D(v-x)\rangle,
\qquad
|\langle v,Dv\rangle|\le\|D\|\,\|v-x\|^2.
\]

The equality accounts for the cross terms exactly. It shows why a small remaining tail may yield a very small correction. **Neither this bound nor boundary localization determines its sign.** No bound on the actual crossing vector's distance to N is claimed.

### C. Precisely limited implications for the proposed routes

- `no_invisible_negative_test` (**2786**): at a PSD carrier point, no vector in N can make the corrected form negative. The correction is evaluated at angle zero, as in the question; the copied `twistD_constant` justifies changing the angle. Thus the bare endpoint vector alone cannot witness the suggested pre-crossing alternative.
- `not_initial_control_of_invisible_kernel` (**2800**): **if the entire exact real kernel** at a PSD singular point inside `(0,pi)` is contained in N, then `InitialKernelControl` fails. The containment is an explicit, **unproved** hypothesis. It is not established for this family.
- `initial_control_requires_interior_tail` (**2815**): assuming `InitialKernelControl`, the copied first-crossing theorem supplies a crossing vector with positive D-pairing and a nonzero W-dressed input on some both-endpoint interior bond. This is a necessary condition, not existence of a successful control instance.

None of these declarations proves a pinned positive or negative goal.

## 3. Pass-1 results recovered with complete verification

The entire pass-1 final source is recompiled verbatim as a prefix. In particular:

- `twistD_zero_amplitude` (**2421**): \(D=0\) at epsilon zero, for all admitted scales/radii, masses and twists;
- `vacuum_pencil_iff_carrier_unit` (**2454**): the corrected and carrier guards coincide at zero amplitude;
- `not_initial_control_zero` (**2487**): initial kernel control fails at epsilon zero, without separately assuming a crossing;
- `no_small_control_of_kernel_expansion` (**2508**) and `not_round5_premise_of_small_obstruction` (**2535**): the earlier conditional routes from a proved uniform negative kernel expansion / interval of failure remain explicit conditional implications.

Unlike pass 1, all their complete successful dependency records are retained in the final log. **Zero amplitude is excluded from the bridge's arbitrarily-small-positive-amplitude premise.** Its failure there still does not refute that premise.

## 4. Concrete remaining obstacle

Read `AHP/round5/RESULTS.md`, all five requested round-5 NOTES files, the round-3 pin, the earlier limits notes/source, and `AHP/round6/probe/PROBE.md`. No new numerical job was run.

The supplied probe's negative first-kernel form and negative linear coefficient at q=2,R=18 remain numerical evidence. They are not certificates used by these Lean proofs. A bare outgoing boundary vector is exactly invisible, but the **actual crossing mode has an inverse-propagated interior tail**. This pass does not prove that tail vanishes; the reported observed-transfer growth argues against trying to do so.

To obtain a genuine positive-amplitude obstruction, the missing work remains:

1. An exact operator/translation/Fourier dictionary for the full carrier, W dressing, constrained inverse, and raw second jet.
2. A finite-volume branch and full-carrier PSD/singularity identification, with the complementary characters controlled. A single compressed sector is insufficient.
3. A sign statement on **every real vector in the exact crossing kernel**. One negative numerical vector does not refute the existential positive-vector clause. The numerical simple complex mode corresponds to two real dimensions; its symmetry/spanning argument has not been formalized here.
4. An exact negative leading coefficient and a uniform small-amplitude remainder bound. The near-degenerate finite-volume splitting cannot be replaced by a half-space calculation or the pre-asymptotic positive grid law.

No nonpositive correction sign on an actual positive-amplitude crossing kernel, failure of initial corrected PSD, or interval of positive-amplitude failure has been proved. No sign is formally evaluated even at one positive-amplitude crossing. Consequently no cofinal obstruction or pinned-goal closure follows.

One fixed admissible q,R with a proved whole interval of small-amplitude failure would suffice to disprove the **all-q sufficient premise** of the round-5 bridge. It would not decide either pinned goal, because that premise is only sufficient. An eventual lattice conclusion still needs its own appropriate cofinal argument.

## 5. Compilation history and hygiene

`COMPILE_HISTORY.json` records the four completed wrapper calls:

1. `BoundaryCheck.lean`: exit 1, dependent-carrier addition could not elaborate and reached Lean's deterministic heartbeat limit. This was a completed compiler failure, **not** a bash timeout.
2. `BoundaryCheck2.lean`: exit 0 after the two explicit elaboration repairs.
3. `SubspaceCheck.lean`: exit 0 for the generalized invisibility/tail work; a deprecated application-lemma spelling was subsequently repaired.
4. `Attempt.lean`: exit 0, including the necessary interior-tail theorem; final full audit passed.

There were **no bash timeouts and no interrupted invocation relaunches**. Temporary candidate sources/logs/exits and the assembly fragment were removed only after final successful verification; their hashes and outcomes remain in the history. The final source, log and exit are retained intact.

All writes and cleanup were confined to `AHP/round6/limits-r2/`. No protected source, other track, earlier round, lakefile, paper, notes directory, expected output, extras, commit, push, direct Lean/Lake invocation, build, update, reproduction script, or BB terminal was used. The required serialization wrapper was the sole compiler entrypoint.
