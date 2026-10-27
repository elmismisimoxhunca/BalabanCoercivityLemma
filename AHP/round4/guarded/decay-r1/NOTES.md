# Guarded item — decay route, round 1

**Closed goal: none.** This is a quantitative partial result for the actual pinned operators, not a proof or refutation of the headline.

## Contract and inspected evidence

Read in full: `AHP/round3/guarded/JUDGEMENT.md`, its `pin/PIN.md`, and `AHP/round2/guarded/JUDGEMENT.md`. Inspected the complete pin, the relevant round-3 proof bodies, the mining report's substantive summary and relevant frozen source declarations (`DH1`, `DY3`, `DLR1`, `MI21`). The 419-entry mining catalogue was not independently rechecked.

`Attempt.lean` starts with the **entire round-3 pin byte-for-byte**, including all four unchanged goal definitions. Its only import is frozen `DrEquiv`. Needed round-2 reduction proofs and round-3 jet-nullspace proofs are copied, not imported. No new assumption is inserted into a goal.

The supplied fresh reproduction pass is taken as context. No reproduction, build, dependency update or direct Lean/Lake command was run.

## New quantitative result

Write the actual assemblies as

\[
 B=G^{-1}_{\rm in},\quad D=\Delta^{(2)}_{\rm in},\quad C=B-D,
 \quad\Theta=G^{-1}_{\rm all}-B,\quad W=\operatorname{range}\Theta.
\]

Let \(N=\texttt{jetInputZero}\), copied verbatim from round 3. This is the nullspace defined by the **actual Wop-dressed input on every positive-level raw-jet read ball**. It is not replaced by a geometric coordinate mask. Put \(J=\Pi_{N^\perp}\), called `jetObservation` here. This projection observes the input; it does not replace the source `JfS` or any pinned operator.

The copied jet-translation proof gives \(DN=0\). Symmetry then yields the exact identity

\[
 \langle x,Dy\rangle=\langle Jx,DJy\rangle.
\]

`actual_return_norm_le_two_pass` proves: under localized `WellDefAt`, if

\[
 \|JB^{-1}y\|\le b\|y\|,\qquad
 \|JC^{-1}y\|\le c\|y\|\quad(y\in W),\qquad b,c\ge0,
\]

then the genuine boundary responses satisfy

\[
 \boxed{\|K_C-K_B\|\le\|\Theta\|\,\|D\|\,b\,c.}
\]

This is a **two-pass**, rather than a single-pass or full-inverse-norm, bound. Its proof tests the return against itself, moves the symmetric corrected inverse onto the test source, and observes both inputs of the correction. Inverses are always on the full carrier. There is no compression/inversion interchange.

### Weighted decay can supply each factor — conditionally

`weighted_inverse_observation` proves the following elementary Combes–Thomas output. Suppose a weight map \(T\) fixes every source in \(W\), and

\[
 c_0\|Tx\|^2\le\langle Tx,TBx\rangle,\qquad c_0>0,
 \qquad \|Jx\|\le e^{-d}\|Tx\|.
\]

With \(B\) a unit it follows that

\[
 \|JB^{-1}y\|\le\frac{e^{-d}}{c_0}\|y\|\quad(y\in W).
\]

Weighted coercivity and separation are **explicit hypotheses**, not inferred from the guard. The argument also applies to \(C\). `pencil_isUnit_of_weighted_decay` substitutes both estimates into the actual response and proves the corrected unit if

\[
 \|K_B^{-1}\|\,\|\Theta\|\,\|D\|
 \frac{e^{-d_B}}{c_B}\frac{e^{-d_C}}{c_C}<1.
\]

`goalPos2_of_two_pass_decay` gives the conditional eventual implication

\[
 \texttt{GShape CTwoPassSmall}\ \Longrightarrow\ \texttt{GoalPos2}.
\]

It retains the entire pinned quantifier prefix, including the radius/cap order and the positive-energy competitor. **Its premise is not proved.** `CTwoPassSmall` is a separately named research obligation, not a weakened goal.

Finally, `guarded_failure_requires_amplification` proves that if the genuine guarded pencil fails despite the two observed decay bounds, necessarily

\[
 1\le\|K_B^{-1}\|\,\|\Theta\|\,\|D\|\,b\,c.
\]

This quantifies the missing inverse-response margin; it does not exhibit a failure.

## Concrete obstacle

Three obligations remain; none can be suppressed in reporting this attempt.

1. **The observation is not a raw support mask.** The assembled correction is not simply an operator on level-zero plaquettes. Frozen `DY3.C2row_level0` says the level-zero raw second-jet rows vanish; the correction is a source pairing of positive-level jets of Wop-dressed inputs. The copied `jetInputZero` retains precisely this dependence. A geometric collar must control this observation of both full inverses, not just distance between raw plaquette sets. This attempt does not construct the two weight maps from the actual collar or discharge their estimates from class membership.
2. **The available ordinary-norm gap loses depth.** Frozen `MI21.wnormSq_ge` converts the weighted lower bound with the factor \(\ell^{-2k}\). Thus a positive weighted constant from Total is not a depth-independent ordinary carrier gap. The mined localized H-column estimates also are not already estimates of the two observed B/C inverse extensions used here. A class-uniform weighted argument with the correct stratified geometry still has to be supplied.
3. **Even granting both decay estimates, the guard does not supply the final bound.** It gives only \(K_B\) a unit, not a class-uniform bound on \(\|K_B^{-1}\|\). The current estimates leave this factor untouched. Finite-radius exponential smallness is not exact zero. Choosing a radius depending on each guarded instance's inverse norm would violate the pinned uniform quantifiers; exterior links and depth come after the thresholds and cap. This is a missing argument, not a theorem that the actual class has arbitrarily large inverse responses or that no positive proof exists.

Consequently, neither the zero-return criterion nor the inverse-relative criterion is established throughout the eventual class. No exact separating lattice instance or cofinal negative certificate is constructed.

## Verification

Final wrapper exit **0**, with no errors or warnings. `audit.py` passed: the entire pin is an exact byte prefix, the four goal definitions are unchanged and unredeclared, the sole import is `DrEquiv`, the forbidden-token scan is clear, and **all 76 local declarations have individual dependency records**, each a subset of `propext`, `Classical.choice`, `Quot.sound`. Exact copies of the reused jet-nullspace definitions/proofs and inverse helpers were checked too. `CHECKS.json` records the details.

Main new results in `Attempt.lean`: `weighted_inverse_observation` at line 735; `actual_return_norm_le_two_pass` at 842; `pencil_isUnit_of_weighted_decay` at 880; `guarded_failure_requires_amplification` at 905; `goalPos2_of_two_pass_decay` at 941. None proves a pinned goal without an additional, unproved premise.

Final source SHA-256: `7f15254dbc50ab07da276c1e22bbbfdbefe5f9629eda9fcc61d583bb3d9c0164`.

Unsuccessful exploratory checks are not counted. Their temporary sources/logs and the assembly scratch files were removed after the successful candidate was promoted; the preliminary outcomes remain recorded in `CHECKS.json`.

The first foreground invocation for the initial `Attempt.lean` ended with an empty log and no exit record. Two process inspections found no surviving compiler/wrapper for that file. It was not relaunched. Subsequent revised candidates are compiled once each, using persistent terminals and the same shared-lock wrapper, with the exit record awaited before reading the outcome. The successful final candidate and its wrapper-generated log/exit are promoted byte-for-byte to the requested `Attempt.lean` names; the original compile path is retained in `CHECKS.json`. No exit code is fabricated.

No numerics were needed. No file outside `AHP/round4/guarded/decay-r1/` was authored or removed. No protected source, lakefile, paper, notes, expected output, other AHP item, git commit or push was touched. This is builder verification, not an independent judge replay.
