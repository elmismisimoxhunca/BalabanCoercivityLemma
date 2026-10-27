# Judgement: guarded all-plaquette reading, round 3

**Status: `open`. Closed by: none.**

Neither pinned positive goal nor either negative goal is proved. The positive attempts establish genuine operator locality and conditional routes to the headline. The negative attempts now supply a complete small-field class family with a positive-energy competitor, but no exact spectral separation. These are verified advances, not a decision of the guarded boundary-response question.

## Contract and decision rule

The unchanged [pin](pin/Statement.lean) defines:

- `AdalyFormal.Round2.Guarded.Pin.GoalPos1` at line 154: eventual `GuardPencilT`.
- `AdalyFormal.Round2.Guarded.Pin.GoalPos2` at line 157: `P428Target8SG selAll selAll`, the original Ginv-only guarded headline.
- `GoalNeg1` and `GoalNeg2` at lines 155 and 158: their exact negations.

The positive pair is equivalent, as is the negative pair (`:178`, `:181`). They are two formulations of **one** unresolved question. The compiled `rfl` checks at `:170–175` identify the frozen statements. The complete round-2 pin is preserved byte-for-byte, and all attempts preserve the complete round-3 pin.

The contract expressly excludes identity checks, certificate implications and the already-known boundary-response reduction as completion targets. **Not `closed-reduced`:** the new equivalences still leave the needed class-wide property unproved; they do not reduce the pinned question to a settled statement. **Not `partly-closed`:** auxiliary results were proved, but no pinned goal was closed. A standard dependency print for a proposition definition is not a proof of that proposition.

## What is now proved

All paths below are relative to `AHP/round3/guarded/`. Every listed result passed independent judge recompilation, with only permitted dependencies. Declaration names in the table have prefix `AdalyFormal.Round3.Guarded.`

| Attempt | Main declaration / source | Accepted result and limitation |
|---|---|---|
| Pass 1, prove | `R1Prove.goalPos2_of_return_offSelectorShell`, `r1-prove/Attempt.lean:835` | Eventual return into the shell-vanishing subspace would imply `GoalPos2`. The propagation premise is not proved. |
| Pass 1, refute | `RefuteR1.probe_not_negative_witness`, `r1-refute/Attempt.lean:472` | For the narrow-top probe family and every radius at least one, compatible Lambda and positive-energy competitors cannot coexist. This excludes that family, not the headline. |
| Pass 2, prove | `R2Prove.goalPos2_of_inverse_boundary_jetInputZero`, `r2-prove/Attempt.lean:976` | Eventual jet-input invisibility after the localized inverse would imply `GoalPos2`. The inverse-propagation premise is not proved. |
| Pass 2, refute | `RefuteR2.wide_probe_geometry_and_competitor`, `r2-refute/Attempt.lean:584` | The widened slab has actual torus compatibility, all admissibility clauses, LambdaOK2 and a positive-energy admissible competitor at every even radius. No class or spectral conclusion occurs in this theorem. |
| Pass 3, prove | `R3Prove.goalPos2_of_diagonal_mixed_boundary_source_zero`, `r3-prove/Attempt.lean:981` | Eventual diagonal cancellation of the genuine mixed-jet/source pairing would imply `GoalPos2`. That cancellation is not proved. |
| Pass 3, refute | `RefuteR3.wide_in_class_nonflat_competitor`, `r3-refute/Attempt.lean:924` | At every even radius at least two and every positive cap, the single-defect family has full class membership, geometry, a positive-energy competitor and a base-point nonidentity bond. It fixes m=1 and proves neither spectral condition. |

The six main dependency records, normalized from the fresh logs, are:

```text
'AdalyFormal.Round3.Guarded.R1Prove.goalPos2_of_return_offSelectorShell' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round3.Guarded.RefuteR1.probe_not_negative_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round3.Guarded.R2Prove.goalPos2_of_inverse_boundary_jetInputZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round3.Guarded.RefuteR2.wide_probe_geometry_and_competitor' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round3.Guarded.R3Prove.goalPos2_of_diagonal_mixed_boundary_source_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round3.Guarded.RefuteR3.wide_in_class_nonflat_competitor' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Positive progress: exact identities, still conditional

For the actual pinned assemblies write

\[
A=G^{-1}_{\mathrm{all}},\quad B=G^{-1}_{\mathrm{in}},\quad
D=\Delta^{(2)}_{\mathrm{in}},\quad C=B-D,\quad
\Theta=A-B,\quad W=\operatorname{range}\Theta.
\]

The inherited equivalence with eventual corrected-response invertibility is independently replayed at `r3-prove/Attempt.lean:624`, `AdalyFormal.Round2.Guarded.R2Prove.goalPos2_iff_boundary_response`. Localized well-definedness is supplied after combining eventual thresholds; it is not silently added as a new headline premise.

- **Selector-shell locality:** `r1-prove/Attempt.lean:562,591,627` proves that the actual Wop agrees with its input on omitted-plaquette edges, that Theta kills fields vanishing there, and that its range lies in the orthogonal complement of that vanishing subspace, under the stated admissibility and room hypotheses. This does not prove support preservation by either inverse. The sufficient propagation condition remains \(C^{-1}DB^{-1}W\subseteq\texttt{offSelectorShell}\).
- **Inverse-relative stability:** `r1-prove/Attempt.lean:751,763,817` proves sufficiency of \(\|K_B^{-1}(K_C-K_B)\|<1\), and that guarded failure forces a nonzero minus-one mode of that relative return and norm at least one. Here \(K_B=I+\Theta B^{-1}\) and \(K_C=I+\Theta C^{-1}\) act on W. No class-uniform bound is obtained.
- **Genuine jet nullspace:** `r2-prove/Attempt.lean:762,789` proves that the actual second jet is unchanged by translation in `jetInputZero` and that D annihilates this subspace. Its definition retains the actual Wop and positive-level raw-jet input balls. The conditional route at `:860` needs \(B^{-1}W\subseteq\texttt{jetInputZero}\), not merely raw jet locality. Guarded failure forces a nonzero response on one such input ball (`:873`), but no failing instance is constructed.
- **Mixed-source cancellation:** `r3-prove/Attempt.lean:762,769,804` defines the genuine localized pairing
  \[
  q(u,v)=\langle H(C_2(u+v)-C_2(u)-C_2(v)),J\rangle
        =\langle u,Dv\rangle
  \]
  and identifies \(\langle z,(C^{-1}-B^{-1})y\rangle=q(C^{-1}z,B^{-1}y)\). Under localized well-definedness, zero return is equivalent to vanishing of these pairings on W, and then to the diagonal tests \(q(C^{-1}y,B^{-1}y)=0\) (`:826,858`). These characterize **the sufficient zero-return condition**, not a necessary condition for the headline. A guarded failure forces a strictly positive mixed pairing for some nonzero boundary sources (`:922`); its existence is not asserted without failure.

All inverses in these comparisons are on the full carrier before testing boundary sources. No compression/inversion interchange is used. None of the new sufficient conditions is derived from capped smallness and admissibility.

### Negative progress: the candidate is now genuinely in the class

The pass-1 thin-top obstruction is exact (`r1-refute/Attempt.lean:402,472`). Pass 2 repairs it by widening the top domain and supplying the actual frozen free-bond competitor. Pass 3 additionally proves **both frozen factor-12 coverage clauses** (`r3-refute/Attempt.lean:826`) and full per-cube regularity (`:887`). It is therefore stale to say that coverage, regularity or Lambda non-vacuity remain missing for this final single-defect family.

The final certificate has \(\ell=M=2\), \(k=1\), hence **m=1**. The fine torus has sides \((12R+16,8,8)\). For every even \(R\ge2\), every cap \(a_0>0\), and every exterior configuration V, it chooses

\[
\alpha=\tfrac12\min(a_0/24,1),\qquad \varepsilon=\alpha/160,
\]

with positive parameters, \(24\alpha\le a_0\), and the complete class/geometry/competitor conjunction. R can be chosen before the cap in this family. The arbitrary V is used only on bonds with neither endpoint in the base domain.

**What this does not prove:** the base-point nonidentity conclusion is not a curvature theorem and does not establish nonzero D or boundary return. The certificate contains neither a unit of A nor a non-unit of \(A-D\). It does not cover the separate two-defect numerical background or unbounded m.

The numerical work progressed from a transverse quotient to sampling all 16 transverse Fourier sectors and a full-lattice raw-jet consistency check. It remains exploratory: the exact Fourier/operator dictionary, exact corrected kernel and simultaneous full-carrier unit are unproved. The reported finite-difference correction-step discrepancies exceed the sampled carrier gaps; these discrepancies themselves are not certified error bounds. Spectral samples fix R=2, outside the reduction's room condition, and do not establish separation for the arbitrarily small amplitudes chosen by the theorem. This judge did not rerun numerics and uses no numerical value as proof.

## What is still open

**Positive direction:** prove `GShape CBoundaryResponse`, equivalently the pinned headline: throughout the eventual class, a unit of \(K_B\) must force a unit of \(K_C\). Sufficient options include exact zero return, the diagonal mixed-source cancellation, or a uniform inverse-relative norm bound. All remain unproved. A carrier-unit guard supplies no uniform inverse-response gap; raw locality does not control inverse-propagated inputs. These are missing arguments, not impossibility theorems.

**Negative direction:** produce an exact full-operator carrier-unit/corrected-singular separation with all pinned class, geometry, smallness and competitor conditions. It must extend to a cofinal family: fixed \(\ell\ge2\), \(a>0\), arbitrarily large m, then arbitrarily large R, with **R chosen before every positive cap**. The final family settles several nonspectral obligations only at m=1. Neither a single exact separating instance nor the required cofinal separation has been constructed.

The already-proved full-guard headline assumes additional invertibility and cannot discharge this missing implication. Earlier flat-interior singular crossings fail the guard and cannot refute it either.

## Verification and fidelity boundary

The judge read every attempt's NOTES and actual new Lean statements/proofs. No attempt-level VERIFY file existed; all supplied verifier fields were null, consistent with all attempts reporting `closedGoal: none`. Rather than promoting those reports to independent verification, this pass copied and recompiled the pin and **all six attempts** serially through `AHP/round3/lean1.sh`.

All **seven exits are 0**, without warnings or errors. The fresh logs contain **578 dependency records including repetitions**, all subsets of the permitted three; every local declaration is printed. [judge/VERIFY.md](judge/VERIFY.md) gives per-file counts, commands, scope and limitations. [judge/CHECKS.json](judge/CHECKS.json) records hashes, exact copied definitions/prefixes, imports, clean forbidden-token scans, fresh log/exit order and dependency coverage. [judge/audit.py](judge/audit.py) passed. Original attempts and builder evidence were not changed.

Acceptance remains about the **pinned formal reading**, not Balaban's unqualified printed lemma. All fifteen departures in [pin/PIN.md](pin/PIN.md) are retained: Ginv-only guarding and other totalized inverses; all-plaquette selectors with the frozen carrier/Dirichlet sandwich; both-endpoint class bonds and added site/interior-plaquette coverage; aligned factor-12 boxes rather than touching/shell repairs; the frozen quantifier order, base-domain/Lambda/test-field rules, parameter ranges, dimension-three SU(2) periodic geometry, norm conventions and separate per-cube gauges. The third-enlargement, common-radius, operator and source-identification qualifications remain. Round 2's guarded localized first-term normalization does not settle this all-plaquette inverse implication. No independent source-page image rereading or new whole-project reproduction is claimed.

Only this judgement and new evidence under `AHP/round3/guarded/judge/` were written. No protected source, other AHP item, build configuration, paper, notes or expected output was edited; no numerical sweep, direct Lean/Lake invocation, build, dependency update, deletion, commit or push was run.

**Plain conclusion:** we have verified stronger conditional proof routes and an actual in-class candidate family with nonzero competitors. We still do not know whether the Ginv-only guarded all-plaquette statement holds or fails.
