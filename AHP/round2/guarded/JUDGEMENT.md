# Judgement: guarded all-plaquette reading

**Status: `open`. Closed by: none.**

Neither `GuardPencilT` nor `P428Target8SG selAll selAll` has been proved or refuted. The four attempts provide valid reductions, sufficient conditions, necessary obstructions, and a proof excluding the numerical candidate from the class. They do not decide the pinned question.

## Contract and decision rule

The unchanged [pin](pin/Statement.lean) defines `GoalPos1` at line 154 as the frozen `GuardPencilT`, and `GoalPos2` at line 157 as the frozen `P428Target8SG selAll selAll`; lines 155 and 158 define their exact negations. Compiled identity checks at lines 170–175 identify the actual frozen statements. The two positives are equivalent (line 178), as are the negatives (line 181). Thus these are two formulations of one open question, not four independent tasks.

The pin explicitly says that its identity checks and certificate implications are **not completion targets**. The new equivalences below still have unproved right-hand sides. Accordingly this is not `closed-reduced`: no reduction to an already settled statement decides the pinned item. Nor is it `partly-closed`: no pinned positive or negative goal was closed. Printing dependencies of a proposition definition proves nothing about whether that proposition holds.

## What is now proved

All paths in this table are relative to `AHP/round2/guarded/`. Every listed declaration was independently recompiled in this judgement pass and its dependency print contains exactly `propext`, `Classical.choice`, `Quot.sound`.

| Attempt | Main declaration and source | Accepted conclusion | Closure |
|---|---|---|---|
| Round 1, prove | `AdalyFormal.Round2.Guarded.R1Prove.goalPos2_iff_boundary_kernel`, `r1-prove/Attempt.lean:441` | The headline is equivalent to eventual containment of the corrected kernel in the subspace of fields zero on all level-zero bonds. | Neither side proved. |
| Round 1, refute | `AdalyFormal.Round2.Guarded.RefuteR1.pencil_failure_iff_second_jet`, `r1-refute/Attempt.lean:322` | Pointwise pencil failure is equivalent to a nonzero vector satisfying the actual polarized second-jet equation against every vector of the full carrier. | No such separating instance constructed. |
| Round 2, prove | `AdalyFormal.Round2.Guarded.R2Prove.goalPos2_iff_boundary_response`, `r2-prove/Attempt.lean:554` | The headline is equivalent to eventual invertibility of the corrected boundary response, using actual localized inverses. | Corrected response invertibility remains unproved. |
| Round 2, refute | `AdalyFormal.Round2.Guarded.RefuteR2.goalNeg2_iff_cofinalPencilFailure`, `r2-refute/Attempt.lean:358` | The exact negative headline is equivalent to the pin's cofinal failure certificate, now in both directions. | Certificate has no witness. |

Further useful, verified content:

- **Round 1 positive:** `pencil_isUnit_of_feedback_norm_lt_one` (`:355`) supplies a sufficient inverse-relative norm criterion; `guarded_kernel_obstruction` (`:376`) says a guarded separation, under the stated geometry and localized corrected invertibility, has a nonzero level-zero coordinate, nonzero correction action, and inverse-relative correction norm at least one. These theorems neither exhibit nor exclude such a separation.
- **Round 1 negative:** `guarded_failure_forces_second_jet` (`:348`) requires a nonzero genuine local correction/source pairing. `guarded_failure_forces_nonflat` (`:379`) excludes backgrounds equal to identity on every bond whose base point lies in the base domain, under its admissibility and room hypotheses. This is not a theorem requiring nonzero curvature, nor an exclusion of every possible background.
- **Round 2 positive:** `boundaryShift_range_le_orthogonal` (`:444`), `carrier_isUnit_iff_response` (`:459`), and `pencil_isUnit_iff_response` (`:467`) are genuine operator comparisons. `pencil_isUnit_of_no_boundary_return` (`:475`) gives a sufficient zero-return condition; `guarded_failure_forces_boundary_return` (`:496`) gives a necessary nonzero return obstruction. Neither establishes that condition throughout the class. The response uses a restriction to the shift's range, not an unjustified interchange of compression and inversion.
- **Round 2 negative:** `original_torus_rejected` (`:285`) rejects the original small torus. `candidate_excluded` (`:335`) proves that the enlarged torus satisfies `TorusOK`, but its specified tower is inadmissible for every radius and outside `ClassCoupled` for every background and every pair of regularity parameters. The level-one domain is not size-four block-closed; every factor-12 cube wraps the side-eight torus and cannot furnish the required coverage. This excludes that candidate, not all counterexamples.

The earlier Stage-B flat-path comparison remains valid at its recorded scope: its singular crossing fails the carrier guard and has zero localized correction. It does not resolve either direction here.

## What is still open

Write, as notation for the actual pinned assemblies,
\[
A=G^{-1}_{\mathrm{all}},\qquad B=G^{-1}_{\mathrm{in}},\qquad
D=\Delta^{(2)}_{\mathrm{in}},\qquad C=B-D,\qquad \Theta=A-B.
\]

**Positive direction:** prove that invertibility of \(A\) forces invertibility of \(A-D\) throughout the entire eventual class, with the pin's positive-energy-test-field condition. Equivalently, prove `GShape CBoundaryResponse`: on \(W=\operatorname{range}\Theta\), invertibility of
\[
K_B y=y+\Theta B^{-1}y
\]
must force invertibility of
\[
K_C y=y+\Theta C^{-1}y.
\]
The known localized units and agreement on zero-level-zero-trace fields do not discharge this. The difference is \(\Theta C^{-1}DB^{-1}y\); neither an exact zero-return theorem nor a sufficient uniform inverse-relative bound is proved. The existing full-guard headline assumes the missing corrected invertibility and cannot be used circularly.

**Negative direction:** construct an exact in-class carrier-unit/corrected-nonunit separation, including torus compatibility, admissibility, coverage/regularity, `LambdaOK2`, capped positive smallness and a positive-energy admissible competitor. It must defeat the eventual quantifiers: fixed \(\ell\ge2\) and \(a>0\), arbitrarily large \(m\), then arbitrarily large \(R\), with **\(R\) chosen before every positive smallness cap**. No attempt supplies that cofinal family or an exact separating in-class instance.

The numerical scripts now probe assembled operators and genuine raw-jet formulas rather than the earlier surrogate correction. They remain floating-point transcriptions with finite-difference derivatives, not Lean operator-identification or singularity certificates. Their chosen geometries are formally excluded as above. A small residual, sampled carrier gaps, or a sign change in one Rayleigh quotient does not prove exact singularity, an interval-wide guard, or the necessary cofinal quantifiers. Numerical scripts were not rerun by this judge; no numerical value is used to establish the verdict.

## Verification performed

Read the handoff, the required open-item sections, Stage-B results and guarded records, the pin and every attempt's notes and appended Lean source. No attempt-level `VERIFY.md` or `Attempt.VERIFY.md` existed when judgement began; all supplied verifier fields were null. The attempts themselves claimed no closure. This judge independently checked the partial results rather than treating builder summaries as verification.

The pin and all four attempts were copied byte-for-byte under `judge/` and compiled **serially**, using the requested `heavy run -- lake env lean` command. All five final exits are **0**, with no warnings or errors. The fresh logs contain respectively **17, 56, 28, 71, 54** dependency records: **226 records including repetitions**, all subsets of the three permitted axioms. All requested prints are present. The whole-source forbidden-token scan is clean, and imports are frozen `DrEquiv`, with only round-1 refutation additionally importing frozen `GdR6b`.

Every attempt preserves the complete pin verbatim after removing only the extra `import GdR6b` at line 2 of round-1 refutation; the other three have the exact unmodified pin as a byte prefix. Source hashes and exact-copy checks are in [judge/CHECKS.json](judge/CHECKS.json); commands, logs and limitations are in [judge/VERIFY.md](judge/VERIFY.md). An initial judge invocation for round-1 refutation terminated without a log body or exit record; it was not counted. After checking that no such process remained, the final serial replay succeeded.

## Fidelity and scope

Acceptance concerns the **pinned formal reading**, not Balaban's unqualified printed assertion. All fifteen departures in [pin/PIN.md](pin/PIN.md) remain: only `Ginv` is guarded; other inverses stay totalized; all-plaquette selectors retain the frozen carrier/Dirichlet sandwich; the class retains both-endpoint bonds and added coverage; factor-12 aligned boxes, frozen base-domain/Lambda/test-field conventions, explicit threshold order, all \(\ell\ge2\) and \(a>0\), dimension three/SU(2)/periodic geometry, and per-cube gauges are unchanged. The eta/tau-star and complete printed-unit dictionary remain unresolved. No touching-class repair or full-inverse guard was substituted. This judge did not independently reread printed page images.

Only `AHP/round2/guarded/JUDGEMENT.md` and new files under `AHP/round2/guarded/judge/` were written. Attempt sources and builder logs were preserved. No protected source, lakefile, paper, notes, expected results or other AHP item was edited; no build, reproduction, dependency update, numerical sweep, deletion, commit or push was run.

**Plain conclusion:** we have checked better descriptions of the missing proof and ruled out the tried numerical geometry. Whether the Ginv-only guarded all-plaquette headline holds or fails is still open.
