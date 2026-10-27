# DECISION — sheet-reading

**Decision: `reading-only`. Stage B declaration targets: none (`leanTargets: []`).**

Retain Q8, Q10 and Q11 as a qualified source-reading record, not a proof or counterexample and not an unconditional “forms agree” certification. The mathematical identities already encoded do not decide whether their ingredients and conventions are the intended printed ones. An optional `#check` / `#print axioms` audit can verify the existing declarations after the reproduction prerequisite, but cannot close the source-reading questions. No such audit is required as a new declaration target here.

## Accepted content and limits

- **Q8:** The mask/padded-inverse construction and the shape `W* Delta W` agree with the stated algebraic templates, conditional on the inverse and the chosen ingredients. The weight comparison is equality at eta = 1 in dimension 3. At general eta the printed weight has the extra factor eta; deleting that factor is a proposed units convention, not an established comparison of the entire form. Keep the D1 plaquette selection and D10/D11 jet disclosures. This decision does not settle S-1 or S-3.
- **Q10:** Accept the abstract chain using the weighted mass (3.16), the symmetric quadratic representative, and the inverse/constraint compositions with their existence qualifications. The random matrices do not instantiate the genuine lattice assembly or prove the printed-unit dictionary. They establish neither a faithful alternative statement nor a counterexample to it.
- **Q11:** Accept the touching-support interpretation as an explicitly chosen reading, not a forced interpretation of “B = 0 on Lambda^c”. `Cop_id` preserves bonds outside the dropped set. `Cop_ker` solves the constraint on rows satisfying `CRowIn`, under bijectivity of `H0`; it does not assert a constraint on all coarse rows. The singular branch is not the printed inverse construction. Joint solution and a one-variable solution with other dropped variables frozen must remain distinguished. The toy Q maps are not `Q1jet`, so they cannot establish decoupling for the printed one-step operator.

The proper nonempty side-4 domain is useful evidence that the support comparison is not vacuous. It is not a witness to all headline hypotheses or to realizability of the stand-in operators by an admissible background.

## Corrections to the design and attack

1. **Do not promote the wired scalar calculation to a compressed-inverse identity.** `lean/src/ZXG3A.lean:35-36,50-51` inverts `Nmat` on the multilevel space `FSp` and only then pairs with `tau* B`. `lean/src/ZXR2Wire2.lean:77-83` defines `Qin` on the unit-bond space using `tau`, and `G1in` using the supported-field inclusion. Thus, if the SPEC's expression “(Q G1in Q*)^-1” means the actual `Qin`, its identification with `firstTerm` is not justified by scalar scaling: it also requires exchanging compression and inversion. In general `tau N^-1 tau*` is not `(tau N tau*)^-1`. If Q instead denotes a multilevel map, specify that carrier and do not identify it with `Qin`. The same-space matrix calculation in the script omits this issue. Neither Grok's sentence nor Kimi's endorsement closes it. The genuine-unit comparison remains with S-3, not an additional target in this reading-only record.
2. **Do not infer a support mismatch merely from an omitted explicit conjunct.** `lean/src/R2Ops1.lean:150-156` defines `NQp` with support in Omega0 AND all level constraints, including level zero. Whether these imply the printed support in Omega1 must be checked with `Qlev` at level zero and the actual tower strata. The SPEC's observation about the explicit support clause alone is not evidence that the spaces differ, nor a proved equality of those spaces. No outcome on that comparison is claimed here.
3. **Citation repairs are still required before reuse.** Kimi's F1 catalogue identifies wrong/loose line references in SPEC and script comments. Preserve that catalogue as outstanding errata; do not treat those files as citation-clean. Spot checks here confirm, for example, `NQp` at `R2Ops1.lean:150-156` and `Rproj` at `:170-171`. This decision does not silently rewrite the design or its numerical source.
4. **The attack overstates singular-branch coverage in one sentence.** Its section 4 says the junk value was not imitated anywhere, whereas its section 3 and the SPEC explicitly describe the singular-H0 zero-inverse branch. The padded-Gp singular case was only diagnosed. Keep these two experiments separate.
5. **Source evidence is qualified.** Kimi compared corpus text but did not independently inspect the renders. Its report is not an independent render-level confirmation. No additional image verification or numerical rerun was performed in this decision.

## Stage B and closure boundary

`leanTargets` is empty because this target supplies a reading disposition, not a newly specified formal variant. Do not manufacture an equality by defining the printed operator to be the frozen operator, or use abstract matrix non-vacuity as genuine-background non-vacuity. Do not count the optional audit's successful axiom prints as validation of the printed interpretation, of the eta/tau convention, or of the one-step jets.

The reading-only disposition is complete for this target. Q8/Q10/Q11 retain the qualifications above; S-1, S-3 and any concrete operator comparisons remain separate work. The SPEC's closing sentence “the reading itself is closed by the term table” is acceptable only as completion of a documented reading record, not as a fidelity verdict.

## Verification and write scope

Read HANDOFF.md; OPEN_ITEMS sections B, K–N, R and S; the complete statement sheet; SPEC.md and ATTACK.md; and the actual source definitions cited in the decisive qualifications above. Also read the existing S-3 decision to avoid duplicating its units-comparison task. No Lean, Lake, reproduction command, build or numerical script was run. Only `AHP/fidelity/sheet-reading/DECISION.md` was written.
