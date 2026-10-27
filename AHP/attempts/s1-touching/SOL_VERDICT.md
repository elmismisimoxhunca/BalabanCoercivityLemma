# SOL VERDICT — s1-touching

```json
{
  "itemId": "s1-touching",
  "verdict": "reject",
  "grade": "2",
  "summary": "Reject the draft as a resolution of S-1. Reading the frozen definitions supports a paper-level comparison only: the proposed touching coverage, with Admissible and M >= 2, collapses the candidate class to empty or whole-torus Omega_0, excluding every proper nonempty domain. The uncompiled script has unresolved elaboration defects and its headline concludes set equality plus the frozen InstIneq, not an independently defined touching inequality. S-1 and statement-sheet rows 5 and 7 remain open.",
  "paperSentence": "",
  "compiled": false,
  "frozenFilesEdited": false
}
```

## Evidence and grade

This is a source-reading review, not a compiler or correctness gate. I read `HANDOFF.md`, all of `paper/OPEN_ITEMS.md`, the entire `Touching.lean`, `AHP/notes/s1-touching.md`, and `PROSECUTION.md` before writing this verdict.

Grade 2 records comparison against the actual underlying frozen Lean definitions, not merely the draft or prosecution summary:

- `lean/src/ZStatementP428.lean:54–82,118–146`: `BlockClosed`, `Admissible`, `towerBj`, `siteBox`, `DescribedAt`, `IsClassCube`, `CubeBond`.
- `lean/src/ZStatementP428.lean:211–234` and `lean/src/ZR2A.lean:35–72,121–123`: `CRowIn`, `OnLambdaTildeIn`, `CurlReads`, `PerCubeRegular2`, `OnLambdaT`.
- `lean/src/ZR6A.lean:27–35,124–125`: both-endpoint plaquette coverage and `ClassCoupled`.
- `lean/src/ZT4A.lean:88–90`; `lean/src/ZT5A.lean:56–61,89–97,170–174,200–201,229–230,291–294`: `LambdaOK2`, the actual inequality, its premises, constants, side conditions, and headline quantifiers.
- `lean/src/ZR2Ops2.lean:74–80`, `lean/src/ZXR2Ops3.lean:26–27`, `lean/src/ZLocOps.lean:181–184`, `lean/src/ZLocJ.lean:71–75`: inside plaquettes, touching support, and the two set-parameterized local operators.
- `lean/src/ZR8Class.lean:31–40,52–65,87–93`, `lean/src/ZR8Geo.lean:175–181`, and `lean/src/AdalyFormal/Target/ClayStatement.lean:1281–1303`: class containment, shifts, tower monotonicity, and plaquette boundary carriers.

The CMP 102 p.277 convention was available here as the quotation in OPEN_ITEMS S-1; I did not independently inspect that printed page. Grade 2 is a frozen-source/type review, not certification of printed-page fidelity or a second independent page-image reading.

## What the text actually proposes

`TouchBond` uses at least one endpoint; `plaqCorner` uses at least one corner. The draft retains the frozen site cubes, site coverage, tower geometry, Lambda predicates, mesh, and cube-factor coupling. Its `CoversPlaqCorner` requires **all four boundary bonds of every one-corner plaquette to touch one class cube**. This is an added formal coverage requirement, not a consequence of the quoted convention alone.

At the type-text level the candidate keeps the frozen quantifier order: for each natural ell >= 2 and real a > 0, choose m_0 >= 1; for every m >= m_0 choose R_0; for every R >= R_0 use M = ell^m and factor 12. Positive a_0 and gamma_0 are then chosen before every k >= 1, torus extent and alpha_0 > 0 with 12 M alpha_0 <= a_0. `TorusOK`, `Admissible`, `LambdaOK2` and `ClassCoupledTouch` remain premises. These constants are not asserted uniform in m or R. The retained `InstIneq` quantifies over all `Bt` satisfying both `OnLambdaTildeIn` and `OnLambdaT`; it supplies no additional invertibility conclusion.

`CoercG8AtTouch` literally concludes plaquette-set equality **and the frozen `InstIneq`**. The terminal declaration is written with type `P428Target8 → P428Target8Touching`. There is no separately defined `InstIneqTouch`. This review does not certify that the proof text inhabits that type.

## Disposition of the prosecution

- **F1 is dispositive.** In `opposite_of_touch` (lines 262–275), the script case-splits the result of `push_neg` as disjunctions although the relevant negated-conjunction normalization yields implications. The mathematical vertex-cover observation does not validate that script.
- **F2 remains an unresolved script objection.** `touchCover_cubeBond` (lines 286–295) uses `rw [h1, h2]` against a folded `CubeBond` goal, with the second rewrite dependent on the endpoint changed by the first. No unfolding or endpoint-wise proof is supplied there. The prosecution's objection is not repaired or discharged by this review.
- **F3–F4 remain elaboration risks, not additional established mathematical counterexamples.** These concern the unspecified bond direction in `bad_plaq_of_exit`, boundary-membership simplification, modular `Fin` arithmetic in `fwdDist_shift`, and a pinned-library lemma name. No compiler experiment was attempted.
- **F5 is essential, not optional wording.** Frozen `DescribedAt` confines class-cube sites to two strata; `Admissible` makes both strata subsets of Omega_0. The draft's exit-edge/block-face argument therefore predicts that, under `Admissible` and M >= 2, `CoversPlaqCorner` requires Omega_0 to be empty or the whole fine torus. As a paper argument this is coherent: a proper nonempty block domain has a one-corner plaquette with an opposite bond whose endpoints are both outside, and no contained class cube can touch that bond. This is a necessary-condition argument, not sufficiency of either trivial domain and not a checked Lean result. Consequently the proposed class has no proper nonempty-domain towers according to that argument; proposed operator agreement is confined to empty/whole domains and the implication is vacuous on every proper nonempty domain. It does not settle fidelity for the intended nontrivial domains.
- **F6 is upheld as an evidence limit.** The file does not instantiate the general obstruction on the D1 slab or establish that family's touching regularity. The statements about `U_theta`, `P1`/`P2`, and exclusion of the literal counterexamples remain prose arguments, not checked facts of this attempt. Their exclusion must not be attributed simply to stronger regularity.
- **F7 is upheld at the type level.** The two local-operator congruence declarations use an assumed set equality. The headline script does not use them or exhibit a full touching `gparams`/`genForm`/`G1invS` comparison. Set substitution is a plausible mathematical route, not evidence of a completed operator bridge here.

The bond implication and regularity-restriction directions are sensible at the definition level. The coverage implication additionally uses the rectangular `siteBox` argument; it is not justified by replacing conjunction with disjunction alone. Neither observation rescues the broken, uncompiled script.

## Decision and remaining work

**Reject**, rather than adopt-with-disclosures: believing this as a Lean reduction would require script repair and a correctness gate, and the headline reading understates the collapse of the coverage class. This is not a refutation of the underlying geometric paper argument or of Balaban's printed lemma. It is a rejection of the claimed resolution on the available evidence.

Retain the attempt only as unfinished work. Any later proposal must prominently disclose the proper-domain vacuity, distinguish the added coverage clause from the printed touching convention, repair the elaboration defects, and either supply an explicit full-operator bridge or restrict its claim to set equality plus frozen `InstIneq`. A nontrivial-domain reading requires reconsidering the coverage/class geometry, not merely repairing tactics. Slab-specific assertions need their own instantiated evidence.

No paper sentence is authorized (`paperSentence` is empty). S-1, S-2 as a checked implication, and statement-sheet rows 5 and 7 are not closed by this review. No Lean source was changed, no build or download was run, and no paper, statement sheet, frozen module, Lake root, or expected output was edited. `compiled` is false throughout this run. The only file written by this review is this verdict.
