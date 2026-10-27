# SOL VERDICT — s2-class-implication

```json
{
  "itemId": "s2-class-implication",
  "verdict": "adopt-with-disclosures",
  "grade": "2",
  "disclosures": [
    "Adopt only the source-reviewed mathematical implication against the frozen ClassCoupled and CubeBond definitions; the note stays within the uncompiled draft.",
    "compiled is false. No elaboration or project theorem is certified. S-2 is not closed as a checked Lean result; theorem-level use requires the correctness gate.",
    "The conclusion remains frozen InstIneq. No touching-operator equivalence or resolution of S-1 is established.",
    "No converse, strict inclusion or proper nonempty-domain non-vacuity is established. The corner-class saturation concern remains conditional and uncompiled.",
    "S-1 and S-2 use different meanings of ClassCoupledTouch in separate namespaces; do not interchange them.",
    "No printed-page fidelity is certified, no paper sentence is authorized, and frozen files were not edited."
  ],
  "paperSentence": ""
}
```

## Evidence and grade

Read before writing: `HANDOFF.md`, all of `paper/OPEN_ITEMS.md`, the complete `ClassImplication.lean`, `AHP/notes/s2-class-implication.md`, and `PROSECUTION.md`. Grade 2 is an independent frozen-definition comparison, not acceptance of the prosecution's table on trust:

- `lean/src/ZStatementP428.lean:118–146`: `siteBox`, `DescribedAt`, `IsClassCube`, and actual both-endpoint `CubeBond`.
- `lean/src/ZR6A.lean:27–35,124–125`: `CoversPlaqOm0c`, `CoversOm0p`, and actual `ClassCoupled` with one shared factor.
- `lean/src/ZR2A.lean:35–72,107–109,121–123`: `CurlReads`, `PerCubeRegular2`, site coverage, and touching Lambda support.
- `lean/src/ZT5A.lean:56–61,89–97,170–177,200–201,229–230,291–294`: retained inequality, premises, side conditions, constants and headline quantifiers.
- `lean/src/ZR2Ops2.lean:74–80`: `plaqIn` and the localized `Delta` definition.
- `lean/src/ZR8Class.lean:52–53,87–93` and `lean/src/AdalyFormal/Target/ClayStatement.lean:1265–1303`: shift signatures, distinct plaquette directions and four boundary edges.

No printed-page fidelity is certified. The CMP convention was available as the quotation in OPEN_ITEMS S-1; no page image was independently read here.

## Implication audit

**Coverage needs geometry, not predicate monotonicity alone.** Frozen plaquette coverage uses `CubeBond` both in its antecedent and its witness. Replacing both by `TouchBond` enlarges the antecedent but weakens the witness requirement. Nevertheless, a frozen antecedent implies the touching antecedent. The resulting witness is a single `IsClassCube`, hence a product `siteBox` by `hc.1.2.1`.

For that product box, touching all four boundary edges gives a vertex cover of the square. The draft's direct case split yields an opposite pair. Each missing corner takes each coordinate from one of the opposite corners, so product membership fills the square. This uses only off-axis shift invariance and commutation, including across periodic seams; no parity or nonwrapping assumption is needed. All boundary endpoints therefore lie in the same witness box. The witness's factor, index and uniqueness clause survive unchanged. This establishes the mathematical route from `CoversPlaqTouch` to frozen coverage.

`CoversPlaqCorner` asks coverage for every one-corner plaquette, a larger antecedent class than all-four-bonds-touch. Applying it to edge AB gives the correctly directed intermediate implication. This is an explicitly added coverage clause, not a consequence of a source bond convention alone.

**Regularity is restriction.** The frozen class is `(CoversOm0c ∧ CoversPlaqOm0c) ∧ PerCubeRegular2`. `CubeBond` implies `TouchBond`; applying this to every value, difference and curl-read hypothesis restricts the touching bounds to the frozen bounds. The same per-cube witnesses `g,A` work. The draft keeps their existential quantifiers inside the universal cube quantifier, all three bounds, and the common factor. Site coverage is unchanged.

Thus, as source-reviewed mathematics, `ClassCoupledCorner → ClassCoupledTouch → ClassCoupled` has the correct direction. Restricting a universal inequality to either subclass gives the drafted headline implications. The constants are repackaged without exchange of quantifiers: choose thresholds after ell and a, then positive a_0 and gamma_0 before depth, torus and alpha_0; retain factor 12 and its smallness condition. No new uniformity in m or R is asserted.

## Note and prosecution disposition

The note describes drafted types, prominently says uncompiled and not a project theorem, retains the frozen `InstIneq`, and expressly declines converse, proper-domain non-vacuity and operator-equivalence claims. Its mathematical summary does not exceed the draft text.

- **F-1:** The S-1/S-2 terminology mismatch is an integration hazard, not a present declaration collision: the namespaces differ. Do not interchange their `ClassCoupledTouch` names.
- **F-2:** Compilation remains unverified. The listed tactic/elaboration concerns do not expose a missing mathematical step. In particular, this S-2 file uses a direct classical case split for the vertex cover and unfolds `CubeBond` before separate endpoint goals; the corresponding S-1 objections must not be transferred to this different script. No successful elaboration or kernel dependency check is inferred.
- **F-3:** No proper nonempty-domain witness is supplied. The prosecution's conditional saturation warning remains a disclosure, not a newly checked result here. Conversely, its phrase “strict weakening” is too strong: only weakening follows from these inclusions; no strictness witness is established by this draft.

The corner headline still concludes the frozen inside-plaquette inequality. It does not become a one-corner-operator theorem, settle the literal refutations, or close S-1 merely because its class is stronger.

## Decision boundary and verification

**Adopt with disclosures only as an uncompiled, source-reviewed implication argument.** Its mathematical inclusion is believable directly from the frozen definitions and the product-box argument; a rebuild is not needed to supply a missing mathematical premise. This is not conditional adoption of a project theorem pending a future build. Any such theorem-level use still requires the correctness gate specified in HANDOFF, and is not authorized by this verdict. S-2 remains unclosed as a checked Lean result.

`paperSentence` is empty: no paper insertion is authorized. No Lean file was rewritten, no compiler/build command or download was run, and no frozen source, Lake configuration, Check file, expected output, paper or statement sheet was edited. The only file written by this review is `AHP/attempts/s2-class-implication/SOL_VERDICT.md`. Verification here consists of direct source comparison and hand reconstruction, not runtime evidence. `compiled` remains false.
