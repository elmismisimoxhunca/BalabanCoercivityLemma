# Sol re-review — two-domain

```json
{
  "itemId": "two-domain",
  "verdict": "adopt-with-disclosures",
  "grade": "2",
  "disclosures": [
    "Adopt only the qualified source-level assessment in this verdict, not the stale review card or the extras lane as a project result. No open mathematical item is closed.",
    "The prosecution now exists and independently confirms the earlier correction: TD1's (hcr ν0 hν0).2.2.1.1 selects x in D union E. The projection objection is withdrawn; the proposed replacement must not be applied.",
    "compiled remains false. gate_record/ is absent; historical build, leanchecker, census, mutation and foundational-dependency reports are not measurements of this package.",
    "The union draft reuses famTorusLayer_union's constants package with R1 raised to max R1 4. Cap and box use famTorusLayerCap; mixed, total and target8 inherit its coercivity package. Equality with the corresponding one-domain box/mixed/total/target8 packages is not established.",
    "The box meeting clause is prose-only in this lane; the box draft avoids it through the cap route. TD7's census selects TD-prefixed modules excluding TD7, not THL1–THL8 as its comment says.",
    "Higher-level agreement, level-zero inclusion, coverage, factors at least 10, smallness and collar thresholds remain. Target8TwoDom concludes InstIneq only, not WellDefG, and is not P428Target8 or Target8Layer.",
    "The reported non-vacuity witness is nested radial slabs at depth two in the M1 regime, with LambdaOK2 at the larger radius. No below-threshold, general-witness or union-cap claim is authorized.",
    "Only this verdict was edited. No build, dependency download, source repair or paper change was made. A later authorized rebuild and dependency audit are required before any project-level mathematical certification."
  ],
  "paperSentence": ""
}
```

## Decision and scope

**ADOPT WITH DISCLOSURES, grade 2, for this corrected reading-level assessment only.** This supersedes the earlier disposition for the present re-review, not its finding that the original review card contains a false objection. It does **not** adopt `REVIEW.md` verbatim, certify successful elaboration, certify foundational dependencies, or adopt the extras lane as a project result. The literal two-domain transfer remains open at project level. `compiled` is **false** and `paperSentence` is empty.

Read the now-present `AHP/attempts/two-domain/PROSECUTION.md`, the existing `REVIEW.md`, `extras/two_domain/STATEMENT.md`, and the previous verdict. The prosecution agrees with the projection correction and reports no mathematical refutation after its broader TD1–TD7 reading. Its outcome is qualified, not a build gate.

For this pass, independently re-read the operative projection block in `TD1`, all of `TD2`–`TD4`, and the census implementation in `TD7`. Compared with the actual frozen definitions of `CurlReads`, `CubeBond`, `DescribedAt`, `DescribedAt0`, `ClassCoupledCap`, `regBody_mono_sites`, `AdmSplitNB`, `FamTorusLayerP`, `FamTorusCapLayer`, `InstIneq` and `InstAtWD`. Grade 2 records that source comparison, not compilation or a new full audit of every auxiliary geometric and witness argument. The prosecution's wider checks remain attributed to it.

## Projection correction retained: no source repair

At `extras/two_domain/src/TD1.lean:162`, put `h := hcr ν0 hν0` and `W := D ∪ E`. The premise is a backward/forward pair:

```text
h : CurlReads W (shiftBack x ν0) ν0 μ AND CurlReads W x ν0 μ
```

The frozen `CurlReads` is right-associated:

```text
C1 AND (C2 AND (C3 AND C4))
C1 = CubeBond W (shift x ν0, μ)
C2 = CubeBond W (x, μ)
C3 = CubeBond W (shift x μ, ν0)
C4 = CubeBond W (x, ν0)
```

Thus `h.2` selects the forward predicate, `h.2.2.1` selects `C2`, and `h.2.2.1.1` selects **`x ∈ W`**, because `CubeBond`'s first component is membership of the bond's start. This is precisely the membership needed by the two calls to `glue_side` after splitting `D ∪ E`.

The card forgot the outer backward/forward conjunction. Its proposed `h.2.1.1` instead selects membership of **`shift x ν0`**, not `x`. The prosecution independently re-derived the same correction. Do not change the projection. The union dependency chain is uncompiled but is not shown defective by this objection.

The card's “Reading defect” section and item 9, together with the corresponding objection in `AHP/notes/two-domain.md`, remain stale and are explicitly excluded from adoption. They were not edited in this narrowly scoped task. Refuting that objection does not verify the entire union draft.

## Prosecution findings accepted with their limits

1. **Missing gates control the status.** Direct filesystem inspection confirms `extras/two_domain/gate_record/` is absent. The reported two byte-identical builds, checker exits, 1,029-root census, 16 mutants and per-headline dependency prints cannot be verified from this package. `SCOPE.md`'s “CLOSED”/“PROVED (Lean)” and `STATEMENT.md`'s “kernel-checked” are lane self-reports, not evidence supplied by this review. Unexecuted print commands do not establish a dependency list.
2. **Constants provenance needs the prosecution's sharper correction.** `TD2.famTwoDom_union` obtains its package from `famTorusLayer_union` and chooses `max R₁ 4`, retaining the other constants. `TD3.famTwoDom_cap` and `famTwoDom_box` both obtain their package from `famTorusLayerCap`. The latter does not call `famTorusLayer_box`. `mixedTwoDom → totalTwoDom → target8TwoDom` inherit the box draft's cap-derived coercivity package; the last also takes `SidePow6` from `target8Layer` and combines thresholds. Therefore the statement document's blanket “same constants as the corresponding one-domain statements” is unsupported for box/mixed/total/target8. Existential headline types do not identify the witnesses chosen by different proofs.
3. **Box meeting is not a lane result.** The prosecution reports no TD declaration formalizing the prose claim that a nonempty box cut always meets `B⁰(S)`. The inspected box proof does not need it: `DescribedAt0` reads only levels 1 and 2, a filtered box family supplies cap coverage, and whole-box regularity restricts to `sites ∩ S.Om 0`. A box of `Sc` may leave `S.Om 0`. This is a box-hypothesis draft using a cap route, not an identification of the two classes.
4. **Census mismatch is confirmed.** `TD7`'s header names `THL1..THL8`, while its loop selects `s.startsWith "TD" && s != "TD7"`. Neither the header nor the historical root count certifies the frozen thin-layer modules. This is a comment/script discrepancy, not evidence of a false coercivity statement.
5. **No new mathematical refutation established.** The source-level reduction directions checked here agree with prosecution: cap regularity restricts along inclusion; box feeds the cap form; union constructs a regular covering family on `S`; mixed and singleton forms retain their hypotheses. This agreement does not settle defeq, simplification, decidability or tactic-elaboration risks. The broader geometric and witness checks in the prosecution remain reading evidence, not execution evidence.

## Boundaries on any later reuse

- Constants precede scales, radii, families, towers and configurations. `Sc` is universal after `S`; its positive levels agree with `S`, and `S.Om 0 ⊆ Sc.Om 0`. The headlines do not separately require `Sc` to be admissible, block-closed or radial. Do not weaken the agreement or inclusion.
- Coverage of sites and plaquettes, factor lower bounds and smallness remain. The class hypothesis sees the shell `Sc.Om 0 \ S.Om 0`; the quadratic form is built from `S`. “No condition on the family remains” is not authorized.
- The union construction raises the existential threshold to `max R₁ 4`; 4 is a proof choice, not a universal binder or a sharpness result. Nothing here supplies an explicit original threshold or covers smaller collars.
- Family/cap/mixed/total conclude `InstAtWD`, containing `WellDefG` and `InstIneq`. `Target8TwoDom` uses factor 12 and `AdmNoBase` at one radius but concludes only `InstIneq`. Neither it nor its name makes it the frozen project headline.
- As the prosecution records, the witness is existential, uses two nested radial slabs at depth two and the M1-regime family `famF c`, and places `LambdaOK2` at the larger radius `Rb`. Do not strengthen it to arbitrary configurations, depths, non-radial layers or general families. The cut-missing example is at index zero, not every index; no union-class cap is stated.
- Inherited dimension 3, SU(2), periodic distance, aligned blocks, both-endpoint `CubeBond`, and fine spacing remain unchanged. The printed one-endpoint convention is not thereby recovered. Formal `a₀` is not the source's `a₁`.
- The two-domain reading is an interpretation, not forced by the two printed occurrences of one domain symbol. The paper's adopted one-domain reading and its still-open literal-transfer sentence stand. Neither the statement-sheet entry nor the extras draft paper sentence overrides that status.

## Remaining gates and actions

Before a project-level mathematical claim, an authorized later environment must establish successful elaboration against the frozen tree and actually print/check that dependencies are restricted to `propext`, `Classical.choice` and `Quot.sound`, with retained artifacts and renewed review. The constants prose, box-meeting attribution and census comment also need reconciliation before reuse. None of these gates was run here; this review authorizes no paper insertion.

Only `AHP/attempts/two-domain/SOL_VERDICT.md` was written in this pass. No Lean source was edited or copied. No compiler/build command, dependency download, deletion, commit or push was run. Frozen modules, Lake configuration, paper, CLAIMS, OPEN_ITEMS and `notes/statement_sheet.tex` were untouched. Verification consists of direct source comparison, explicit conjunction bookkeeping and the missing-directory check; `compiled` remains false.
