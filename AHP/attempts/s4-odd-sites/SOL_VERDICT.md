# SOL VERDICT — s4-odd-sites

```json
{
  "itemId": "s4-odd-sites",
  "verdict": "adopt-with-disclosures",
  "grade": "2",
  "disclosures": [
    "Adopt the blocked disposition and the hand-checked arithmetic only. The odd-ell sites-only body remains open, including odd ell > 11; neither direction is established.",
    "The obstruction concerns integer profiles with steps of a fixed positive natural magnitude and two exactly zero aligned block sums. It excludes that cancellation route, not every odd-ell construction or gauge background.",
    "Correct the note's agnosticism about chain_instance_S: its frozen statement applies at odd ell >= 3 under its remaining hypotheses. Its constrained-chain crossing and overlap conclusion is not the full analytic counterexample.",
    "The arithmetic window c = 9 ell + 1, w = 19 is valid. The frozen sites_not_imp_plaq_S and so_stag0_class also have no evenness binder; geometry and regularity alone do not decide the sites-only inequality.",
    "A single nonzero homogeneous tau exists, but is not a blocked-gauge identity, a nearby-parameter family, an inverse certificate, or a counterexample.",
    "compiled is false. The draft is not elaboration-checked and possible tactic failures remain unresolved. No draft declaration is certified as a theorem of the project tree, and no compiler-dependency audit was performed.",
    "The CMP 109 p.251 convention is used only as recorded in OPEN_ITEMS S-4; no page-image or cross-paper standing-convention verification was performed. No paper edit or insertion is authorized."
  ],
  "paperSentence": ""
}
```

## Evidence and grade

Read `HANDOFF.md` and all of `paper/OPEN_ITEMS.md` before writing. Independently read both draft files and `PROSECUTION.md`, then the actual frozen definitions and statements below. Grade **2** is a source-level review, not a compilation grade.

| Question | Independently inspected source |
|---|---|
| Exact sites-only body and order of quantifiers | `lean/src/CaT2d.lean:122–132` |
| Site coverage, plaquette coverage, per-cube regularity | `lean/src/NtFam.lean:26–38` |
| Guard in the conclusion | `lean/src/CvS1.lean:70–72` |
| Even-only negative result and divisible window | `lean/src/SoA1.lean:37–39`, `SoA2.lean:18–44` |
| Geometric separation without evenness | `lean/src/SoA3.lean:86–90` |
| Thin-width instance and arithmetic relation | `lean/src/NsCvNe2.lean:31–33`, `SoGeo.lean:35` |
| Uncovered transverse slice and unrestricted angle | `lean/src/SoGeo.lean:71–76`, `SoD0.lean:22–26` |
| Analytic use of evenness | `lean/src/SoM3.lean:34` and its proof; `SoU2.lean:43–112` |
| Existing odd-ell chain fact | `lean/src/SoE8.lean:70` and its complete proof |
| Exact-cancellation and nearby-parameter obstructions | Complete `lean/src/SoPar.lean` and `SolSitesAffine.lean` |
| Direction of implication to the covered body | `lean/src/CsA2.lean:84–91` |

A direct search of `lean/src/` for `FamilyTorusSitesConstAt` found the definition, ell = 2 negation, even-ell negations/table, and the one-way implication to the both-clause body. These inspected declarations do not decide odd ell. This is not a metamathematical undecidability claim or a proof that no differently packaged argument could exist.

## Mathematical assessment

### The formal cell is accurately identified

For fixed c, ell and a, the body first chooses thresholds and positive constants, then quantifies over arbitrarily large m and R, all positive depths and the qualified torus/tower/Lambda/configuration data. It keeps `CovSitesF` and `PerCubeRegularF`. Its conclusion is `InstIneqWDH`, hence **WellDefG implies the inequality**; it does not itself assert inverse existence. A singular configuration alone cannot refute this body.

The even refutation supplies a regular, sites-covered configuration with the guard and a negative competitor. Its entry point, `main_neg_S`, and the analytic/temporal-background lemmas explicitly require evenness. Their binders cannot be dropped because a scalar chain still has a crossing.

The converse coverage implication fails geometrically at odd ell as well. Under `SoRel` and the other hypotheses, `sites_not_imp_plaq_S` supplies site coverage and failure of plaquette coverage; `so_stag0_class` supplies regularity at every real angle. The uncovered set is a transverse slice of direction-0 bonds, not one isolated bond. These facts do not provide the missing guarded analytic inequality or its failure.

### The arithmetic is sound, with narrow scope

For positive natural d, each step ±d is congruent to d modulo 2d. Consequently

\[
h(\ell+i,j)-h(i,j)\equiv \ell d\pmod{2d}.
\]

Summing over the two aligned blocks gives a difference congruent to \(\ell^3d\). If both sums vanish, \(2d\mid\ell^3d\), and cancellation of nonzero d forces \(2\mid\ell^3\), impossible for odd ell. The draft's odd-cube expansion is correct. Zero d would invalidate the conclusion and is excluded. The argument needs only horizontal steps; it neither classifies variable-magnitude profiles nor handles the physical principal-log branches.

The window is genuinely nonempty: with \(c=9\ell+1\) and w = 19, both sides of the relation equal \(18\ell\), and the stated inequalities hold for ell >= 3. At ell = 13 this gives c = 118. This is parameter arithmetic, not a new tower or analytic witness.

Put \(A=2\pi\ell^2\). If \(S_0\ne0\), choosing \(\tau=AS_0\) yields the integer multipliers \(S_0^2\) and \(S_0S_1\); otherwise use the nonzero \(S_1\). Thus one nonzero homogeneous parameter exists. No smallness, prescribed cosine, interval of parameters, or blocked-background conclusion follows. The frozen nearby-parameter statements retain their separation hypothesis and, in the affine version, the same branch-offset function at both parameters.

## Prosecution findings

**Finding 1 upheld.** Replace the note's agnosticism by: `chain_instance_S` applies to odd ell >= 3 satisfying its remaining hypotheses. It gives a constrained quadratic-chain crossing, null vector and overlap. The subsequent reduction to the full form and the inverse certificates still require work. Build membership is recorded in `MODULES.tsv`; no historical build was independently rerun here.

**Finding 2 warrants a compilation disclosure, not a certified error list.** Trailing `rfl` after a potentially closing `rw` is a plausible script problem. However, I do not adopt the blanket premise that `rw` always rewrites every matching occurrence: rewrites are occurrence-sensitive, so duplication alone does not establish failure. Nor does the local-let `unfold` allegation establish failure by inspection alone. The file remains untested; no repair or elaboration-success claim is made. Hand validity of the arithmetic statements is separate from acceptance of these proof scripts.

## Verification and decision boundary

Adopt **with disclosures**, not as closure of S-4. No conclusion about the truth or falsity of Balaban's printed lemma, safety of odd L, or an odd-ell sites-only counterexample is justified. The note's chain sentence remains unedited and must not be reused without the correction above. The quotation in S-4 does not by itself establish that the later paper's convention governs every earlier statement.

Source-hash checks matched the manifest for all 16 inspected/auxiliary modules checked. A raw scan of `OddSites.lean` found zero prohibited-token matches. Nine arithmetic-window spot checks passed; they are diagnostics only. `git diff --name-only` was empty before writing this verdict; status showed only untracked `.bb/` and `AHP/`.

Only `AHP/attempts/s4-odd-sites/SOL_VERDICT.md` was written by this review. No compiler/build command, download, deletion, commit or push was run. Frozen modules, configuration, Check files, expected outputs, paper and statement sheet were untouched. `compiled` remains false, and `paperSentence` is empty.
