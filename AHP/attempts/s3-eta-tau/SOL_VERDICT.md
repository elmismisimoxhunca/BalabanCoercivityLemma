# SOL VERDICT — s3-eta-tau

```json
{
  "itemId": "s3-eta-tau",
  "verdict": "reject",
  "grade": "2",
  "disclosures": [
    "Reject the submitted draft as a whole: its negative claim about BaseDataS.K and an extra L^{-k} in the correction is not established by the frozen definitions. The draft and its note were not rewritten by this review.",
    "Retain only the source-reviewed flat/full-support mass cancellation, the scalar-free top-level embedding, the unit-bond energy normalization, and the dimension-3 measure/source cancellation for a fixed test field.",
    "The displayed J term is not certified as the printed operator expression for nonzero J. Its H1in depends on the unresolved comparison of the second-order constraint term and G1inv with the print.",
    "Correct the conflation of the constant-a bond mass with the recursive site weights, the erroneous scalar factor attributed to Cop, the omitted sign of Jf, and the reference to [REV D-12].",
    "compiled is false. This is a direct frozen-source and printed-transcription review, not a compiler check or a theorem of the project tree. No source-page image was successfully inspected.",
    "S-3 remains open at the full non-flat operator-fidelity level. No deviation-table row or paper insertion is justified by this draft; frozen files and the paper were not edited."
  ],
  "paperSentence": ""
}
```

## Scope and evidence

Read `HANDOFF.md` and the whole of `paper/OPEN_ITEMS.md` before writing. Read both draft files and `PROSECUTION.md`. Grade **2** reflects direct comparison with actual frozen definitions, not reliance on either agent's summary:

| Subject | Frozen text independently read |
|---|---|
| First term, full form, reparametrization | `lean/src/ZXG3A.lean:33–60` |
| Mesh, signed localized source, covariance normalization, solution map, one-step remainder | `lean/src/ZXR2Wire2.lean:36–92` |
| Top-level extraction | `lean/src/ZXR2Wire1.lean:27–44` |
| Embedding norm and mass identity, with hypotheses | `lean/src/ZGU1D.lean:28–100` |
| Actual flat reduction and cancellation proof text | `lean/src/ZGU1E.lean:32–73` |
| Level-weighted first and second jets | `lean/src/ZXR2Sector.lean:57–111` |
| Mass weights and concrete assembly of C2 and J | `lean/src/ZXR2Ops3.lean:97–149` |
| K, H, second-order correction, G1 and H1 | `lean/src/R2Algebra.lean:125–231,306–309` |
| Constraint matrix, lift and Cop | `lean/src/ZXR2Unit2.lean:84–107,126–154` |
| Mesh dependence of localized source | `lean/src/ZLocJ.lean:48–89`, and `lean/src/ZIngredientJ.lean:109–115` |
| Bond energy and matrix norm | `lean/src/AdalyFormal/Balaban/RegularUPerturbation.lean:355–356`, `lean/src/AdalyFormal/Balaban/RMapLipschitz.lean:143–150`, actual `hsInner` in `SuTwoInner.lean:109–112` |

Also read the convention and gradient definitions in `R2Ops1.lean`, and the printed transcriptions `sources/corpus/pages/CMP99b_p392.md`, `CMP99b_p393.md`, `CMP99b_p421.md`, `CMP99b_p422.md`, `CMP99b_p427.md`, `CMP99b_p428.md`. These provide (3.11), (3.14), (3.16), (3.127)–(3.129), (3.134)–(3.136), and (3.155)–(3.157). The paper's existing normalization disclosure was read at `paper/paper.tex:580–595` without modification.

The image reader rejected the two attempted large page images; local image-processing dependencies were unavailable. No installation was attempted. Thus the printed comparison is against repository transcriptions, **not an independent page-image verification**.

## Findings that survive

### 1. Mass cancellation: yes, with the exact scope

`ZGU1E.genForm_reduction` assumes full support, the whole fine domain, flat background, and invertibility of both `G1inv` and `Nmat`. Its proof explicitly uses

\[
\eta\ell^k=1,\qquad
\eta\bigl(a\ell^k\|B\|^2\bigr)=a\|B\|^2.
\]

`ZGU1D.mass_inner` supplies the mass coefficient under full support; `tau_adj_norm` supplies the norm equality. This is strong source-level evidence that the external factor and the subtracted mass term have compatible units on this family. It is not a comparison of non-flat covariances with the print, and nothing was recompiled here.

The relevant printed **bond** weight is already the constant-a expression in (3.16): at dimension three it is \(aL^j\eta\), which becomes the code's \(aL^j\) after dividing by \(\eta\). At the top level it is \(a\). Equation (3.128) also uses constant a. The draft's equality with a recursive \(a_j\) is incorrect: `R2Ops1` distinguishes the **site** operator involving `Q'` and its recursive weights. Those weights must not be substituted into this bond-mass comparison.

### 2. Tau-star and bond energy: no extra scalar

`tauExt` reads the embedded top-level coordinate, or zero if absent. There is no multiplication by the mesh. With the unweighted carriers its adjoint has the corresponding insertion interpretation; the explicit full-support value and norm identities are in `ZGU1D`. The latter norm identity must keep its full-support qualification.

`bondEnergy Bt` is precisely the unweighted sum of squared fiber norms. The `PiLp 2` self-pairing uses the same sum, and the fiber norm has the normalized trace scale, one half the ordinary Frobenius square. This establishes the common energy normalization. It does **not** equate the energies of `Bt` and `C Bt`.

### 3. Source pairing: only the measure/source factor is confirmed

The signed code source is `-(JSU2Loc 1 ...)`. For a fixed localization, background and test-field value, `JSU2Loc` carries mesh dependence \(\eta^{-3}\), while (3.11) weights the pairing by \(\eta^d\). Thus in dimension three

\[
\eta^3\eta^{-3}=1.
\]

This confirms that **these two factors alone** require no additional mesh prefactor. The sign is a separate chart convention; the draft drops it in two places. This calculation does not compare the actual `H1in (D2in B)` with its printed counterpart. In particular, it cannot certify the whole displayed J summand when J is nonzero.

## Why the negative headline fails

The draft identifies the lane cross term with the complete printed cross term solely from the mesh dependence of J. That premise is unproved: the field paired with J also contains the second-order constraint map and H.

The actual code is

\[
\mathrm{C2fullOf}(A)_{j,b}=L^{-j}\mathrm{C2rawB}(A)_{j,b},
\]

and concrete `baseData.C2` applies this map to `Wop (iE A)`. The explicit level weight is absent from the draft's count. The printed (3.14) distinguishes the raw argument \(\eta A\) from the rescaled argument \(L^j\eta A\). The p.421 representation sentence distinguishes two H conventions and assigns \(L^j\eta C_j^{(2)}(A)\) to the plain-H representation. Formula (3.136) further carries the level-dependent weight \((L^j\eta)^{d+1}\). These cannot be discarded while comparing the cross term.

`Units.lean.k_cross_not_homogeneous` is only an arithmetic rearrangement of an expression with abstract scalars q and c. It neither identifies c with the frozen cross term nor proves a non-homogeneity statement. Its equality is compatible with vanishing c and with mesh one. Even a successful future elaboration of that identity would not supply the missing operator comparison.

I agree with the prosecution's **disposition** of F1: withdraw the asserted mismatch and leave a convention-level comparison open. I do **not** promote its illustrative alternate power counts to a proved replacement identity. In particular, neither "K is not homogeneous" nor "K equals the printed K divided by eta on every tower" is established here. Nor does the existence of level weights by itself prove that a uniform overall factor is impossible; other factors may compensate them. A complete audit must track the field-coordinate conversion, level pairing weights, adjoints, H, the projected C2 and J together.

Since `R2Algebra.H1` is built using the inverse of `G1inv`, and `ZXR2Wire2.H1in` uses that H1, this unresolved comparison propagates to any claimed fidelity of the non-flat displayed J term. The flat reduction cannot detect it: its J vanishes.

## Remaining corrections and limits

- **F2 upheld, with a qualification to the prosecution.** `Cop = id - hLift Q`; `hLift = iotaD H0inv rhoD`. The explicit one-step \(L^{-1}\) belongs to `D2in`, not to `Cop`. For a nonzero scalar rescaling of Q on the invertible constraint domain, inverse scaling cancels it in Cop. This concerns scalar normalization only: Cop still depends on its geometric parameters and on Q, so it is not a proof of k-independent operators or a uniform norm bound as backgrounds vary.
- **F3 upheld.** Use (3.16) and (3.128)'s constant a, not the recursive site weights of (3.24).
- **F4 upheld.** Restrict the J confirmation to the measure/source factor for fixed field values; do not claim printed operator equality.
- **F5–F6 upheld.** Restore the minus sign in the K-section and `Units.lean` source description. Cite **[REV D-12]**, not deviation-table D12. The eta cancellation occurs in an anonymous local fact in `genForm_reduction`, not as a separately named identity there.

## Decision boundary and verification

**Reject as submitted**, rather than adopt the still-uncorrected negative headline with a footnote. The narrower confirmations above are usable as uncompiled review evidence. A revised note should remove the asserted correction error and clearly separate internal flat consistency from full printed-operator fidelity. S-3 is not closed by this pass.

No new deviation-table row follows from an unsupported mismatch, and the paper's existing inherited-normalization disclosure is not refuted. `paperSentence` is empty: no paper insertion is authorized.

Only this verdict file was written. The draft note and `Units.lean` remain unchanged, so their rejected wording is still present and must not be reused without this verdict. No prohibited compiler/build command, download, deletion, commit or push was run. No frozen module, configuration, Check file, expected output, paper or statement sheet was edited. `compiled` remains false; no project-tree theorem or compiler-dependency certification is claimed.
