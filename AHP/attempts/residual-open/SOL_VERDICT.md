# Sol review — residual-open

## Verdict: adopt-with-disclosures; grade 2

This replaces the earlier grade-0 rejection of an empty submission. The classification and prosecution now exist. Adoption is of a source-level classification only: no residual is closed, no new mathematical result is certified, and nothing submitted here is a theorem. `compiled` is false. `paperSentence` is empty.

Read both `AHP/notes/residual-open.md` and `AHP/attempts/residual-open/NOTE.md`, the complete `PROSECUTION.md`, the adjudicated transcription `sources/corpus/pages/CMP99b_p408.md`, and the relevant frozen definitions and declarations below. Grade 2 reflects those direct definition checks, not compilation, dependency certification, or a fresh page-image adjudication.

## Direct checks

- **R-b:** `lean/src/C5C.lean:29–30` defines `IsDCube` by an index bound, grid corner, and a seed in both the cube and `towerBj`. `lean/src/C5G.lean:33–35` defines `IsDCubePrint` with a seed in the cube and the alternative
  \[
  (x_0\in\Omega_j\land x_0\notin\Omega_{j+1})\ \lor\ (j=0\land x_0\notin\Omega_1).
  \]
  Neither includes a third-enlargement clause. The page transcription places that assertion in the subsequent local-sequence construction, separately from the membership sentence. Sufficiency on a larger formal family restricts to a subfamily; necessity and sharpness do not follow in that direction. This review does not re-certify the historical sufficiency result.
- **R-c:** `cube5_in_union` in `C5C.lean:60` binds natural parameters with the displayed lower bounds, not power equalities. `SH2.lean:29` defines `collarOK` by the inequality with the actual \(+3\); `ZStatementP428.lean:51` defines `bigSide`. For \(j\ge1\), \(\ell=2\), and \(R=34\), writing \(t=M2^{j-1}\), the inequality is \(36t+3\le37t\), equivalent to \(t\ge3\). Thus this example requires that regime; at \(j=1\), it requires \(M\ge3\). It is not a level-0 claim. `RB3.lean:55–66` supplies separate power arithmetic: \(34\le2^r\) iff \(6\le r\). Neither the arithmetic nor restriction of sufficiency establishes sharpness on the power-restricted set. The page explicitly takes the large parameters as powers of \(L\).
- **Altered level-0 class:** `P4L4.lean:141–144` requires equality to one grid box in `DescribedAt0`, containment in \((\Omega_1)^c\cup B^1\), and a meeting with \((\Omega_1)^c\). It does not require containment in \(\Omega_0\). `L0C2.lean:25–30` uses that descriptor at zero and `DescribedAt` at positive indices, adding index uniqueness in `IsClassCubeAlt`. `ZStatementP428.lean:131–142` confirms the original descriptor is also a single box. `ClassCoupledCap` and `FamTorusCap` (`L0C2.lean:134–159`) use these descriptors and regularity on the intersection with \(\Omega_0\); the declaration `capHeadline_imp_box` has the stated direction. `GenCl1.lean:125–130` instead requires two sites in different level blocks and enclosure in a box, without single-box equality. None of these checks extends the altered box headline to arbitrary non-box unions. The unreconstructed cap-route example is not a refutation of their coercivity statement.
- **Corollary 3.6:** the p.408 transcription uses the source threshold \(a_1\) and concludes Theorems 3.1–3.3 for the localized operators. `FamTorusCap` quantifies an existential positive \(a_0\), with \(fM\alpha_0\le a_0\), where its instantiated \(M=\ell^m\). `L0C5.lean:32–49` uses the factor \(12\ell\) against formal \(a_0\). `L0C3.lean:33–44` packages geometric containment and altered-class membership at factors 10 and 12 with `FamTorusCap`. It does not assert the printed analytic conclusions, exterior regularity of the local domain, or an identification of \(a_0\) and \(a_1\). Its comment must not be used as a stronger statement.

## Disclosures and prosecution qualifications

1. The trial distances \(12,21,18\) and first radii \(12,11,18\) were checked as transcriptions of `paper/OPEN_ITEMS.md` R-b, not recomputed. They remain three bounded samples, not a threshold or least-radius result for the restricted family.
2. Retain both \(j\ge1\) and \(M\ell^{j-1}\ge3\) when discussing the radius-34 collar example. No level-0 sharp-collar conclusion follows.
3. Read the compressed `IsDCubePrint` paraphrase as the exact alternative displayed above, not as an extra conjunct imposed on every seed.
4. “At or above 34” correctly gives the first allowed power 64; it changes no sharpness status.
5. The prosecution's references to “five other” lanes are a counting slip: all **six** named lanes (`cube5`, `mixed12`, `level0_class`, `p409_sharp`, `r_bridge`, `thin_layer`) remain separate review debt in this classification. This residual-open prosecution and review discharge none of those gates. Their historical logs and detailed results were not independently re-audited here.
6. R-b restricted-family necessity/sharpness, R-c restricted-parameter optima and exact local-domain questions, level-0 non-box coercivity, and analytic transfer of Corollary 3.6 remain open. The draft's must-not-write list remains binding on any later use of this classification.

The prosecution found no refutation of the bounded classification. The independent frozen-definition checks support adoption with these disclosures; they do not justify expanding its scope.

## Execution limits

Only this verdict file was written in this review. No compiler, build, dependency download, deletion, commit, or push was run. Frozen modules, configuration, paper, registries, and statement sheet were untouched. No fresh dependency print was obtained; historical logs do not certify this submission. Any later theorem designation remains contingent on the separately authorized rebuild and required dependency output.

`paperSentence`: `""`  
`compiled`: `false`
