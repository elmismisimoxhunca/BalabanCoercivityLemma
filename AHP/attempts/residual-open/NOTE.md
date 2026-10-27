# residual-open — classification note

Review only. No Lean fragment. Not a Lake root. Not compiled. Not a theorem of the project tree. Frozen files were not edited. No `lean`, `lake`, `elan`, `REPRODUCE.sh`, or `#print axioms` was run. `compiled` is false.

This file classifies residuals already recorded in `paper/OPEN_ITEMS.md` section R (R-b, R-c, and the level-0 / Corollary 3.6 lines) against the frozen definitions and the adjudicated page text. It does not close them. The earlier [Sol verdict](SOL_VERDICT.md) rejected an empty submission at grade 0. This note is the missing classification. It is not a replacement verdict and it does not discharge any gate.

Full note: [residual-open.md](/home/sebastian/BalabanCoercivityLemma/AHP/notes/residual-open.md).

## R-b — third enlargement is not a clause of `IsDCube`

Page, adjudicated verbatim (`sources/corpus/pages/CMP99b_p408.md`): after \(\mathscr{D}_j\) is defined as cubes that are unions of \(2^d\) big blocks with at least one block in \(B^j(\Lambda_j)\), and after \(\tilde\square^n\) is defined as the concentric cube of size \((2+2n)ML^j\eta\),

> The cube \(\tilde\square^3\) is either contained in \(B^j(\Lambda_j)\), or intersects also the domain \(B^{j+1}(\Lambda_{j+1})\).

That sentence starts the local sequence \(\{\Omega_n(\square)\}\). It is not part of the membership sentence for \(\mathscr{D}_j\).

`IsDCube` (`lean/src/C5C.lean`, the definition) is only

\[
j \le k \land \mathrm{GridCorner}(\mathrm{bigSide}\,M\,\ell\,j,\, c) \land \exists x_0,\; x_0 \in B^j(S) \land x_0 \in \mathrm{dCube}(\mathrm{bigSide}\,M\,\ell\,j,\, c).
\]

`IsDCubePrint` (`lean/src/C5G.lean`) adds the \(j = 0\) disjunct \(x_0 \notin \Omega_1\). Neither predicate mentions \(\tilde\square^3\), containment in \(B^j\), or a meeting with \(B^{j+1}\).

Recorded, not re-proved here (`paper/OPEN_ITEMS.md`, R-b): isolated-seed sharpness witnesses need not satisfy the printed sentence (\(k = j = 1\): \(B^2\) empty, third enlargement not inside the seed block). If that sentence is imposed on the tested family, necessity and sharpness for the restricted family are not established. Sufficiency already proved for the larger formal family still applies to any subfamily. A smaller hypothesis does not become a necessity theorem.

Sol's concentric trial, as recorded in that same paragraph and not recomputed here: the whole concentric third enlargement taken as seed gave worst distances \(12\), \(21\), \(18\) and first \(R = 12\), \(11\), \(18\) for \((\ell, M) = (2,1)\), \((2,2)\), \((3,1)\). Three pairs. A bounded diagnostic. Not a threshold for all \(\ell, M\). Not a theorem that those radii are least, and not a theorem that the formal collar stays sharp, or fails, once the extra clause is required.

## R-c — powers of \(L\) on the page, all naturals in the formal statement

Same page: "We take these numbers as powers of \(L\)." The numbers are \(R\) and \(M\), after "sufficiently large." Later \(M = KR_0M_0\) with \(K\) a positive integer. The page presents a choice of large parameters, not a proved necessity of the power restriction.

Formal binders do not impose it.

- `cube5_in_union` (`lean/src/C5C.lean`): \(\ell, M, R : \mathbb{N}\) with \(2 \le \ell\), \(0 < M\), \(21\ell \le R\). No \(R = \ell^r\) and no \(M = \ell^s\).
- `collarOK` (`lean/src/SH2.lean`): \(18 \cdot \mathrm{bigSide}\,M\,\ell\,j + 3 \le (R+3)\cdot\mathrm{bigSide}\,M\,\ell\,(j-1)\), with `bigSide M ell j = M * ell^j` (`lean/src/ZStatementP428.lean`). Any naturals satisfying the inequality.
- `collar_power_ell2` (`lean/src/RB3.lean`): \(\forall r,\; 34 \le 2^r \leftrightarrow 6 \le r\). The docstring identifies \(34\) as the integer threshold \(18\ell - 2\) for \(\ell = 2\) once \(M\ell^{j-1} \ge 3\). Then \(2^5 = 32 < 34 \le 64 = 2^6\). So \(34\) is admitted by the natural-number collar in that regime and is not a power of \(2\). The power fact is separate arithmetic. It does not restrict `collarOK`, and restricting a sufficient statement to powers does not prove sharpness on that subset.

`paper/OPEN_ITEMS.md` (integration of `p409_sharp`): least \(R\) is the least natural for the universal formal statement, not per tower and not a power of \(\ell\).

Still open on the same R-c line, not settled by this note: no multi-cube-cover optimum, no exact local-domain window, no \(j = 0\) sharp-collar theorem. The `SH2.lean` module comment writes \(3/(M\ell^{j-1})\). That quotient is not the definition. `collarOK` is the inequality with \(+3\). Do not read the comment as floor division.

## Level-0 non-box unions

`DescribedAt0` (`lean/src/P4L4.lean`) requires the site set to equal one grid box `siteBox z (f * bigSide M ell 0)`. It may meet the complement of \(\Omega_1\) and may leave \(\Omega_0\). It is not an arbitrary union of \(M\)-blocks.

`DescribedAtAlt` / `IsClassCubeAlt` (`lean/src/L0C2.lean`): index \(0\) is `DescribedAt0`; index \(\ge 1\) is `DescribedAt`, again one `siteBox`. `boxClass` (`lean/src/UNI_Tor.lean`) is `IsClassCube`.

`FamTorusCap` and `cap_unconditional` are the coercivity headline for that altered box class, with regularity on the cube cut by \(\Omega_0\). `capHeadline_imp_box` sends it to the original box headline. The quantifiers do not range over level-0 sets that meet several \(M\)-blocks and are not a single box.

`IsClassSetW` (`lean/src/GenCl1.lean`) is a different predicate: two distinct level-\(j\) blocks, enclosed in a box. It is the non-box superset used for refutation. It is not `DescribedAt0`, and `FamTorusCap` does not claim the inequality for it.

`paper/OPEN_ITEMS.md` section R: the altered-class coercivity lemma is for boxes. Level-0 non-box unions are not included. The coercivity statement for those unions stays open. The same paragraph records that Sol's cap route fails on a finite example and that the example does not decide the statement. This note does not reconstruct the example and does not call the statement false.

## Corollary 3.6 — source \(a_1\), formal \(a_0\)

Printed corollary (`sources/corpus/pages/CMP99b_p408.md`): if \(U\) satisfies (3.35) with \(O(1)\,M\alpha_0 \le a_1\), and \(\Omega'_0 \subset \square\) for a cube \(\square\) of that class, then Theorems 3.1–3.3 hold for \(G'(U)\), \((Q'(U)G'^2(U)Q'^*(U))^{-1}\), and \(G(U)\) on \(\{\Omega'_j\}\). The line above sets \(\alpha_1 = O(1)\,M\alpha_0\) and assumes \(O(1)\,M\alpha_0 \le a_1\).

Formal smallness, in `FamTorusCap` (`lean/src/L0C2.lean`) and in the frozen coercivity binders (`lean/src/ZStatementP428.lean`), is an existential \(a_0 > 0\) with \(f \cdot M \cdot \alpha_0 \le a_0\). In `level0_instance_inequality` (`lean/src/L0C5.lean`) the factor that appears is \(12\ell\), still compared with that formal \(a_0\). Neither binder is the source constant \(a_1\).

`level0_case_complete` (`lean/src/L0C3.lean`) is the pair: geometric membership of the local domain and of \(\tilde\square^5\) in `IsClassCubeAlt` at factors \(10\) and \(12\), together with `FamTorusCap`. The module comment calls this "the level-0 case of p.409 in Corollary 3.6." `paper/OPEN_ITEMS.md` lists `L0C3.lean` lines 31–32 on the must-not-write list. The pair is not Theorems 3.1–3.3, not exterior regularity of a local \(\Omega_0(\square)\), and not \(a_0 = a_1\).

Section Q item 6 and section R keep the analytic transfer open, including at factor \(12\ell\), with the source threshold \(a_1\) kept apart from the formal \(a_0\). `DescribedAt0` itself has no unique-index clause (`IsClassCubeAlt` adds one) and admits sites outside \(\Omega_0\). Nothing here shows Corollary 3.6 under the original (3.35).

## Document debt — Kimi lanes, no axiom print

No axiom print was run for this draft. Historical lane logs are not a print of this note and are not re-certified. Kimi reviews recorded as owed, and not discharged here:

| Lane | Recorded Sol status | Kimi |
|---|---|---|
| `cube5` (`p409_cube5`) | adopt with disclosures | not done |
| `mixed12` | adopt with disclosures, grade 2 | none |
| `level0_class` | adopt with disclosures, grade 2 | none |
| `p409_sharp` | adopt with disclosures, grade 2 | none |
| `r_bridge` | adopt with disclosures, grade 2 | none |
| `thin_layer` | adopt with disclosures, grade 2 | none |

Locators: `paper/OPEN_ITEMS.md` (sections O, Q, R, R-a, R-a2) and `HANDOFF.md` (the same six lanes). A later authorized rebuild would still have to print only `propext`, `Classical.choice`, and `Quot.sound` before any new text is called a theorem. This run does not authorize that rebuild.

## Must not write

- That the third-enlargement sentence is a clause of `IsDCube` or `IsDCubePrint`.
- That Sol's three radii are a threshold, a least \(R\), or a sharpness theorem for the restricted family.
- That formal sufficiency fails on the printed subfamily, or that sufficiency for a larger family is necessity for a smaller one.
- That the formal collar requires \(R\) or \(M\) to be a power of \(L\), or that \(34\) is excluded.
- That `collar_power_ell2` is sharpness on the power-restricted set.
- That the `SH2` comment's quotient is `collarOK`.
- That level-0 non-box unions are refuted by the unreproduced cap-route example, or proved by `FamTorusCap`.
- That Corollary 3.6 holds at level 0, that \(a_0 = a_1\), or that \(12\ell\, M\alpha_0 \le a_0\) is the printed hypothesis \(O(1)\,M\alpha_0 \le a_1\).
- That `level0_case_complete` is Theorems 3.1–3.3.
- That any of the six Kimi gates is discharged, or that a historical axiom log certifies this note.
