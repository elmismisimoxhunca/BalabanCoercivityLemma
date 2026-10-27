# Residual-open — classification

Review only. No Lean file was added. Not compiled. Not a theorem of the project tree. Frozen modules, the lakefile, `paper/`, `CLAIMS`, `OPEN_ITEMS`, and `notes/statement_sheet.tex` were not edited. No axiom print was run. `compiled` is false.

The four mathematical residuals below stay open. The six Kimi lanes stay document debt. Attempt record: [NOTE.md](/home/sebastian/BalabanCoercivityLemma/AHP/attempts/residual-open/NOTE.md).

## R-b. The third enlargement is not in `IsDCube`

On CMP 99b p. 408 the family \(\mathscr{D}_j\) is cubes of \(2^d\) big blocks with at least one block in \(B^j(\Lambda_j)\). Separately, the page says that the concentric third enlargement \(\tilde\square^3\) is either contained in \(B^j(\Lambda_j)\) or also meets \(B^{j+1}(\Lambda_{j+1})\), and then builds the local sequence from that alternative. Source text: `sources/corpus/pages/CMP99b_p408.md`.

`IsDCube` (`lean/src/C5C.lean`) is an index bound \(j \le k\), a grid corner, and one seed site in \(B^j\) and in the seed cube. `IsDCubePrint` (`lean/src/C5G.lean`) adds, at \(j = 0\), a seed outside \(\Omega_1\). There is no third-enlargement clause in either definition.

`paper/OPEN_ITEMS.md` R-b already records that isolated-seed sharpness witnesses need not obey the printed sentence, and that necessity and sharpness are not known for the family that does obey it. Sufficiency for the larger formal family still specialises to any subfamily. That specialisation is not a sharpness theorem for the extra clause.

Sol's concentric trial is recorded in the same paragraph and was not rerun: worst distances \(12\), \(21\), \(18\) and first radii \(12\), \(11\), \(18\) at \((\ell,M) = (2,1)\), \((2,2)\), \((3,1)\), with the whole concentric third enlargement as seed. Three bounded samples. Not a threshold in \(\ell\) and \(M\). Not a theorem.

## R-c. Powers of \(L\) on the page, naturals in the formal result

p. 408 takes the sufficiently large \(R\) and \(M\) to be powers of \(L\). The formal statements do not. `cube5_in_union` quantifies over naturals with \(2 \le \ell\), \(0 < M\), and \(21\ell \le R\). `collarOK` (`lean/src/SH2.lean`) is the inequality

\[
18\cdot M\cdot \ell^{j} + 3 \le (R+3)\cdot M\cdot \ell^{j-1}
\]

for \(j \ge 1\), with \(M\) and \(R\) any naturals that satisfy it (`bigSide` in `lean/src/ZStatementP428.lean`). No binder requires a power.

`collar_power_ell2` (`lean/src/RB3.lean`) is the separate arithmetic fact that \(34 \le 2^r\) if and only if \(6 \le r\). The integer threshold named in its docstring is \(34 = 18\cdot 2 - 2\), in the regime \(M\ell^{j-1} \ge 3\). Then \(32 < 34 \le 64\), so the natural-number collar can hold at a radius that is not a power of \(2\). The first power of \(2\) at or above \(34\) is \(64\). Restricting a sufficient statement to powers of \(L\) does not prove that the restricted statement is sharp.

Still open, and not touched here: a multi-cube-cover optimum, an exact local-domain window, and a sharp collar at \(j = 0\). The comment in `SH2.lean` that writes a quotient \(3/(M\ell^{j-1})\) is not `collarOK`.

## Level 0. Non-box unions are not the altered box class

`DescribedAt0` (`lean/src/P4L4.lean`) is one grid-aligned box of side \(f M\): contained in \((\Omega_1)^c \cup B^1\), and meeting \((\Omega_1)^c\). It may leave \(\Omega_0\). `DescribedAtAlt` (`lean/src/L0C2.lean`) uses that box at index \(0\) and the original one-box `DescribedAt` at positive index. `FamTorusCap` is the coercivity headline for this class. It implies the original box headline. It does not quantify over a level-0 union of several \(M\)-blocks that is not a single box.

`IsClassSetW` (`lean/src/GenCl1.lean`) does allow more than one block, inside a bounding box. That predicate is not the altered class, and the level-0 headline does not claim coercivity for it.

Section R of `paper/OPEN_ITEMS.md` leaves the coercivity lemma for level-0 non-box unions open. It also records that a cap-route attempt fails on a finite example and that the example does not decide the statement. The example is not reconstructed here. The statement is not called false and not called proved.

## Corollary 3.6. Source \(a_1\) stays apart from formal \(a_0\)

The printed corollary assumes (3.35) with \(O(1)\,M\alpha_0 \le a_1\), and a local domain inside a cube of that class, and concludes Theorems 3.1–3.3 for the localized operators. The source threshold is \(a_1\).

The formal headlines use an existential \(a_0 > 0\) and a bound \(f\cdot M\cdot\alpha_0 \le a_0\). `level0_instance_inequality` (`lean/src/L0C5.lean`) uses the factor \(12\ell\) against that same formal \(a_0\). These are not the printed hypothesis \(O(1)\,M\alpha_0 \le a_1\).

`level0_case_complete` (`lean/src/L0C3.lean`) packages geometric membership in `IsClassCubeAlt` at factors \(10\) and \(12\) with `FamTorusCap`. Its comment mentions Corollary 3.6. That comment is stale: the declaration is not Theorems 3.1–3.3, and `paper/OPEN_ITEMS.md` forbids reading it as "Corollary 3.6 now proved at level zero." Exterior regularity of a local \(\Omega_0(\square)\) is not part of the declaration. Analytic transfer under the altered class, including at factor \(12\ell\), remains open. \(a_1\) and \(a_0\) are not identified.

## Document debt

Kimi reviews are still owed for `cube5`, `mixed12`, `level0_class`, `p409_sharp`, `r_bridge`, and `thin_layer`. Sol reviews of those lanes are already recorded, with disclosures, in `paper/OPEN_ITEMS.md` and `HANDOFF.md`. This classification does not replace a Kimi pass and does not rerun their historical axiom logs.

Nothing in this note is a theorem. A later rebuild, if one is authorized, is what would have to print only `propext`, `Classical.choice`, and `Quot.sound`.
