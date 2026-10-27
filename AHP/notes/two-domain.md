# Two-domain lane — review only

Uncompiled reading of `extras/two_domain/`. Not a Lake root. Not imported by `lean/`. Not checked by `REPRODUCE.sh`. Not a theorem of the project tree. Frozen files were not edited. No `lean` run, no axiom print.

No Claude prosecution and no Sol review of this lane exist. `paper/OPEN_ITEMS.md` R-a2 and `paper/paper.tex` (the thin-layer paragraph, label `thin-two-domain`) still say the literal two-domain transfer is not proved. This note does not change that sentence.

`notes/statement_sheet.tex` already names `target8TwoDom`, `famTwoDom_union`, `famTwoDom_box`, and `famTwoDom_cap`. Those names are not declarations of this build. Do not treat that row as a gated claim.

## What is actually in the package

Present: `LOG.md`, `READING.md`, `SCOPE.md`, `STATEMENT.md`, and `src/TD1.lean`–`src/TD7.lean` (1,328 lines). A text search of those seven sources found no `sorry`, `admit`, `native_decide`, `unsafe`, `implemented_by`, or `extern`. The string `axiom` occurs in a comment in `TD7.lean`. That is not an axiom print.

Absent: `gate_record/`, mutant sources, control modules, build logs, and oleans. `LOG.md` reports two byte-identical builds, a 1,029-root census, standard axioms, and 16 failing mutants. Those files are not here, so those numbers are not measurements of this package. `HANDOFF.md` says the last gate record was not committed. `TD7.lean` only contains the `#print axioms` and `run_cmd` scripts that would have written that record.

`TD7`'s comment says the census covers `THL1`–`THL8`. The script counts constants of modules whose names start with `TD`, excluding `TD7`. The comment and the script disagree. `TD7` is not imported by `TD1`–`TD6`.

## The two readings

`READING.md` quotes CMP 99b pp. 394 and 396. The print uses one letter \(\Omega_0\) twice:

- p. 394: the operator domain, any union of big blocks containing \(\Omega_1\) (the \(\le RM\) layer is an "e.g.", and a thinner layer is also permitted);
- p. 396: the stratum \(\Lambda_0 = \Omega_0 \setminus \Omega_1\) of the cube class, with \(\Omega_0\) written as the \(\le RM\) layer.

The print does not say which set is meant when they differ. The one-domain reading (class and operators on the same tower) is the thin-layer lane already in `lean/`. The two-domain reading is this extras lane. Neither reading is forced by those sentences.

## What the headline types say

Namespace `AdalyFormal.TwoDom`. In every headline, `Sc` is universally quantified after `S`. It is not existential. The hypotheses on `Sc` are only

\[
\forall j \ge 1,\; Sc.Om\, j = S.Om\, j, \qquad S.Om\, 0 \subseteq Sc.Om\, 0.
\]

`Sc` need not be `Admissible`, block-closed, or radial. `Admissible` of `Sc` is not a hypothesis of the six headlines. It is a conclusion of the witness, where `Sc` is the radial slab of radius \(Rb\).

`S` carries the operators and \(\Lambda\). The conclusion mentions `S`, never `Sc`.

Shared prefix of `TwoDomFamP`, `TwoDomCapP`, `MixedTwoDom`, and `TotalTwoDom`: for \(\ell \ge 2\) and \(a > 0\), there exist \(m_1 \ge 1\), \(R_1\), \(a_0 > 0\), and \(\gamma_0 > 0\) such that for every \(m \ge m_1\), every \(R_0 \ge R_1\), every higher-radius function with \(R_0 \le Rs(j)\) for \(j \ge 1\), every \(\Lambda\)-radius \(RL \ge R_0\), every \(k \ge 1\), every torus and every \(\alpha_0 > 0\), every admitted family of factors \(f \ge 10\) with \(f \cdot \ell^m \cdot \alpha_0 \le a_0\), every `TorusOK` datum, every `AdmSplitNB` tower `S` at level-0 collar \(R_0\), and every `Sc` as above, the class hypothesis on `Sc` implies `InstAtWD` at `S`. `InstAtWD` is `WellDefG` and `InstIneq` (`lean/src/ZT5A.lean`). `AdmSplitNB` is the thin-layer predicate: nested block-closed domains, no base law, strict periodic \(\ell^1\) collar \(R_0 \cdot M\) at level 0 (`lean/src/THL6.lean`).

| Declaration | Class hypothesis, read on `Sc` | \(R_1\) the proof actually supplies | Conclusion |
|---|---|---|---|
| `famTwoDom_union` : `TwoDomFamP unionClass` | `ClassCoupledP unionClass` (`IsClassUnion`: block-closed unions, not boxes) | `max` of the thin-layer union \(R_1\) and \(4\) | `InstAtWD` on `S` |
| `famTwoDom_box` : `TwoDomFamP boxClass` | `ClassCoupledP boxClass` (`IsClassCube`: grid boxes \(z + f M \ell^j\)) | the thin-layer cap \(R_1\), not the max with \(4\) | `InstAtWD` on `S` |
| `famTwoDom_cap` : `TwoDomCapP` | `ClassCoupledCap`: level-0 boxes may leave \(\Omega_0\), regularity on the intersection with \(Sc.Om\, 0\) | the thin-layer cap \(R_1\) | `InstAtWD` on `S` |
| `mixedTwoDom` | `ClassCoupledΦ` for a set \(\Phi\) of factors \(\ge 10\) | from `famTwoDom_box`, hence the cap \(R_1\) | `InstAtWD` on `S` |
| `totalTwoDom` | `ClassCoupled` at one factor \(c \ge 10\) | from `mixedTwoDom` | `InstAtWD` on `S` |
| `target8TwoDom` | `ClassCoupled` at factor \(12\) | see below | `InstIneq` only |

`target8TwoDom` is not `P428Target8` and not `Target8Layer`. Its quantifiers follow `Target8Layer`: \(\exists m_0 \ge 1\), \(\forall m \ge m_0\), \(\exists R_0\), \(\forall R \ge R_0\), `SidePow6`, then \(\exists a_0, \gamma_0\), factor exactly \(12\), tower hypothesis `AdmNoBase` at one radius \(R\) (no base law, no separate higher radii), `LambdaOK2` at that same \(R\), class on `Sc`, conclusion `InstIneq`. There is no `WellDefG` conjunct. `SidePow6` is taken from `target8Layer`; it is not a two-domain result. The proof specialises `totalTwoDom` at \(c = 12\) and `Rs = fun _ => R`.

The numeral \(4\) is not a binder of `TwoDomFamP`. It appears because `famTwoDom_union` sets its existential \(R_1\) to `max R₁ 4` before calling `famTorusLayer_union`. Box, cap, mixed, total, and the frozen-shaped form do not take that max.

`oneDom_of_twoDom`, `oneDomCap_of_twoDom`, and `totalLayer_of_twoDom` only recover the one-domain headline by setting `Sc := S`. For the union form that recovered threshold is the larger one (`max` with \(4\)), so it does not replace `famTorusLayer_union`. There is no named `target8Layer_of_twoDom` or `mixedLayer_of_twoDom`.

## How the proofs move the class, on a reading

Cap. `classCoupledCap_of_two` rewrites `DescribedAtAlt` along `Sc.Om j = S.Om j` for \(j \ge 1\). `DescribedAtAlt` does not look at `Om 0` (`lean/src/L0C2.lean`). Site and plaquette coverage of the smaller domain follow from coverage of the larger one. Regularity is `RegBodyH` on `sites ∩ Om 0`, and `regBody_mono_sites` sends a regular set to a subset. `famTwoDom_cap` then calls `famTorusLayerCap` on `S`. This is monotonicity of the cap, not a cut-and-glue.

Box. `famTwoDom_box` does not call `famTwoDom_union`. It builds a sub-family of those members of \(F\) that are `IsClassCube` on `Sc`, turns a level-0 `DescribedAt` of `Sc` into a `DescribedAt0` of `S` (`descAt0_of_described`), and feeds `ClassCoupledCap` on `S` to `famTorusLayerCap`. `DescribedAt0` (`lean/src/P4L4.lean`) is the p. 408 box: grid box of side \(f M\), contained in \((Om\, 1)^c \cup B^1\), meeting \((Om\, 1)^c\). It does not require the witness point to lie in `S.Om 0`. A box of `Sc` may leave the operator domain. Regularity on the whole box, which is what `ClassCoupledP boxClass` gives, restricts to the intersection. This lane does not contain `path_exists` and does not prove that the cut of a box meets \(B^0(S)\).

Mixed and total. `mixedTwoDom` rebuilds a box family on `Sc` from `ClassCoupledΦ` and calls `famTwoDom_box`. `perCubeRegular2_iff` is the frozen "every class box of this factor is regular." `totalTwoDom` is the singleton \(\Phi = \{c\}\) via `classCoupledΦ_single`.

Union. `famTwoDom_union` does not pass \(F\) to the one-domain theorem. It builds a new family \(F'\) of `S`-class unions that are already regular at a factor occurring in \(F\), proves `ClassCoupledP unionClass` for \(F'\) on `S` by `cover_cut`, and calls `famTorusLayer_union`. For index \(j \ge 1\), `cover_cut` keeps the cube: `towerBj` agrees. For index \(0\), it cuts by `S.Om 0`. If the cut meets \(B^0(S)\), the cut is the `S`-class union. If the cut misses \(B^0(S)\), the text tries to glue an aligned \(M\)-block of a far site (`far_block_exists`, `pdist_block_le`, `regBody_glue`). That block is regular only because site coverage on `Sc` supplies some level-0 class union containing it. The glued factor is `max` of the two factors, which still occurs in \(F\).

The far-site arithmetic, as written, is why the \(4\) appears. `far_block_exists` asks for a site at periodic distance \(\ge 3M+1\) from `Om 1` once \(R_0 \ge 4\) and \(M \ge 1\), because \(3M+1 \le 4M\). `pdist_block_le` bounds the \(\ell^1\) diameter of one aligned \(M\)-block by \(3(M-1)\). The difference is \(4\), and `regBody_glue` refuses distance \(< 4\). The stencil being protected is `ddA`: a backward step plus a plaquette (`lean/src/ZR2A.lean`). This is a reading of the inequalities, not a checked build. Nothing here proves that \(4\) is necessary.

## The union proof text does not match `CurlReads`

`regBody_glue` (`extras/two_domain/src/TD1.lean`) cases the `ddA` clause on

```lean
(hcr ν0 hν0).2.2.1.1
```

and feeds that proof to `glue_side` as `x ∈ D` or `x ∈ E`.

`hcr ν` has type `CurlReads W (shiftBack x ν) ν μ ∧ CurlReads W x ν μ`. `CurlReads` is four `CubeBond`s (`lean/src/ZR2A.lean`). `∧` is right-associative, and `CubeBond sites b` is `b.1 ∈ sites ∧ shift b.1 b.2 ∈ sites` (`lean/src/ZStatementP428.lean`). The projection `.2.2.1.1` of `CurlReads W x ν0 μ` is membership of `periodicLatticeShift x μ`, not of `x`. The base point `x` is `.2.1.1`.

So `regBody_glue`, as written, does not match the definitions it calls. `cover_cut`, `famTwoDom_union`, and `twodom_union_instance_inequality` call that lemma. This is a reading defect, not a failed build: nothing was compiled. The box, cap, mixed, total, and `target8TwoDom` texts do not call `regBody_glue`. Their being free of this projection does not make them theorems of the tree.

`plain_cut_fails` (`TD6.lean`) is the explicit slab example the glue is meant to repair. On `S = slabT` at radius \(R\) and `Sc = slabT` at radius \(Rb > R\), it asserts an `IsClassUnion` of `Sc` at index \(0\) whose intersection with `S.Om 0` is nonempty, contained in `S.Om 1`, and not a `UnionAt` of `S` at index \(0\). It does not say the cut fails to be a class union at every index. `READING.md`'s appeal to `path_exists_T` for connected cubes is not a declaration in `TD1`–`TD7`.

## What the witness types say

`twodom_instance_inequality` is existential. For every \(c \ge 10\), every large \(m\), every \(R \ge \max(R_1, 1)\), and every \(Rb > R\), there exist \(k \ge 2\), a torus, towers, \(\Lambda\), a link field, and one positive-energy test field such that:

- `S` is `AdmSplitNB` at level-0 radius \(R\) with higher radii \(Rb\);
- `Sc` is `Admissible` at radius \(Rb\) (the radial \(\le Rb\, M\) slab, not an arbitrary superset);
- `Om 0` of `S` is a proper subset of `Om 0` of `Sc`, and the two towers agree for \(j \ge 1\);
- `U` is in `ClassCoupled` at factor \(c\) on `Sc` (boxes, one factor), with a plaquette in `S.Om 2` not equal to \(1\), and `U` not pure gauge;
- `LambdaOK2` is at radius \(Rb\), the larger one, not at \(R\);
- `WellDefG` and the inequality hold for that test field on `S`.

The proof picks \(k = 2\) and the nested radial slabs of lane `nonvac_c`. It does not inhabit a non-radial operator domain. It does not quantify over every `U`, every \(k\), or every pair of towers.

`twodom_union_instance_inequality` is the same slabs, plus `ClassCoupledP unionClass` on `famF c` and a cut-missing cube. `famF c` is every triple of factor \(c\), not a printed finite family. `classCoupledU_of_M1` gets that hypothesis from the global M1 regime (one gauge and one \(A\), every union of factor \(c\) regular). The inequality step calls `famTwoDom_union`, so it sits on the broken glue.

## What must not be written in the paper

- That any declaration in `extras/two_domain/` is a theorem of this repository, or that its axioms are `propext`, `Classical.choice`, and `Quot.sound`. No axiom print was run here.
- That prosecution or a Sol review adopted the lane. Neither exists. Do not replace the sentence that the literal two-domain transfer is not proved.
- That pp. 394 and 396 force operators on a thin domain and the class on the \(\le RM\) domain. One letter is used twice. The one-domain reading remains the reading the paper has adopted.
- That `target8TwoDom` is `P428Target8` or `Target8Layer`. It drops `WellDefG`, uses `AdmNoBase`, and reads factor \(12\) from a second tower. `SidePow6` is inherited.
- That "the same constants" means numerical equality with the print, with each other, or with a computed \(m_1, a_0, \gamma_0\). The proofs reuse the existential package of whichever one-domain theorem they call. The union package is not the thin-layer union package: its \(R_1\) is forced up to at least \(4\).
- That the union form holds for \(R_0 < 4\), or that any form holds below its \(R_1\), or that \(R_1\) has a value, or that \(4\) is sharp. No negative theorem and no mutant log is in this package.
- That a disconnected union cuts to a class union of the operator domain. `plain_cut_fails` is the text that says the opposite, at index \(0\), and it is uncompiled. Do not say the cut fails at every index.
- That this lane proves the meeting clause for boxes, or that `famTwoDom_box` is the cap theorem. The hypothesis is the box class on `Sc`. The proof route is the cap on `S`. A box of `Sc` may leave `S.Om 0`. The paper's existing disclosure stands: the cap theorem is not the literal two-domain class.
- That `famTwoDom_union` is finished proof text. `regBody_glue` projects `CurlReads` onto the wrong site.
- That `Sc` may differ from `S` at some level \(j \ge 1\), or that `S.Om 0` need not be contained in `Sc.Om 0`. Those are not the statements.
- That the headlines assume the \(\le RM\) shape. They do not. Only the witness builds that shape, and only as one radial slab inside another.
- That the witness is non-vacuity for every configuration, every \(k\), a non-radial layer, or a general union family. `famF` is the M1 regime.
- That a union-class cap (level-0 unions allowed to leave `Om 0`) is proved. It is not stated.
- That `CubeBond` is Balaban's bond convention. It is both endpoints. CMP 96 uses at least one. Pre-existing, not changed here.
- That the distance is the print's non-periodic distance, that the dimension is not \(3\), that the gauge group is not \(SU(2)\), or that \(\eta\) is not \(\ell^{-k}\). All inherited. The formal \(a_0\) is not the source's \(a_1\).
- That regularity is required only on the operator domain. The class hypothesis constrains \(U\) on cubes of the larger domain, including the shell `Sc.Om 0 \ S.Om 0`. The quadratic form is the one `gparams` builds from `S`.
- That "no condition on the family remains." Factors \(\ge 10\) and the smallness bound remain.
- `SCOPE.md`'s "CLOSED", `STATEMENT.md`'s "kernel-checked", and the draft paper sentence in `STATEMENT.md`. Those are the lane's own summary. The paper does not copy a lane's summary sentence.

## Obstruction

The review is finished. The obstruction to any stronger claim is: these modules are outside the build, their recorded gate is not in the package, and the union transfer's glue step does not match `CurlReads`. Repairing that projection, rebuilding, and both gates are future work. They are not done here.
