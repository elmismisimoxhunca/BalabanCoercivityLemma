# two-domain — review card

Review only. Sources read: `extras/two_domain/LOG.md`, `READING.md`, `SCOPE.md`, `STATEMENT.md`, `src/TD1.lean`–`TD7.lean`, and the frozen definitions those texts call (`AdmSplitNB`, `AdmNoBase`, `InstAtWD`, `InstIneq`, `ClassCoupled`, `ClassCoupledP`, `ClassCoupledCap`, `ClassCoupledΦ`, `UnionAt`, `IsClassUnion`, `RegBodyH`, `CubeBond`, `CurlReads`, `DescribedAt0`, `DescribedAtAlt`, `regBody_mono_sites`). Nothing was compiled. Nothing was copied into `lean/src`. Full note: [two-domain.md](/home/sebastian/BalabanCoercivityLemma/AHP/notes/two-domain.md).

Status of this package: the seven Lean files are present; `gate_record/` is not. `LOG.md`'s census, mutant count, and byte-identical builds are not measurements here. No prosecution. No Sol review. `compiled` is false. Not a theorem of the project tree.

## Headlines, as the types quantify

`Sc` is universal, after `S`. Only `Sc.Om j = S.Om j` for \(j \ge 1\) and `S.Om 0 ⊆ Sc.Om 0`. No admissibility of `Sc` in the six headlines.

- `famTwoDom_union` — `TwoDomFamP unionClass`. Class `ClassCoupledP unionClass` on `Sc`. Conclusion `InstAtWD` on `S` (`WellDefG` and `InstIneq`). The proof's \(R_1\) is `max` of `famTorusLayer_union`'s \(R_1\) and \(4\). The \(4\) is not a binder of the type.
- `famTwoDom_box` — `TwoDomFamP boxClass`. Boxes on `Sc`. Proof calls `famTorusLayerCap` on `S`, not the union glue. Threshold is the cap's \(R_1\).
- `famTwoDom_cap` — `TwoDomCapP`. `ClassCoupledCap` on `Sc`, pushed to `S` by monotonicity (`classCoupledCap_of_two`), then `famTorusLayerCap`.
- `mixedTwoDom` — `ClassCoupledΦ` on `Sc`, reduced to `famTwoDom_box`.
- `totalTwoDom` — `ClassCoupled` at one \(c \ge 10\) on `Sc`, the singleton of the mixed form.
- `target8TwoDom` — factor \(12\), `AdmNoBase` at one radius, `LambdaOK2` at that radius, conclusion `InstIneq` only. Not `P428Target8`. Not `Target8Layer`. `SidePow6` is inherited from `target8Layer`.
- `oneDom_of_twoDom`, `oneDomCap_of_twoDom`, `totalLayer_of_twoDom` — set `Sc := S`. The union specialisation keeps the larger threshold. It does not replace the thin-layer union theorem.
- `twodom_instance_inequality` — existential nested radial slabs, \(k = 2\), \(Rb > R \ge \max(R_1, 1)\), box class `ClassCoupled` on the larger slab, proper inclusion of level-0 domains, one positive-energy test field, `WellDefG` and the inequality on the thinner slab. `LambdaOK2` uses \(Rb\). Not every \(U\), not every \(k\), not a non-radial layer.
- `twodom_union_instance_inequality` — same slabs, plus `ClassCoupledP unionClass` on `famF c` (every triple of factor \(c\); M1 regime) and a cut-missing cube. Calls `famTwoDom_union`.
- `plain_cut_fails` — on those slabs, an index-\(0\) `IsClassUnion` of the larger tower whose cut to the thinner `Om 0` is nonempty, sits in `Om 1`, and is not `UnionAt` at index \(0\). Not a claim about every index.

## Reading defect

`TD1.regBody_glue` cases `(hcr ν0 hν0).2.2.1.1` and passes it to `glue_side` as membership of the `ddA` base point `x`.

`CurlReads` (`lean/src/ZR2A.lean`) is four right-associated `CubeBond`s. `CubeBond` (`lean/src/ZStatementP428.lean`) projects `.1` to the bond's start. That projection is `periodicLatticeShift x μ ∈ W`, not `x ∈ W`. The base point is `(hcr ν0 hν0).2.1.1`.

`cover_cut`, `famTwoDom_union`, and `twodom_union_instance_inequality` depend on this lemma. Box, cap, mixed, total, and `target8TwoDom` do not. Uncompiled either way.

`TD7`'s comment says the census covers `THL1`–`THL8`. The script counts modules named `TD*`, excluding `TD7`.

## Must not be written in the paper

1. Any `extras/two_domain` declaration is a theorem of this tree, or prints only `propext`, `Classical.choice`, `Quot.sound`.
2. Prosecution or Sol adopted the lane. `OPEN_ITEMS.md` R-a2 and the thin-layer paragraph (`thin-two-domain`) still say the literal transfer is not proved.
3. The print forces this reading. One \(\Omega_0\) is used on p. 394 and on p. 396. The adopted reading remains one domain.
4. `target8TwoDom` is the frozen headline or `Target8Layer`. It has no `WellDefG` conjunct.
5. "Same constants" as equal numbers. Union's \(R_1\) is at least \(4\) and at least the thin-layer union threshold; the others inherit the cap or total package they call.
6. Anything below that \(R_1\), an explicit \(R_1\), or sharpness of \(4\). No mutant log is in the package.
7. The plain cut of a disconnected union is a class union of the operator domain. Do not promote `plain_cut_fails` to a theorem, and do not strengthen it to every index.
8. This lane proves the box meeting clause, or that the box headline is the cap theorem. Hypothesis: boxes on `Sc`. Route: cap on `S`. A box of `Sc` may leave `S.Om 0`. The cap theorem is still not the literal two-domain class.
9. `famTwoDom_union` is finished proof text, while `regBody_glue` mismatches `CurlReads`.
10. Higher levels may differ, or the operator domain need not sit inside the class domain.
11. The headlines assume a radial \(\le RM\) class domain. Only the witness builds one radial slab inside another.
12. The witness covers every configuration, every \(k\), a non-radial layer, or a general union family. `famF` is the M1 regime.
13. A union-class cap is proved. It is not stated.
14. `CubeBond` matches CMP 96 (both endpoints here; at least one there). Distance is periodic \(\ell^1\). Dimension \(3\), \(SU(2)\), \(\eta = \ell^{-k}\), formal \(a_0\) separate from the source \(a_1\). All inherited.
15. Regularity is only required on the operator domain. The class hypothesis sees the shell. The form is `gparams` of `S`.
16. "No condition on the family remains." Factors \(\ge 10\) and smallness remain.
17. `SCOPE.md`'s "CLOSED", `STATEMENT.md`'s "kernel-checked", its draft paper sentence, or the statement-sheet row that already names these files. That row is not a build claim.
