# Independent verification — S-2 non-vacuity, round 1 refutation

**Verdict: `closes-goal`, for `AdalyFormal.AHP.Round2.S2Nonvacuity.GoalNeg2` only.**

Checks (1)–(4) pass. This is **partial progress on the item**, not closure of the four-bond non-vacuity question, S-2 printed-class fidelity, or the printed coercivity lemma. The distinction is required by `pin/PIN.md:7–11`.

## 1. Fresh compilation of the unedited attempt

Executed independently, serially, using the ready frozen oleans:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/r1-refute/Attempt.lean > /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/r1-refute/Attempt.verify.log 2>&1
code=$?
echo "$code" > /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/r1-refute/Attempt.verify.exit
```

- [Fresh compiler log](Attempt.verify.log); [exit record](Attempt.verify.exit): **0**.
- No warnings or errors in the fresh log.
- Attempt SHA-256: `c4a1d4d0614dd1fcf700219fbd12fd03349a4b7f600dea0da15d678dfb553ccd`.
- Pin SHA-256: `826f93c754d1c78a13e8ee7a832fc3041b36cd9cbe4628cde3a7475d752909f9`.
- The attempt was not edited. No build, update, reproduction script, commit, push, or removal was run.

## 2. Exact type and definition identity

`Attempt.lean:519` declares:

```lean
theorem goalNeg2_proved : GoalNeg2 := by
```

The fresh compiler prints:

```text
AdalyFormal.AHP.Round2.S2Nonvacuity.goalNeg2_proved : GoalNeg2
```

The file's sole namespace is `AdalyFormal.AHP.Round2.S2Nonvacuity`; `GoalNeg2` is the local definition at line 149, identical to `pin/Statement.lean:161`. There are no extra parameters, hypotheses, local notation changes, or alternate namespace definitions. In particular the ambient extent variable is not an extra theorem parameter: the goal itself quantifies `Lu` and uses `scaleUp ell k Lu`.

Independently compared **all 14 pinned definitions**, declaration by declaration, not just names or signatures. All are character-identical (excluding separator whitespace after each declaration), which is stronger than the requested whitespace-normalized equality:

| Definition | Pin line | Attempt line |
|---|---:|---:|
| `TouchBond` | 41 | 29 |
| `CoversPlaqFour` | 44 | 32 |
| `plaqCorner` | 49 | 37 |
| `CoversPlaqCorner` | 54 | 42 |
| `CurlReadsTouch` | 59 | 47 |
| `PerCubeRegularTouch` | 64 | 52 |
| `ClassCoupledFour` | 84 | 72 |
| `ClassCoupledCorner` | 87 | 75 |
| `ProperFourAt` | 98 | 86 |
| `ProperCornerAt` | 113 | 101 |
| `GoalPos1` | 133 | 121 |
| `GoalNeg1` | 142 | 130 |
| `GoalPos2` | 153 | 141 |
| `GoalNeg2` | 161 | 149 |

The additional four `cornerA`–`cornerD` definitions are not in the pin; they are exact copies of the Stage-B definitions, not substitutions for pinned objects. Independently checked 26 overlapping declarations against `AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean`, including those four definitions and all the copied product-box helpers. Also checked `shift_iter` and `forall_of_shift` against frozen `lean/src/CvN4.lean:36–61`: both exact.

The only imports are frozen `ZT5A` and `ZR8Class`; neither is an AHP import. `siteBox`, `DescribedAt`, `IsClassCube`, `Admissible`, `TorusOK`, and the operators used by the class are the imported frozen declarations, not stand-ins. In particular, `lean/src/ZStatementP428.lean:122–143` really supplies the product-box and two-stratum clauses used in the argument.

Audit reproducibility: [independent checker](verify_independent.py), [results](Attempt.verify.audit.json), [checker exit](Attempt.verify.audit.exit), **0**. This checker reads the fresh verification log, not the builder's log or `AUDIT.json`.

## 3. Axioms and forbidden constructs

All **48** requested dependency records are present in the fresh log, covering all **45 local declarations** and the three printed frozen helpers. Multiline dependency lists were parsed as complete records. Every list is a subset of `propext`, `Classical.choice`, `Quot.sound`; two declarations have no axioms.

Main record:

```text
'AdalyFormal.AHP.Round2.S2Nonvacuity.goalNeg2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Whole-source token scan, including comments, found **zero** occurrences of the forbidden tokens `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`. The allowed diagnostic command `#print axioms` is not an `axiom` declaration. Source inspection found no substitute elaborator, macro, or runtime escape mechanism.

## 4. What the proof actually establishes

- `touchCover_all_corners`, line 371: a product box touching every boundary edge of a square contains every corner. A vertex cover contains an opposite pair; coordinate-product membership fills the other pair.
- `class_sites_subset_om0`, line 413: an actual frozen class cube lies inside the base domain by its two-stratum clause and tower monotonicity.
- `exists_exit`, line 454: a proper nonempty subset of the finite periodic torus has an exit bond, using finite-torus connectivity.
- `explicit_exit_square`, line 468, and `proper_domain_uncovered`, line 488: a square at the inside endpoint of such a bond satisfies the corner antecedent but cannot be covered by any one contained class box.
- `corner_saturation`, line 506: admissibility plus `CoversPlaqCorner` therefore forces the base domain to be empty or the entire torus.
- `goalNeg2_proved`, line 519: specializes this stronger geometric fact to the exact pinned binders. `not_goalPos2`, line 524, excludes the positive corner-family pin.

This does not assume the sought saturation or a proper-domain class witness. The unused positivity, scale, torus, and regularity premises in the final specialization are harmless: the geometric theorem proves a stronger assertion. Numerical evidence is unnecessary to this acceptance; no numerical scan was rerun or treated as proof.

## 5. Faithfulness audit and remaining concerns

Read `HANDOFF.md`, `paper/OPEN_ITEMS.md` B, K–N, R and S, `AHP/fidelity/STAGE_B_RESULTS.md`, the S-2 specification/attack/decision and Lean comparison, `pin/PIN.md`, the pin and attempt, and the builder's notes. Read the supplied adjudicated transcriptions of CMP99 pp.393, 396, 408, 427, 428. Independently rendered and visually read those five printed pages from `sources/compute/balaban_su2_papers/balaban_CMP99_1985_propagators_backgroundfield.pdf`; also read printed pp.394 and 409 for the thinner-layer and factor-12 disclosures. Review renders are retained in [verify-pages/](verify-pages/).

No mismatch was found between **this proof** and **GoalNeg2**. The following limits prevent interpreting that exact match as complete item or source fidelity:

1. **Wrong branch for complete item closure.** GoalNeg2 concerns `ClassCoupledCorner`, not `ClassCoupledFour`. The pin expressly says only the four-bond branch settles this round's item. Nothing in this attempt proves `GoalPos1` or `GoalNeg1`. The corner-to-four inclusion goes in the wrong direction for transferring corner saturation to the larger four-bond class.
2. **Additional, load-bearing coverage requirement.** Printed p.396 imposes per-cube regularity (3.35)–(3.36), not the assertion that every plaquette with one corner in the base domain has all four boundary edges touching one contained class cube. That extra assertion is exactly `CoversPlaqCorner` (`Statement.lean:54`, `Attempt.lean:42`), and it causes saturation. Merely identifying a domain's plaquettes by one-corner incidence does not supply this one-cube witness. Saturation here is not a theorem that the printed class is empty on proper domains.
3. **Frozen box family and fixed factor.** The pin keeps aligned periodic product boxes, a unique index, two-stratum containment, and factor 12. The p.396 class is described as cubes assembled from big blocks with a size parameter \(O(1)\ge10\); p.409 motivates choosing 12 but does not prove that the frozen family captures every intended cube convention. Product structure and containment in the base domain are essential to this proof. Arbitrary non-box unions, shell cubes allowed to leave the domain, and the p.408 changed level-zero family are not established by it.
4. **Base-domain and lattice reading retained.** The pin uses the exact p.396 collar selection through frozen `Admissible`, the finite 3D periodic torus, periodic \(\ell^1\) distance, aligned half-open blocking, and empty padding. The printed p.393 nested-domain discussion and p.394 thinner-layer option do not uniquely identify all these conventions. This is neither the arbitrary thinner-layer class nor a two-domain transfer. The stronger geometric lemma uses only the nesting/box portion, but the pinned source identification remains limited.
5. **Scale scope differs from printed conventions.** The pin permits every natural radius and every blocking factor \(\ell\ge2\), with \(M=\ell^m\). P.408 says R and M are powers of L; the supplied S-4 reading records odd L greater than 11 elsewhere. The universal negative theorem includes those numerical subranges, so this is not a loophole in the formal refutation, but it is not a fresh source-correspondence proof. The p.408 third-enlargement clause is not encoded as an additional class condition.
6. **Regularity boundary and norm conventions remain choices.** Touching bonds, all-stencil-read guards for derivative bounds, global representatives of per-cube gauge/field data, and the full Frobenius norm are retained. Their equality with a unique printed boundary prescription and printed norm is not proved here. These regularity predicates are present in the exact pin but unused by the saturation argument.
7. **Negative alternative is stronger than an exact logical negation.** GoalNeg2 is universal geometric saturation, without Lambda, caps, or nonzero test-field premises; it is not defined as `¬ GoalPos2`. The copied implication and `not_goalPos2` correctly bridge the two. This strengthens the no-go result for the formal corner class; it does not independently validate the positive pin's Lambda/support/axial/dropped-row reading of pp.427–428.
8. **No analytic or changed-operator statement.** P.428 asserts a positive lower bound for the actual constrained quadratic form. GoalNeg2 contains no quadratic form, inverse, coercivity constant, or operator comparison. It cannot refute that printed claim, settle S-1's consistently touching operators, or settle S-3's eta/tau-star normalization. It only rules out proper nonempty domains for the specified additional corner class.
9. **Remaining source-access limitation.** No local CMP102 p.277 image or PDF was found. Its endpoint/corner convention was read through `OPEN_ITEMS.md` S-1 and the pin's disclosure, not independently reverified from that printed page. Nothing in the formal acceptance depends on claiming otherwise.

**Safe disposition:** exact pinned corner saturation verified; corner proper-domain non-vacuity refuted. Four-bond non-vacuity and identification with the printed class remain open in this attempt. `closes-goal` must not be promoted to `closed-fails` for the entire item.

All verification writes are confined to `AHP/round2/s2-nonvacuity/r1-refute/`. Protected files, the pin, and the attempt source were left unchanged.
