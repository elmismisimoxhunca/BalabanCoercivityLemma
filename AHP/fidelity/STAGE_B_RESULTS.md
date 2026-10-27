# Stage B results

## Summary and evidence

All ten queued files passed independent recompilation: **39 contracted declarations accepted, none failed or missing**, plus three separately checked sheet proof helpers. Acceptance is limited to the comparisons and re-exports authorized by [STAGE_B.md](STAGE_B.md) and the linked decisions. It does **not** close S-1, substantive S-2 statement fidelity, S-3, or the guarded headline.

The coordinator confirmed the fresh 2026-10-21 `REPRODUCE.sh` pass: lake build exit 0, 2762 modules, expected axiom output unchanged, and oleans ready. This report consolidates the supplied builder/verifier results. The report pass read all ten independent `.verify.log`, `.verify.exit`, and `.VERIFY.md` records and checked that each current Lean source SHA-256 matches its verifier's recorded hash. It did not run another compilation, `lake build`, or `REPRODUCE.sh`. Exact-signature and definition checks are recorded in the independent verification reports; none reported a mismatch, forbidden construct, or missing axiom print.

For each file below, its sibling `.verify.log` and `.verify.exit` contain the independent recompilation evidence; `.VERIFY.md` records the command and contract audit. Original builder `.log` and `.exit` files remain separate. Every one of the 42 printed dependency records contains only permitted axioms. `CollarNonStrict.lean` has three unused-simp-argument warnings; `LambdaScale.lean` has one tactic-style warning. These are not compilation failures.

Only this report was written by this consolidation pass. The protected statement sheet, frozen Lean tree, Lake configuration, and other files were not edited. Pre-existing workspace changes were left untouched.

## One row per queued entry

Paths below are relative to `AHP/fidelity/`. Declaration names are shortened by these exact namespaces: coverage declarations are global; S-1 uses `Fidelity.S1`; S-2 uses `AdalyFormal.AHP.FidelS2Inclusion`; S-3 uses `AdalyFormal.AHP.FidelS3Normalisation`; all six sheet entries use `AdalyFormal.Fidelity.SheetVariants`.

In the axiom column, **standard three** means exactly `propext`, `Classical.choice`, `Quot.sound`; **two** means exactly `propext`, `Quot.sound`.

| Entry / file | Recompiled exit code | Accepted declarations | Failed or missing declarations | Axiom summary | Verdict |
|---|---:|---|---|---|---|
| coverage-row — [coverage-row/lean/CoverageRow.lean](coverage-row/lean/CoverageRow.lean) | 0 | `coverage_row_fails`; `coverage_row_both`; `coverage_row_ell2` | None | Standard three for all 3 | Accept existing-result re-exports only |
| s3-normalisation — [s3-normalisation/lean/JetBoundaryComparison.lean](s3-normalisation/lean/JetBoundaryComparison.lean) | 0 | `raw_level_zero`; `linear_level_zero`; `plainH_eq_uniformBody_at_depth_one` | None | Standard three for all 3 | Accept structural jet comparisons only |
| s1-touching — [s1-touching/lean/ShellComparison.lean](s1-touching/lean/ShellComparison.lean) | 0 | `cubeBond_readBond`; `perCubeRegularShell_toFrozen`; `classCoupledShell_toFrozen`; `classCoupledShell_one`; `shell_slab_nonvacuous`; `readBond_not_touchBond_slab6`; `no_plaqIn_eq_plaqCorner_slab6` | None | Standard three for all 7 | Accept shell comparisons, flat hypothesis-family witness, and geometric separators only |
| s2-inclusion — [s2-inclusion/lean/ClassInclusion.lean](s2-inclusion/lean/ClassInclusion.lean) | 0 | `touchCover_cubeBond`; `CoversPlaqFour.toFrozen`; `CoversPlaqCorner.toFour`; `PerCubeRegularTouch.toFrozen`; `ClassCoupledFour.toFrozen`; `ClassCoupledCorner.toFour`; `ClassCoupledCorner.toFrozen`; `targetFour_of_frozen`; `targetCorner_of_four`; `targetCorner_of_frozen` | None | Standard three for all 10 | Accept conditional class/headline comparisons only; non-vacuity hold remains |
| sheet-q2b — [sheet-variants/lean/CollarNonStrict.lean](sheet-variants/lean/CollarNonStrict.lean) | 0 | `admissible_imp_nonstrict`; `admissibleNonStrict_k1_iff`; `collar_separator`; helper `pdist_L8` | None | Standard three for all 4 | Accept predicate comparisons and geometry-only separator |
| sheet-q3 — [sheet-variants/lean/ReadingB.lean](sheet-variants/lean/ReadingB.lean) | 0 | `readingB_of_layer` | None | Standard three | Accept conditional restriction only |
| sheet-q4 — [sheet-variants/lean/LambdaScale.lean](sheet-variants/lean/LambdaScale.lean) | 0 | `unitEmb_val`; `pdist_emb_scales`; `lambda_collar_scale_iff`; `headline_fine_side_ge16`; helpers `scaleUp_length`, `pcd_scale` | None | Two for `unitEmb_val` and both helpers; standard three for the other 3 | Accept coordinate, distance, collar-atom, and fine-side comparisons only |
| sheet-q6a — [sheet-variants/lean/GlobalGauge.lean](sheet-variants/lean/GlobalGauge.lean) | 0 | `global_imp_perCube`; `globalClass_imp_frozenClass`; `global_flat` | None | Standard three for all 3 | Accept inclusions and flat regularity only |
| sheet-q12 — [sheet-variants/lean/NormHS.lean](sheet-variants/lean/NormHS.lean) | 0 | `bondEnergyHS_eq_two`; `instIneqHS_iff`; `target_iff_hs` | None | Standard three for all 3 | Accept left-hand norm re-expression only |
| sheet-q13 — [sheet-variants/lean/QuantifierOrder.lean](sheet-variants/lean/QuantifierOrder.lean) | 0 | `total_imp_frozen`; `threshold_order_toy` | None | Standard three for `total_imp_frozen`; two for `threshold_order_toy` | Accept existing implication and abstract quantifier example only |

## Audit-item dispositions

### S-1: touching bonds and plaquettes — still open

Under [s1-touching/DECISION.md](s1-touching/DECISION.md), Lean now proves that frozen cube bonds are read-bonds, shell regularity implies frozen regularity, and the shell class implies the frozen class with coverage unchanged. The regularity transfer includes pointwise, difference, and curl guards.

The flat configuration belongs to the shell class under the specified positive parameters and coverage premise. More substantially, `shell_slab_nonvacuous` supplies the complete depth-two slab conjunction for positive even M, R at least 18, and every positive cap: torus compatibility, admissibility, Lambda compatibility, proper nonempty base domain, and a positive capped smallness parameter with flat shell membership. Coverage and proper-domain geometry are proved, not additional assumptions. This is a flat hypothesis-family witness, not a coercivity theorem or proof of non-flat richness.

The side-six example proves that a read-bond can have neither endpoint in the slab, and that no site set has its all-corners-inside plaquette selector equal to the slab's one-corner selector. Thus the shell is stronger than the endpoint convention. Selector nonrepresentability rules out that selector-identification route, not every possible identity or inequality between forms.

**Still open:** the fully consistent endpoint/corner/coverage reading of S-1, the repaired shell coercivity inequality, and analytic comparisons for changed corner operators. No refutation of the actual gauge-fixed headline was proved. Statement-sheet rows 5 and 7 remain open; the sheet was not edited.

### S-2: class inclusion — conditional comparisons proved; substantive acceptance held

Under [s2-inclusion/DECISION.md](s2-inclusion/DECISION.md), Lean proves the supporting product-box coverage and regularity implications, then the chain from the corner class to the four-touch-bond class to the frozen class. It also proves the conditional headline chain from `P428Target8` to `P428Target8Four` to `P428Target8Corner`, including the direct composite implication.

The variants retain the frozen class cubes, site coverage, factor 12, Lambda predicate, smallness and quantifier order. Their conclusion remains frozen `InstIneq`, with the frozen `plaqIn` operators. These results are not changed-operator theorems.

**Still open:** identification with the printed class and independent proper nonempty admissible-domain inhabitation of the touching classes, including actual factor-12 coverage, positive parameters, Lambda, and a nontrivial admissible test-field regime. No reverse or strict inclusion, shell-class inclusion, or universal empty/whole-torus saturation theorem is certified here. The S-1 flat shell witness does not silently discharge these different class obligations. S-2 statement fidelity remains open.

### Coverage row — existing formal result confirmed; sheet integration not performed

Under [coverage-row/DECISION.md](coverage-row/DECISION.md), the three checked re-exports establish:

- For every natural cube factor c at least 10, every blocking factor ell at least 2, and every positive real a, `FailsAtEll c ell hell a`: the full coverage-free granting-existence threshold body fails. The negative branch includes the actual `WellDefG` guard, not a junk inverse-value shortcut.
- Keeping both site and plaquette coverage gives `CovAssume.P428Target8NCWDHcov c` for every c at least 10, by the existing Total implication.
- At ell equal to 2, for every such c and positive a, the constant-family both-coverage body holds while its sites-only body fails.

This confirms the already-settled B1 result and supports the proposed stale-row correction in [coverage-row/ROW6.md](coverage-row/ROW6.md). It is not a new analytic argument or invertibility result.

**Still open or outside scope:** whether the printed p.396 sentence supplies both coverage clauses; cases with c below 10; other sites-only scale cells. The ell-equal-to-2 result is not an unqualified necessity claim at every scale. Integrating ROW6 into the protected statement sheet was not authorized and remains undone.

### S-3: eta/tau-star normalisation — structural comparisons proved; fidelity still open

Under [s3-normalisation/DECISION.md](s3-normalisation/DECISION.md), Lean proves that the actual level-zero raw second jet vanishes and the level-zero linear jet is the identity. It proves the exact plainH/uniformBody scalar-action equality at levels zero and one, with no extra positivity or inverse hypotheses. This invalidates treating a nonzero arbitrary level-zero second jet as a realization of these genuine operators.

**Still open:** the full printed-unit dictionary for Q, adjoints and pairings, H, the second jets, J, and the top-level embedding; comparison with the actual mass subtraction, nonlinear J term, and bond energy; and the compression/inversion issue. No full Schur-complement identity or printed-normalisation counterexample is accepted. The abstract matrix `no_scalar_*` proposals are not accepted fidelity targets. Any new genuine lower-level-jet counterexample needs actual operator/background realization (at depth at least two for a nonzero lower-level second jet), or a comparison on the actual admissible test subspace. Q12's norm result below does not close S-3.

### Statement-sheet questions — six formal comparisons accepted, reading limits retained

The formal scope follows [sheet-variants/DECISION.md](sheet-variants/DECISION.md):

- **Q2(b):** Lean proves strict admissibility implies non-strict admissibility, equivalence at depth one, and the exact non-strict-but-not-strict collar separator. The separator has M equal to 1 and whole-torus base domain and is outside the headline regime. It proves neither non-strict coercivity nor its failure; the print's strict condition is not replaced.
- **Q3:** Lean proves `Target8Layer` implies the specified reading-B target by restriction using the tower predicate's first conjunct, with the same class, operators, and one radius. Proper in-regime covered reading-B instances with a nonzero admissible test field remain unprovided. Intended source meaning of the base set remains a reading question, not an unconditional fidelity conclusion.
- **Q4:** For positive scaling, Lean proves the explicit modulo map's coordinate identity, periodic-distance scaling on embedded unit-site pairs for arbitrary rectangular extents, and equivalence of the strict collar atoms. Actual torus compatibility with ell and depth at least two forces every fine side to be at least 16. This does not identify the full fine complement with an embedded unit complement or decide the printed common-radius convention. No depth-at-least-two headline instance fits under a fine-side-eight numerical cap.
- **Q6(a):** Lean proves global regularity implies per-cube regularity, global coupled-class membership implies frozen coupled-class membership, and the flat field is globally regular under all five positivity assumptions. The flat witness uses gauge one and matrix field zero. It supplies neither coverage nor a nonzero admissible test field. Strict inclusion, a global-gauge analytic headline, and identification of the global variant with the printed per-cube convention are not established.
- **Q12:** Lean proves full Frobenius bond energy equals twice the frozen energy, the instance equivalence with the Frobenius constant divided by two, and the headline equivalence through unchanged binders. Only the left-hand norm changes: the form, operators, a, and smallness parameter are unchanged. This is not a class-bound norm-factor comparison or an eta/tau-star normalisation result.
- **Q13:** Lean re-exports Total's implication to the frozen headline and proves an abstract unbounded-natural-number separation between a radius threshold chosen after m and one chosen uniformly before m. It does not prove non-implication between the actual closed coercivity propositions. Total also chooses thresholds/constants earlier, quantifies all cube factors at least 10 rather than just 12, and includes well-definedness; those distinctions remain. Intended source uniformity is reading-only.

**No duplicate new targets:** Q1/Q2(a) retain existing conventions and the reading-A bridge; Q5 retains existing factor/family/union results. Their source acceptability remains reading-only. Q6(b), Q7, and Q9 stay with the other fidelity targets, without extra closure from this run.

**Q8/Q10/Q11 are reading-only**, under [sheet-reading/DECISION.md](sheet-reading/DECISION.md); they have no new Lean target in this run. The documented reading disposition is complete, but it is not an operator-identification proof:

- Q8 retains inverse/ingredient qualifications for the padded inverse and pulled-back form. Weight agreement at eta equal to one does not remove the extra printed eta factor at general eta or settle S-1/S-3.
- Q10 retains the abstract weighted-mass and inverse/constraint chain with existence qualifications. Stand-in matrices do not realize the lattice assembly. Compressing an inverse cannot be identified with inverting a compression without an additional theorem.
- Q11 treats touching support as a chosen reading. `Cop_id` preserves bonds outside the dropped set; `Cop_ker` addresses only selected `CRowIn` rows under H0 bijectivity, not all coarse rows. Singular fallback is not the printed inverse construction; toy maps are not genuine one-step jets. Joint and one-variable constrained solutions remain distinct. An omitted explicit support conjunct alone does not prove a support mismatch; the actual level-zero constraints must be checked.

Outstanding citation repairs in the reading record, source-render confirmation, and concrete operator/support identifications remain outstanding. Small proper-domain examples do not certify all headline hypotheses or actual-background realization.

## Guarded target — not in this run

For the later authorized compilation and its limited acceptance, see [Guarded target (compiled after the main run)](#guarded-target-compiled-after-the-main-run).

## Bottom line

The queued implementation and independent verification work passed at its authorized scope: 39 required declarations and three checked helpers. The coverage-row correction has formal support but has not been integrated into the protected sheet. The sheet comparisons and qualified reading record are now documented. S-1, substantive S-2 acceptance, S-3, and the guarded headline remain open; successful compilation is not certification of the printed assertion.

## Guarded target (compiled after the main run)

The later [guarded/DECISION.md](guarded/DECISION.md) supplies the authorized contract and supersedes the stale NOT READY note in STAGE_B.md. The coordinator's fresh reproduction confirmation applies. This addition consolidates the supplied builder/verifier results and checks the on-disk [independent verification report](guarded/lean/UthCross.VERIFY.md), [recompilation log](guarded/lean/UthCross.verify.log), and [exit record](guarded/lean/UthCross.verify.exit). The current `UthCross.lean` SHA-256 matches the verifier's recorded `f206f691c8d56be9a6ba73c9c5992be3d34bc0ec67e076b96e99cb51f00fa63b`. The report records exact signatures, context and imports, with no mismatches or forbidden tokens. All three required axiom prints are present; the independent log has no warnings or errors. This report-only update ran no compilation, build, or reproduction command and changed no other file.

| Entry / file | Recompiled exit code | Accepted declarations | Failed or missing declarations | Axiom summary | Verdict |
|---|---:|---|---|---|---|
| 11 (guarded) — [guarded/lean/UthCross.lean](guarded/lean/UthCross.lean) | 0 | `AdalyFormal.FidelityGuarded.Ginv_lit_psd_at_zero`; `AdalyFormal.FidelityGuarded.Uth_hits_nonunit`; `AdalyFormal.FidelityGuarded.Uth_singular_is_not_a_split` | None | Exactly `propext`, `Classical.choice`, `Quot.sound` for each of the 3; no missing prints or nonstandard axioms | Accept: flat-path comparison audited; item 5 remains open |

### What the guarded declarations prove — and do not prove

- `Ginv_lit_psd_at_zero` proves positive semidefiniteness of the actual all-plaquette literal `Ginv` at the flat starting point, for positive blocking factor and nonnegative mass parameter. It wraps existing flat positivity, not a newly discovered missing analytic step.
- `Uth_hits_nonunit` proves an actual literal non-unit crossing with full `ClassCoupled` membership for every \(m\ge1\), \(R\ge18\), and \(\alpha_0>0\), on the specified slab family with \(\ell=k=2\), \(M=2^m\), factor 12, and \(a=1\). The angle satisfies \(0\le\theta<\pi\), not a strictly positive lower bound. The crossing explicitly **fails the guard**, so it is not a guarded counterexample. The declaration does not export PSD at the crossing or a first-singularity characterization.
- `Uth_singular_is_not_a_split` proves, under the exact admissibility and room hypotheses, that the actual local `Delta2` is zero, the all-plaquette literal `G1invS` equals the all-plaquette `Ginv`, and its unit condition is equivalent to that of `Ginv - Delta2` along the entire specified flat-interior path. No invertibility premise is assumed; equality therefore applies at singular points too. This is an actual-operator no-separation comparison on this path, not a general guarded-pencil identity.

**GuardPencilT and P428Target8SG remain open.** None of these declarations proves either proposition or its negation. Closure still needs a general guarded proof, or an actual in-class separation with a nonzero admissible test field and the necessary cofinal threshold quantifiers. Numerical compressions, indefinite directions, and a failed-guard crossing do not supply that. The general non-flat-interior class, all-inverse qualifications, and printed interpretation remain unresolved. The accepted disposition is exactly: **flat-path comparison audited; item 5 remains open**.

### Updated audit-item dispositions

The main-run dispositions above remain in force; the guarded addition does not enlarge their scope.

- **S-1 — proved in Lean:** frozen cube bonds are read-bonds; shell regularity (including difference and curl guards) and shell class membership imply their frozen counterparts with unchanged coverage; the positive-parameter covered flat shell witness and the complete proper nonempty depth-two slab hypothesis family exist at every positive cap; the side-six geometric examples separate read-bonds from endpoint-touching bonds and rule out representing the one-corner selector as `plaqIn` of any site set. **Still open:** the consistent printed endpoint/corner/coverage convention, shell coercivity, changed-corner-operator comparisons, and statement-sheet rows 5 and 7. Neither a non-flat-richness theorem nor a counterexample to the actual gauge-fixed headline is proved; selector nonrepresentability excludes only that identification route.
- **S-2 — proved in Lean:** product-box coverage and regularity comparisons, the corner-to-four-touch-to-frozen class chain, and the conditional frozen-to-four-touch-to-corner headline chain, including composites. The conclusion remains frozen `InstIneq` on `plaqIn`, with the contracted factor 12, Lambda, smallness and quantifier order. **Still open:** printed-class identification and independent proper nonempty admissible-domain touching-class witnesses with actual coverage, positive parameters, Lambda and a nontrivial admissible test-field regime. No reverse/strict inclusion, shell-class inclusion, changed-operator result, or universal saturation result is certified. Neither the S-1 shell witness nor the new guarded frozen-class crossing discharges these distinct obligations; substantive acceptance remains held.
- **Coverage row — proved in Lean:** the full coverage-free granting-existence threshold body fails for every \(c\ge10\), \(\ell\ge2\), \(a>0\), with the actual `WellDefG` guard; retaining both coverage clauses gives `P428Target8NCWDHcov c` for every \(c\ge10\); at \(\ell=2\), the constant-family both-coverage body holds while the sites-only body fails for those \(c,a\). These are checked re-exports of the already-settled B1 results. **Still open or outside scope:** the source meaning of the p.396 coverage sentence, \(c<10\), and other sites-only scale cells. The supported correction in `coverage-row/ROW6.md` has still not been integrated into the protected statement sheet. There is no new invertibility result or all-scale sites-only necessity theorem.
- **S-3 — proved in Lean:** the actual level-zero raw second jet is zero, the level-zero linear jet is the identity, and the exact plainH/uniformBody scalar actions agree for levels zero and one without extra positivity or inverse hypotheses. **Still open:** the complete printed-unit dictionary for Q, adjoints/pairings, H, second jets, J and the top embedding; the genuine mass-subtraction, nonlinear-J and bond-energy comparison; and compression versus inversion. Neither a full Schur-complement identity nor a printed-normalisation counterexample is proved. An arbitrary nonzero level-zero second jet is not a genuine realization; a nonzero lower-level proposal needs depth at least two with actual realization, or a comparison on the actual admissible test subspace. The guarded flat-path equality and Q12 do not close these gaps.
- **Sheet questions — proved in Lean:** Q2(b)'s strict-to-nonstrict implication, depth-one equivalence and out-of-regime geometry-only separator; Q3's conditional reading-B restriction with unchanged operators/class and one radius; Q4's positive-scale coordinate, rectangular periodic-distance and collar-atom identities on embedded site pairs, plus the fine-side lower bound 16 under actual depth-at-least-two torus hypotheses; Q6(a)'s global-to-per-cube/class implications and positive-parameter flat regularity; Q12's full-Frobenius energy factor two, instance equivalence with constant divided by two and unchanged-binder headline equivalence; Q13's Total implication and abstract unbounded-natural threshold-order separator. **Still open:** non-strict coercivity, proper covered in-regime reading-B instances with nonzero tests, identification of the entire fine complement/common-radius reading, strict global-class inclusion or a global-gauge analytic headline, class-bound norm scaling/S-3, and source uniformity. The Q6(a) witness supplies neither coverage nor nonzero tests; Q13 does not separate the actual closed coercivity propositions. Q1/Q2(a) and Q5 retain existing results with source acceptability reading-only; Q6(b), Q7 and Q9 receive no duplicate closure. Q8/Q10/Q11 remain qualified reading-only records with no new Lean targets: inverse/ingredient and general-eta qualifications, compression/inversion, actual support and level-zero constraints, selected `CRowIn` rows under H0 bijectivity, singular fallback, and joint versus one-variable solutions are not resolved by toy matrices or this guarded path. Citation repairs and independent source-render confirmation remain outstanding.

**Combined accounting:** eleven independently compiled files, **42 contracted declarations accepted, none failed or missing**, plus three checked sheet helpers (45 accepted printed dependency records in total). This closes the authorized compilation/comparison tasks only. It does not close S-1, substantive S-2 fidelity, S-3, GuardPencilT, P428Target8SG, or the remaining source-reading and sheet-integration obligations.
