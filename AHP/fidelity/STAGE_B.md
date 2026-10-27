# Stage B — ordered work list

## Authority and gate

This list is derived **only from the current `DECISION.md` files**, not from design JSON, SPEC proposals or attack recommendations. Exact signatures, definitions, binders and namespace opens in each linked decision are the implementation contract; the shorter descriptions below do not weaken them. The supplied workflow array has a null `sheet-variants` entry, but its on-disk decision exists and is included. `guarded/DECISION.md` is absent and that target is **not ready**.

Nothing listed here has been compiled by this consolidation pass. Do not begin until the coordinator confirms that the current `REPRODUCE.sh` run passed and its oleans are ready. A historical successful build in HANDOFF is not that confirmation. No Lean, Lake, reproduction command or numerical script was run in this pass.

For each ready file below:

1. Write or repair only that target's `AHP/fidelity/<id>/lean/` files. Keep the stated frozen imports and definitions. Do not edit `lean/`, the lakefile, paper, notes, expected outputs or extras. Keep unrelated/pre-existing drafts out of the import chain.
2. Append the listed `#print axioms` commands after the declarations (outside their namespace, using the qualified names shown). For `sheet-variants`, also print every new proof helper's axioms, as its decision requires.
3. From the existing `lean/` project, run the following **in Stage B only**, separately for each file, substituting the literal target/file names:

   ```sh
   cd /home/sebastian/BalabanCoercivityLemma/lean
   "$BB_CLI" heavy run -- lake env lean ../AHP/fidelity/<id>/lean/<File>.lean > ../AHP/fidelity/<id>/lean/<File>.log 2>&1
   rc=$?
   printf '%s\n' "$rc" > ../AHP/fidelity/<id>/lean/<File>.exit
   ```

   Preserve the command, complete output and exit status. Compilation must exit zero and every requested axiom print must be present. Only subsets of `propext`, `Classical.choice`, `Quot.sound` are acceptable, including the empty set. No placeholders, additional axioms, `sorryAx`, `native_decide` or unverified external computation. An imported declaration's print does not replace the requested local declaration's print. A failed target remains unfinished; do not silently drop it or narrow its statement.
4. Record acceptance only at the scope in its decision. Successful comparisons are not certification of the printed assertion, of changed operators, or of a nonempty admissible class.

## Ordered implementation queue

### 1. Coverage row — three existing-result re-exports

- **Decision:** [coverage-row/DECISION.md](coverage-row/DECISION.md), “Exact Stage-B declarations”; route `already-settled`.
- **File:** `AHP/fidelity/coverage-row/lean/CoverageRow.lean`.
- **Frozen imports:** `NuA3`, `CaT1`, `CaT2d`.
- **Declarations:** use the decision's exact global signatures and source applications:
  - `coverage_row_fails`: `FailsAtEll c ell hell a`, for every natural `c >= 10`, `ell >= 2`, and real `a > 0`; source `NcwdhFam.ncwdh_fails_ge_two`.
  - `coverage_row_both`: `CovAssume.P428Target8NCWDHcov c` for `c >= 10`; source `CovAssume.p428Target8NCWDHcov_of_total`.
  - `coverage_row_ell2`: the conjunction of the constant-family both-coverage body and negation of its sites-only body, at `ell = 2`, `c >= 10`, `a > 0`; source `CovAssume.covPlaq_separately_necessary_two`.
- **Expected outcome:** exact re-exports supporting the stale-row correction, not a new analytic argument. The negative branch includes the actual `WellDefG` guard. No claim about the printed sentence, `c < 10`, or other sites-only cells.
- **Axiom checks:**
  ```lean
  #print axioms coverage_row_fails
  #print axioms coverage_row_both
  #print axioms coverage_row_ell2
  ```
- **After acceptance:** retain [coverage-row/ROW6.md](coverage-row/ROW6.md) as the proposed correction. Integrating it into the protected statement sheet is not authorized here.

### 2. S-3 — actual jet boundary comparisons, not the matrix counterexample

- **Decision:** [s3-normalisation/DECISION.md](s3-normalisation/DECISION.md), “Exact Stage B targets”; route `lean-comparison`.
- **File:** `AHP/fidelity/s3-normalisation/lean/JetBoundaryComparison.lean`.
- **Frozen import:** `ZXR2Sector`.
- **Namespace:** `AdalyFormal.AHP.FidelS3Normalisation`.
- **Declarations:**
  - `raw_level_zero`: `C2rawB G U 0 A = 0` for the actual bond-field jets.
  - `linear_level_zero`: `QlinB G U 0 A = A`.
  - `plainH_eq_uniformBody_at_depth_one`: for `j <= 1`, the exact coefficient identity displayed in the decision, namely
    \[
    (\ell^{-1})^2\,C_{\mathrm{raw},j}
      =\ell^{-1}(\ell^j)^{-1}\,C_{\mathrm{raw},j}.
    \]
    Preserve its scalar-action Lean signature and its lack of extra positivity or inverse hypotheses.
- **Expected outcome:** verify the structural obstruction to the proposed nonzero level-zero second jet and compare two recipes at depth one. Not a full Schur-complement or units identity. Do **not** implement `NoScalar.lean` or `no_scalar_*` as accepted fidelity targets.
- **Axiom checks:**
  ```lean
  #print axioms AdalyFormal.AHP.FidelS3Normalisation.raw_level_zero
  #print axioms AdalyFormal.AHP.FidelS3Normalisation.linear_level_zero
  #print axioms AdalyFormal.AHP.FidelS3Normalisation.plainH_eq_uniformBody_at_depth_one
  ```

### 3. S-1 — shell comparisons and flat proper-domain non-vacuity

- **Decision:** [s1-touching/DECISION.md](s1-touching/DECISION.md), “Stage-B definitions and import contract” and seven exact signatures; route `lean-comparison`.
- **File:** `AHP/fidelity/s1-touching/lean/ShellComparison.lean` (filename assigned here within the decision's permitted directory).
- **Frozen imports:** `ZStatementP428`, `ZR2A`, `ZR6A`, `ZR2Ops2`, `AdalyFormal.Target.ClayStatement`, `D1Final`. The last supplies the slab-family scaffolding. Do not add separate `D1Lit`/`D1Path` raw-form deliverables.
- **Namespace:** `Fidelity.S1`.
- **Definitions:** copy `TouchBond`, `plaqCorner`, `ReadBond`, `CurlReadsRead`, `PerCubeRegularShell`, `ClassCoupledShell` as explicitly authorized by the decision; add its `L6 := fun _ => 5` and `slab6 := {x | (x 0).val < 2}`. Keep coverage, cube sites, admissibility and Lambda predicates frozen.
- **Declarations, in order:**
  1. `cubeBond_readBond`: every frozen cube bond is a read-bond, with no side-length restriction.
  2. `perCubeRegularShell_toFrozen`: transfer all pointwise, difference and curl guards.
  3. `classCoupledShell_toFrozen`: retain the unchanged coverage conjunct.
  4. `classCoupledShell_one`: flat `U = 1` belongs to the shell class under the decision's positive parameters and coverage premise.
  5. `shell_slab_nonvacuous`: the complete depth-two slab conjunction, for positive even `M`, `R >= 18`, every positive cap `a₀`: `TorusOK`, `Admissible`, `LambdaOK2`, proper nonempty `Omega_0`, and positive capped `α₀` with shell membership. Do not leave coverage or proper-domain geometry assumed.
  6. `readBond_not_touchBond_slab6`: an edge is read but has neither endpoint in this slab.
  7. `no_plaqIn_eq_plaqCorner_slab6`: no site set `T` has `plaqIn T = plaqCorner slab6`.
- **Expected outcome:** structural comparisons and a flat hypothesis-family witness. `ReadBond` is stronger than the printed endpoint convention. Neither the fully consistent touching assertion nor shell coercivity is decided. The selector separator rules out only selector identification, not all comparisons of forms.
- **Axiom checks:**
  ```lean
  #print axioms Fidelity.S1.cubeBond_readBond
  #print axioms Fidelity.S1.perCubeRegularShell_toFrozen
  #print axioms Fidelity.S1.classCoupledShell_toFrozen
  #print axioms Fidelity.S1.classCoupledShell_one
  #print axioms Fidelity.S1.shell_slab_nonvacuous
  #print axioms Fidelity.S1.readBond_not_touchBond_slab6
  #print axioms Fidelity.S1.no_plaqIn_eq_plaqCorner_slab6
  ```

### 4. S-2 — conditional class and headline inclusion

- **Decision:** [s2-inclusion/DECISION.md](s2-inclusion/DECISION.md), “Exact Stage B declaration targets”; route `lean-comparison`, with a non-vacuity hold.
- **File:** `AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean` (existing uncompiled draft; repair tactics, not definitions or signature strength).
- **Frozen imports:** `ZT5A`, `ZR2Ops2`, `ZR8Class`.
- **Namespace:** `AdalyFormal.AHP.FidelS2Inclusion`.
- **Declarations:** the ten exact signatures in the decision, in the order below. Preserve its `ClassCoupledFour`, `ClassCoupledCorner`, touching regularity, frozen `InstIneq` on `plaqIn`, and unchanged Lambda/quantifier order. The product-box coverage argument is essential; plain predicate monotonicity is not enough.
- **Expected outcome:** `ClassCoupledCorner → ClassCoupledFour → ClassCoupled` and conditional `P428Target8 → P428Target8Four → P428Target8Corner`, plus the supporting geometric/regularity implications. No reverse inclusion, strictness, shell-class inclusion or changed-operator comparison. Independent proper nonempty admissible-domain and nontrivial test-field evidence remains necessary before substantive variant acceptance; this queue does not invent a witness target absent an exact decision contract.
- **Axiom checks (also the declaration order):**
  ```lean
  #print axioms AdalyFormal.AHP.FidelS2Inclusion.touchCover_cubeBond
  #print axioms AdalyFormal.AHP.FidelS2Inclusion.CoversPlaqFour.toFrozen
  #print axioms AdalyFormal.AHP.FidelS2Inclusion.CoversPlaqCorner.toFour
  #print axioms AdalyFormal.AHP.FidelS2Inclusion.PerCubeRegularTouch.toFrozen
  #print axioms AdalyFormal.AHP.FidelS2Inclusion.ClassCoupledFour.toFrozen
  #print axioms AdalyFormal.AHP.FidelS2Inclusion.ClassCoupledCorner.toFour
  #print axioms AdalyFormal.AHP.FidelS2Inclusion.ClassCoupledCorner.toFrozen
  #print axioms AdalyFormal.AHP.FidelS2Inclusion.targetFour_of_frozen
  #print axioms AdalyFormal.AHP.FidelS2Inclusion.targetCorner_of_four
  #print axioms AdalyFormal.AHP.FidelS2Inclusion.targetCorner_of_frozen
  ```

### 5. Sheet Q2(b) — strict versus non-strict tower predicates

- **Decision:** [sheet-variants/DECISION.md](sheet-variants/DECISION.md), section 4.1; route `lean-comparison`.
- **File:** `AHP/fidelity/sheet-variants/lean/CollarNonStrict.lean`.
- **Frozen import:** `ZT5A`; the decision also permits `RB2` if needed.
- **Namespace for entries 5–10:** `AdalyFormal.Fidelity.SheetVariants`.
- **Definitions:** exactly `AdmissibleNonStrict`, `L8`, `collarSep` from section 4.1.
- **Declarations:** `admissible_imp_nonstrict`; `admissibleNonStrict_k1_iff`; `collar_separator` with the exact `AdmissibleNonStrict 2 1 1 2 collarSep ∧ ¬ Admissible 2 1 1 2 collarSep` statement.
- **Expected outcome:** predicate inclusion, depth-one equivalence and a geometry-only separator. `M = 1` and this separator are outside the headline regime. No non-strict coercivity conclusion or refutation.
- **Axiom checks:**
  ```lean
  #print axioms AdalyFormal.Fidelity.SheetVariants.admissible_imp_nonstrict
  #print axioms AdalyFormal.Fidelity.SheetVariants.admissibleNonStrict_k1_iff
  #print axioms AdalyFormal.Fidelity.SheetVariants.collar_separator
  ```

### 6. Sheet Q3 — conditional reading-B restriction

- **Decision:** [sheet-variants/DECISION.md](sheet-variants/DECISION.md), section 4.2.
- **File:** `AHP/fidelity/sheet-variants/lean/ReadingB.lean`.
- **Frozen imports:** `THL6`, `RB2`.
- **Definitions:** exact `ReadingBTower` and `P428Target8_ReadingB` from section 4.2.
- **Declaration:** `readingB_of_layer : Target8Layer → P428Target8_ReadingB`.
- **Expected outcome:** restriction using the first conjunct of `ReadingBTower`, with the same class, operators and one radius. Not an identification of source intent or a supplied proper-domain analytic witness.
- **Axiom check:**
  ```lean
  #print axioms AdalyFormal.Fidelity.SheetVariants.readingB_of_layer
  ```

### 7. Sheet Q4 — explicit embedding and collar scaling

- **Decision:** [sheet-variants/DECISION.md](sheet-variants/DECISION.md), section 4.3.
- **File:** `AHP/fidelity/sheet-variants/lean/LambdaScale.lean`.
- **Frozen import:** `ZStatementP428`.
- **Definition:** exact total `unitEmb` with modulo, not an embedding supposedly exported by `LambdaOK`.
- **Declarations:** `unitEmb_val`; `pdist_emb_scales`; `lambda_collar_scale_iff`, all with `0 < ell ^ k`; `headline_fine_side_ge16`, under actual `TorusOK`, `ell >= 2`, `k >= 2`.
- **Expected outcome:** coordinate and distance identities on embedded unit-site pairs for arbitrary rectangular extents; equivalent strict collar atoms; the fine-side lower bound 16. Not an identification of the entire fine complement or a verdict on the source's common radius.
- **Axiom checks:**
  ```lean
  #print axioms AdalyFormal.Fidelity.SheetVariants.unitEmb_val
  #print axioms AdalyFormal.Fidelity.SheetVariants.pdist_emb_scales
  #print axioms AdalyFormal.Fidelity.SheetVariants.lambda_collar_scale_iff
  #print axioms AdalyFormal.Fidelity.SheetVariants.headline_fine_side_ge16
  ```

### 8. Sheet Q6(a) — global gauge implies per-cube regularity

- **Decision:** [sheet-variants/DECISION.md](sheet-variants/DECISION.md), section 4.4.
- **File:** `AHP/fidelity/sheet-variants/lean/GlobalGauge.lean`.
- **Frozen import:** `ZT5A`.
- **Definitions:** full `GlobalRegular` and `ClassCoupledGlobal` from section 4.4; no opaque surrogates or `True` placeholders.
- **Declarations:** `global_imp_perCube`; `globalClass_imp_frozenClass`; `global_flat` with all five strict-positivity hypotheses.
- **Expected outcome:** precise inclusion and regularity non-emptiness using gauge one and matrix field zero. `global_flat` supplies neither coverage nor a nonzero admissible test field. No strict inclusion or global-gauge analytic headline.
- **Axiom checks:**
  ```lean
  #print axioms AdalyFormal.Fidelity.SheetVariants.global_imp_perCube
  #print axioms AdalyFormal.Fidelity.SheetVariants.globalClass_imp_frozenClass
  #print axioms AdalyFormal.Fidelity.SheetVariants.global_flat
  ```

### 9. Sheet Q12 — left-hand norm re-expression

- **Decision:** [sheet-variants/DECISION.md](sheet-variants/DECISION.md), section 4.5.
- **File:** `AHP/fidelity/sheet-variants/lean/NormHS.lean`.
- **Frozen imports:** `ZT5A`, `AdalyFormal.Balaban.RMapLipschitz`.
- **Definitions:** exact `bondEnergyHS`, `InstIneqHS`, `CoercG8AtHS`, `P428Target8_HS` from section 4.5.
- **Declarations:** `bondEnergyHS_eq_two`; `instIneqHS_iff` with HS constant `γ / 2`; `target_iff_hs`.
- **Expected outcome:** full Frobenius energy equals twice the frozen energy; transport this identity through the instance and unchanged headline binders. Do not bypass the identity by independently importing analytic conclusions. No changes to `genForm`, `a`, `α₀`, operators or class-bound norm; no S-3 closure.
- **Axiom checks:**
  ```lean
  #print axioms AdalyFormal.Fidelity.SheetVariants.bondEnergyHS_eq_two
  #print axioms AdalyFormal.Fidelity.SheetVariants.instIneqHS_iff
  #print axioms AdalyFormal.Fidelity.SheetVariants.target_iff_hs
  ```

### 10. Sheet Q13 — existing implication and abstract threshold order

- **Decision:** [sheet-variants/DECISION.md](sheet-variants/DECISION.md), section 4.6.
- **File:** `AHP/fidelity/sheet-variants/lean/QuantifierOrder.lean`.
- **Frozen import:** `TT_F`.
- **Declarations:** `total_imp_frozen : AdalyFormal.Total.P428Target8Total → P428Target8`, re-exporting `AdalyFormal.Total.P428Target8Total.toTarget`; `threshold_order_toy`, exactly the conjunction in section 4.6 with the inequality `m <= R` over unbounded naturals.
- **Expected outcome:** existing implication and separation of unrestricted quantifier patterns only. Do not infer non-implication between the actual closed coercivity propositions. Total also varies when constants are chosen, quantifies all `c >= 10`, and includes well-definedness; retain those distinctions.
- **Axiom checks:**
  ```lean
  #print axioms AdalyFormal.Fidelity.SheetVariants.total_imp_frozen
  #print axioms AdalyFormal.Fidelity.SheetVariants.threshold_order_toy
  ```

## Dispositions outside the implementation queue

### Guarded all-plaquette target — NOT READY

`AHP/fidelity/guarded/DECISION.md` is missing at consolidation. No file, declaration or frozen import set is authorized for Stage B. In particular, do not promote `guarded/SPEC.md`'s `UthCross.lean` proposal into this decision-only work list. Obtain a decision first. `P428Target8SG` remains unresolved.

### Sheet reading — reading-only; no new Lean target

[sheet-reading/DECISION.md](sheet-reading/DECISION.md) sets `leanTargets: []`. Therefore no required `ReadingAudit.lean`, imports or new axiom checks are scheduled. Optional checks of existing declarations are not fidelity closure. Keep Q8/Q10/Q11 as qualified reading records, with outstanding citation repairs, the compression/inversion issue, and `Cop_ker` limited to selected rows under `H0` bijectivity.

### Other sheet dispositions — no duplicate targets

Per `sheet-variants/DECISION.md`: Q1/Q2(a) keep the existing conventions/reading-A bridge; Q5 has existing factor/family/union results; Q6(b), Q7 and Q9 belong to the other fidelity targets; Q8/Q10/Q11 belong to `sheet-reading`. Their source-acceptability questions do not become new formal obligations here.

**Queue size:** ten files, 39 named proof declarations, plus any proof helpers requiring checks. This is a work list, not a count of completed results. S-1, substantive S-2 acceptance, S-3 and the guarded headline are not closed by this plan.
