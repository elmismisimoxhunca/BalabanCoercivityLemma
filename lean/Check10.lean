-- Check10.lean: accepted AHP fidelity results. Separate environments preserve copied names.
import AHP.JetBoundaryComparison
import AHP.ShellComparison
import AHP.ClassInclusion
import AHP.CollarNonStrict
import AHP.ReadingB
import AHP.LambdaScale
import AHP.GlobalGauge
import AHP.NormHS
import AHP.QuantifierOrder
import AHP.UthCross

-- AHP/fidelity/s3-normalisation/lean/JetBoundaryComparison.lean; review: AHP/fidelity/s3-normalisation/lean/JetBoundaryComparison.VERIFY.md
#print axioms AdalyFormal.AHP.FidelS3Normalisation.raw_level_zero
#print axioms AdalyFormal.AHP.FidelS3Normalisation.linear_level_zero
#print axioms AdalyFormal.AHP.FidelS3Normalisation.plainH_eq_uniformBody_at_depth_one
-- AHP/fidelity/s1-touching/lean/ShellComparison.lean; review: AHP/fidelity/s1-touching/lean/ShellComparison.VERIFY.md
#print axioms Fidelity.S1.cubeBond_readBond
#print axioms Fidelity.S1.perCubeRegularShell_toFrozen
#print axioms Fidelity.S1.classCoupledShell_toFrozen
#print axioms Fidelity.S1.classCoupledShell_one
#print axioms Fidelity.S1.shell_slab_nonvacuous
#print axioms Fidelity.S1.readBond_not_touchBond_slab6
#print axioms Fidelity.S1.no_plaqIn_eq_plaqCorner_slab6
-- AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean; review: AHP/fidelity/s2-inclusion/lean/ClassInclusion.VERIFY.md
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
-- AHP/fidelity/sheet-variants/lean/CollarNonStrict.lean; review: AHP/fidelity/sheet-variants/lean/CollarNonStrict.VERIFY.md
#print axioms AdalyFormal.Fidelity.SheetVariants.admissible_imp_nonstrict
#print axioms AdalyFormal.Fidelity.SheetVariants.admissibleNonStrict_k1_iff
#print axioms AdalyFormal.Fidelity.SheetVariants.pdist_L8
#print axioms AdalyFormal.Fidelity.SheetVariants.collar_separator
-- AHP/fidelity/sheet-variants/lean/ReadingB.lean; review: AHP/fidelity/sheet-variants/lean/ReadingB.VERIFY.md
#print axioms AdalyFormal.Fidelity.SheetVariants.readingB_of_layer
-- AHP/fidelity/sheet-variants/lean/LambdaScale.lean; review: AHP/fidelity/sheet-variants/lean/LambdaScale.VERIFY.md
#print axioms AdalyFormal.Fidelity.SheetVariants.scaleUp_length
#print axioms AdalyFormal.Fidelity.SheetVariants.unitEmb_val
#print axioms AdalyFormal.Fidelity.SheetVariants.pcd_scale
#print axioms AdalyFormal.Fidelity.SheetVariants.pdist_emb_scales
#print axioms AdalyFormal.Fidelity.SheetVariants.lambda_collar_scale_iff
#print axioms AdalyFormal.Fidelity.SheetVariants.headline_fine_side_ge16
-- AHP/fidelity/sheet-variants/lean/GlobalGauge.lean; review: AHP/fidelity/sheet-variants/lean/GlobalGauge.VERIFY.md
#print axioms AdalyFormal.Fidelity.SheetVariants.global_imp_perCube
#print axioms AdalyFormal.Fidelity.SheetVariants.globalClass_imp_frozenClass
#print axioms AdalyFormal.Fidelity.SheetVariants.global_flat
-- AHP/fidelity/sheet-variants/lean/NormHS.lean; review: AHP/fidelity/sheet-variants/lean/NormHS.VERIFY.md
#print axioms AdalyFormal.Fidelity.SheetVariants.bondEnergyHS_eq_two
#print axioms AdalyFormal.Fidelity.SheetVariants.instIneqHS_iff
#print axioms AdalyFormal.Fidelity.SheetVariants.target_iff_hs
-- AHP/fidelity/sheet-variants/lean/QuantifierOrder.lean; review: AHP/fidelity/sheet-variants/lean/QuantifierOrder.VERIFY.md
#print axioms AdalyFormal.Fidelity.SheetVariants.total_imp_frozen
#print axioms AdalyFormal.Fidelity.SheetVariants.threshold_order_toy
-- AHP/fidelity/guarded/lean/UthCross.lean; review: AHP/fidelity/guarded/lean/UthCross.VERIFY.md
#print axioms AdalyFormal.FidelityGuarded.Ginv_lit_psd_at_zero
#print axioms AdalyFormal.FidelityGuarded.Uth_hits_nonunit
#print axioms AdalyFormal.FidelityGuarded.Uth_singular_is_not_a_split
