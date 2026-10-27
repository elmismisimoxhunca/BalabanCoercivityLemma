-- Check8.lean (part 8): cited declarations added 2026-10-19 (CLAIMS rows of the printed-statement bridge lane r_bridge_20261019, modules RB1-RB4, namespace RBridge, and of the thinner-layer lane thin_layer_20261019, modules THL1-THL3, THL5-THL8; reviewer files SolRBridgeAudit (Sol, originally Audit.lean) and SolThinAudit (Sol, originally Audit.lean)). Separate environment. The census/gate module THL4 and the controls (which deliberately contain sorry/axiom) are NOT in this project; SolThinAudit imports THL3, THL6, THL7, THL8, Lean instead of THL4.
import RB4
import SolRBridgeAudit
import THL1
import THL2
import THL3
import THL5
import THL6
import THL7
import THL8
import SolThinAudit
#print axioms AdalyFormal.RBridge.PrintedTower  -- r-printedtower
#print axioms AdalyFormal.RBridge.PadAbove  -- r-padabove
#print axioms AdalyFormal.RBridge.Om0Print  -- r-om0print
#print axioms AdalyFormal.RBridge.blockClosed_iff_sum  -- r-blockclosed-iff-sum
#print axioms AdalyFormal.RBridge.om0clause_iff_print  -- r-om0clause-iff
#print axioms AdalyFormal.RBridge.collar_iff_rat  -- r-collar-iff-rat
#print axioms AdalyFormal.RBridge.admissible_iff_print  -- r-admissible-iff-print
#print axioms AdalyFormal.RBridge.om0Print_collar  -- r-om0print-collar
#print axioms AdalyFormal.RBridge.om0Print_least  -- r-om0print-least
#print axioms AdalyFormal.RBridge.collar0_violated_of_not_sup  -- r-collar0-violated
#print axioms AdalyFormal.RBridge.om0Print_char  -- r-om0print-char
#print axioms AdalyFormal.RBridge.om0Lt_eq_rad  -- r-om0lt-eq-rad
#print axioms AdalyFormal.RBridge.om0Print_sub_unit  -- r-om0print-sub-unit
#print axioms AdalyFormal.RBridge.radius_rescale  -- r-radius-rescale
#print axioms AdalyFormal.RBridge.readings_differ  -- r-readings-differ
#print axioms AdalyFormal.RBridge.alt_readings_violate_collar0  -- r-alt-readings-violate
#print axioms AdalyFormal.RBridge.cube5_class_box_printed  -- r-cube5-class-box-printed
#print axioms AdalyFormal.RBridge.collar_threshold_iff_printed  -- r-collar-threshold-iff
#print axioms AdalyFormal.RBridge.collar_power_ell2  -- r-collar-power-ell2
#print axioms AdalyFormal.RBridge.collar_power_ell3  -- r-collar-power-ell3
#print axioms AdalyFormal.RBridge.core8Applied_iff_print  -- r-core8-iff-print
#print axioms AdalyFormal.RBridge.headline_in_print_terms  -- r-headline-print-terms
#print axioms AdalyFormal.RBridge.headline_R_before_k  -- r-headline-r-before-k
#print axioms AdalyFormal.RBridge.printed_nonvacuous  -- r-printed-nonvacuous
#print axioms AdalyFormal.RBridge.printed_discriminates  -- r-printed-discriminates
#print axioms SolRBridge.readingB_satisfies_collar  -- rev-readingb-collar
#print axioms SolRBridge.readingB_fine_blockClosed  -- rev-readingb-fine
#print axioms SolRBridge.readingB_strictly_larger  -- rev-readingb-larger
#print axioms SolRBridge.boundary_bond_omitted  -- rev-boundary-bond
#print axioms AdalyFormal.ThinLayer.AdmNoBase  -- thin-admnobase
#print axioms AdalyFormal.ThinLayer.AdmSplit  -- thin-admsplit
#print axioms AdalyFormal.ThinLayer.AdmSplitNB  -- thin-admsplitnb
#print axioms AdalyFormal.ThinLayer.admNoBase_of_splitNB  -- thin-admnobase-of-splitnb
#print axioms AdalyFormal.ThinLayer.admissible_of_admSplit  -- thin-admissible-of-admsplit
#print axioms AdalyFormal.ThinLayer.lambdaOK2_mono  -- thin-lambdaok2-mono
#print axioms AdalyFormal.ThinLayer.famTorusThin_iff  -- thin-famtorusthin-iff
#print axioms AdalyFormal.ThinLayer.famTorusLayer_union  -- thin-fam-union
#print axioms AdalyFormal.ThinLayer.famTorusLayer_box  -- thin-fam-box
#print axioms AdalyFormal.ThinLayer.famTorusLayerCap  -- thin-fam-cap
#print axioms AdalyFormal.ThinLayer.totalLayer  -- thin-total
#print axioms AdalyFormal.ThinLayer.mixedLayer  -- thin-mixed
#print axioms AdalyFormal.ThinLayer.Target8Layer  -- thin-target8layer-def
#print axioms AdalyFormal.ThinLayer.target8Layer  -- thin-target8layer
#print axioms Sol_frozen_target_of_layer  -- thin-sol-implies
#print axioms AdalyFormal.Thin.admissible_lift_T  -- thin-admissible-lift-t
#print axioms AdalyFormal.L0C.path_exists_T  -- thin-path-exists-t
#print axioms AdalyFormal.ThinLayer.asym_layer_class  -- thin-asym-layer-class
#print axioms AdalyFormal.NonVacC.asym_instance_inequality  -- thin-asym-instance
#print axioms AdalyFormal.ThinLayer.competitor_support_in_Om0  -- thin-competitor-support
