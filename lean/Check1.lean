-- Check1.lean (part 1 of 3): imports the modules hosting cited declarations and prints their axioms. Split because modules from different lanes declare the same names and cannot be imported into one environment.
import AC_Base
import AC_CF
import AC_Final
import AC_NV
import AU_XFinal
import AdalyFormal.Balaban.Erratum2127
import AdalyFormal.Balaban.RMapLipschitz
import AdalyFormal.Balaban.RegularUPerturbation
import BLC6
import BLC8
import BLC9
import BallCharts
import C5B
import C5C
import C5D
import C5E
import C5F
import C5G
import CvF1
import CvN1
import CvN6
import CvN7
import CvNe2
import CvO1
import CvOF10
import CvOF12
import CvOF14
import CvOF16
import CvOF17
import CvOF18
import CvOF19
import CvOG1
import CvOX1
import CvOX2
import CvS1
import CvS3c
import CvSl1
import D1Collapse
import D1Cons
import D1Final
import D1Lit
import D1Main
import D1PGen
import D2Cons
import D2Final
import D2Geo6
import D2Lit
import D2Main
import DLR97
import EmptyCaseAudit
import Fourth
import GE5
import GE6
import GE8
import GG3
import GG5
import GL2
import GV13
import GV14
import GdFam
import GdGap
import GdGeo
import GdSchur
import GenCl1
import GenCl3
import GenCl4
import GenP0
import GenP1
import M1B
import M1Cov
import M1G2
import M1G3
import M2B2
import M2B3
import MA19
import MC2
import MR2
import MR4
import MXQ_Tor
import MZ1
import MZ3
import MZ5
import NC1
import NC5
import NC7
import NMX4
import NV7
import NV8
import NVC7
import NVC8
import NsCS1
import OG10
import OG11
import OL11
import OL12
import OL15
import P409D
import PRO_Joint
import ProsX0
import Q409L2
import Q409W3
import Q409W4
import RI5
import RI6
import SVS
import StatementAudit
import TL17c
import TL21a
import TL21b
import TT_A
import TT_C
import TT_F
import TT_G
import TT_Z
import UA
import UMF
import UNI_Base
import UNI_Joint
import UNI_Red
import UNI_Strict
import UNI_Tor
import UNI_Wit2
import UW13
import ZLocJet
import ZR2A
import ZR2Ops2
import ZR6A
import ZR8Class
import ZR8Data
import ZR8DataB
import ZStatementP428
import ZT4A
import ZT5A
import ZXG3A
import ZXR2Ops3
import ZXR2Sector
import ZXR2Wire2

#print axioms AdalyFormal.AllC.ClassCoupled.toH  -- disc-toH
#print axioms AdalyFormal.AllC.ClassCoupledH.toOrig  -- disc-toOrig
#print axioms AdalyFormal.M2GlueGeo.cubeIndex_ge_pred  -- route-cip
#print axioms AdalyFormal.AllC.P428Target8StrongC  -- strongc-def
#print axioms AdalyFormal.AllC.p428Target8StrongC  -- inter-strongc
#print axioms AdalyFormal.AllC.classHyps_nonvacuous  -- nonvac-allc
#print axioms AdalyFormal.AllC.P428Target8MaxAllC.toStrongC  -- comp-P428Target8MaxAllC.toStrongC
#print axioms AdalyFormal.AllC.P428Target8MaxAllC  -- maxallc-def
#print axioms AdalyFormal.AllC.p428Target8MaxAllC  -- inter-maxallc
#print axioms AdalyFormal.Balaban.Erratum2127.erratum_2127  -- erratum2127
#print axioms AdalyFormal.Balaban.Erratum2127.Printed2127  -- def-Printed2127
#print axioms AdalyFormal.Balaban.RMapLipschitz.norm_sq_eq_half_frobSq  -- conv-norm
#print axioms AdalyFormal.Balaban.RMapLipschitz.frobNorm  -- conv-frob
#print axioms AdalyFormal.Balaban.RegularUPerturbation.bondEnergy  -- conv-bondenergy
#print axioms AdalyFormal.M2BallCharts.ball_chart_pos  -- ballcharts-mech8
#print axioms AdalyFormal.M2BallCharts.ball_chart_zero  -- ballcharts-mech7
#print axioms AdalyFormal.M2BallCharts.target8_of_residual  -- composition
#print axioms AdalyFormal.M2BallCharts.ballChartsG  -- constants2
#print axioms AdalyFormal.OneGap.ballCharts_of_G  -- ballcharts-from-g
#print axioms AdalyFormal.OneGap.BallChartsG  -- ballcharts-def
#print axioms AdalyFormal.OneGap.BallChartsAtG  -- ballcharts-def2
#print axioms AdalyFormal.P409C5.cubeR  -- cuber-def
#print axioms AdalyFormal.P409C5.tildeCube  -- tildecube-def
#print axioms AdalyFormal.P409C5.printedCube5  -- printedcube5-def
#print axioms AdalyFormal.P409C5.IsDCube  -- isdcube-def
#print axioms AdalyFormal.P409C5.cube5_in_union  -- cube5-in-union
#print axioms AdalyFormal.P409C5.tg_cube5_needs_12ell  -- tg-cube5-needs
#print axioms AdalyFormal.P409C5.cube5_sharp_pair  -- cube5-sharp-pair
#print axioms AdalyFormal.P409C5.cube5_in_union_scaleUp  -- cube5-in-union-scaleup
#print axioms AdalyFormal.P409C5.cube5_index  -- cube5-index
#print axioms AdalyFormal.P409C5.IsDCubePrint  -- isdcubeprint-def
#print axioms AdalyFormal.P409C5.cube5_print0_anchor_full  -- cube5-print0-anchor
#print axioms AdalyFormal.P409C5.cube5_in_union_print0  -- cube5-print0
#print axioms AdalyFormal.CoverFinish.FailAt  -- omega-failAt-def
#print axioms AdalyFormal.CoverNec.exists_not_isUnit  -- singular-tip2
#print axioms AdalyFormal.CoverNec.not_P428Target8NC  -- cov-nec2
#print axioms AdalyFormal.CoverNec.tip_counterexample  -- tip-counterex
#print axioms AdalyFormal.CoverNec.exists_singular_tip  -- singular-tip
#print axioms AdalyFormal.CoverNec.not_P428Target8G  -- gc-necessary
#print axioms AdalyFormal.CoverNec.coverage_necessary  -- cov-nec
#print axioms AdalyFormal.CoverNec.coverage_necessary_general  -- gc-necessary2
#print axioms AdalyFormal.CoverNested.neLu  -- omega-fam-neLu
#print axioms AdalyFormal.CoverNested.neS  -- omega-fam-neS
#print axioms AdalyFormal.CoverNested.neLam  -- omega-fam-neLam
#print axioms AdalyFormal.CoverOmega.stagCfg  -- omega-fam-stagCfg
#print axioms AdalyFormal.CoverOmega.stagU  -- omega-fam-stagU
#print axioms AdalyFormal.CoverOmega.nested_genForm  -- omega-genForm
#print axioms AdalyFormal.CoverOmega.IsCrossingN  -- omega-crossing
#print axioms AdalyFormal.CoverOmega.nested_Zchain  -- omega-Zchain
#print axioms AdalyFormal.CoverOmega.onLambdaT_gU  -- omega-onLambdaT
#print axioms AdalyFormal.CoverOmega.nested_genForm_neg  -- omega-genForm-neg
#print axioms AdalyFormal.CoverOmega.NearUnits  -- omega-nearUnits
#print axioms AdalyFormal.CoverOmega.nested_stag_failAt  -- omega-failAt
#print axioms AdalyFormal.CoverOmega.not_WDH_of_nearUnits  -- omega-notWDH
#print axioms AdalyFormal.CoverOmega.NGeo  -- omega-ngeo
#print axioms AdalyFormal.CoverOmega.delpA_unit  -- omega-delpA
#print axioms AdalyFormal.CoverOmega.not_WDH_of_nearUnitsRest  -- omega-notWDH-rest
#print axioms AdalyFormal.CoverOmega.UnitsRest  -- omega-unitsrest
#print axioms AdalyFormal.CoverOmega.NearUnitsRest  -- omega-nearunitsrest
#print axioms AdalyFormal.CoverStrong.toWDH_of_NC  -- wdh-implies
#print axioms AdalyFormal.CoverStrong.P428Target8NCWDH  -- wdh-def
#print axioms AdalyFormal.CoverStrong.InstIneqWDH  -- wdh-def2
#print axioms AdalyFormal.CoverStrong.not_NC_of_not_WDH  -- wdh-implies2
#print axioms AdalyFormal.CoverStrong.not_P428Target8NCWD  -- ncwd-false
#print axioms AdalyFormal.CoverStrong.P428Target8NCWD  -- def-P428Target8NCWD
#print axioms AdalyFormal.CoverStrong.CoercG8AtNCWDH  -- ncwdh-inner-def
#print axioms AdalyFormal.CoverStrong.tip_InstIneq_const  -- tip-no-strong
#print axioms AdalyFormal.CoverStrong.tip_no_strong_failure  -- tip-no-strong2
#print axioms AdalyFormal.CoverSlab.StrongWitness  -- strong-witness
#print axioms AdalyFormal.CoverSlab.not_WDH_of_witness  -- strong-sufficient
#print axioms AdalyFormal.CoverSlab.coverage_necessary_strong_of_witness  -- strong-sufficient2
#print axioms AdalyFormal.CoverSlab.perCube_of_classTriv  -- strong-triv
#print axioms AdalyFormal.D1Literal.genFormS_collapse  -- d1-collapse
#print axioms AdalyFormal.D1Literal.not_InstIneqS_of_not_unit  -- d1-not-instineq
#print axioms AdalyFormal.D1Literal.localised_holds_literal_fails  -- d1-holds-literal
#print axioms AdalyFormal.D1Literal.literal_Ginv_indefinite  -- d1-indef-lit
#print axioms AdalyFormal.D1Literal.literal_Ginv_depends_outside  -- d1-depends
#print axioms AdalyFormal.D1Literal.not_P428Target8Literal  -- d1-not-literal
#print axioms AdalyFormal.D1Literal.not_P428Target8LiteralDelta  -- d1-not-literaldelta
#print axioms AdalyFormal.D1Literal.PlaqSel  -- d1-plaqsel-def
#print axioms AdalyFormal.D1Literal.P428Target8S  -- d1-target-s
#print axioms AdalyFormal.D1Literal.selIn  -- d1-selin
#print axioms AdalyFormal.D1Literal.selAll  -- d1-selall
#print axioms AdalyFormal.D1Literal.pin_target8  -- d1-pin
#print axioms AdalyFormal.D1Literal.P428Target8Literal  -- d1-literal-def
#print axioms AdalyFormal.D1Literal.P428Target8LiteralDelta  -- d1-literaldelta-def
#print axioms AdalyFormal.D1Literal.Fth_pi_neg  -- d1-fth-pi-neg
#print axioms AdalyFormal.D1Literal.Fth_zero_psd  -- d1-fth-zero-psd
#print axioms AdalyFormal.D1Literal.exists_nonunit_Ginv  -- d1-nonunit
#print axioms AdalyFormal.D1Literal.not_literal_every_ell  -- d1-not-literal-ell
#print axioms AdalyFormal.D1Literal.localised_holds_both_fails  -- d1-holds-both
#print axioms AdalyFormal.D1Literal.both_Ginv_indefinite  -- d1-indef-both
#print axioms AdalyFormal.D1Literal.P428Target8SG  -- d1-guarded-def
#print axioms AdalyFormal.D1Literal.localised_guarded_holds  -- d1-guarded-holds
#print axioms AdalyFormal.D1Literal.not_P428Target8LiteralBoth  -- d1-not-both
#print axioms AdalyFormal.D1Literal.not_both_every_ell  -- d1-not-both-ell
#print axioms AdalyFormal.D1Literal.FthM_both_pi_neg  -- d1-fthm-pi-neg
#print axioms AdalyFormal.D1Literal.P428Target8M  -- d1-target-m
#print axioms AdalyFormal.D1Literal.dataM_univ  -- d1-datam-univ
#print axioms AdalyFormal.D1Literal.dataM_touch  -- d1-datam-touch
#print axioms AdalyFormal.D1Literal.P428Target8LiteralBoth  -- d1-both-def
#print axioms AdalyFormal.D1Literal.exists_nonunit_GinvM  -- d1-nonunit-both
#print axioms AdalyFormal.DLayer.M0Target_unconditional  -- m0-target
#print axioms SolCube5EmptyCase.print_cube  -- sol-empty-printcube
#print axioms SolCube5EmptyCase.empty_target  -- sol-empty-target
#print axioms SolCube5EmptyCase.no_class_set  -- sol-empty-noset
#print axioms AdalyFormal.D1Guarded.wd_NG  -- d1g-wdng
#print axioms AdalyFormal.M2GlueGeo.slab_cube  -- ballcharts-mech6
#print axioms AdalyFormal.M2GlueGeo.cover_geometry  -- ballcharts-mech5
#print axioms AdalyFormal.M2GlueGeo.thin_torus_counterexample  -- thin-counterex
#print axioms AdalyFormal.M2Glue2.GChart  -- gchart
#print axioms AdalyFormal.M2Glue2.glue_two  -- ballcharts-mech2
#print axioms AdalyFormal.M2Glue2.gchart_of_cube  -- ballcharts-mech
#print axioms AdalyFormal.M2Glue.wrap_counterexample  -- wrap-counterex
#print axioms AdalyFormal.M2Glue.no_proportional_constant  -- wrap-counterex2
#print axioms AdalyFormal.M2Glue3.gchart_at_bad_vertex  -- ballcharts-mech3
#print axioms AdalyFormal.M2Glue3.sweep_glue  -- ballcharts-mech4
#print axioms AdalyFormal.M2Glue3.sweep_close  -- ballcharts-mech9
#print axioms AdalyFormal.D1Guarded.G1invS_eq_Ginv_theta  -- d1g-g1inv-eq
#print axioms AdalyFormal.D1Guarded.GapAt_theta_iff  -- d1g-gap-theta-iff
#print axioms AdalyFormal.D1Guarded.genFormS_theta  -- d1g-form-theta
#print axioms AdalyFormal.D1Guarded.WellDefAt  -- d1g-welldef
#print axioms AdalyFormal.D1Guarded.GapAt  -- d1g-gapat
#print axioms AdalyFormal.D1Guarded.InstIneqSG2  -- d1g-sg2
#print axioms AdalyFormal.D1Guarded.genFormS_collapse_N  -- d1g-collapse-N
#print axioms AdalyFormal.D1Guarded.genFormS_collapse_G1inv  -- d1g-collapse-G1inv
#print axioms AdalyFormal.D1Guarded.gap_of_instIneqSG  -- d1g-gap-of-sg
#print axioms AdalyFormal.D1Guarded.instIneqSG_iff  -- d1g-iff
#print axioms AdalyFormal.D1Guarded.P428Target8SG2  -- d1g-target-sg2
#print axioms AdalyFormal.D1Guarded.localised_SG2_holds  -- d1g-localised-sg2
#print axioms AdalyFormal.D1Guarded.SG_forces_gap_slab  -- d1g-forces-gap
#print axioms AdalyFormal.D1Guarded.not_SG_of_gapfail  -- d1g-not-sg
#print axioms AdalyFormal.D1Guarded.JfS_vanish  -- d1g-jfs
#print axioms AdalyFormal.D1Guarded.isUnit_Q_inv_Qs_of_pos_ker  -- d1g-schur
#print axioms AdalyFormal.D1Guarded.GapAt_theta_of_pos_ker  -- d1g-gap-pos-ker
#print axioms AdalyFormal.GeneralClass.p428Target8GC  -- gc-holds
#print axioms AdalyFormal.GeneralClass.P428Target8.toGC  -- gc-holds2
#print axioms AdalyFormal.GeneralClass.P428Target8G  -- gc-def
#print axioms AdalyFormal.GeneralClass.IsClassCubeG  -- def-isclasscubeG
#print axioms AdalyFormal.GeneralClass.PerCubeRegularG  -- def-perCubeRegularG
#print axioms AdalyFormal.GeneralClass.P428Target8GC  -- def-P428Target8GC
#print axioms AdalyFormal.GeneralClass.IsClassSetW  -- isclasssetw-def
#print axioms AdalyFormal.GeneralClass.gc_class_gap  -- gc-gap
#print axioms AdalyFormal.GeneralClass.gc_tip_uncovered  -- gc-gap2
#print axioms AdalyFormal.P409.tg_sharp_cube  -- p409-tg-sharp
#print axioms AdalyFormal.P409.PerCubeFails  -- p409-percube-def
#print axioms AdalyFormal.P409.p409_percube_counterexample_pow  -- p409-percube
#print axioms AdalyFormal.P409.p409_percube_counterexample  -- p409-percube-base
#print axioms AdalyFormal.M1.M1Core_of_headline  -- m1-from-main
#print axioms AdalyFormal.M1.perCube_of_M1  -- m1-from-main2
#print axioms AdalyFormal.M1.M1Regular  -- m1-target2
#print axioms AdalyFormal.M1.M1Target  -- m1-target3
#print axioms AdalyFormal.M1.M1Target_of_target  -- m1-target-of-target
#print axioms AdalyFormal.M1.coverage_fails_slab  -- coverage-fails
#print axioms AdalyFormal.M1.strat_geom_sum_flat  -- m1-stratgeom
#print axioms AdalyFormal.M1.patch_mult  -- m1-patchmult
#print axioms AdalyFormal.M1.patch  -- patch-def
#print axioms AdalyFormal.M1.IsPatch  -- patch-def2
#print axioms AdalyFormal.M2Bridge.patch_inter_not_in_class_cube  -- patch-inter
#print axioms AdalyFormal.M2Bridge.b0_counterexample  -- b0-counterex
#print axioms AdalyFormal.M2Bridge.b0_counterexample_R  -- b0-counterex2
#print axioms AdalyFormal.M1Assembly.m1Target  -- m1-target
#print axioms AdalyFormal.M0Corollary.M0Core  -- m0-core
#print axioms AdalyFormal.M0Corollary.M0Target  -- m0-core2
#print axioms AdalyFormal.M0Corollary.GlobalRegular2  -- m0-global
#print axioms AdalyFormal.M0Corollary.M0Core_of_headline  -- m0-core-of-headline
#print axioms AdalyFormal.M0Corollary.M0Target_of_target  -- m0-target-of-target
#print axioms AdalyFormal.M0Corollary.classCoupled_of_global  -- m0-classcoupled-global
#print axioms AdalyFormal.M2Route.ChartOn  -- chart-on
#print axioms AdalyFormal.M2Route.InterfaceCharts  -- interface-charts
#print axioms MXQ.Total.P428Target8FamilyTorus  -- fam-torus-def
#print axioms MXQ.Total.ClassCoupledF  -- fam-class-def
#print axioms MXQ.Total.p428Target8FamilyTorus  -- fam-torus-thm
#print axioms AdalyFormal.M2DLayer.unc_two_near  -- dlayer-uncnear
#print axioms AdalyFormal.M2DLayer.StencilCovered  -- dlayer-stencil
#print axioms AdalyFormal.M2DLayer.Jf_split  -- dlayer-jfsplit
#print axioms AdalyFormal.M2DLayer.dlayerStrat_class  -- dlayer-class
#print axioms AdalyFormal.NoCover.P428Target8NC  -- nc-def
#print axioms AdalyFormal.NoCover.nc_class_gap  -- coverage-fails2
#print axioms AdalyFormal.NoCover.genForm_of_not_unit  -- junk-value
#print axioms AdalyFormal.NonVacMix.headline_regime_nonvacuousMixed  -- nonvac-mixed
#print axioms AdalyFormal.NonVac.headline_regime_nonvacuous  -- nonvac-regime
#print axioms AdalyFormal.NonVac.headline_instance_inequality  -- nonvac-instance
#print axioms AdalyFormal.NonVacC.headline_regime_nonvacuousC  -- nonvac-c
#print axioms AdalyFormal.NonVacC.headline_instance_inequalityC  -- nonvac-c-ineq
#print axioms AdalyFormal.NcwdhStrong.P428Target8NCWDHc  -- ncwdh-target-c-def
#print axioms AdalyFormal.NcwdhStrong.target_twelve_iff  -- ncwdh-pin
#print axioms AdalyFormal.NcwdhStrong.NcwdhBodyAt  -- ncwdh-body-def
#print axioms AdalyFormal.NcwdhStrong.FailsAtEll  -- ncwdh-fails-def
#print axioms AdalyFormal.OneGap.instIneq_empty  -- instIneq-empty
#print axioms AdalyFormal.OneGap.Residual  -- composition5
#print axioms AdalyFormal.OneGap.ThinTori  -- composition6
#print axioms AdalyFormal.M2Skel.class_coreK  -- class-coreK
#print axioms AdalyFormal.M2OpLayer.ClassRightInv  -- def-classrightinv
#print axioms AdalyFormal.M2OpLayer.opLayerThick_of  -- oplayer
#print axioms AdalyFormal.M2OpLayer.ClassRightInvCov  -- rightinv-cov
#print axioms AdalyFormal.M2OpLayer.classRightInv_of_cov  -- oplayer2
#print axioms AdalyFormal.M2OpLayer.target8_of_rightInvCov  -- composition2
#print axioms AdalyFormal.P409.p409_regime_counterexample_pow  -- p409-regime-pow
#print axioms AdalyFormal.P409.p409_regime_counterexample  -- p409-regime-gen
#print axioms AdalyFormal.P409.p409_regime_counterexample_exists  -- p409-regime-exists
#print axioms AdalyFormal.P409.InRegimeCounterexample  -- p409-regime-def
#print axioms PRO.joint_nonvacuous  -- union-joint-nonvac
#print axioms AdalyFormal.P409.cube5_needs_12ell  -- cube5-needs-12ell
#print axioms AdalyFormal.P409.LFail  -- p409-lf-def
#print axioms AdalyFormal.P409.lf_counterexample_pow  -- p409-lf
#print axioms AdalyFormal.P409W.p409_setw_holds  -- p409-setw
#print axioms AdalyFormal.P409W.degenerate_no_setw  -- p409-degenerate
#print axioms AdalyFormal.P409W.p409_setw_holds_general  -- p409-setw-general
#print axioms AdalyFormal.P409W.p409_setwB_holds  -- p409-setwb
#print axioms AdalyFormal.M2RightInv.classRightInvCov  -- rightinv-cov2
#print axioms AdalyFormal.M2RightInv.cWR  -- rightinv-cwr
#print axioms AdalyFormal.M2RightInv.cGR  -- rightinv-cgr
#print axioms AdalyFormal.M2RightInv.p428Target8  -- main
#print axioms AdalyFormal.M2RightInv.p428Target8_of_rightInvCov  -- composition3
#print axioms AdalyFormal.M2RightInv.thinTori_RI  -- composition4
#print axioms AdalyFormal.StrongVariants.P428Target8Max.toStrong  -- comp-P428Target8Max.toStrong
#print axioms AdalyFormal.StrongVariants.P428Target8Strong.toWD  -- comp-P428Target8Strong.toWD
#print axioms AdalyFormal.StrongVariants.P428Target8Max.toUnif  -- comp-P428Target8Max.toUnif
#print axioms AdalyFormal.StrongVariants.P428Target8Max  -- max-def
#print axioms AdalyFormal.StrongVariants.P428Target8AllC  -- allc-def
#print axioms SolP409Review.setw_index_unique  -- setw-index-unique
#print axioms AdalyFormal.Thin.bondEnergy_pull  -- thin-lift3
#print axioms AdalyFormal.Thin.genForm_lift  -- thin-lift2
#print axioms AdalyFormal.Thin.instIneq_of_lift  -- thin-lift
#print axioms AdalyFormal.Total.BallChartsGT  -- bcgt
#print axioms AdalyFormal.Total.strong_coreTC  -- route-strongcore
#print axioms AdalyFormal.Total.P428Target8Total  -- main-total
#print axioms AdalyFormal.Total.p428Target8Total  -- total-main
#print axioms AdalyFormal.Total.fieldsT  -- total-fieldsT
#print axioms AdalyFormal.Total.P428Target8Total.toMax  -- total-toMax
#print axioms AdalyFormal.Total.P428Target8Total.toMaxAllC  -- total-toMaxAllC
#print axioms AdalyFormal.Total.P428Target8Total.toAllC  -- total-toAllC
#print axioms AdalyFormal.Total.P428Target8Total.toTarget  -- total-toTarget
#print axioms AdalyFormal.Total.p428Target8_fromTotal  -- total-fromTotal
#print axioms AdalyFormal.Total.p428Target8Max_fromTotal  -- total-fromTotal-max
#print axioms AdalyFormal.Total.p428Target8MaxAllC_fromTotal  -- total-fromTotal-maxallc
#print axioms AdalyFormal.Total.p428Target8AllC_fromTotal  -- total-fromTotal-allc
#print axioms AdalyFormal.Total.coverGeomUT  -- route-cgu
#print axioms AdalyFormal.Total.coverGeomBoxUT  -- route-cgbu
#print axioms AdalyFormal.Total.ballChartsGT_proved  -- inter-bcgt
#print axioms AdalyFormal.UnifLane.P428Target8UnifStrong  -- unifstrong-def
#print axioms AdalyFormal.UnifLane.BallChartsGU  -- inter-bcgu-def
#print axioms AdalyFormal.UnifMax.p428Target8UnifStrong_proved  -- inter-unifstrong
#print axioms AdalyFormal.UnifMax.p428Target8Max_proved  -- inter-max
#print axioms UNI.AllC.UnionAt  -- unionat-def
#print axioms UNI.AllC.IsClassUnion  -- isclassunion-def
#print axioms UNI.Joint.joint_union_only  -- union-joint-only
#print axioms UNI.Total.famTorusU_imp_box  -- union-imp-box
#print axioms UNI.Total.boxClass_iff  -- boxclass-iff
#print axioms UNI.Total.unionBoxClass  -- unionboxclass-def
#print axioms UNI.Total.unionSeveralClass  -- unionseveralclass-def
#print axioms UNI.Total.famTorus_unionBox  -- union-imp-box-size
#print axioms UNI.Total.famTorus_unionSeveral  -- union-imp-several
#print axioms UNI.Strict.strict_hyps  -- union-strict
#print axioms UNI.Total.unionClass  -- unionclass-def
#print axioms UNI.Total.ClassCoupledU  -- classcoupledu-def
#print axioms UNI.Total.P428Target8FamilyTorusU  -- union-headline-def
#print axioms UNI.Total.p428Target8FamilyTorusU  -- union-thm
#print axioms UNI.Wit2.admissible_T8  -- union-wit-adm
#print axioms UNI.Wit2.isClassUnion_W8  -- union-wit-union
#print axioms UNI.Wit2.not_box_W8  -- union-wit-notbox
#print axioms AdalyFormal.UnifLane.Z.p428Target8Unif_proved  -- inter-unif
#print axioms AdalyFormal.UnifLane.Z.ballChartsGU_proved  -- inter-bcgu
#print axioms AdalyFormal.IngredientFamilyR2.QlinCompL  -- dev-D11
#print axioms AdalyFormal.IngredientFamilyR2.QlinStepL  -- fderiv-junk
#print axioms AdalyFormal.StatementLane2.PerCubeRegular2  -- def-class2
#print axioms AdalyFormal.StatementLane2.ddA  -- def-class3
#print axioms AdalyFormal.StatementLane2.OnLambdaT  -- def-bt2
#print axioms AdalyFormal.IngredientFamilyR2.plaqIn  -- dev-D1
#print axioms AdalyFormal.StatementLane2.CoversOm0p  -- def-coverage
#print axioms AdalyFormal.StatementLane2.ClassCoupled  -- def-coverage2
#print axioms AdalyFormal.StatementLane2.ClassCoupled.plaq_gauge  -- plaq-gauge
#print axioms AdalyFormal.StatementLaneR8.classBond_iff_bothIn  -- locality2
#print axioms AdalyFormal.StatementLaneR8.InstIneq_congr_class  -- locality3
#print axioms AdalyFormal.StatementLaneR8.genForm_congr_outside  -- locality
#print axioms AdalyFormal.StatementLaneR8.LocHyp  -- dev-D12
#print axioms AdalyFormal.StatementLane.Admissible  -- def-admissible
#print axioms AdalyFormal.StatementLane.pdist  -- def-pdist
#print axioms AdalyFormal.StatementLane.LambdaOK  -- def-lambda2
#print axioms AdalyFormal.StatementLane.TorusOK  -- def-torusok
#print axioms AdalyFormal.StatementLane.IsClassCube  -- def-class
#print axioms AdalyFormal.StatementLane.OnLambdaTildeIn  -- def-bt
#print axioms AdalyFormal.StatementLane.admissible_k0_om0_empty  -- dev-D8
#print axioms AdalyFormal.StatementLane.scaleUp  -- conv-defs
#print axioms AdalyFormal.StatementLane.siteBox  -- def-sitebox
#print axioms AdalyFormal.StatementLane.BlockClosed  -- blockclosed-def
#print axioms AdalyFormal.StatementLaneG.LambdaOK2  -- def-lambda
#print axioms AdalyFormal.StatementLaneG.LamBlockSum  -- def-lambda3
#print axioms AdalyFormal.StatementLaneG.GenP.WellDefG  -- def-welldefg
#print axioms AdalyFormal.StatementLaneG.GenP.GuardsUnit  -- def-guardsunit
#print axioms AdalyFormal.StatementLaneG.P428Target8  -- def-target
#print axioms AdalyFormal.StatementLaneG.P428Genuine8  -- def-target2
#print axioms AdalyFormal.StatementLaneG.P428Core8At  -- def-target3
#print axioms AdalyFormal.StatementLaneG.CoercG8At  -- def-target4
#print axioms AdalyFormal.StatementLaneG.SidePow6  -- def-target5
#print axioms AdalyFormal.StatementLaneG.InstIneq  -- def-form-ineq
#print axioms AdalyFormal.StatementLaneG.core6_is_c12  -- dev-D3
#print axioms AdalyFormal.StatementLaneG.P428Genuine8AllC  -- dev-D3b
#print axioms AdalyFormal.StatementLaneG.InstIneq.toBoth  -- dev-N1
#print axioms AdalyFormal.StatementLaneG.P428Target8Unif  -- main-binders
#print axioms AdalyFormal.StatementLaneG.P428Target8Unif.toTarget  -- main-binders2
#print axioms AdalyFormal.StatementLaneG.P428Genuine8.toPrint  -- main-variants
#print axioms AdalyFormal.StatementLaneG.P428Genuine8.toBoth  -- main-variants2
#print axioms AdalyFormal.StatementLaneG.P428Genuine8WD  -- wd-variant
#print axioms AdalyFormal.StatementLaneG.CoercG8AtWD  -- def-coercwd
#print axioms AdalyFormal.StatementLaneG.InstAtWD  -- def-instatwd
#print axioms AdalyFormal.StatementLaneG.InstAtWD.toHead  -- def-instatwd-tohead
#print axioms AdalyFormal.StatementLaneG.GenP.genForm  -- def-form
#print axioms AdalyFormal.StatementLaneG.GenP.firstTerm  -- def-form2
#print axioms AdalyFormal.StatementLaneG.GenP.WellDef  -- def-welldef
#print axioms AdalyFormal.StatementLaneG.GenP.genC  -- def-genC
#print axioms AdalyFormal.IngredientFamilyR2.FSp  -- rightinv-fsp
#print axioms AdalyFormal.IngredientFamilyR2.QlinB_eq_r7  -- dev-D10
#print axioms AdalyFormal.IngredientFamilyR2.IngrBParams  -- def-ingr
