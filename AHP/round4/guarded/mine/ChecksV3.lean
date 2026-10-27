import TT_F
import MXQ_Br
import MXQ_Tor
import DrEquiv
import MI34
import DLR1

set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option format.width 120
set_option pp.proofs false
set_option pp.deepTerms true

-- D001 lean/src/AC_MR4.lean:26
#check AdalyFormal.M2Route.patchCoercive_class_existsAC
#print axioms AdalyFormal.M2Route.patchCoercive_class_existsAC

-- D002 lean/src/AC_MZ3.lean:32
#check AdalyFormal.M2DLayer.UncAC
#print axioms AdalyFormal.M2DLayer.UncAC

-- D003 lean/src/AC_MZ3.lean:37
#check AdalyFormal.M2DLayer.Jf_splitAC
#print axioms AdalyFormal.M2DLayer.Jf_splitAC

-- D004 lean/src/AC_MZ4.lean:111
#check AdalyFormal.M2DLayer.col_classAC
#print axioms AdalyFormal.M2DLayer.col_classAC

-- D005 lean/src/AC_MZ5.lean:27
#check AdalyFormal.M2DLayer.dlayerStrat_classAC
#print axioms AdalyFormal.M2DLayer.dlayerStrat_classAC

-- D006 lean/src/AC_MZ5.lean:69
#check AdalyFormal.M2DLayer.DLayerObligationClassAC
#print axioms AdalyFormal.M2DLayer.DLayerObligationClassAC

-- D007 lean/src/AC_MZ5.lean:79
#check AdalyFormal.M2DLayer.dlayerObligationClass_holdsAC
#print axioms AdalyFormal.M2DLayer.dlayerObligationClass_holdsAC

-- D008 lean/src/AC_OL10.lean:49
#check AdalyFormal.M2OpLayer.hH1L2_cfgAC
#print axioms AdalyFormal.M2OpLayer.hH1L2_cfgAC

-- D009 lean/src/AC_OL8.lean:35
#check AdalyFormal.M2OpLayer.psi_classAC
#print axioms AdalyFormal.M2OpLayer.psi_classAC

-- D010 lean/src/AC_OL8.lean:77
#check AdalyFormal.M2OpLayer.delta2_classAC
#print axioms AdalyFormal.M2OpLayer.delta2_classAC

-- D011 lean/src/AC_SK3.lean:31
#check AdalyFormal.M2Skel.holRegime_rho1AC
#print axioms AdalyFormal.M2Skel.holRegime_rho1AC

-- D012 lean/src/AC_SK3.lean:57
#check AdalyFormal.M2Skel.w4_classAC
#print axioms AdalyFormal.M2Skel.w4_classAC

-- D013 lean/src/AC_SV1.lean:27
#check AdalyFormal.AllC.wellDefG_of_coverHyp
#print axioms AdalyFormal.AllC.wellDefG_of_coverHyp

-- D014 lean/src/AC_Thin.lean:50
#check AdalyFormal.Thin.unitReg_of_classH
#print axioms AdalyFormal.Thin.unitReg_of_classH

-- D015 lean/src/AU_SK3.lean:31
#check AdalyFormal.M2Skel.w4_classU
#print axioms AdalyFormal.M2Skel.w4_classU

-- D016 lean/src/AU_SK5.lean:29
#check AdalyFormal.M2Skel.config_inst_classU
#print axioms AdalyFormal.M2Skel.config_inst_classU

-- D017 lean/src/CJ2.lean:156
#check AdalyFormal.ClassJets.rawStep_congrA
#print axioms AdalyFormal.ClassJets.rawStep_congrA

-- D018 lean/src/CJ4.lean:50
#check AdalyFormal.ClassJets.ClassSmall
#print axioms AdalyFormal.ClassJets.ClassSmall

-- D019 lean/src/D1Collapse.lean:30
#check AdalyFormal.D1Literal.gen_G_zero
#print axioms AdalyFormal.D1Literal.gen_G_zero

-- D020 lean/src/D1Collapse.lean:32
#check AdalyFormal.D1Literal.gen_H_zero
#print axioms AdalyFormal.D1Literal.gen_H_zero

-- D021 lean/src/D1Collapse.lean:37
#check AdalyFormal.D1Literal.gen_Ginv_isG1inv
#print axioms AdalyFormal.D1Literal.gen_Ginv_isG1inv

-- D022 lean/src/D1Collapse.lean:42
#check AdalyFormal.D1Literal.gen_G1inv_eq
#print axioms AdalyFormal.D1Literal.gen_G1inv_eq

-- D023 lean/src/D1Collapse.lean:45
#check AdalyFormal.D1Literal.gen_G1_zero
#print axioms AdalyFormal.D1Literal.gen_G1_zero

-- D024 lean/src/D1Collapse.lean:50
#check AdalyFormal.D1Literal.gen_H1_zero
#print axioms AdalyFormal.D1Literal.gen_H1_zero

-- D025 lean/src/D1Collapse.lean:57
#check AdalyFormal.D1Literal.genFormS_collapse
#print axioms AdalyFormal.D1Literal.genFormS_collapse

-- D026 lean/src/D1Lit.lean:134
#check AdalyFormal.D1Literal.pin_target8
#print axioms AdalyFormal.D1Literal.pin_target8

-- D027 lean/src/D1Lit.lean:135
#check AdalyFormal.D1Literal.pin_target8_iff
#print axioms AdalyFormal.D1Literal.pin_target8_iff

-- D028 lean/src/D1Lit.lean:138
#check AdalyFormal.D1Literal.pin_genForm
#print axioms AdalyFormal.D1Literal.pin_genForm

-- D029 lean/src/DC2.lean:90
#check AdalyFormal.M1DStrat.WSchur.cjpGinv_Gi
#print axioms AdalyFormal.M1DStrat.WSchur.cjpGinv_Gi

-- D030 lean/src/DC2.lean:94
#check AdalyFormal.M1DStrat.WSchur.cjp_form_lower
#print axioms AdalyFormal.M1DStrat.WSchur.cjp_form_lower

-- D031 lean/src/DC2.lean:112
#check AdalyFormal.M1DStrat.WSchur.sqrtE_of_pair
#print axioms AdalyFormal.M1DStrat.WSchur.sqrtE_of_pair

-- D032 lean/src/DC2.lean:149
#check AdalyFormal.M1DStrat.WSchur.N_lower
#print axioms AdalyFormal.M1DStrat.WSchur.N_lower

-- D033 lean/src/DC2.lean:296
#check AdalyFormal.M1DStrat.WSchur.N_cjp_coer
#print axioms AdalyFormal.M1DStrat.WSchur.N_cjp_coer

-- D034 lean/src/DC2.lean:334
#check AdalyFormal.M1DStrat.WSchur.H_cjp_w
#print axioms AdalyFormal.M1DStrat.WSchur.H_cjp_w

-- D035 lean/src/DG1.lean:183
#check AdalyFormal.M1DStrat.GSplit.hHB_of_split
#print axioms AdalyFormal.M1DStrat.GSplit.hHB_of_split

-- D036 lean/src/DG2a.lean:145
#check AdalyFormal.M1DStrat.ginv_bil
#print axioms AdalyFormal.M1DStrat.ginv_bil

-- D037 lean/src/DG2b.lean:193
#check AdalyFormal.M1DStrat.CTData.NE
#print axioms AdalyFormal.M1DStrat.CTData.NE

-- D038 lean/src/DG2b.lean:202
#check AdalyFormal.M1DStrat.CTData.E_nonneg
#print axioms AdalyFormal.M1DStrat.CTData.E_nonneg

-- D039 lean/src/DG2b.lean:206
#check AdalyFormal.M1DStrat.CTData.Nn_le
#print axioms AdalyFormal.M1DStrat.CTData.Nn_le

-- D040 lean/src/DG2b.lean:216
#check AdalyFormal.M1DStrat.CTData.Y1_le
#print axioms AdalyFormal.M1DStrat.CTData.Y1_le

-- D041 lean/src/DG2b.lean:416
#check AdalyFormal.M1DStrat.CTData.Dg0
#print axioms AdalyFormal.M1DStrat.CTData.Dg0

-- D042 lean/src/DG2b.lean:488
#check AdalyFormal.M1DStrat.CTData.Dg1
#print axioms AdalyFormal.M1DStrat.CTData.Dg1

-- D043 lean/src/DH1.lean:137
#check AdalyFormal.M1DStrat.CTData.Ginv_inj
#print axioms AdalyFormal.M1DStrat.CTData.Ginv_inj

-- D044 lean/src/DH1.lean:155
#check AdalyFormal.M1DStrat.CTData.Ginv_unit
#print axioms AdalyFormal.M1DStrat.CTData.Ginv_unit

-- D045 lean/src/DH1.lean:162
#check AdalyFormal.M1DStrat.CTData.Ginv_G
#print axioms AdalyFormal.M1DStrat.CTData.Ginv_G

-- D046 lean/src/DH1.lean:168
#check AdalyFormal.M1DStrat.CTData.G_Ginv
#print axioms AdalyFormal.M1DStrat.CTData.G_Ginv

-- D047 lean/src/DH1.lean:174
#check AdalyFormal.M1DStrat.CTData.N_unit
#print axioms AdalyFormal.M1DStrat.CTData.N_unit

-- D048 lean/src/DH1.lean:300
#check AdalyFormal.M1DStrat.CTData.H_col
#print axioms AdalyFormal.M1DStrat.CTData.H_col

-- D049 lean/src/DLR1.lean:65
#check AdalyFormal.DLayer.coercive_isUnit
#print axioms AdalyFormal.DLayer.coercive_isUnit

-- D050 lean/src/DLR1.lean:77
#check AdalyFormal.DLayer.coercive_apply_inverse
#print axioms AdalyFormal.DLayer.coercive_apply_inverse

-- D051 lean/src/DLR1.lean:84
#check AdalyFormal.DLayer.coercive_inv_bound
#print axioms AdalyFormal.DLayer.coercive_inv_bound

-- D052 lean/src/DLR2.lean:37
#check AdalyFormal.DLayer.delta2_pair
#print axioms AdalyFormal.DLayer.delta2_pair

-- D053 lean/src/DLR2.lean:42
#check AdalyFormal.DLayer.delta2_abs_le
#print axioms AdalyFormal.DLayer.delta2_abs_le

-- D054 lean/src/DLR27.lean:93
#check AdalyFormal.DLayer.rawStep_congr
#print axioms AdalyFormal.DLayer.rawStep_congr

-- D055 lean/src/DLR58.lean:39
#check AdalyFormal.DLayer.LocRep.J_local_bound
#print axioms AdalyFormal.DLayer.LocRep.J_local_bound

-- D056 lean/src/DLR67.lean:151
#check AdalyFormal.DLayer.C2StepX_row_le
#print axioms AdalyFormal.DLayer.C2StepX_row_le

-- D057 lean/src/DLR69.lean:62
#check AdalyFormal.DLayer.C2Step_l1
#print axioms AdalyFormal.DLayer.C2Step_l1

-- D058 lean/src/DLR72.lean:120
#check AdalyFormal.DLayer.C2CompX_zero
#print axioms AdalyFormal.DLayer.C2CompX_zero

-- D059 lean/src/DLR73.lean:44
#check AdalyFormal.DLayer.C2Comp_l1
#print axioms AdalyFormal.DLayer.C2Comp_l1

-- D060 lean/src/DLR78.lean:37
#check AdalyFormal.DLayer.polar_eq
#print axioms AdalyFormal.DLayer.polar_eq

-- D061 lean/src/DQ2.lean:45
#check AdalyFormal.M1DStrat.DQ.C2Comp_depth
#print axioms AdalyFormal.M1DStrat.DQ.C2Comp_depth

-- D062 lean/src/DQ2.lean:158
#check AdalyFormal.M1DStrat.DQ.C2Comp_depth_any
#print axioms AdalyFormal.M1DStrat.DQ.C2Comp_depth_any

-- D063 lean/src/DQ4.lean:251
#check AdalyFormal.M1DStrat.DQ.C2full_norm
#print axioms AdalyFormal.M1DStrat.DQ.C2full_norm

-- D064 lean/src/DQ4.lean:258
#check AdalyFormal.M1DStrat.DQ.gauge_C2full_norm
#print axioms AdalyFormal.M1DStrat.DQ.gauge_C2full_norm

-- D065 lean/src/DQ5.lean:105
#check AdalyFormal.M1DStrat.DQ.C2full_strat
#print axioms AdalyFormal.M1DStrat.DQ.C2full_strat

-- D066 lean/src/DQ5.lean:239
#check AdalyFormal.M1DStrat.DQ.dqSmall_exists
#print axioms AdalyFormal.M1DStrat.DQ.dqSmall_exists

-- D067 lean/src/DQ5.lean:323
#check AdalyFormal.M1DStrat.DQ.K2strat_mono
#print axioms AdalyFormal.M1DStrat.DQ.K2strat_mono

-- D068 lean/src/DQ5.lean:332
#check AdalyFormal.M1DStrat.DQ.C2full_strat_window
#print axioms AdalyFormal.M1DStrat.DQ.C2full_strat_window

-- D069 lean/src/DS1.lean:33
#check AdalyFormal.M1DStrat.psi_le_of_wcol
#print axioms AdalyFormal.M1DStrat.psi_le_of_wcol

-- D070 lean/src/DS1.lean:56
#check AdalyFormal.M1DStrat.psi1u_le_of_wcol
#print axioms AdalyFormal.M1DStrat.psi1u_le_of_wcol

-- D071 lean/src/DS1.lean:77
#check AdalyFormal.M1DStrat.delta2_strat
#print axioms AdalyFormal.M1DStrat.delta2_strat

-- D072 lean/src/DS1.lean:98
#check AdalyFormal.M1DStrat.hJ_strat
#print axioms AdalyFormal.M1DStrat.hJ_strat

-- D073 lean/src/DS1.lean:111
#check AdalyFormal.M1DStrat.DParts
#print axioms AdalyFormal.M1DStrat.DParts

-- D074 lean/src/DS1.lean:133
#check AdalyFormal.M1DStrat.dparts_bounds
#print axioms AdalyFormal.M1DStrat.dparts_bounds

-- D075 lean/src/DS1.lean:144
#check AdalyFormal.M1DStrat.dlayerStrat_of_parts
#print axioms AdalyFormal.M1DStrat.dlayerStrat_of_parts

-- D076 lean/src/DY1.lean:63
#check AdalyFormal.M1DStrat.polar_l1_T
#print axioms AdalyFormal.M1DStrat.polar_l1_T

-- D077 lean/src/DY2.lean:65
#check AdalyFormal.M1DStrat.C2row_congr
#print axioms AdalyFormal.M1DStrat.C2row_congr

-- D078 lean/src/DY2.lean:83
#check AdalyFormal.M1DStrat.polar_row_ball
#print axioms AdalyFormal.M1DStrat.polar_row_ball

-- D079 lean/src/DY3.lean:39
#check AdalyFormal.M1DStrat.C2row_level0
#print axioms AdalyFormal.M1DStrat.C2row_level0

-- D080 lean/src/DY3.lean:58
#check AdalyFormal.M1DStrat.delta2_bil
#print axioms AdalyFormal.M1DStrat.delta2_bil

-- D081 lean/src/DY3.lean:158
#check AdalyFormal.M1DStrat.delta2_conj
#print axioms AdalyFormal.M1DStrat.delta2_conj

-- D082 lean/src/DY4a.lean:32
#check AdalyFormal.M1DStrat.GSplit.pert_lower
#print axioms AdalyFormal.M1DStrat.GSplit.pert_lower

-- D083 lean/src/DY4a.lean:40
#check AdalyFormal.M1DStrat.GSplit.pert_E_le
#print axioms AdalyFormal.M1DStrat.GSplit.pert_E_le

-- D084 lean/src/DY4a.lean:55
#check AdalyFormal.M1DStrat.GSplit.pert_sqrtE
#print axioms AdalyFormal.M1DStrat.GSplit.pert_sqrtE

-- D085 lean/src/DY4a.lean:63
#check AdalyFormal.M1DStrat.GSplit.pert_n
#print axioms AdalyFormal.M1DStrat.GSplit.pert_n

-- D086 lean/src/DY4a.lean:72
#check AdalyFormal.M1DStrat.GSplit.pert_EE
#print axioms AdalyFormal.M1DStrat.GSplit.pert_EE

-- D087 lean/src/DY4a.lean:90
#check AdalyFormal.M1DStrat.GSplit.pert_nn
#print axioms AdalyFormal.M1DStrat.GSplit.pert_nn

-- D088 lean/src/DY4b.lean:80
#check AdalyFormal.M1DStrat.CTData.W4_nq
#print axioms AdalyFormal.M1DStrat.CTData.W4_nq

-- D089 lean/src/DrEquiv.lean:33
#check AdalyFormal.D1Residual.GShape
#print axioms AdalyFormal.D1Residual.GShape

-- D090 lean/src/DrEquiv.lean:46
#check AdalyFormal.D1Residual.CRes
#print axioms AdalyFormal.D1Residual.CRes

-- D091 lean/src/DrEquiv.lean:51
#check AdalyFormal.D1Residual.CPen
#print axioms AdalyFormal.D1Residual.CPen

-- D092 lean/src/DrEquiv.lean:57
#check AdalyFormal.D1Residual.guardResidualT_eq_shape
#print axioms AdalyFormal.D1Residual.guardResidualT_eq_shape

-- D093 lean/src/DrEquiv.lean:60
#check AdalyFormal.D1Residual.GShape_imp
#print axioms AdalyFormal.D1Residual.GShape_imp

-- D094 lean/src/DrEquiv.lean:99
#check AdalyFormal.D1Residual.GuardPencilT
#print axioms AdalyFormal.D1Residual.GuardPencilT

-- D095 lean/src/DrEquiv.lean:101
#check AdalyFormal.D1Residual.residualT_iff_pencilT
#print axioms AdalyFormal.D1Residual.residualT_iff_pencilT

-- D096 lean/src/DrEquiv.lean:116
#check AdalyFormal.D1Residual.P428Target8SG_iff_pencilT
#print axioms AdalyFormal.D1Residual.P428Target8SG_iff_pencilT

-- D097 lean/src/DrRed1.lean:36
#check AdalyFormal.D1Residual.Delta2_lit_eq_loc
#print axioms AdalyFormal.D1Residual.Delta2_lit_eq_loc

-- D098 lean/src/DrRed1.lean:52
#check AdalyFormal.D1Residual.G1inv_lit_eq_pencil
#print axioms AdalyFormal.D1Residual.G1inv_lit_eq_pencil

-- D099 lean/src/DrRed1.lean:60
#check AdalyFormal.D1Residual.isUnit_G1inv_lit_iff_pencil
#print axioms AdalyFormal.D1Residual.isUnit_G1inv_lit_iff_pencil

-- D100 lean/src/FE3.lean:188
#check AdalyFormal.FlatExt.flatE_rightInv
#print axioms AdalyFormal.FlatExt.flatE_rightInv

-- D101 lean/src/GCa3L.lean:107
#check AdalyFormal.GaugeCov.D2StepL_gauge
#print axioms AdalyFormal.GaugeCov.D2StepL_gauge

-- D102 lean/src/GCa3L.lean:115
#check AdalyFormal.GaugeCov.C2StepL_gauge
#print axioms AdalyFormal.GaugeCov.C2StepL_gauge

-- D103 lean/src/GCa3L.lean:144
#check AdalyFormal.GaugeCov.C2CompL_gauge
#print axioms AdalyFormal.GaugeCov.C2CompL_gauge

-- D104 lean/src/GCa4.lean:45
#check AdalyFormal.GaugeCov.C2fullOf_gauge
#print axioms AdalyFormal.GaugeCov.C2fullOf_gauge

-- D105 lean/src/GW2.lean:161
#check AdalyFormal.M1GaugeW4.holRegime_of_plaq
#print axioms AdalyFormal.M1GaugeW4.holRegime_of_plaq

-- D106 lean/src/GdGap.lean:56
#check AdalyFormal.D1Guarded.genFormS_collapse_G1inv
#print axioms AdalyFormal.D1Guarded.genFormS_collapse_G1inv

-- D107 lean/src/GdGap.lean:77
#check AdalyFormal.D1Guarded.WellDefAt
#print axioms AdalyFormal.D1Guarded.WellDefAt

-- D108 lean/src/GdGap.lean:81
#check AdalyFormal.D1Guarded.GapAt
#print axioms AdalyFormal.D1Guarded.GapAt

-- D109 lean/src/GdGap.lean:161
#check AdalyFormal.D1Guarded.P428Target8SG2
#print axioms AdalyFormal.D1Guarded.P428Target8SG2

-- D110 lean/src/GdGap.lean:179
#check AdalyFormal.D1Guarded.localised_SG2_holds
#print axioms AdalyFormal.D1Guarded.localised_SG2_holds

-- D111 lean/src/GdGen2.lean:35
#check AdalyFormal.D1Guarded.dataS_C2_eq
#print axioms AdalyFormal.D1Guarded.dataS_C2_eq

-- D112 lean/src/GdGen2.lean:37
#check AdalyFormal.D1Guarded.dataS_Ginv_eq
#print axioms AdalyFormal.D1Guarded.dataS_Ginv_eq

-- D113 lean/src/GdGen2.lean:46
#check AdalyFormal.D1Guarded.V0
#print axioms AdalyFormal.D1Guarded.V0

-- D114 lean/src/GdGen2.lean:66
#check AdalyFormal.D1Guarded.C2full_level0_coord
#print axioms AdalyFormal.D1Guarded.C2full_level0_coord

-- D115 lean/src/GdGen3.lean:30
#check AdalyFormal.D1Guarded.plaq_near_in
#print axioms AdalyFormal.D1Guarded.plaq_near_in

-- D116 lean/src/GdGen3.lean:44
#check AdalyFormal.D1Guarded.JfS_eq_near
#print axioms AdalyFormal.D1Guarded.JfS_eq_near

-- D117 lean/src/GdGen3.lean:66
#check AdalyFormal.D1Guarded.Ginv_eq_on_V
#print axioms AdalyFormal.D1Guarded.Ginv_eq_on_V

-- D118 lean/src/GdGen4.lean:31
#check AdalyFormal.D1Guarded.NG_unit_of_N1
#print axioms AdalyFormal.D1Guarded.NG_unit_of_N1

-- D119 lean/src/GdGen4.lean:50
#check AdalyFormal.D1Guarded.Q_H1_apply
#print axioms AdalyFormal.D1Guarded.Q_H1_apply

-- D120 lean/src/GdGen4.lean:58
#check AdalyFormal.D1Guarded.unit_transfer
#print axioms AdalyFormal.D1Guarded.unit_transfer

-- D121 lean/src/GdGen4.lean:87
#check AdalyFormal.D1Guarded.TwoData.inner_H1_J_eq
#print axioms AdalyFormal.D1Guarded.TwoData.inner_H1_J_eq

-- D122 lean/src/GdGen4.lean:106
#check AdalyFormal.D1Guarded.twoData_lit_loc
#print axioms AdalyFormal.D1Guarded.twoData_lit_loc

-- D123 lean/src/GdGen5.lean:32
#check AdalyFormal.D1Guarded.genFormS_eq_loc
#print axioms AdalyFormal.D1Guarded.genFormS_eq_loc

-- D124 lean/src/GdGen6.lean:32
#check AdalyFormal.D1Guarded.genFormS_collapse_of_not_wd
#print axioms AdalyFormal.D1Guarded.genFormS_collapse_of_not_wd

-- D125 lean/src/GdGen7.lean:32
#check AdalyFormal.D1Guarded.GapAt_of_loc
#print axioms AdalyFormal.D1Guarded.GapAt_of_loc

-- D126 lean/src/GdGen7.lean:72
#check AdalyFormal.D1Guarded.InstIneqSG_general
#print axioms AdalyFormal.D1Guarded.InstIneqSG_general

-- D127 lean/src/GdGen8.lean:30
#check AdalyFormal.D1Guarded.WellDefAt_loc_of_inst
#print axioms AdalyFormal.D1Guarded.WellDefAt_loc_of_inst

-- D128 lean/src/GdGen9.lean:72
#check AdalyFormal.D1Guarded.P428Target8SG_of_residual
#print axioms AdalyFormal.D1Guarded.P428Target8SG_of_residual

-- D129 lean/src/GdR5a.lean:114
#check AdalyFormal.D1Guarded.P428Target8SG_iff_residualT
#print axioms AdalyFormal.D1Guarded.P428Target8SG_iff_residualT

-- D130 lean/src/GdStat.lean:29
#check AdalyFormal.D1Guarded.stat_eq
#print axioms AdalyFormal.D1Guarded.stat_eq

-- D131 lean/src/GdStat.lean:62
#check AdalyFormal.D1Guarded.TwoData
#print axioms AdalyFormal.D1Guarded.TwoData

-- D132 lean/src/GdStat.lean:73
#check AdalyFormal.D1Guarded.TwoData.H_eq
#print axioms AdalyFormal.D1Guarded.TwoData.H_eq

-- D133 lean/src/GdStat.lean:83
#check AdalyFormal.D1Guarded.TwoData.Delta2_eq
#print axioms AdalyFormal.D1Guarded.TwoData.Delta2_eq

-- D134 lean/src/GdStat.lean:101
#check AdalyFormal.D1Guarded.TwoData.G1inv_eq_on
#print axioms AdalyFormal.D1Guarded.TwoData.G1inv_eq_on

-- D135 lean/src/GdStat.lean:109
#check AdalyFormal.D1Guarded.TwoData.N1inv_H1_eq
#print axioms AdalyFormal.D1Guarded.TwoData.N1inv_H1_eq

-- D136 lean/src/M1B.lean:151
#check AdalyFormal.M1.wnormSq
#print axioms AdalyFormal.M1.wnormSq

-- D137 lean/src/M1B.lean:155
#check AdalyFormal.M1.DLayerStrat
#print axioms AdalyFormal.M1.DLayerStrat

-- D138 lean/src/MA13.lean:124
#check AdalyFormal.M1Num.cw_uniform
#print axioms AdalyFormal.M1Num.cw_uniform

-- D139 lean/src/MA18.lean:50
#check AdalyFormal.M1Assembly.cwW4_lower
#print axioms AdalyFormal.M1Assembly.cwW4_lower

-- D140 lean/src/MA7.lean:38
#check AdalyFormal.M1Assembly.ginv_eq_Fform
#print axioms AdalyFormal.M1Assembly.ginv_eq_Fform

-- D141 lean/src/MI18.lean:124
#check AdalyFormal.M1IMS.ginv_form
#print axioms AdalyFormal.M1IMS.ginv_form

-- D142 lean/src/MI2.lean:133
#check AdalyFormal.M1IMS.PatchCoercive
#print axioms AdalyFormal.M1IMS.PatchCoercive

-- D143 lean/src/MI2.lean:141
#check AdalyFormal.M1IMS.GinvIMS
#print axioms AdalyFormal.M1IMS.GinvIMS

-- D144 lean/src/MI2.lean:185
#check AdalyFormal.M1IMS.ginv_weighted_coercive_of
#print axioms AdalyFormal.M1IMS.ginv_weighted_coercive_of

-- D145 lean/src/MI21.lean:32
#check AdalyFormal.M1IMS.wnormSq_ge
#print axioms AdalyFormal.M1IMS.wnormSq_ge

-- D146 lean/src/MI21.lean:51
#check AdalyFormal.M1IMS.G1inv_coercive_strat
#print axioms AdalyFormal.M1IMS.G1inv_coercive_strat

-- D147 lean/src/MI21.lean:68
#check AdalyFormal.M1IMS.G1inv_coercive_plain
#print axioms AdalyFormal.M1IMS.G1inv_coercive_plain

-- D148 lean/src/MI21.lean:86
#check AdalyFormal.M1IMS.units_strat
#print axioms AdalyFormal.M1IMS.units_strat

-- D149 lean/src/MI22.lean:71
#check AdalyFormal.M1IMS.ginvIMS_of
#print axioms AdalyFormal.M1IMS.ginvIMS_of

-- D150 lean/src/MI22.lean:172
#check AdalyFormal.M1IMS.ginv_weighted_coercive
#print axioms AdalyFormal.M1IMS.ginv_weighted_coercive

-- D151 lean/src/MI28.lean:85
#check AdalyFormal.M1IMS.ginv_weighted_coercive_M1
#print axioms AdalyFormal.M1IMS.ginv_weighted_coercive_M1

-- D152 lean/src/MI33.lean:64
#check AdalyFormal.M1IMS.ginv_weighted_coercive_full
#print axioms AdalyFormal.M1IMS.ginv_weighted_coercive_full

-- D153 lean/src/MI33.lean:95
#check AdalyFormal.M1IMS.wellDef_strat
#print axioms AdalyFormal.M1IMS.wellDef_strat

-- D154 lean/src/MI33.lean:131
#check AdalyFormal.M1IMS.wellDef_strat_small
#print axioms AdalyFormal.M1IMS.wellDef_strat_small

-- D155 lean/src/MI34.lean:50
#check AdalyFormal.M1IMS.ginv_congr_U
#print axioms AdalyFormal.M1IMS.ginv_congr_U

-- D156 lean/src/MI34.lean:74
#check AdalyFormal.M1IMS.ginv_weighted_coercive_loc
#print axioms AdalyFormal.M1IMS.ginv_weighted_coercive_loc

-- D157 lean/src/MI34.lean:107
#check AdalyFormal.M1IMS.wellDef_strat_loc
#print axioms AdalyFormal.M1IMS.wellDef_strat_loc

-- D158 lean/src/MR2.lean:95
#check AdalyFormal.M2Route.patchCoercive_charts
#print axioms AdalyFormal.M2Route.patchCoercive_charts

-- D159 lean/src/MR2.lean:183
#check AdalyFormal.M2Route.patchCoercive_charts_exists
#print axioms AdalyFormal.M2Route.patchCoercive_charts_exists

-- D160 lean/src/MXQ_A.lean:31
#check MXQ.Total.ClassFamT
#print axioms MXQ.Total.ClassFamT

-- D161 lean/src/MXQ_A.lean:44
#check MXQ.Total.BallChartsGT
#print axioms MXQ.Total.BallChartsGT

-- D162 lean/src/MXQ_A.lean:50
#check MXQ.Total.BallChartsT
#print axioms MXQ.Total.BallChartsT

-- D163 lean/src/MXQ_A.lean:56
#check MXQ.Total.FieldsKT
#print axioms MXQ.Total.FieldsKT

-- D164 lean/src/MXQ_A.lean:68
#check MXQ.Total.ClassRightInvCovT
#print axioms MXQ.Total.ClassRightInvCovT

-- D165 lean/src/MXQ_A.lean:82
#check MXQ.Total.ClassRightInvT
#print axioms MXQ.Total.ClassRightInvT

-- D166 lean/src/MXQ_A.lean:96
#check MXQ.Total.OpLayerThickT
#print axioms MXQ.Total.OpLayerThickT

-- D167 lean/src/MXQ_AC_MZ3.lean:42
#check MXQ.M2DLayer.Jf_splitACΦ
#print axioms MXQ.M2DLayer.Jf_splitACΦ

-- D168 lean/src/MXQ_AC_MZ5.lean:30
#check MXQ.M2DLayer.dlayerStrat_classACΦ
#print axioms MXQ.M2DLayer.dlayerStrat_classACΦ

-- D169 lean/src/MXQ_AC_MZ5.lean:72
#check MXQ.M2DLayer.DLayerObligationClassACΦ
#print axioms MXQ.M2DLayer.DLayerObligationClassACΦ

-- D170 lean/src/MXQ_AC_MZ5.lean:82
#check MXQ.M2DLayer.dlayerObligationClass_holdsACΦ
#print axioms MXQ.M2DLayer.dlayerObligationClass_holdsACΦ

-- D171 lean/src/MXQ_AC_OL10.lean:52
#check MXQ.M2OpLayer.hH1L2_cfgACΦ
#print axioms MXQ.M2OpLayer.hH1L2_cfgACΦ

-- D172 lean/src/MXQ_AC_OL8.lean:39
#check MXQ.M2OpLayer.psi_classACΦ
#print axioms MXQ.M2OpLayer.psi_classACΦ

-- D173 lean/src/MXQ_AC_OL8.lean:81
#check MXQ.M2OpLayer.delta2_classACΦ
#print axioms MXQ.M2OpLayer.delta2_classACΦ

-- D174 lean/src/MXQ_AC_SK3.lean:34
#check MXQ.M2Skel.holRegime_rho1ACΦ
#print axioms MXQ.M2Skel.holRegime_rho1ACΦ

-- D175 lean/src/MXQ_AU_SK3.lean:34
#check MXQ.M2Skel.w4_classUΦ
#print axioms MXQ.M2Skel.w4_classUΦ

-- D176 lean/src/MXQ_B.lean:43
#check MXQ.Total.ballChartsT_of_G
#print axioms MXQ.Total.ballChartsT_of_G

-- D177 lean/src/MXQ_B.lean:101
#check MXQ.Total.fieldsKT_of_ball
#print axioms MXQ.Total.fieldsKT_of_ball

-- D178 lean/src/MXQ_B.lean:223
#check MXQ.Total.classRightInvCovT
#print axioms MXQ.Total.classRightInvCovT

-- D179 lean/src/MXQ_B.lean:286
#check MXQ.Total.classRightInvT_of_cov
#print axioms MXQ.Total.classRightInvT_of_cov

-- D180 lean/src/MXQ_B.lean:456
#check MXQ.Total.opLayerThickT_of
#print axioms MXQ.Total.opLayerThickT_of

-- D181 lean/src/MXQ_Br.lean:19
#check MXQ.Total.famPhi
#print axioms MXQ.Total.famPhi

-- D182 lean/src/MXQ_Br.lean:21
#check MXQ.Total.classCoupledΦ_toQ
#print axioms MXQ.Total.classCoupledΦ_toQ

-- D183 lean/src/MXQ_Br.lean:31
#check MXQ.Total.P428Target8Family.toMixed
#print axioms MXQ.Total.P428Target8Family.toMixed

-- D184 lean/src/MXQ_Br.lean:38
#check MXQ.Total.p428Target8Mixed_fromFamily
#print axioms MXQ.Total.p428Target8Mixed_fromFamily

-- D185 lean/src/MXQ_Br.lean:41
#check MXQ.Total.family_hyps_nonvacuous
#print axioms MXQ.Total.family_hyps_nonvacuous

-- D186 lean/src/MXQ_C.lean:52
#check MXQ.Total.dlayer_explicitΦ
#print axioms MXQ.Total.dlayer_explicitΦ

-- D187 lean/src/MXQ_C.lean:92
#check MXQ.Total.strong_coreTΦ
#print axioms MXQ.Total.strong_coreTΦ

-- D188 lean/src/MXQ_C.lean:375
#check MXQ.Total.strong_coreTM
#print axioms MXQ.Total.strong_coreTM

-- D189 lean/src/MXQ_F.lean:24
#check MXQ.Total.CoercG8AtWDFamily
#print axioms MXQ.Total.CoercG8AtWDFamily

-- D190 lean/src/MXQ_F.lean:34
#check MXQ.Total.P428Target8Family
#print axioms MXQ.Total.P428Target8Family

-- D191 lean/src/MXQ_F.lean:41
#check MXQ.Total.fieldsTQ
#print axioms MXQ.Total.fieldsTQ

-- D192 lean/src/MXQ_F.lean:48
#check MXQ.Total.p428Target8Family
#print axioms MXQ.Total.p428Target8Family

-- D193 lean/src/MXQ_Thin.lean:218
#check MXQ.Thin.unitReg_of_classHQ
#print axioms MXQ.Thin.unitReg_of_classHQ

-- D194 lean/src/MXQ_Tor.lean:31
#check MXQ.Total.IsClassCubeF
#print axioms MXQ.Total.IsClassCubeF

-- D195 lean/src/MXQ_Tor.lean:36
#check MXQ.Total.ClassCoupledF
#print axioms MXQ.Total.ClassCoupledF

-- D196 lean/src/MXQ_Tor.lean:58
#check MXQ.Total.P428Target8FamilyTorus
#print axioms MXQ.Total.P428Target8FamilyTorus

-- D197 lean/src/MXQ_Tor.lean:72
#check MXQ.Total.p428Target8FamilyTorus
#print axioms MXQ.Total.p428Target8FamilyTorus

-- D198 lean/src/MX_A.lean:30
#check MXP.Total.ClassFamT
#print axioms MXP.Total.ClassFamT

-- D199 lean/src/MX_A.lean:43
#check MXP.Total.BallChartsGT
#print axioms MXP.Total.BallChartsGT

-- D200 lean/src/MX_A.lean:49
#check MXP.Total.BallChartsT
#print axioms MXP.Total.BallChartsT

-- D201 lean/src/MX_A.lean:55
#check MXP.Total.FieldsKT
#print axioms MXP.Total.FieldsKT

-- D202 lean/src/MX_A.lean:67
#check MXP.Total.ClassRightInvCovT
#print axioms MXP.Total.ClassRightInvCovT

-- D203 lean/src/MX_A.lean:81
#check MXP.Total.ClassRightInvT
#print axioms MXP.Total.ClassRightInvT

-- D204 lean/src/MX_A.lean:95
#check MXP.Total.OpLayerThickT
#print axioms MXP.Total.OpLayerThickT

-- D205 lean/src/MX_AC_MZ3.lean:40
#check MXP.M2DLayer.Jf_splitACΦ
#print axioms MXP.M2DLayer.Jf_splitACΦ

-- D206 lean/src/MX_AC_MZ5.lean:29
#check MXP.M2DLayer.dlayerStrat_classACΦ
#print axioms MXP.M2DLayer.dlayerStrat_classACΦ

-- D207 lean/src/MX_AC_MZ5.lean:71
#check MXP.M2DLayer.DLayerObligationClassACΦ
#print axioms MXP.M2DLayer.DLayerObligationClassACΦ

-- D208 lean/src/MX_AC_MZ5.lean:81
#check MXP.M2DLayer.dlayerObligationClass_holdsACΦ
#print axioms MXP.M2DLayer.dlayerObligationClass_holdsACΦ

-- D209 lean/src/MX_AC_OL10.lean:51
#check MXP.M2OpLayer.hH1L2_cfgACΦ
#print axioms MXP.M2OpLayer.hH1L2_cfgACΦ

-- D210 lean/src/MX_AC_OL8.lean:38
#check MXP.M2OpLayer.psi_classACΦ
#print axioms MXP.M2OpLayer.psi_classACΦ

-- D211 lean/src/MX_AC_OL8.lean:80
#check MXP.M2OpLayer.delta2_classACΦ
#print axioms MXP.M2OpLayer.delta2_classACΦ

-- D212 lean/src/MX_AC_SK3.lean:33
#check MXP.M2Skel.holRegime_rho1ACΦ
#print axioms MXP.M2Skel.holRegime_rho1ACΦ

-- D213 lean/src/MX_AU_SK3.lean:33
#check MXP.M2Skel.w4_classUΦ
#print axioms MXP.M2Skel.w4_classUΦ

-- D214 lean/src/MX_B.lean:41
#check MXP.Total.ballChartsT_of_G
#print axioms MXP.Total.ballChartsT_of_G

-- D215 lean/src/MX_B.lean:99
#check MXP.Total.fieldsKT_of_ball
#print axioms MXP.Total.fieldsKT_of_ball

-- D216 lean/src/MX_B.lean:221
#check MXP.Total.classRightInvCovT
#print axioms MXP.Total.classRightInvCovT

-- D217 lean/src/MX_B.lean:284
#check MXP.Total.classRightInvT_of_cov
#print axioms MXP.Total.classRightInvT_of_cov

-- D218 lean/src/MX_B.lean:454
#check MXP.Total.opLayerThickT_of
#print axioms MXP.Total.opLayerThickT_of

-- D219 lean/src/MX_C.lean:51
#check MXP.Total.dlayer_explicitΦ
#print axioms MXP.Total.dlayer_explicitΦ

-- D220 lean/src/MX_C.lean:91
#check MXP.Total.strong_coreTΦ
#print axioms MXP.Total.strong_coreTΦ

-- D221 lean/src/MX_C.lean:369
#check MXP.Total.strong_coreTM
#print axioms MXP.Total.strong_coreTM

-- D222 lean/src/MX_F.lean:29
#check MXP.Total.CoercG8AtWDMixed
#print axioms MXP.Total.CoercG8AtWDMixed

-- D223 lean/src/MX_F.lean:39
#check MXP.Total.P428Target8Mixed
#print axioms MXP.Total.P428Target8Mixed

-- D224 lean/src/MX_F.lean:46
#check MXP.Total.fieldsTM
#print axioms MXP.Total.fieldsTM

-- D225 lean/src/MX_F.lean:53
#check MXP.Total.p428Target8Mixed
#print axioms MXP.Total.p428Target8Mixed

-- D226 lean/src/MX_F.lean:62
#check MXP.Total.P428Target8Mixed.toTotal
#print axioms MXP.Total.P428Target8Mixed.toTotal

-- D227 lean/src/MX_F.lean:70
#check MXP.Total.p428Target8Total_fromMixed
#print axioms MXP.Total.p428Target8Total_fromMixed

-- D228 lean/src/MX_Thin.lean:153
#check MXP.Thin.unitReg_of_classHΦ
#print axioms MXP.Thin.unitReg_of_classHΦ

-- D229 lean/src/MZ3.lean:51
#check AdalyFormal.M2DLayer.Jf_covered
#print axioms AdalyFormal.M2DLayer.Jf_covered

-- D230 lean/src/MZ3.lean:152
#check AdalyFormal.M2DLayer.Jf_split
#print axioms AdalyFormal.M2DLayer.Jf_split

-- D231 lean/src/MZ4.lean:55
#check AdalyFormal.M2DLayer.Ageo
#print axioms AdalyFormal.M2DLayer.Ageo

-- D232 lean/src/MZ4.lean:151
#check AdalyFormal.M2DLayer.col_class
#print axioms AdalyFormal.M2DLayer.col_class

-- D233 lean/src/MZ5.lean:35
#check AdalyFormal.M2DLayer.OpLayer
#print axioms AdalyFormal.M2DLayer.OpLayer

-- D234 lean/src/MZ5.lean:70
#check AdalyFormal.M2DLayer.dlayerStrat_class
#print axioms AdalyFormal.M2DLayer.dlayerStrat_class

-- D235 lean/src/MZ5.lean:112
#check AdalyFormal.M2DLayer.DLayerObligationClass
#print axioms AdalyFormal.M2DLayer.DLayerObligationClass

-- D236 lean/src/MZ5.lean:122
#check AdalyFormal.M2DLayer.dlayerObligationClass_holds
#print axioms AdalyFormal.M2DLayer.dlayerObligationClass_holds

-- D237 lean/src/OL10.lean:50
#check AdalyFormal.M2OpLayer.hH1L2_cfg
#print axioms AdalyFormal.M2OpLayer.hH1L2_cfg

-- D238 lean/src/OL12.lean:43
#check AdalyFormal.M2OpLayer.opLayerThick_of
#print axioms AdalyFormal.M2OpLayer.opLayerThick_of

-- D239 lean/src/OL13.lean:31
#check AdalyFormal.M2OpLayer.class_coreK_RI
#print axioms AdalyFormal.M2OpLayer.class_coreK_RI

-- D240 lean/src/OL14.lean:168
#check AdalyFormal.M1DStrat.ginv_upper_cov
#print axioms AdalyFormal.M1DStrat.ginv_upper_cov

-- D241 lean/src/OL14.lean:207
#check AdalyFormal.M1DStrat.hext_of_rightinv_cov
#print axioms AdalyFormal.M1DStrat.hext_of_rightinv_cov

-- D242 lean/src/OL2.lean:123
#check AdalyFormal.M2OpLayer.C2full_strat12
#print axioms AdalyFormal.M2OpLayer.C2full_strat12

-- D243 lean/src/OL2.lean:258
#check AdalyFormal.M2OpLayer.C2row_congr_U
#print axioms AdalyFormal.M2OpLayer.C2row_congr_U

-- D244 lean/src/OL2.lean:297
#check AdalyFormal.M2OpLayer.hC2_class
#print axioms AdalyFormal.M2OpLayer.hC2_class

-- D245 lean/src/OL5.lean:258
#check AdalyFormal.M1DStrat.hHB_genuineR
#print axioms AdalyFormal.M1DStrat.hHB_genuineR

-- D246 lean/src/OL6.lean:54
#check AdalyFormal.M1DStrat.H_l2_colR
#print axioms AdalyFormal.M1DStrat.H_l2_colR

-- D247 lean/src/OL7.lean:68
#check AdalyFormal.M1DStrat.G1_symmR
#print axioms AdalyFormal.M1DStrat.G1_symmR

-- D248 lean/src/OL7.lean:75
#check AdalyFormal.M1DStrat.G1_coerR
#print axioms AdalyFormal.M1DStrat.G1_coerR

-- D249 lean/src/OL7.lean:89
#check AdalyFormal.M1DStrat.G1_unitR
#print axioms AdalyFormal.M1DStrat.G1_unitR

-- D250 lean/src/OL7.lean:106
#check AdalyFormal.M1DStrat.N1_unitR
#print axioms AdalyFormal.M1DStrat.N1_unitR

-- D251 lean/src/OL7.lean:213
#check AdalyFormal.M1DStrat.H1_l2_colR
#print axioms AdalyFormal.M1DStrat.H1_l2_colR

-- D252 lean/src/OL7.lean:290
#check AdalyFormal.M1DStrat.H1_eqR
#print axioms AdalyFormal.M1DStrat.H1_eqR

-- D253 lean/src/OL8.lean:36
#check AdalyFormal.M2OpLayer.psi_class
#print axioms AdalyFormal.M2OpLayer.psi_class

-- D254 lean/src/OL8.lean:78
#check AdalyFormal.M2OpLayer.delta2_class
#print axioms AdalyFormal.M2OpLayer.delta2_class

-- D255 lean/src/OL9.lean:37
#check AdalyFormal.M2OpLayer.qs_inj_of_hext
#print axioms AdalyFormal.M2OpLayer.qs_inj_of_hext

-- D256 lean/src/OL9.lean:69
#check AdalyFormal.M2OpLayer.hHL2_cfg
#print axioms AdalyFormal.M2OpLayer.hHL2_cfg

-- D257 lean/src/PB1.lean:32
#check AdalyFormal.PortSlice.G1inv_form_eq_Phi
#print axioms AdalyFormal.PortSlice.G1inv_form_eq_Phi

-- D258 lean/src/PSC10e.lean:32
#check AdalyFormal.ScaledCoercivity.G1inv_coercive_explicit2
#print axioms AdalyFormal.ScaledCoercivity.G1inv_coercive_explicit2

-- D259 lean/src/PSC10e.lean:110
#check AdalyFormal.ScaledCoercivity.scaled_G1inv2
#print axioms AdalyFormal.ScaledCoercivity.scaled_G1inv2

-- D260 lean/src/PSC10f.lean:103
#check AdalyFormal.ScaledCoercivity.scaled_G1inv2_simple
#print axioms AdalyFormal.ScaledCoercivity.scaled_G1inv2_simple

-- D261 lean/src/R2Algebra.lean:145
#check AdalyFormal.IngredientFamilyR2.BaseDataS.Ginv
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.Ginv

-- D262 lean/src/R2Algebra.lean:147
#check AdalyFormal.IngredientFamilyR2.BaseDataS.G
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.G

-- D263 lean/src/R2Algebra.lean:149
#check AdalyFormal.IngredientFamilyR2.BaseDataS.H
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.H

-- D264 lean/src/R2Algebra.lean:157
#check AdalyFormal.IngredientFamilyR2.BaseDataS.IsG1inv
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.IsG1inv

-- D265 lean/src/R2Algebra.lean:167
#check AdalyFormal.IngredientFamilyR2.BaseDataS.inner_Ginv
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.inner_Ginv

-- D266 lean/src/R2Algebra.lean:173
#check AdalyFormal.IngredientFamilyR2.BaseDataS.K_eq
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.K_eq

-- D267 lean/src/R2Algebra.lean:176
#check AdalyFormal.IngredientFamilyR2.BaseDataS.Ginv_symm
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.Ginv_symm

-- D268 lean/src/R2Algebra.lean:186
#check AdalyFormal.IngredientFamilyR2.BaseDataS.exists_G1inv
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.exists_G1inv

-- D269 lean/src/R2Algebra.lean:205
#check AdalyFormal.IngredientFamilyR2.BaseDataS.G1inv_unique
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.G1inv_unique

-- D270 lean/src/R2Algebra.lean:212
#check AdalyFormal.IngredientFamilyR2.BaseDataS.delta2Bil
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.delta2Bil

-- D271 lean/src/R2Algebra.lean:220
#check AdalyFormal.IngredientFamilyR2.BaseDataS.Delta2
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.Delta2

-- D272 lean/src/R2Algebra.lean:222
#check AdalyFormal.IngredientFamilyR2.BaseDataS.Delta2_spec
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.Delta2_spec

-- D273 lean/src/R2Algebra.lean:230
#check AdalyFormal.IngredientFamilyR2.BaseDataS.isG1inv_sub
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.isG1inv_sub

-- D274 lean/src/R2Algebra.lean:238
#check AdalyFormal.IngredientFamilyR2.BaseDataS.G1inv_coercive
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.G1inv_coercive

-- D275 lean/src/R2Algebra.lean:258
#check AdalyFormal.IngredientFamilyR2.isUnit_Q_inv_Qs
#print axioms AdalyFormal.IngredientFamilyR2.isUnit_Q_inv_Qs

-- D276 lean/src/R2Algebra.lean:307
#check AdalyFormal.IngredientFamilyR2.BaseDataS.G1
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.G1

-- D277 lean/src/R2Algebra.lean:308
#check AdalyFormal.IngredientFamilyR2.BaseDataS.H1
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.H1

-- D278 lean/src/R2Algebra.lean:311
#check AdalyFormal.IngredientFamilyR2.BaseDataS.QG1Qs_isUnit
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.QG1Qs_isUnit

-- D279 lean/src/R2Algebra.lean:318
#check AdalyFormal.IngredientFamilyR2.BaseDataS.QG1Qs_isUnit_of_small
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.QG1Qs_isUnit_of_small

-- D280 lean/src/R2Algebra.lean:330
#check AdalyFormal.IngredientFamilyR2.inverse_sub_eq_tsum
#print axioms AdalyFormal.IngredientFamilyR2.inverse_sub_eq_tsum

-- D281 lean/src/R2RawX.lean:265
#check AdalyFormal.IngredientFamilyR2.C2CompX_succ
#print axioms AdalyFormal.IngredientFamilyR2.C2CompX_succ

-- D282 lean/src/RC2.lean:60
#check AdalyFormal.ReadsetComplete.QlinCompL_eq_compQ
#print axioms AdalyFormal.ReadsetComplete.QlinCompL_eq_compQ

-- D283 lean/src/RC2.lean:85
#check AdalyFormal.ReadsetComplete.r8Steps_local
#print axioms AdalyFormal.ReadsetComplete.r8Steps_local

-- D284 lean/src/RI2.lean:56
#check AdalyFormal.M2RightInv.Dvec_supp
#print axioms AdalyFormal.M2RightInv.Dvec_supp

-- D285 lean/src/RI2.lean:64
#check AdalyFormal.M2RightInv.Tvec_supp
#print axioms AdalyFormal.M2RightInv.Tvec_supp

-- D286 lean/src/RI2.lean:134
#check AdalyFormal.M2RightInv.Tlin_rightInv
#print axioms AdalyFormal.M2RightInv.Tlin_rightInv

-- D287 lean/src/RI5.lean:62
#check AdalyFormal.M2RightInv.num_RI
#print axioms AdalyFormal.M2RightInv.num_RI

-- D288 lean/src/RI5.lean:165
#check AdalyFormal.M2RightInv.rightInv_cfg
#print axioms AdalyFormal.M2RightInv.rightInv_cfg

-- D289 lean/src/RI5.lean:237
#check AdalyFormal.M2RightInv.classRightInvCov
#print axioms AdalyFormal.M2RightInv.classRightInvCov

-- D290 lean/src/RI5.lean:283
#check AdalyFormal.M2RightInv.classRightInv
#print axioms AdalyFormal.M2RightInv.classRightInv

-- D291 lean/src/RI6.lean:35
#check AdalyFormal.M2RightInv.thin_core_RI
#print axioms AdalyFormal.M2RightInv.thin_core_RI

-- D292 lean/src/RI6.lean:305
#check AdalyFormal.M2RightInv.thinTori_RI
#print axioms AdalyFormal.M2RightInv.thinTori_RI

-- D293 lean/src/RI6.lean:313
#check AdalyFormal.M2RightInv.p428Target8_of_rightInvCov
#print axioms AdalyFormal.M2RightInv.p428Target8_of_rightInvCov

-- D294 lean/src/RI6.lean:323
#check AdalyFormal.M2RightInv.p428Target8
#print axioms AdalyFormal.M2RightInv.p428Target8

-- D295 lean/src/SK2.lean:39
#check AdalyFormal.M2Skel.chart_core_class
#print axioms AdalyFormal.M2Skel.chart_core_class

-- D296 lean/src/SK3.lean:40
#check AdalyFormal.M2Skel.holRegime_rho1
#print axioms AdalyFormal.M2Skel.holRegime_rho1

-- D297 lean/src/SK3.lean:135
#check AdalyFormal.M2Skel.w4_class
#print axioms AdalyFormal.M2Skel.w4_class

-- D298 lean/src/SK5.lean:49
#check AdalyFormal.M2Skel.config_inst_class
#print axioms AdalyFormal.M2Skel.config_inst_class

-- D299 lean/src/SL1.lean:58
#check AdalyFormal.SliceCoerc.ext_of_rightInverse
#print axioms AdalyFormal.SliceCoerc.ext_of_rightInverse

-- D300 lean/src/TL0.lean:133
#check AdalyFormal.TowerLoc.rawStep_congr_al
#print axioms AdalyFormal.TowerLoc.rawStep_congr_al

-- D301 lean/src/TL0.lean:152
#check AdalyFormal.TowerLoc.qStepComp_congr_bg_al
#print axioms AdalyFormal.TowerLoc.qStepComp_congr_bg_al

-- D302 lean/src/TL1.lean:65
#check AdalyFormal.TowerLoc.step_cut_agree
#print axioms AdalyFormal.TowerLoc.step_cut_agree

-- D303 lean/src/TL11e.lean:17
#check AdalyFormal.Thin.D2StepL_row_nat
#print axioms AdalyFormal.Thin.D2StepL_row_nat

-- D304 lean/src/TL11f.lean:59
#check AdalyFormal.Thin.D2StepL_row_natT
#print axioms AdalyFormal.Thin.D2StepL_row_natT

-- D305 lean/src/TL12c.lean:40
#check AdalyFormal.Thin.C2fullOf_apply
#print axioms AdalyFormal.Thin.C2fullOf_apply

-- D306 lean/src/TL12c.lean:43
#check AdalyFormal.Thin.C2fullOf_nat
#print axioms AdalyFormal.Thin.C2fullOf_nat

-- D307 lean/src/TL13b.lean:67
#check AdalyFormal.Thin.HDesc.inverse
#print axioms AdalyFormal.Thin.HDesc.inverse

-- D308 lean/src/TL15a.lean:50
#check AdalyFormal.Thin.BDLink.ginv
#print axioms AdalyFormal.Thin.BDLink.ginv

-- D309 lean/src/TL15b.lean:64
#check AdalyFormal.Thin.BDLink.G
#print axioms AdalyFormal.Thin.BDLink.G

-- D310 lean/src/TL15b.lean:67
#check AdalyFormal.Thin.BDLink.H
#print axioms AdalyFormal.Thin.BDLink.H

-- D311 lean/src/TL15b.lean:98
#check AdalyFormal.Thin.BDLink.G1inv
#print axioms AdalyFormal.Thin.BDLink.G1inv

-- D312 lean/src/TL15c.lean:31
#check AdalyFormal.Thin.BDLink.H1
#print axioms AdalyFormal.Thin.BDLink.H1

-- D313 lean/src/TL18a.lean:23
#check AdalyFormal.Thin.C2tilde_nat
#print axioms AdalyFormal.Thin.C2tilde_nat

-- D314 lean/src/TL19c.lean:22
#check AdalyFormal.Thin.C2full_E1
#print axioms AdalyFormal.Thin.C2full_E1

-- D315 lean/src/TL19c.lean:31
#check AdalyFormal.Thin.C2full_equi
#print axioms AdalyFormal.Thin.C2full_equi

-- D316 lean/src/TL22a.lean:33
#check AdalyFormal.Thin.guardsUnit_of_fields
#print axioms AdalyFormal.Thin.guardsUnit_of_fields

-- D317 lean/src/TL22a.lean:74
#check AdalyFormal.Thin.unitReg_of_class
#print axioms AdalyFormal.Thin.unitReg_of_class

-- D318 lean/src/TL22a.lean:88
#check AdalyFormal.Thin.coverHyp_of_wd
#print axioms AdalyFormal.Thin.coverHyp_of_wd

-- D319 lean/src/TL3c.lean:53
#check AdalyFormal.Thin.isUnit_of_desc
#print axioms AdalyFormal.Thin.isUnit_of_desc

-- D320 lean/src/TL3c.lean:71
#check AdalyFormal.Thin.Desc.inverse
#print axioms AdalyFormal.Thin.Desc.inverse

-- D321 lean/src/TT_A.lean:29
#check AdalyFormal.Total.ClassFamT
#print axioms AdalyFormal.Total.ClassFamT

-- D322 lean/src/TT_A.lean:42
#check AdalyFormal.Total.BallChartsGT
#print axioms AdalyFormal.Total.BallChartsGT

-- D323 lean/src/TT_A.lean:48
#check AdalyFormal.Total.BallChartsT
#print axioms AdalyFormal.Total.BallChartsT

-- D324 lean/src/TT_A.lean:54
#check AdalyFormal.Total.FieldsKT
#print axioms AdalyFormal.Total.FieldsKT

-- D325 lean/src/TT_A.lean:66
#check AdalyFormal.Total.ClassRightInvCovT
#print axioms AdalyFormal.Total.ClassRightInvCovT

-- D326 lean/src/TT_A.lean:80
#check AdalyFormal.Total.ClassRightInvT
#print axioms AdalyFormal.Total.ClassRightInvT

-- D327 lean/src/TT_A.lean:94
#check AdalyFormal.Total.OpLayerThickT
#print axioms AdalyFormal.Total.OpLayerThickT

-- D328 lean/src/TT_B.lean:48
#check AdalyFormal.Total.ballChartsT_of_G
#print axioms AdalyFormal.Total.ballChartsT_of_G

-- D329 lean/src/TT_B.lean:106
#check AdalyFormal.Total.fieldsKT_of_ball
#print axioms AdalyFormal.Total.fieldsKT_of_ball

-- D330 lean/src/TT_B.lean:228
#check AdalyFormal.Total.classRightInvCovT
#print axioms AdalyFormal.Total.classRightInvCovT

-- D331 lean/src/TT_B.lean:291
#check AdalyFormal.Total.classRightInvT_of_cov
#print axioms AdalyFormal.Total.classRightInvT_of_cov

-- D332 lean/src/TT_B.lean:461
#check AdalyFormal.Total.opLayerThickT_of
#print axioms AdalyFormal.Total.opLayerThickT_of

-- D333 lean/src/TT_C.lean:39
#check AdalyFormal.Total.strong_coreT
#print axioms AdalyFormal.Total.strong_coreT

-- D334 lean/src/TT_C.lean:317
#check AdalyFormal.Total.strong_coreTC
#print axioms AdalyFormal.Total.strong_coreTC

-- D335 lean/src/TT_F.lean:29
#check AdalyFormal.Total.P428Target8Total
#print axioms AdalyFormal.Total.P428Target8Total

-- D336 lean/src/TT_F.lean:36
#check AdalyFormal.Total.fieldsT
#print axioms AdalyFormal.Total.fieldsT

-- D337 lean/src/TT_F.lean:43
#check AdalyFormal.Total.p428Target8Total
#print axioms AdalyFormal.Total.p428Target8Total

-- D338 lean/src/TT_F.lean:52
#check AdalyFormal.Total.P428Target8Total.toMax
#print axioms AdalyFormal.Total.P428Target8Total.toMax

-- D339 lean/src/TT_F.lean:58
#check AdalyFormal.Total.P428Target8Total.toMaxAllC
#print axioms AdalyFormal.Total.P428Target8Total.toMaxAllC

-- D340 lean/src/TT_F.lean:66
#check AdalyFormal.Total.P428Target8Total.toAllC
#print axioms AdalyFormal.Total.P428Target8Total.toAllC

-- D341 lean/src/TT_F.lean:70
#check AdalyFormal.Total.P428Target8Total.toTarget
#print axioms AdalyFormal.Total.P428Target8Total.toTarget

-- D342 lean/src/TT_F.lean:73
#check AdalyFormal.Total.p428Target8Max_fromTotal
#print axioms AdalyFormal.Total.p428Target8Max_fromTotal

-- D343 lean/src/TT_F.lean:74
#check AdalyFormal.Total.p428Target8MaxAllC_fromTotal
#print axioms AdalyFormal.Total.p428Target8MaxAllC_fromTotal

-- D344 lean/src/TT_F.lean:75
#check AdalyFormal.Total.p428Target8AllC_fromTotal
#print axioms AdalyFormal.Total.p428Target8AllC_fromTotal

-- D345 lean/src/TT_F.lean:76
#check AdalyFormal.Total.p428Target8_fromTotal
#print axioms AdalyFormal.Total.p428Target8_fromTotal

-- D346 lean/src/TT_Z.lean:232
#check AdalyFormal.Total.ballChartsGT_proved
#print axioms AdalyFormal.Total.ballChartsGT_proved

-- D347 lean/src/UMC.lean:34
#check AdalyFormal.UnifMax.a1D
#print axioms AdalyFormal.UnifMax.a1D

-- D348 lean/src/UMC.lean:38
#check AdalyFormal.UnifMax.a1D_pos
#print axioms AdalyFormal.UnifMax.a1D_pos

-- D349 lean/src/UMC.lean:45
#check AdalyFormal.UnifMax.dlayer_explicit
#print axioms AdalyFormal.UnifMax.dlayer_explicit

-- D350 lean/src/W2C1.lean:71
#check AdalyFormal.M1W2.curl_congr_U
#print axioms AdalyFormal.M1W2.curl_congr_U

-- D351 lean/src/W2C1.lean:78
#check AdalyFormal.M1W2.Qcomposite_congr_in
#print axioms AdalyFormal.M1W2.Qcomposite_congr_in

-- D352 lean/src/W2C3.lean:70
#check AdalyFormal.M1W2.rvU_congr_U
#print axioms AdalyFormal.M1W2.rvU_congr_U

-- D353 lean/src/WN4.lean:149
#check AdalyFormal.W3NF.flat_rightInv_patch
#print axioms AdalyFormal.W3NF.flat_rightInv_patch

-- D354 lean/src/ZGU1D.lean:29
#check AdalyFormal.GenuineU1.Gen.firstTerm_core
#print axioms AdalyFormal.GenuineU1.Gen.firstTerm_core

-- D355 lean/src/ZGU1I.lean:39
#check AdalyFormal.GenuineU1.Gen.G1inv_form
#print axioms AdalyFormal.GenuineU1.Gen.G1inv_form

-- D356 lean/src/ZLocJet.lean:96
#check AdalyFormal.IngredientFamilyR2.D2StepL_apply
#print axioms AdalyFormal.IngredientFamilyR2.D2StepL_apply

-- D357 lean/src/ZLocJet.lean:118
#check AdalyFormal.IngredientFamilyR2.C2CompL_zero
#print axioms AdalyFormal.IngredientFamilyR2.C2CompL_zero

-- D358 lean/src/ZLocJet.lean:123
#check AdalyFormal.IngredientFamilyR2.C2CompL_succ
#print axioms AdalyFormal.IngredientFamilyR2.C2CompL_succ

-- D359 lean/src/ZLocJet.lean:128
#check AdalyFormal.IngredientFamilyR2.C2StepL_smul
#print axioms AdalyFormal.IngredientFamilyR2.C2StepL_smul

-- D360 lean/src/ZLocJet.lean:134
#check AdalyFormal.IngredientFamilyR2.C2StepL_eq_C2StepX
#print axioms AdalyFormal.IngredientFamilyR2.C2StepL_eq_C2StepX

-- D361 lean/src/ZLocJet.lean:158
#check AdalyFormal.IngredientFamilyR2.C2CompX_zero_eq
#print axioms AdalyFormal.IngredientFamilyR2.C2CompX_zero_eq

-- D362 lean/src/ZLocJet.lean:167
#check AdalyFormal.IngredientFamilyR2.C2CompL_eq_C2CompX
#print axioms AdalyFormal.IngredientFamilyR2.C2CompL_eq_C2CompX

-- D363 lean/src/ZR8Data.lean:82
#check AdalyFormal.StatementLaneR8.Q1_rows_congr
#print axioms AdalyFormal.StatementLaneR8.Q1_rows_congr

-- D364 lean/src/ZR8Data.lean:94
#check AdalyFormal.StatementLaneR8.C2tilde_rows_congr
#print axioms AdalyFormal.StatementLaneR8.C2tilde_rows_congr

-- D365 lean/src/ZR8Data.lean:106
#check AdalyFormal.StatementLaneR8.H0_congr_rows
#print axioms AdalyFormal.StatementLaneR8.H0_congr_rows

-- D366 lean/src/ZR8Data.lean:116
#check AdalyFormal.StatementLaneR8.hLift_congr_rows
#print axioms AdalyFormal.StatementLaneR8.hLift_congr_rows

-- D367 lean/src/ZR8Data.lean:151
#check AdalyFormal.StatementLaneR8.D2in_congr
#print axioms AdalyFormal.StatementLaneR8.D2in_congr

-- D368 lean/src/ZR8Data.lean:162
#check AdalyFormal.StatementLaneR8.WellDef_congr
#print axioms AdalyFormal.StatementLaneR8.WellDef_congr

-- D369 lean/src/ZR8Data.lean:187
#check AdalyFormal.StatementLaneR8.GuardsUnit_congr
#print axioms AdalyFormal.StatementLaneR8.GuardsUnit_congr

-- D370 lean/src/ZR8Data.lean:198
#check AdalyFormal.StatementLaneR8.WellDefG_congr
#print axioms AdalyFormal.StatementLaneR8.WellDefG_congr

-- D371 lean/src/ZR8DataA.lean:51
#check AdalyFormal.StatementLaneR8.QfullOf_congr
#print axioms AdalyFormal.StatementLaneR8.QfullOf_congr

-- D372 lean/src/ZR8DataA.lean:67
#check AdalyFormal.StatementLaneR8.C2fullOf_congr_U
#print axioms AdalyFormal.StatementLaneR8.C2fullOf_congr_U

-- D373 lean/src/ZR8DataA.lean:83
#check AdalyFormal.StatementLaneR8.C2fullOf_congr_in
#print axioms AdalyFormal.StatementLaneR8.C2fullOf_congr_in

-- D374 lean/src/ZR8DataA.lean:103
#check AdalyFormal.StatementLaneR8.sector_congr
#print axioms AdalyFormal.StatementLaneR8.sector_congr

-- D375 lean/src/ZR8DataB.lean:37
#check AdalyFormal.StatementLaneR8.LocHyp
#print axioms AdalyFormal.StatementLaneR8.LocHyp

-- D376 lean/src/ZR8DataB.lean:45
#check AdalyFormal.StatementLaneR8.BaseDataS_ext'
#print axioms AdalyFormal.StatementLaneR8.BaseDataS_ext'

-- D377 lean/src/ZR8DataB.lean:54
#check AdalyFormal.StatementLaneR8.data_congr
#print axioms AdalyFormal.StatementLaneR8.data_congr

-- D378 lean/src/ZR8DataB.lean:87
#check AdalyFormal.StatementLaneR8.G1inv_congr
#print axioms AdalyFormal.StatementLaneR8.G1inv_congr

-- D379 lean/src/ZR8Jet.lean:27
#check AdalyFormal.StatementLaneR8.AgreeX
#print axioms AdalyFormal.StatementLaneR8.AgreeX

-- D380 lean/src/ZR8Jet.lean:29
#check AdalyFormal.StatementLaneR8.AgreeX.mono
#print axioms AdalyFormal.StatementLaneR8.AgreeX.mono

-- D381 lean/src/ZR8Jet.lean:34
#check AdalyFormal.StatementLaneR8.QlinStepL_congr_bg
#print axioms AdalyFormal.StatementLaneR8.QlinStepL_congr_bg

-- D382 lean/src/ZR8Jet.lean:38
#check AdalyFormal.StatementLaneR8.QlinStepL_congr_in
#print axioms AdalyFormal.StatementLaneR8.QlinStepL_congr_in

-- D383 lean/src/ZR8Jet.lean:44
#check AdalyFormal.StatementLaneR8.D2StepL_congr_bg
#print axioms AdalyFormal.StatementLaneR8.D2StepL_congr_bg

-- D384 lean/src/ZR8Jet.lean:48
#check AdalyFormal.StatementLaneR8.D2StepL_congr_in
#print axioms AdalyFormal.StatementLaneR8.D2StepL_congr_in

-- D385 lean/src/ZR8Jet.lean:56
#check AdalyFormal.StatementLaneR8.C2StepL_congr_bg
#print axioms AdalyFormal.StatementLaneR8.C2StepL_congr_bg

-- D386 lean/src/ZR8Jet.lean:61
#check AdalyFormal.StatementLaneR8.C2StepL_congr_in
#print axioms AdalyFormal.StatementLaneR8.C2StepL_congr_in

-- D387 lean/src/ZR8Jet.lean:68
#check AdalyFormal.StatementLaneR8.QlinCompL_congr_in
#print axioms AdalyFormal.StatementLaneR8.QlinCompL_congr_in

-- D388 lean/src/ZR8Jet.lean:79
#check AdalyFormal.StatementLaneR8.C2CompL_congr_in
#print axioms AdalyFormal.StatementLaneR8.C2CompL_congr_in

-- D389 lean/src/ZR8Jet.lean:97
#check AdalyFormal.StatementLaneR8.QlinCompL_congr_U
#print axioms AdalyFormal.StatementLaneR8.QlinCompL_congr_U

-- D390 lean/src/ZR8Jet.lean:111
#check AdalyFormal.StatementLaneR8.C2CompL_congr_U
#print axioms AdalyFormal.StatementLaneR8.C2CompL_congr_U

-- D391 lean/src/ZR8Read.lean:160
#check AdalyFormal.StatementLaneR8.rawStep_congr
#print axioms AdalyFormal.StatementLaneR8.rawStep_congr

-- D392 lean/src/ZR8Read.lean:196
#check AdalyFormal.StatementLaneR8.qStepComp_congr_bg
#print axioms AdalyFormal.StatementLaneR8.qStepComp_congr_bg

-- D393 lean/src/ZR8Site.lean:143
#check AdalyFormal.StatementLaneR8.Gp_congr
#print axioms AdalyFormal.StatementLaneR8.Gp_congr

-- D394 lean/src/ZR8Site.lean:166
#check AdalyFormal.StatementLaneR8.Rproj_congr
#print axioms AdalyFormal.StatementLaneR8.Rproj_congr

-- D395 lean/src/ZR8Site.lean:190
#check AdalyFormal.StatementLaneR8.RImage_support
#print axioms AdalyFormal.StatementLaneR8.RImage_support

-- D396 lean/src/ZR8Site.lean:253
#check AdalyFormal.StatementLaneR8.Wop_congr_both
#print axioms AdalyFormal.StatementLaneR8.Wop_congr_both

-- D397 lean/src/ZR8Site.lean:288
#check AdalyFormal.StatementLaneR8.DpiFull_congr
#print axioms AdalyFormal.StatementLaneR8.DpiFull_congr

-- D398 lean/src/ZT4A.lean:46
#check AdalyFormal.StatementLaneG.GenP.GuardsUnit
#print axioms AdalyFormal.StatementLaneG.GenP.GuardsUnit

-- D399 lean/src/ZT4A.lean:51
#check AdalyFormal.StatementLaneG.GenP.WellDefG
#print axioms AdalyFormal.StatementLaneG.GenP.WellDefG

-- D400 lean/src/ZT5A.lean:64
#check AdalyFormal.StatementLaneG.InstAtWD
#print axioms AdalyFormal.StatementLaneG.InstAtWD

-- D401 lean/src/ZT5A.lean:99
#check AdalyFormal.StatementLaneG.CoercG8AtWD
#print axioms AdalyFormal.StatementLaneG.CoercG8AtWD

-- D402 lean/src/ZT5A.lean:291
#check AdalyFormal.StatementLaneG.P428Target8
#print axioms AdalyFormal.StatementLaneG.P428Target8

-- D403 lean/src/ZXG3A.lean:35
#check AdalyFormal.StatementLaneG.GenP.Nmat
#print axioms AdalyFormal.StatementLaneG.GenP.Nmat

-- D404 lean/src/ZXG3A.lean:43
#check AdalyFormal.StatementLaneG.GenP.WellDef
#print axioms AdalyFormal.StatementLaneG.GenP.WellDef

-- D405 lean/src/ZXR2Sector.lean:86
#check AdalyFormal.IngredientFamilyR2.C2rawB_eq
#print axioms AdalyFormal.IngredientFamilyR2.C2rawB_eq

-- D406 lean/src/ZXR2Unit1.lean:100
#check AdalyFormal.IngredientFamilyR2.C2tilde_eq_r7
#print axioms AdalyFormal.IngredientFamilyR2.C2tilde_eq_r7


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let n := ``AdalyFormal.M2Route.patchCoercive_class_existsAC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2DLayer.UncAC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2DLayer.Jf_splitAC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2DLayer.col_classAC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2DLayer.dlayerStrat_classAC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2DLayer.DLayerObligationClassAC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2DLayer.dlayerObligationClass_holdsAC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.hH1L2_cfgAC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.psi_classAC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.delta2_classAC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2Skel.holRegime_rho1AC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2Skel.w4_classAC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.AllC.wellDefG_of_coverHyp
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.unitReg_of_classH
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2Skel.w4_classU
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2Skel.config_inst_classU
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.ClassJets.rawStep_congrA
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.ClassJets.ClassSmall
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Literal.gen_G_zero
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Literal.gen_H_zero
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Literal.gen_Ginv_isG1inv
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Literal.gen_G1inv_eq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Literal.gen_G1_zero
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Literal.gen_H1_zero
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Literal.genFormS_collapse
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Literal.pin_target8
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Literal.pin_target8_iff
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Literal.pin_genForm
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.WSchur.cjpGinv_Gi
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.WSchur.cjp_form_lower
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.WSchur.sqrtE_of_pair
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.WSchur.N_lower
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.WSchur.N_cjp_coer
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.WSchur.H_cjp_w
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.GSplit.hHB_of_split
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.ginv_bil
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.CTData.NE
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.CTData.E_nonneg
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.CTData.Nn_le
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.CTData.Y1_le
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.CTData.Dg0
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.CTData.Dg1
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.CTData.Ginv_inj
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.CTData.Ginv_unit
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.CTData.Ginv_G
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.CTData.G_Ginv
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.CTData.N_unit
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.CTData.H_col
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.DLayer.coercive_isUnit
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.DLayer.coercive_apply_inverse
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.DLayer.coercive_inv_bound
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.DLayer.delta2_pair
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.DLayer.delta2_abs_le
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.DLayer.rawStep_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.DLayer.LocRep.J_local_bound
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.DLayer.C2StepX_row_le
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.DLayer.C2Step_l1
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.DLayer.C2CompX_zero
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.DLayer.C2Comp_l1
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.DLayer.polar_eq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.DQ.C2Comp_depth
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.DQ.C2Comp_depth_any
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.DQ.C2full_norm
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.DQ.gauge_C2full_norm
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.DQ.C2full_strat
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.DQ.dqSmall_exists
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.DQ.K2strat_mono
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.DQ.C2full_strat_window
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.psi_le_of_wcol
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.psi1u_le_of_wcol
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.delta2_strat
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.hJ_strat
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.DParts
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.dparts_bounds
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.dlayerStrat_of_parts
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.polar_l1_T
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.C2row_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.polar_row_ball
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.C2row_level0
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.delta2_bil
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.delta2_conj
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.GSplit.pert_lower
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.GSplit.pert_E_le
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.GSplit.pert_sqrtE
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.GSplit.pert_n
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.GSplit.pert_EE
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.GSplit.pert_nn
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.CTData.W4_nq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Residual.GShape
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Residual.CRes
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Residual.CPen
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Residual.guardResidualT_eq_shape
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Residual.GShape_imp
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Residual.GuardPencilT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Residual.residualT_iff_pencilT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Residual.P428Target8SG_iff_pencilT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Residual.Delta2_lit_eq_loc
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Residual.G1inv_lit_eq_pencil
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Residual.isUnit_G1inv_lit_iff_pencil
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.FlatExt.flatE_rightInv
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.GaugeCov.D2StepL_gauge
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.GaugeCov.C2StepL_gauge
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.GaugeCov.C2CompL_gauge
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.GaugeCov.C2fullOf_gauge
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1GaugeW4.holRegime_of_plaq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.genFormS_collapse_G1inv
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.WellDefAt
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.GapAt
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.P428Target8SG2
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.localised_SG2_holds
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.dataS_C2_eq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.dataS_Ginv_eq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.V0
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.C2full_level0_coord
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.plaq_near_in
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.JfS_eq_near
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.Ginv_eq_on_V
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.NG_unit_of_N1
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.Q_H1_apply
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.unit_transfer
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.TwoData.inner_H1_J_eq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.twoData_lit_loc
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.genFormS_eq_loc
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.genFormS_collapse_of_not_wd
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.GapAt_of_loc
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.InstIneqSG_general
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.WellDefAt_loc_of_inst
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.P428Target8SG_of_residual
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.P428Target8SG_iff_residualT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.stat_eq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.TwoData
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.TwoData.H_eq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.TwoData.Delta2_eq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.TwoData.G1inv_eq_on
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Guarded.TwoData.N1inv_H1_eq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1.wnormSq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1.DLayerStrat
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1Num.cw_uniform
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1Assembly.cwW4_lower
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1Assembly.ginv_eq_Fform
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.ginv_form
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.PatchCoercive
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.GinvIMS
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.ginv_weighted_coercive_of
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.wnormSq_ge
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.G1inv_coercive_strat
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.G1inv_coercive_plain
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.units_strat
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.ginvIMS_of
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.ginv_weighted_coercive
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.ginv_weighted_coercive_M1
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.ginv_weighted_coercive_full
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.wellDef_strat
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.wellDef_strat_small
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.ginv_congr_U
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.ginv_weighted_coercive_loc
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1IMS.wellDef_strat_loc
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2Route.patchCoercive_charts
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2Route.patchCoercive_charts_exists
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.ClassFamT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.BallChartsGT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.BallChartsT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.FieldsKT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.ClassRightInvCovT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.ClassRightInvT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.OpLayerThickT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.M2DLayer.Jf_splitACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.M2DLayer.dlayerStrat_classACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.M2DLayer.DLayerObligationClassACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.M2DLayer.dlayerObligationClass_holdsACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.M2OpLayer.hH1L2_cfgACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.M2OpLayer.psi_classACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.M2OpLayer.delta2_classACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.M2Skel.holRegime_rho1ACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.M2Skel.w4_classUΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.ballChartsT_of_G
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.fieldsKT_of_ball
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.classRightInvCovT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.classRightInvT_of_cov
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.opLayerThickT_of
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.famPhi
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.classCoupledΦ_toQ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.P428Target8Family.toMixed
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.p428Target8Mixed_fromFamily
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.family_hyps_nonvacuous
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.dlayer_explicitΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.strong_coreTΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.strong_coreTM
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.CoercG8AtWDFamily
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.P428Target8Family
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.fieldsTQ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.p428Target8Family
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Thin.unitReg_of_classHQ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.IsClassCubeF
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.ClassCoupledF
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.P428Target8FamilyTorus
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXQ.Total.p428Target8FamilyTorus
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.ClassFamT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.BallChartsGT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.BallChartsT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.FieldsKT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.ClassRightInvCovT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.ClassRightInvT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.OpLayerThickT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.M2DLayer.Jf_splitACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.M2DLayer.dlayerStrat_classACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.M2DLayer.DLayerObligationClassACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.M2DLayer.dlayerObligationClass_holdsACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.M2OpLayer.hH1L2_cfgACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.M2OpLayer.psi_classACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.M2OpLayer.delta2_classACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.M2Skel.holRegime_rho1ACΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.M2Skel.w4_classUΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.ballChartsT_of_G
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.fieldsKT_of_ball
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.classRightInvCovT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.classRightInvT_of_cov
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.opLayerThickT_of
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.dlayer_explicitΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.strong_coreTΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.strong_coreTM
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.CoercG8AtWDMixed
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.P428Target8Mixed
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.fieldsTM
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.p428Target8Mixed
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.P428Target8Mixed.toTotal
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Total.p428Target8Total_fromMixed
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``MXP.Thin.unitReg_of_classHΦ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2DLayer.Jf_covered
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2DLayer.Jf_split
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2DLayer.Ageo
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2DLayer.col_class
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2DLayer.OpLayer
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2DLayer.dlayerStrat_class
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2DLayer.DLayerObligationClass
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2DLayer.dlayerObligationClass_holds
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.hH1L2_cfg
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.opLayerThick_of
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.class_coreK_RI
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.ginv_upper_cov
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.hext_of_rightinv_cov
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.C2full_strat12
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.C2row_congr_U
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.hC2_class
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.hHB_genuineR
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.H_l2_colR
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.G1_symmR
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.G1_coerR
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.G1_unitR
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.N1_unitR
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.H1_l2_colR
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1DStrat.H1_eqR
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.psi_class
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.delta2_class
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.qs_inj_of_hext
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.hHL2_cfg
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.PortSlice.G1inv_form_eq_Phi
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.ScaledCoercivity.G1inv_coercive_explicit2
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.ScaledCoercivity.scaled_G1inv2
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.ScaledCoercivity.scaled_G1inv2_simple
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.Ginv
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.G
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.H
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.IsG1inv
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.inner_Ginv
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.K_eq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.Ginv_symm
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.exists_G1inv
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.G1inv_unique
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.delta2Bil
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.Delta2
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.Delta2_spec
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.isG1inv_sub
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.G1inv_coercive
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.isUnit_Q_inv_Qs
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.G1
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.H1
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.QG1Qs_isUnit
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.BaseDataS.QG1Qs_isUnit_of_small
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.inverse_sub_eq_tsum
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.C2CompX_succ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.ReadsetComplete.QlinCompL_eq_compQ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.ReadsetComplete.r8Steps_local
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2RightInv.Dvec_supp
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2RightInv.Tvec_supp
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2RightInv.Tlin_rightInv
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2RightInv.num_RI
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2RightInv.rightInv_cfg
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2RightInv.classRightInvCov
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2RightInv.classRightInv
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2RightInv.thin_core_RI
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2RightInv.thinTori_RI
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2RightInv.p428Target8_of_rightInvCov
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2RightInv.p428Target8
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2Skel.chart_core_class
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2Skel.holRegime_rho1
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2Skel.w4_class
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2Skel.config_inst_class
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.SliceCoerc.ext_of_rightInverse
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.TowerLoc.rawStep_congr_al
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.TowerLoc.qStepComp_congr_bg_al
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.TowerLoc.step_cut_agree
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.D2StepL_row_nat
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.D2StepL_row_natT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.C2fullOf_apply
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.C2fullOf_nat
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.HDesc.inverse
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.BDLink.ginv
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.BDLink.G
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.BDLink.H
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.BDLink.G1inv
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.BDLink.H1
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.C2tilde_nat
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.C2full_E1
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.C2full_equi
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.guardsUnit_of_fields
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.unitReg_of_class
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.coverHyp_of_wd
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.isUnit_of_desc
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Thin.Desc.inverse
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.ClassFamT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.BallChartsGT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.BallChartsT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.FieldsKT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.ClassRightInvCovT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.ClassRightInvT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.OpLayerThickT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.ballChartsT_of_G
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.fieldsKT_of_ball
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.classRightInvCovT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.classRightInvT_of_cov
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.opLayerThickT_of
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.strong_coreT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.strong_coreTC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.P428Target8Total
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.fieldsT
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.p428Target8Total
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.P428Target8Total.toMax
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.P428Target8Total.toMaxAllC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.P428Target8Total.toAllC
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.P428Target8Total.toTarget
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.p428Target8Max_fromTotal
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.p428Target8MaxAllC_fromTotal
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.p428Target8AllC_fromTotal
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.p428Target8_fromTotal
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.Total.ballChartsGT_proved
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.UnifMax.a1D
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.UnifMax.a1D_pos
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.UnifMax.dlayer_explicit
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1W2.curl_congr_U
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1W2.Qcomposite_congr_in
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M1W2.rvU_congr_U
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.W3NF.flat_rightInv_patch
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.GenuineU1.Gen.firstTerm_core
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.GenuineU1.Gen.G1inv_form
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.D2StepL_apply
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.C2CompL_zero
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.C2CompL_succ
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.C2StepL_smul
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.C2StepL_eq_C2StepX
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.C2CompX_zero_eq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.C2CompL_eq_C2CompX
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.Q1_rows_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.C2tilde_rows_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.H0_congr_rows
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.hLift_congr_rows
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.D2in_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.WellDef_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.GuardsUnit_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.WellDefG_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.QfullOf_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.C2fullOf_congr_U
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.C2fullOf_congr_in
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.sector_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.LocHyp
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.BaseDataS_ext'
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.data_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.G1inv_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.AgreeX
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.AgreeX.mono
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.QlinStepL_congr_bg
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.QlinStepL_congr_in
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.D2StepL_congr_bg
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.D2StepL_congr_in
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.C2StepL_congr_bg
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.C2StepL_congr_in
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.QlinCompL_congr_in
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.C2CompL_congr_in
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.QlinCompL_congr_U
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.C2CompL_congr_U
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.rawStep_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.qStepComp_congr_bg
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.Gp_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.Rproj_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.RImage_support
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.Wop_congr_both
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneR8.DpiFull_congr
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneG.GenP.GuardsUnit
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneG.GenP.WellDefG
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneG.InstAtWD
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneG.CoercG8AtWD
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneG.P428Target8
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneG.GenP.Nmat
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.StatementLaneG.GenP.WellDef
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.C2rawB_eq
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.IngredientFamilyR2.C2tilde_eq_r7
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
