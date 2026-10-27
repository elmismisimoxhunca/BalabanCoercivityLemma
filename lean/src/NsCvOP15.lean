import NsCvOP14

/-!
# CvOP15 -- assembly: `DstructG` is analytic in `t` along an analytic regular tower (lane omega/near2/struct)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverOmega
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {L : PeriodicLatticeExtent}

theorem AhOf_analytic (G : TowerGeom L) (U : ℝ → Cfg L) {t0 : ℝ} (hT : TowerOK G U t0) (hk : G.k ≤ 2)
    {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell) (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    AnalyticAt ℝ (fun t => AhOf G (U t) a (bondSectorOf G (U t))) t0 := by
  have hU : LinkEA U t0 := LinkEA_of_AnaFam (hT.1 0 (by norm_num))
  have hW := WhOf_analytic G U hT hk ha hell hout
  have hD := Delta_analytic G hU
  have hTh := ThOf_analytic G U hT hk hout
  have hg := gOf_analytic G U hT hk hout
  have hM := MassFull_analytic G U hT hk a
  unfold AhOf
  refine AnalyticAt.add (AnalyticAt.add ?_ ?_) ?_
  · exact anal_comp analyticAt_const (anal_comp (anal_comp (anal_adjoint hW) (anal_comp hD hW)) analyticAt_const)
  · exact anal_comp (anal_adjoint hTh) hTh
  · exact ((hg.pow 2).smul (anal_comp analyticAt_const (anal_comp hM analyticAt_const)))

/-- **`DstructG` is analytic in `t`**, given an analytic source family `Jf`. -/
theorem DstructG_analytic (G : TowerGeom L) (U : ℝ → Cfg L) {t0 : ℝ} (hT : TowerOK G U t0) (hk : G.k ≤ 2)
    {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell) (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0)
    (Jf : ℝ → BondFnL2 L) (hJ : AnalyticAt ℝ Jf t0) :
    AnalyticAt ℝ (fun t => DstructG G (U t) a (bondSectorOf G (U t)) (Jf t)) t0 := by
  have hg := gOf_analytic G U hT hk hout
  have hA := AhOf_analytic G U hT hk ha hell hout
  have hQ : AnalyticAt ℝ (fun t => (bondSectorOf G (U t)).Qfull.comp (iE G)) t0 :=
    anal_comp (QfullOf_analytic G U hT hk) analyticAt_const
  have hC := CbhOf_analytic G U hT hk ha hell hout
  have hJ' : AnalyticAt ℝ (fun t => pE G (Jf t)) t0 := anal_apply analyticAt_const hJ
  unfold DstructG
  exact hg.mul (analyticAt_Dcore hA hQ hC hJ')

end AdalyFormal.CoverOmega.Struct
