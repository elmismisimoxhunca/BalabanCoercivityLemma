import NtCvOP8

/-!
# CvOP9 -- `gOf`, `RhOf`, `WhOf`, `ThOf` are analytic along an analytic regular tower (lane omega/near2/struct)
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

section Rh
variable (G : TowerGeom L) (U : ℝ → Cfg L) {t0 : ℝ}

theorem inverseLm_analytic (hT : TowerOK G U t0) (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    AnalyticAt ℝ (fun t => Ring.inverse (LmOf G (U t))) t0 := by
  have hU : LinkEA U t0 := LinkEA_of_AnaFam (hT.1 0 (by norm_num))
  have hX := LmOf_analytic G hU
  have hu : IsUnit (LmOf G (U t0)) := LmOf_unit G (U t0) hout
  have hinv := analyticAt_inverse (𝕜 := ℝ) (A := SiteL2 L →L[ℝ] SiteL2 L) hu.unit
  rw [hu.unit_spec] at hinv
  exact AnalyticAt.comp (g := Ring.inverse) (f := fun t => LmOf G (U t)) hinv hX

theorem Cc_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    AnalyticAt ℝ (fun t => Cc (LmOf G (U t)) (Bq G (U t))) t0 :=
  anal_comp (Bq_analytic G U hT hk) (inverseLm_analytic G U hT hout)

theorem GmOf_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    AnalyticAt ℝ (fun t => GmOf G (U t)) t0 := by
  have hC := Cc_analytic G U hT hk hout
  exact anal_comp (anal_comp hC analyticAt_const) (anal_adjoint hC)

theorem gOf_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    AnalyticAt ℝ (fun t => gOf G (U t)) t0 :=
  analyticAt_cdet (GmOf_analytic G U hT hk hout)

theorem RhOf_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    AnalyticAt ℝ (fun t => RhOf G (U t)) t0 := by
  have hC := Cc_analytic G U hT hk hout
  have hg := gOf_analytic G U hT hk hout
  have hG := GmOf_analytic G U hT hk hout
  unfold RhOf Rhat
  exact (hg.smul analyticAt_const).sub
    (anal_comp (anal_comp (anal_comp analyticAt_const (anal_adjoint hC)) (analyticAt_cadj hG))
      (anal_comp hC analyticAt_const))

theorem WhOf_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell)
    (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    AnalyticAt ℝ (fun t => WhOf G (U t) a) t0 := by
  have hU : LinkEA U t0 := LinkEA_of_AnaFam (hT.1 0 (by norm_num))
  have hg := gOf_analytic G U hT hk hout
  have hRh := RhOf_analytic G U hT hk hout
  have hGp := Gp_analytic G U hT hk ha hell hout
  unfold WhOf
  exact (hg.smul analyticAt_const).sub
    (anal_comp (gradL2_analytic hU) (anal_comp hGp (anal_comp hRh (gradAdj_analytic hU))))

theorem ThOf_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    AnalyticAt ℝ (fun t => ThOf G (U t)) t0 := by
  have hU : LinkEA U t0 := LinkEA_of_AnaFam (hT.1 0 (by norm_num))
  unfold ThOf
  exact anal_comp (RhOf_analytic G U hT hk hout) (anal_comp (gradAdj_analytic hU) analyticAt_const)

end Rh

end AdalyFormal.CoverOmega.Struct
