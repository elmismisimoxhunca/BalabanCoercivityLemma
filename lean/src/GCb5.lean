import GCb4

/-!
# GCb5 -- `G' = (Δ'_a|_{Ω₀})⁻¹`, `W`, `T = R D*` equivariant under `Ad_γ`   (`Delta` was done in GC2: `deltaKLocCLM_gauge`)
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply RMap_one)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply gaugeInv)
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

theorem Gp_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) (a : ℝ) (f : SiteL2 L) :
    Gp G (periodicGaugeTransform γ U) a (adSL γ f) = adSL γ (Gp G U a f) := by
  unfold Gp
  simp only [ContinuousLinearMap.comp_apply]
  rw [siteMask_adSL]
  refine ringInverse_eqv (adSL γ) (DelpA G U a + (1 - siteMask G.Om0))
    (DelpA G (periodicGaugeTransform γ U) a + (1 - siteMask G.Om0)) (fun x => ?_) _
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    DelpA_gauge, siteMask_adSL, map_add, map_sub]

theorem Tfull_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) (x : BondFnL2 L) :
    Tfull G (periodicGaugeTransform γ U) (adBL γ x) = adSL γ (Tfull G U x) := by
  unfold Tfull
  simp only [ContinuousLinearMap.comp_apply]
  rw [gradAdj_gauge, Rproj_gauge]

theorem Wop_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) (a : ℝ) (x : BondFnL2 L) :
    Wop G (periodicGaugeTransform γ U) a (adBL γ x) = adBL γ (Wop G U a x) := by
  unfold Wop
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
  rw [gradAdj_gauge, Rproj_gauge, Gp_gauge, gradL2_gauge, map_sub]

#print axioms ringInverse_eqv
#print axioms Gp_gauge
#print axioms Tfull_gauge
#print axioms Wop_gauge

end AdalyFormal.GaugeCov
