import GCb2

/-!
# GCb3 -- `N(Q')`, `Δ_U|_{Ω₀}`, `R(U)` equivariant under `Ad_γ`
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

theorem RMap_eq_zero_iff (g : SU2g) (X : SuTwo) : RMap g X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have := AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap g X
    rw [h, norm_zero] at this
    exact norm_eq_zero.mp this.symm
  · intro h; rw [h, map_zero]

theorem mem_NQp_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) (f : SiteL2 L) :
    adSL γ f ∈ NQp G (periodicGaugeTransform γ U) ↔ f ∈ NQp G U := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun j hj y hy => ?_⟩
    · have := h1 x hx
      exact (RMap_eq_zero_iff _ _).mp this
    · have := h2 j hj y hy
      rw [Qlev_gauge] at this
      exact (RMap_eq_zero_iff _ _).mp this
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun j hj y hy => ?_⟩
    · show RMap (γ x) (f x) = 0
      rw [h1 x hx, map_zero]
    · rw [Qlev_gauge, h2 j hj y hy, map_zero]

theorem lapDir_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) (f : SiteL2 L) :
    lapDir G (periodicGaugeTransform γ U) (adSL γ f) = adSL γ (lapDir G U f) := by
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply]
  rw [siteMask_adSL, lapFull_gauge, siteMask_adSL]

theorem RImage_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) :
    RImage G (periodicGaugeTransform γ U)
      = (RImage G U).map (adSL γ).toLinearIsometry.toLinearMap := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨f, rfl⟩ := (adSL γ).surjective w
    refine ⟨lapDir G U f, ⟨f, (mem_NQp_gauge G γ U f).mp hw, rfl⟩, ?_⟩
    exact (lapDir_gauge G γ U f).symm
  · rintro ⟨u, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨adSL γ f, (mem_NQp_gauge G γ U f).mpr hf, (lapDir_gauge G γ U f)⟩

theorem Rproj_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) (f : SiteL2 L) :
    Rproj G (periodicGaugeTransform γ U) (adSL γ f) = adSL γ (Rproj G U f) := by
  have key : ∀ (K K' : Submodule ℝ (SiteL2 L)) [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection],
      K = K' → ∀ x, K.starProjection x = K'.starProjection x := by
    intro K K' _ _ h x; subst h; rfl
  unfold Rproj
  rw [key _ _ (RImage_gauge G γ U)]
  exact ((adSL γ).toLinearIsometry.map_starProjection (RImage G U) f).symm

#print axioms mem_NQp_gauge
#print axioms RImage_gauge
#print axioms Rproj_gauge

end AdalyFormal.GaugeCov
