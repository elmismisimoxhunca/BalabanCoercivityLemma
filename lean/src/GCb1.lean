import GC3

/-!
# GCb1 -- gradient / divergence / Laplacian / masks, equivariance under `Ad_γ`
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply RMap_one gradValueCovariant)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply gaugeInv)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

/-- adjoint of an equivariant operator is equivariant (generic). -/
theorem adjoint_eqv {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E ≃ₗᵢ[ℝ] E) (B : F ≃ₗᵢ[ℝ] F) (T T' : E →L[ℝ] F) (h : ∀ x, T' (A x) = B (T x)) (y : F) :
    ContinuousLinearMap.adjoint T' (B y) = A (ContinuousLinearMap.adjoint T y) := by
  refine ext_inner_left ℝ (fun v => ?_)
  obtain ⟨w, rfl⟩ := A.surjective v
  rw [ContinuousLinearMap.adjoint_inner_right, h, B.inner_map_map, A.inner_map_map,
    ContinuousLinearMap.adjoint_inner_right]

theorem grad_gauge' (γ : GaugeFn L) (U : Cfg L) (lam : PeriodicLatticeSite L → SuTwo) (b : Bond L) :
    gradValueCovariant (periodicGaugeTransform γ U) (fun x => RMap (γ x) (lam x)) b
      = RMap (γ b.1) (gradValueCovariant U lam b) := by
  unfold gradValueCovariant periodicGaugeTransform
  rw [RMap_mul_apply, map_sub, RMap_mul_apply]
  congr 2
  group

/-- `D_{U^γ} Ad_γ = Ad_γ D_U` on `L²` sites → bonds. -/
theorem gradL2_gauge (γ : GaugeFn L) (U : Cfg L) (f : SiteL2 L) :
    gradL2 (periodicGaugeTransform γ U) (adSL γ f) = adBL γ (gradL2 U f) := by
  refine PiLp.ext (fun b => ?_)
  show (WithLp.ofLp (gradL2 (periodicGaugeTransform γ U) (adSL γ f))) b = RMap (γ b.1) ((WithLp.ofLp (gradL2 U f)) b)
  rw [gradL2_apply, gradL2_apply]
  exact grad_gauge' γ U (WithLp.ofLp f) b

theorem gradAdj_gauge (γ : GaugeFn L) (U : Cfg L) (x : BondFnL2 L) :
    gradAdj (periodicGaugeTransform γ U) (adBL γ x) = adSL γ (gradAdj U x) :=
  adjoint_eqv (adSL γ) (adBL γ) (gradL2 U) (gradL2 (periodicGaugeTransform γ U))
    (fun f => gradL2_gauge γ U f) x

theorem lapFull_gauge (γ : GaugeFn L) (U : Cfg L) (f : SiteL2 L) :
    lapFull (periodicGaugeTransform γ U) (adSL γ f) = adSL γ (lapFull U f) := by
  show gradAdj _ (gradL2 _ (adSL γ f)) = adSL γ (gradAdj U (gradL2 U f))
  rw [gradL2_gauge, gradAdj_gauge]

theorem siteMask_adSL (γ : GaugeFn L) (S : Set (PeriodicLatticeSite L)) (f : SiteL2 L) :
    siteMask S (adSL γ f) = adSL γ (siteMask S f) := by
  classical
  refine PiLp.ext (fun x => ?_)
  rw [siteMask_apply]
  show _ = RMap (γ x) ((siteMask S f) x)
  rw [siteMask_apply]
  split_ifs
  · rfl
  · simp

#print axioms adjoint_eqv
#print axioms gradL2_gauge
#print axioms gradAdj_gauge
#print axioms lapFull_gauge
#print axioms siteMask_adSL

end AdalyFormal.GaugeCov
