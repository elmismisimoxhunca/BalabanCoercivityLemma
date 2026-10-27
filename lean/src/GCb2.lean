import GCb1

/-!
# GCb2 -- `Q'_j(U)`, `Q'*aQ'`, `Δ'_a|_{Ω₀}` equivariant under `Ad_γ`
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

/-- operator identity from the form identity, for an isometric equivalence. -/
theorem op_of_form_iso {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E ≃ₗᵢ[ℝ] E)
    (T T' : E →L[ℝ] E) (h : ∀ x y, ⟪A x, T' (A y)⟫ = ⟪x, T y⟫) (y : E) : T' (A y) = A (T y) := by
  refine ext_inner_left ℝ (fun v => ?_)
  obtain ⟨x, rfl⟩ := A.surjective v
  rw [h, A.inner_map_map]

theorem Qlev_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) (j : ℕ) (y : PeriodicLatticeSite L)
    (f : SiteL2 L) :
    Qlev G (periodicGaugeTransform γ U) j y (adSL γ f) = RMap (γ y) (Qlev G U j y f) := by
  rw [Qlev_apply, Qlev_apply]
  have h := AdalyFormal.Balaban.UbarTowerCov.tower_feeds_Qcomposite
    AdalyFormal.Balaban.SuTwoLogExp.su2LogExp G.ell γ U j (WithLp.ofLp f)
  exact congrFun h y

open Classical in
theorem inner_Qpa_bil (G : TowerGeom L) (U : Cfg L) (a : ℝ) (f g : SiteL2 L) :
    ⟪f, Qpa G U a g⟫ = ∑ j ∈ Finset.range (G.k + 1), ∑ y : PeriodicLatticeSite L,
      if y ∈ G.Lam j then (ajSeq a G.ell j * (G.ell : ℝ) ^ j) * ⟪Qlev G U j y f, Qlev G U j y g⟫ else 0 := by
  simp only [Qpa, ContinuousLinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun y _ => ?_)
  split_ifs
  · simp [real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
  · simp

theorem Qpa_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) (a : ℝ) (f : SiteL2 L) :
    Qpa G (periodicGaugeTransform γ U) a (adSL γ f) = adSL γ (Qpa G U a f) := by
  refine op_of_form_iso (adSL γ) (Qpa G U a) (Qpa G (periodicGaugeTransform γ U) a) (fun x y => ?_) f
  rw [inner_Qpa_bil, inner_Qpa_bil]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun y' _ => ?_))
  rw [Qlev_gauge, Qlev_gauge, AdalyFormal.Balaban.SuTwoInner.inner_RMap]

theorem DelpA_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) (a : ℝ) (f : SiteL2 L) :
    DelpA G (periodicGaugeTransform γ U) a (adSL γ f) = adSL γ (DelpA G U a f) := by
  unfold DelpA
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  rw [siteMask_adSL, lapFull_gauge, Qpa_gauge, ← map_add, siteMask_adSL]

#print axioms Qlev_gauge
#print axioms Qpa_gauge
#print axioms DelpA_gauge

end AdalyFormal.GaugeCov
