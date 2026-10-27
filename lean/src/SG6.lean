import SG5

/-!
# SG6 -- gauge covariance of `Xop` and of the row bound (lane m2_fields123_20261015)

With `adYP Γ = adGen (p ↦ Γ(rowSite p))` on the constraint space `YP G`:
* `QpP_gauge`   : `QpP G (U^Γ) a (Ad_Γ f) = Ad^YP_Γ (QpP G U a f)`   (`Qlev_gauge`, `siteMask_adSL`);
* `QpP_adjoint_gauge`, `LP_gauge`, `Xop_gauge` : `Xop G (U^Γ) a (Ad^YP_Γ u) = Ad_Γ (Xop G U a u)` when `LP G U^Γ a` is a unit;
* `rowBound_of_gauge` : `RowBound` at `U^Γ` with constant `γ` gives `RowBound` at `U` with the same `γ` (the weight `e^{σ}` is constant on rows, `Ad` is an isometry).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2F123

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.GaugeCov (adSL adGen)

variable {L : PeriodicLatticeExtent}

/-- the gauge action on the constraint space -/
noncomputable def adYP (G : TowerGeom L) (Γ : GaugeFn L) : YP G ≃ₗᵢ[ℝ] YP G :=
  adGen (fun p : PIdx G => Γ (rowSite p))

theorem adYP_apply (G : TowerGeom L) (Γ : GaugeFn L) (u : YP G) (p : PIdx G) :
    (adYP G Γ u).ofLp p = RMap (Γ (rowSite p)) (u.ofLp p) := rfl

theorem QpP_gauge (G : TowerGeom L) (Γ : GaugeFn L) (U : Cfg L) (a : ℝ) (f : SiteL2 L) :
    QpP G (periodicGaugeTransform Γ U) a (adSL Γ f) = adYP G Γ (QpP G U a f) := by
  refine PiLp.ext (fun p => ?_)
  cases p with
  | inl q =>
    rw [adYP_apply]
    show Real.sqrt (wq G a q.1.1.val) • Qlev G (periodicGaugeTransform Γ U) q.1.1.val q.1.2 (siteMask G.Om0 (adSL Γ f))
      = RMap (Γ q.1.2) (Real.sqrt (wq G a q.1.1.val) • Qlev G U q.1.1.val q.1.2 (siteMask G.Om0 f))
    rw [AdalyFormal.GaugeCov.siteMask_adSL, AdalyFormal.GaugeCov.Qlev_gauge, map_smul]
  | inr x =>
    rw [adYP_apply]
    show (adSL Γ f).ofLp x.1 = RMap (Γ x.1) (f.ofLp x.1)
    exact adSL_apply Γ f x.1

theorem QpP_adjoint_gauge (G : TowerGeom L) (Γ : GaugeFn L) (U : Cfg L) (a : ℝ) (u : YP G) :
    ContinuousLinearMap.adjoint (QpP G (periodicGaugeTransform Γ U) a) (adYP G Γ u)
      = adSL Γ (ContinuousLinearMap.adjoint (QpP G U a) u) := by
  refine ext_inner_left ℝ (fun f => ?_)
  obtain ⟨h, rfl⟩ := (adSL Γ).surjective f
  rw [ContinuousLinearMap.adjoint_inner_right, QpP_gauge, LinearIsometryEquiv.inner_map_map,
    LinearIsometryEquiv.inner_map_map, ContinuousLinearMap.adjoint_inner_right]

theorem LP_gauge (G : TowerGeom L) (Γ : GaugeFn L) (U : Cfg L) (a : ℝ) (g : SiteL2 L) :
    LP G (periodicGaugeTransform Γ U) a (adSL Γ g) = adSL Γ (LP G U a g) := by
  unfold LP
  simp only [add_apply, sub_apply, one_apply_eq_self, map_add, map_sub,
    AdalyFormal.GaugeCov.DelpA_gauge, AdalyFormal.GaugeCov.siteMask_adSL]

theorem Xop_gauge (G : TowerGeom L) (Γ : GaugeFn L) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (LP G (periodicGaugeTransform Γ U) a)) (u : YP G) :
    ‖Xop G U a u‖ = ‖Xop G (periodicGaugeTransform Γ U) a (adYP G Γ u)‖ := by
  set U' := periodicGaugeTransform Γ U with hU'
  set A' := LP G U' a with hA'
  set A := LP G U a with hA
  -- E = Ad_Γ as a continuous linear equivalence
  let E : SiteL2 L ≃L[ℝ] SiteL2 L := (adSL Γ).toContinuousLinearEquiv
  have hE : ∀ g, E g = adSL Γ g := fun g => rfl
  have hES : ∀ g, E.symm (E g) = g := fun g => E.symm_apply_apply g
  have hSE : ∀ g, E (E.symm g) = g := fun g => E.apply_symm_apply g
  obtain ⟨B', hAB', hBA'⟩ : ∃ B' : SiteL2 L →L[ℝ] SiteL2 L, A' * B' = 1 ∧ B' * A' = 1 := by
    obtain ⟨v, hv⟩ := hu
    exact ⟨↑v⁻¹, by rw [← hv]; exact v.mul_inv, by rw [← hv]; exact v.inv_mul⟩
  have hconj : ∀ g, A' (E g) = E (A g) := fun g => LP_gauge G Γ U a g
  -- the inverse of A
  let B : SiteL2 L →L[ℝ] SiteL2 L :=
    (E.symm : SiteL2 L →L[ℝ] SiteL2 L).comp (B'.comp (E : SiteL2 L →L[ℝ] SiteL2 L))
  have hB_apply : ∀ g, B g = E.symm (B' (E g)) := fun g => rfl
  have hAB : A * B = 1 := by
    ext1 g
    show A (B g) = g
    rw [hB_apply]
    have h1 : A (E.symm (B' (E g))) = E.symm (A' (B' (E g))) := by
      have := hconj (E.symm (B' (E g)))
      rw [hSE] at this
      rw [this, hES]
    rw [h1]
    have : A' (B' (E g)) = E g := by
      have := congrArg (fun T => T (E g)) hAB'
      simpa using this
    rw [this, hES]
  have hBA : B * A = 1 := by
    ext1 g
    show B (A g) = g
    rw [hB_apply]
    have h1 : E (A g) = A' (E g) := (hconj g).symm
    rw [h1]
    have : B' (A' (E g)) = E g := by
      have := congrArg (fun T => T (E g)) hBA'
      simpa using this
    rw [this, hES]
  have hinv : Ring.inverse A = B := by
    have : A = ↑(Units.mk A B hAB hBA) := rfl
    rw [this, Ring.inverse_unit]; rfl
  have hinv' : Ring.inverse A' = B' := by
    have : A' = ↑(Units.mk A' B' hAB' hBA') := rfl
    rw [this, Ring.inverse_unit]; rfl
  have hX : Xop G U a u = E.symm (Xop G U' a (adYP G Γ u)) := by
    show LinvP G U a (ContinuousLinearMap.adjoint (QpP G U a) u)
      = E.symm (LinvP G U' a (ContinuousLinearMap.adjoint (QpP G U' a) (adYP G Γ u)))
    rw [QpP_adjoint_gauge]
    unfold LinvP
    rw [hinv, hinv']
    rw [hB_apply]
    rfl
  rw [hX]
  exact (adSL Γ).symm.norm_map _

theorem ypWt_norm_gauge (G : TowerGeom L) (Γ : GaugeFn L) (φ : PeriodicLatticeSite L → ℝ) (u : YP G) :
    ‖ypWt G φ (adYP G Γ u)‖ = ‖ypWt G φ u‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  show ‖Real.exp (φ (rowSite p)) • (adYP G Γ u).ofLp p‖ ^ 2 = ‖Real.exp (φ (rowSite p)) • u.ofLp p‖ ^ 2
  rw [adYP_apply, norm_smul, norm_smul, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]

/-- the row bound transfers along a gauge (same constant) -/
theorem rowBound_of_gauge (G : TowerGeom L) (Γ : GaugeFn L) (U : Cfg L) (a γ : ℝ)
    (hu : IsUnit (LP G (periodicGaugeTransform Γ U) a))
    (h : ∀ u, ‖ypWt G (sigG G) u‖ ≤ γ * ‖Xop G (periodicGaugeTransform Γ U) a u‖) :
    ∀ u, ‖ypWt G (sigG G) u‖ ≤ γ * ‖Xop G U a u‖ := by
  intro u
  have h1 := h (adYP G Γ u)
  rw [ypWt_norm_gauge] at h1
  rw [Xop_gauge G Γ U a hu u]
  exact h1

end AdalyFormal.M2F123

#print axioms AdalyFormal.M2F123.QpP_gauge
#print axioms AdalyFormal.M2F123.QpP_adjoint_gauge
#print axioms AdalyFormal.M2F123.LP_gauge
#print axioms AdalyFormal.M2F123.Xop_gauge
#print axioms AdalyFormal.M2F123.ypWt_norm_gauge
#print axioms AdalyFormal.M2F123.rowBound_of_gauge
