import PSiteC16
import PSiteC2

/-!
# SiteC17 -- Dirichlet wrappers: from the masked-form bound to `hu` and `‖G'‖` for a PROPER region `Ω₀`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.SiteCoercivity

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap gradValueCovariant)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

theorem inner_DelpA_mask (G : TowerGeom L) (U : Cfg L) (a : ℝ) (f : SiteL2 L) :
    ⟪f, DelpA G U a f⟫ = ‖gradL2 U (siteMask G.Om0 f)‖ ^ 2 + ⟪siteMask G.Om0 f, Qpa G U a (siteMask G.Om0 f)⟫ := by
  unfold DelpA
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  rw [← siteMask_symm, inner_add_right, inner_lapFull]

theorem mask_norm_sq (G : TowerGeom L) (f : SiteL2 L) :
    ‖f‖ ^ 2 = ‖siteMask G.Om0 f‖ ^ 2 + ‖f - siteMask G.Om0 f‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  classical
  simp only [PiLp.sub_apply, siteMask_apply]
  split_ifs <;> simp

theorem inner_mask_self (G : TowerGeom L) (f : SiteL2 L) :
    ⟪f, siteMask G.Om0 f⟫ = ‖siteMask G.Om0 f‖ ^ 2 := by
  have h := siteMask_symm G.Om0 f (siteMask G.Om0 f)
  rw [siteMask_idem] at h
  rw [← h, real_inner_self_eq_norm_sq]

theorem inner_X_ge (G : TowerGeom L) (U : Cfg L) (a : ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hc : ∀ f : SiteL2 L, c * ‖siteMask G.Om0 f‖ ^ 2 ≤ ⟪f, DelpA G U a f⟫) (f : SiteL2 L) :
    c * ‖f‖ ^ 2 ≤ ⟪f, (DelpA G U a + (1 - siteMask G.Om0)) f⟫ := by
  have e : ⟪f, (DelpA G U a + (1 - siteMask G.Om0)) f⟫
      = ⟪f, DelpA G U a f⟫ + ‖f - siteMask G.Om0 f‖ ^ 2 := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      inner_add_right, inner_sub_right, inner_mask_self, real_inner_self_eq_norm_sq]
    have := mask_norm_sq G f
    linarith
  rw [e, mask_norm_sq G f]
  have h1 := hc f
  have h2 : 0 ≤ ‖f - siteMask G.Om0 f‖ ^ 2 := sq_nonneg _
  nlinarith

theorem unit_Gp_of_masked_coercive (G : TowerGeom L) (U : Cfg L) (a : ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hc : ∀ f : SiteL2 L, c * ‖siteMask G.Om0 f‖ ^ 2 ≤ ⟪f, DelpA G U a f⟫) :
    IsUnit (DelpA G U a + (1 - siteMask G.Om0)) ∧ ∀ s : SiteL2 L, ‖Gp G U a s‖ ≤ (1 / c) * ‖s‖ := by
  have hX := inner_X_ge G U a hc0 hc1 hc
  have hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0)) := by
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    set X : SiteL2 L →L[ℝ] SiteL2 L := DelpA G U a + (1 - siteMask G.Om0) with hXdef
    have hinj : Function.Injective X := by
      rw [injective_iff_map_eq_zero]
      intro f hf
      have h := hX f
      rw [hf, inner_zero_right] at h
      have h2 : ‖f‖ ^ 2 ≤ 0 := by nlinarith
      have : ‖f‖ = 0 := by nlinarith [norm_nonneg f]
      exact norm_eq_zero.mp this
    exact ⟨hinj, LinearMap.surjective_of_injective (f := (X : SiteL2 L →ₗ[ℝ] SiteL2 L)) hinj⟩
  refine ⟨hu, fun s => ?_⟩
  obtain ⟨hmv, hDv⟩ := Gp_spec G U a hu s
  set v := Gp G U a s with hv
  have hXv : (DelpA G U a + (1 - siteMask G.Om0)) v = siteMask G.Om0 s := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [hDv, hmv]; abel
  have h := hX v
  rw [hXv] at h
  have h2 : ⟪v, siteMask G.Om0 s⟫ ≤ ‖v‖ * ‖siteMask G.Om0 s‖ := real_inner_le_norm _ _
  have h3 : ‖siteMask G.Om0 s‖ ≤ ‖s‖ := by
    have := mask_norm_sq G s
    have h0 : 0 ≤ ‖s - siteMask G.Om0 s‖ ^ 2 := sq_nonneg _
    exact le_of_sq_le_sq' (norm_nonneg _) (by nlinarith)
  have hv0 := norm_nonneg v
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc0]
  by_cases h0 : ‖v‖ = 0
  · rw [h0, zero_mul]; exact norm_nonneg s
  · have hp : 0 < ‖v‖ := lt_of_le_of_ne hv0 (Ne.symm h0)
    nlinarith [mul_le_mul_of_nonneg_left h3 hv0]

end AdalyFormal.SiteCoercivity
