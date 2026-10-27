import NsCvOS7
import NsCvOX1

/-!
# CvOS8 -- the Dirichlet unit for `lapDir`, the constraint operator `Bq` of `N(Q')`, and `Rproj = g⁻¹ • Rhat` (lane omega/near2/struct)

For a tower geometry `G`, configuration `U`:  `Lm = lapDir + (1 - mask)` is a unit (some site outside `Om0`), `Nsub (mask) (Bq) = NQp`,
`Rproj G U = (cdet (Gm ..))⁻¹ • Rhat ..` whenever `cdet (Gm ..) ≠ 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega.Struct

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverOmega (covConst_norm)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant)
open AdalyFormal.Balaban.SuTwoInner (hsInner hsInner_RMap hsInner_self_nonneg hsInner_self_eq_zero)

variable {L : PeriodicLatticeExtent}

/-- `Lm = lapDir + (1 - mask)`. -/
noncomputable def LmOf (G : TowerGeom L) (U : Cfg L) : SiteL2 L →L[ℝ] SiteL2 L :=
  lapDir G U + (1 - siteMask G.Om0)

theorem lapDir_inner_ge (G : TowerGeom L) (U : Cfg L) (f : SiteL2 L) :
    ‖gradL2 U (siteMask G.Om0 f)‖ ^ 2 + ‖f - siteMask G.Om0 f‖ ^ 2 ≤ ⟪f, LmOf G U f⟫ := by
  set m := siteMask G.Om0 with hm
  have hsym : ∀ u v : SiteL2 L, ⟪m u, v⟫ = ⟪u, m v⟫ := fun u v => siteMask_symm _ u v
  have hidem : ∀ u : SiteL2 L, m (m u) = m u := fun u => siteMask_idem _ u
  have e1 : ⟪f, lapDir G U f⟫ = ⟪m f, lapFull U (m f)⟫ := by
    unfold lapDir
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hsym]
  have e2 : ⟪f, ((1 : SiteL2 L →L[ℝ] SiteL2 L) - m) f⟫ = ‖f - m f‖ ^ 2 := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [← real_inner_self_eq_norm_sq]
    have h0 : ⟪m f, f - m f⟫ = 0 := by
      rw [inner_sub_right]
      have a1 : ⟪m f, m f⟫ = ⟪f, m f⟫ := by rw [hsym, hidem]
      have a2 : ⟪m f, f⟫ = ⟪f, m f⟫ := real_inner_comm _ _
      rw [a1, a2, sub_self]
    have hdec : f = (f - m f) + m f := by abel
    calc ⟪f, f - m f⟫ = ⟪(f - m f) + m f, f - m f⟫ := by rw [← hdec]
      _ = ⟪f - m f, f - m f⟫ := by rw [inner_add_left, h0, add_zero]
  have e3 : ⟪m f, lapFull U (m f)⟫ = ‖gradL2 U (m f)‖ ^ 2 := by
    unfold lapFull gradAdj
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  show _ ≤ ⟪f, lapDir G U f + ((1 : SiteL2 L →L[ℝ] SiteL2 L) - m) f⟫
  rw [inner_add_right, e1, e2, e3]

theorem LmOf_unit (G : TowerGeom L) (U : Cfg L) (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    IsUnit (LmOf G U) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  set X : SiteL2 L →L[ℝ] SiteL2 L := LmOf G U with hX
  have hinj : Function.Injective X := by
    refine (injective_iff_map_eq_zero X).mpr (fun f hf => ?_)
    have h1 := lapDir_inner_ge G U f
    rw [hf, inner_zero_right] at h1
    have hs1 := sq_nonneg ‖gradL2 U (siteMask G.Om0 f)‖
    have hs2 := sq_nonneg ‖f - siteMask G.Om0 f‖
    have hD : ‖gradL2 U (siteMask G.Om0 f)‖ ^ 2 = 0 := by linarith
    have hR : ‖f - siteMask G.Om0 f‖ ^ 2 = 0 := by linarith
    have hfm : f = siteMask G.Om0 f :=
      sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp hR))
    have hDm : gradL2 U (siteMask G.Om0 f) = 0 := norm_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp hD)
    have hDf : gradL2 U f = 0 := by rw [← hfm] at hDm; exact hDm
    obtain ⟨x0, hx0⟩ := hout
    have hx0f : f x0 = 0 := by
      have : (siteMask G.Om0 f) x0 = 0 := by rw [siteMask_apply, if_neg hx0]
      rw [← hfm] at this; exact this
    ext x
    have := covConst_norm U f hDf x x0
    rw [hx0f] at this
    have h0 : hsInner (f x) (f x) = 0 := by
      rw [this]; exact AdalyFormal.Balaban.DeltaKU.hsInner_zero_right _
    have := hsInner_self_eq_zero h0
    simp [this]
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (X : SiteL2 L →ₗ[ℝ] SiteL2 L))).mp hinj⟩

#print axioms lapDir_inner_ge
#print axioms LmOf_unit

end AdalyFormal.CoverOmega.Struct
