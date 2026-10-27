import NuPtZ5

/-!
# PtZ6 -- `gOf ≠ 0` at the flat nested point (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmegaTwo
open AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverOmega.Struct

variable {ell M R : ℕ}

theorem LmOf_symm {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (u v : SiteL2 L) :
    ⟪LmOf G U u, v⟫ = ⟪u, LmOf G U v⟫ := by
  unfold LmOf
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  congr 1
  · unfold lapDir
    simp only [ContinuousLinearMap.comp_apply]
    rw [siteMask_symm, lapFull_symm, siteMask_symm]
  · rw [siteMask_symm]

theorem lapDir_eq_mask_lap_all {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (f : SiteL2 L) :
    lapDir G U f = siteMask G.Om0 (lapFull U (siteMask G.Om0 f)) := rfl

theorem gOf_ne_zero_flat (hP : PGeo ell M R) (hell : 0 < ell) :
    gOf (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) ≠ 0 := by
  have hp0 := hP.p0pos
  set G := geomOf ell 2 (neS ell M R) with hG
  set U : Cfg (scaleUp ell 2 (neLu M R)) := flatCfg with hU
  have hout : ∃ x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)), x ∉ G.Om0 := by
    refine ⟨mkS (scaleUp ell 2 (neLu M R)) 0 0 0, fun h => ?_⟩
    have := (Omv_site 0 _).mp h
    rw [x0val hP 0 0 0 hP.hNpos] at this
    simp only [Omv] at this
    omega
  have hunit := LmOf_unit G U hout
  obtain ⟨uL, huL⟩ := hunit
  set Lm := LmOf G U with hLm
  set I : SiteL2 (scaleUp ell 2 (neLu M R)) →L[ℝ] SiteL2 (scaleUp ell 2 (neLu M R)) := Ring.inverse Lm with hI
  have hLI : ∀ f, Lm (I f) = f := by
    intro f
    have := Ring.mul_inverse_cancel _ (⟨uL, huL⟩ : IsUnit Lm)
    exact ContinuousLinearMap.ext_iff.mp this f
  have hIL : ∀ f, I (Lm f) = f := by
    intro f
    have := Ring.inverse_mul_cancel _ (⟨uL, huL⟩ : IsUnit Lm)
    exact ContinuousLinearMap.ext_iff.mp this f
  have hIsymm : ∀ u v, ⟪I u, v⟫ = ⟪u, I v⟫ := by
    intro u v
    calc ⟪I u, v⟫ = ⟪I u, Lm (I v)⟫ := by rw [hLI]
      _ = ⟪Lm (I u), I v⟫ := (LmOf_symm G U _ _).symm
      _ = ⟪u, I v⟫ := by rw [hLI]
  have hIadj : ContinuousLinearMap.adjoint I = I := by
    ext1 f
    refine ext_inner_left ℝ (fun g => ?_)
    rw [ContinuousLinearMap.adjoint_inner_right, hIsymm]
  unfold gOf cdet
  intro hdet
  have hker := LinearMap.bot_lt_ker_of_det_eq_zero hdet
  obtain ⟨w, hwk, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (ne_of_gt hker)
  apply hw0
  have hGw : (GmOf G U) w = 0 := hwk
  -- C = Bq ∘ I
  set B := Bq G U with hB
  have hC : Cc Lm B = B.comp I := rfl
  have hGm : GmOf G U = ((B.comp I).comp (siteMask G.Om0)).comp (ContinuousLinearMap.adjoint (B.comp I)) := rfl
  have hCadj : ContinuousLinearMap.adjoint (B.comp I) = I.comp (ContinuousLinearMap.adjoint B) := by
    rw [ContinuousLinearMap.adjoint_comp, hIadj]
  -- m (C* w) = 0
  set f := I (ContinuousLinearMap.adjoint B w) with hf
  have hmf : siteMask G.Om0 f = 0 := by
    have h1 : ⟪w, (GmOf G U) w⟫ = 0 := by rw [hGw, inner_zero_right]
    rw [hGm] at h1
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [hCadj] at h1
    simp only [ContinuousLinearMap.comp_apply] at h1
    have h2 : ⟪w, B (I (siteMask G.Om0 f))⟫ = ‖siteMask G.Om0 f‖ ^ 2 := by
      have e1 : ⟪w, B (I (siteMask G.Om0 f))⟫ = ⟪ContinuousLinearMap.adjoint B w, I (siteMask G.Om0 f)⟫ :=
        (ContinuousLinearMap.adjoint_inner_left B _ w).symm
      have e2 : ⟪ContinuousLinearMap.adjoint B w, I (siteMask G.Om0 f)⟫ = ⟪f, siteMask G.Om0 f⟫ :=
        (hIsymm _ _).symm
      have e3 : ⟪f, siteMask G.Om0 f⟫ = ‖siteMask G.Om0 f‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq]
        calc ⟪f, siteMask G.Om0 f⟫ = ⟪f, siteMask G.Om0 (siteMask G.Om0 f)⟫ := by rw [siteMask_idem]
          _ = ⟪siteMask G.Om0 f, siteMask G.Om0 f⟫ := (siteMask_symm _ _ _).symm
      rw [e1, e2, e3]
    rw [h2] at h1
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
  -- Lm f = Bq* w, and Lm f = f
  have hLf : Lm f = ContinuousLinearMap.adjoint B w := hLI _
  have hlapf : lapDir G U f = 0 := by
    rw [lapDir_eq_mask_lap_all G U f, hmf]
    simp
  have hLf2 : Lm f = f := by
    rw [hLm]
    show (lapDir G U + (1 - siteMask G.Om0)) f = f
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hlapf, hmf,
      sub_zero, zero_add]
  have hfB : f = ContinuousLinearMap.adjoint B w := by rw [← hLf2, hLf]
  -- m (Bq* w) = Bq* w
  have hmB : siteMask G.Om0 (ContinuousLinearMap.adjoint B w) = ContinuousLinearMap.adjoint B w := by
    refine ext_inner_left ℝ (fun u => ?_)
    rw [← siteMask_symm, ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right, hB,
      Bq_mask hP hell]
  have hB0 : ContinuousLinearMap.adjoint B w = 0 := by
    rw [← hmB, ← hfB, hmf]
  exact Bq_star_inj hP hell w hB0

#print axioms gOf_ne_zero_flat

end AdalyFormal.CoverOmegaTwo
