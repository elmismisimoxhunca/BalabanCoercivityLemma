import GN1

/-!
# GN2 (text port of nonflat_hunit_20261009/NF2b.lean to the r7 carrier, namespace renamed) -- consequences of NF2 at the full Dirichlet region `Ω₀ = univ`: `D* W = (1-R) D*`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {L : PeriodicLatticeExtent}

theorem siteMask_univ (f : SiteL2 L) : siteMask (Set.univ : Set (PeriodicLatticeSite L)) f = f :=
  siteMask_of_support _ _ (fun x hx => absurd (Set.mem_univ x) hx)

theorem lapDir_univ (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (f : SiteL2 L) :
    lapDir G U f = lapFull U f := by
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply, hOm, siteMask_univ]

/-- **`D* W x = (1 - R) D* x`**, at every background `U` (full Dirichlet region, Dirichlet operator invertible). -/
theorem gradAdj_Wop (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0))) (x : BondFnL2 L) :
    gradAdj U (Wop G U a x) = gradAdj U x - Rproj G U (gradAdj U x) := by
  have h := (Gp_Rproj_mem G U a hu (gradAdj U x)).2
  rw [lapDir_univ G hOm] at h
  have hl : gradAdj U (gradL2 U (Gp G U a (Rproj G U (gradAdj U x)))) =
      lapFull U (Gp G U a (Rproj G U (gradAdj U x))) := rfl
  simp only [Wop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, map_sub]
  rw [hl, h]

/-- `‖D G' R s‖² = ⟨G' R s, R s⟩`. -/
theorem norm_grad_Gp_Rproj_sq (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0))) (s : SiteL2 L) :
    ‖gradL2 U (Gp G U a (Rproj G U s))‖ ^ 2 = ⟪Gp G U a (Rproj G U s), Rproj G U s⟫ := by
  have h := (Gp_Rproj_mem G U a hu s).2
  rw [lapDir_univ G hOm] at h
  rw [← inner_lapFull, h]

#print axioms gradAdj_Wop
#print axioms norm_grad_Gp_Rproj_sq

end AdalyFormal.SliceCoerc
