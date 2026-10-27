import ZR2Ops2

/-!
# GN1 (text port of nonflat_hunit_20261009/NF2.lean to the r7 carrier, namespace renamed) -- exact structure of the genuine gauge-fixing map `W = I - D G' R D*` at ANY background `U`
(full Dirichlet region `Ω₀ = univ`), given invertibility of the Dirichlet operator (the print's
"`Δ'_a` is positive", p.395).  Nothing here is perturbative; no smallness.

 * `Gp_Rproj_mem`   : `G' R s ∈ N(Q')` and `Δ_U (G' R s) = R s`.
 * `gradAdj_Wop`    : `D* W x = D* x - R D* x`   (so `D*(Wx) = (1-R) D*x`).
 * `norm_grad_Gp_Rproj_sq` : `‖D G' R s‖² = ⟨G' R s, R s⟩`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {L : PeriodicLatticeExtent}

theorem siteMask_of_support (S : Set (PeriodicLatticeSite L)) (f : SiteL2 L)
    (h : ∀ x, x ∉ S → f x = 0) : siteMask S f = f := by
  classical
  refine PiLp.ext (fun x => ?_)
  rw [siteMask_apply]
  by_cases hx : x ∈ S
  · simp [hx]
  · simp [hx, h x hx]

theorem Qpa_apply_of_NQp (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ν : SiteL2 L)
    (hν : ν ∈ NQp G U) : Qpa G U a ν = 0 := by
  classical
  unfold Qpa
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  refine Finset.sum_eq_zero (fun y _ => ?_)
  split_ifs with hy
  · have hj' : j ≤ G.k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h0 := hν.2 j hj' y hy
    simp [h0]
  · simp

theorem Gp_lapDir_of_NQp (G : TowerGeom L) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0))) (ν : SiteL2 L) (hν : ν ∈ NQp G U) :
    Gp G U a (lapDir G U ν) = ν := by
  obtain ⟨u, hu'⟩ := hu
  have hmν : siteMask G.Om0 ν = ν := siteMask_of_support _ _ hν.1
  have hD : DelpA G U a ν = lapDir G U ν := by
    unfold DelpA lapDir
    simp only [ContinuousLinearMap.comp_apply, hmν, ContinuousLinearMap.add_apply,
      Qpa_apply_of_NQp G U a ν hν, add_zero]
  have hX : (DelpA G U a + (1 - siteMask G.Om0)) ν = lapDir G U ν := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, hmν, sub_self, add_zero, hD]
  have hmask : siteMask G.Om0 (lapDir G U ν) = lapDir G U ν := by
    unfold lapDir
    simp only [ContinuousLinearMap.comp_apply]
    exact siteMask_idem _ _
  unfold Gp
  simp only [ContinuousLinearMap.comp_apply]
  rw [hmask, ← hX, ← hu']
  rw [Ring.inverse_unit]
  exact ContinuousLinearMap.ext_iff.mp u.inv_mul _

theorem Gp_Rproj_mem (G : TowerGeom L) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0))) (s : SiteL2 L) :
    Gp G U a (Rproj G U s) ∈ NQp G U ∧ lapDir G U (Gp G U a (Rproj G U s)) = Rproj G U s := by
  have hR : Rproj G U s ∈ RImage G U := Submodule.starProjection_apply_mem _ _
  obtain ⟨ν, hν, hνR⟩ := Submodule.mem_map.mp hR
  have hνR' : lapDir G U ν = Rproj G U s := hνR
  have hG : Gp G U a (Rproj G U s) = ν := by
    rw [← hνR']; exact Gp_lapDir_of_NQp G U a hu ν hν
  rw [hG]
  exact ⟨hν, hνR'⟩

#print axioms siteMask_of_support
#print axioms Qpa_apply_of_NQp
#print axioms Gp_lapDir_of_NQp
#print axioms Gp_Rproj_mem

end AdalyFormal.SliceCoerc
