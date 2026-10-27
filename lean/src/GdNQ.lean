import GdH1

/-!
# GdNQ -- the gauge potential `f = G' R D* A` of `W A = A - D f` lies in `N(Q')`.

`R f = Δ_U l₀` with `l₀ ∈ N(Q')` (`Rproj_minimiser`); `Q'*aQ' l₀ = 0` because `Q'_j l₀ = 0` on `Λ_j`; hence the Dirichlet operator
`Δ'_a|Ω₀` maps `l₀` to `Δ_U l₀` and `G' (R f) = l₀` (when the Dirichlet operator is invertible; otherwise `G' = 0`).
Consequence: `f` vanishes off `Ω₀` and on `Λ₀` (level-0 constraint, `Q'_0 = id`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {L : PeriodicLatticeExtent}

theorem Qpa_apply_NQp (G : TowerGeom L) (U : Cfg L) (a : ℝ) {l0 : SiteL2 L} (hl0 : l0 ∈ NQp G U) :
    Qpa G U a l0 = 0 := by
  classical
  unfold Qpa
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_eq_zero (fun j hj => Finset.sum_eq_zero (fun y _ => ?_))
  split_ifs with hy
  · have hjk : j ≤ G.k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h0 := hl0.2 j hjk y hy
    simp [h0]
  · simp

theorem siteMask_of_out (S : Set (PeriodicLatticeSite L)) {f : SiteL2 L} (h : ∀ x, x ∉ S → f x = 0) :
    siteMask S f = f := by
  classical
  ext x
  rw [siteMask_apply]
  by_cases hx : x ∈ S
  · simp [hx]
  · simp [hx, h x hx]

/-- **the gauge potential lies in `N(Q')`.** -/
theorem Gp_Rproj_mem_NQp (G : TowerGeom L) (U : Cfg L) (a : ℝ) (f : SiteL2 L) :
    Gp G U a (Rproj G U f) ∈ NQp G U := by
  obtain ⟨l0, hl0, hR, -⟩ := Rproj_minimiser G U f
  by_cases hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0))
  · obtain ⟨u, hu'⟩ := hu
    set X : SiteL2 L →L[ℝ] SiteL2 L := DelpA G U a + (1 - siteMask G.Om0) with hX
    have hml : siteMask G.Om0 l0 = l0 := siteMask_of_out _ hl0.1
    have hQ0 : Qpa G U a l0 = 0 := Qpa_apply_NQp G U a hl0
    have hXl : X l0 = lapDir G U l0 := by
      have e1 : DelpA G U a l0 = lapDir G U l0 := by
        unfold DelpA lapDir
        simp only [ContinuousLinearMap.comp_apply, hml, ContinuousLinearMap.add_apply, hQ0, add_zero]
      show (DelpA G U a + (1 - siteMask G.Om0)) l0 = _
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hml,
        sub_self, add_zero]
      exact e1
    have hmR : siteMask G.Om0 (Rproj G U f) = Rproj G U f := by
      rw [hR]
      unfold lapDir
      simp only [ContinuousLinearMap.comp_apply]
      rw [siteMask_idem]
    have key : Gp G U a (Rproj G U f) = l0 := by
      unfold Gp
      simp only [ContinuousLinearMap.comp_apply]
      rw [hmR, ← hX, ← hu', Ring.inverse_unit, hR, ← hXl, ← hu']
      exact ContinuousLinearMap.ext_iff.mp (u.inv_mul) l0
    rw [key]; exact hl0
  · have : Gp G U a (Rproj G U f) = 0 := by
      unfold Gp
      simp only [ContinuousLinearMap.comp_apply]
      rw [Ring.inverse_non_unit _ hu]
      simp
    rw [this]; exact (NQp G U).zero_mem

/-- the potential vanishes off `Ω₀`. -/
theorem Gp_Rproj_out (G : TowerGeom L) (U : Cfg L) (a : ℝ) (f : SiteL2 L) {x : PeriodicLatticeSite L}
    (hx : x ∉ G.Om0) : (Gp G U a (Rproj G U f)) x = 0 :=
  (Gp_Rproj_mem_NQp G U a f).1 x hx

/-- the potential vanishes on `Λ₀` (level-0 constraint of `N(Q')`, `Q'_0 = id`). -/
theorem Gp_Rproj_lam0 (G : TowerGeom L) (U : Cfg L) (a : ℝ) (f : SiteL2 L) {x : PeriodicLatticeSite L}
    (hx : x ∈ G.Lam 0) : (Gp G U a (Rproj G U f)) x = 0 := by
  have h := (Gp_Rproj_mem_NQp G U a f).2 0 (Nat.zero_le _) x hx
  rw [Qlev_apply] at h
  exact h

#print axioms Qpa_apply_NQp
#print axioms Gp_Rproj_mem_NQp
#print axioms Gp_Rproj_out
#print axioms Gp_Rproj_lam0

end AdalyFormal.D1Guarded
