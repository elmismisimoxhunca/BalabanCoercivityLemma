import PSiteC18

/-!
# SiteC21 -- the covariant Poincare inequality ON `N(Q'(U))` (the subspace of (3.21)), as a corollary of the proper-tower site coercivity:
for `ν ∈ N(Q')` the mass term vanishes.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.SiteCoercivity

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

theorem Qpa_form_zero_of_NQp (G : TowerGeom L) (U : Cfg L) (a : ℝ) {ν : SiteL2 L} (hν : ν ∈ NQp G U) :
    ⟪ν, Qpa G U a ν⟫ = 0 := by
  rw [inner_Qpa]
  refine Finset.sum_eq_zero (fun j hj => Finset.sum_eq_zero (fun y _ => ?_))
  by_cases hy : y ∈ G.Lam j
  · rw [if_pos hy, hν.2 j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) y hy]
    simp
  · rw [if_neg hy]

/-- **Covariant Poincare inequality on `N(Q'(U))`, proper (Dirichlet) towers**: `(1 − 72α² − 4E²)‖ν‖² ≤ max(6,16/(3a)) n² ‖D_U ν‖²`. -/
theorem poincare_NQp_proper (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (U : Cfg L) (a : ℝ) (ha : 0 < a) (α E : ℝ) (hα : 0 ≤ α)
    (hU : ∀ b : Bond L, periodicLatticeShift b.1 b.2 ∈ G.Om0 →
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α / (ell : ℝ) ^ k)
    (δ : ℕ → ℝ) (hδ0 : ∀ i, 0 ≤ δ i)
    (hT : ∀ i, i < k → ∀ z ∈ G.Om0, ∀ μ : Fin 3,
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ i)
    (hE : ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i ≤ E)
    {ν : SiteL2 L} (hν : ν ∈ NQp G U) :
    (1 - 72 * α ^ 2 - 4 * E ^ 2) * ‖ν‖ ^ 2
      ≤ max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 * ‖gradL2 U ν‖ ^ 2 := by
  have h := site_coercive_proper_core ell k hell hdvd hP U a ha α E hα hU δ hδ0 hT hE ν hν.1
  rw [Qpa_form_zero_of_NQp G U a hν, add_zero] at h
  exact h

#print axioms poincare_NQp_proper

end AdalyFormal.SiteCoercivity
