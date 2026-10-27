import NsCvO41

/-!
# CvO42 -- `<Q w, zrow rho> = c0 Σ_x θ_w(x,1) Wt(x₀)` for sigma_3-valued `w` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

open Classical in
theorem pair_Q_zrow {ell c : ℕ} {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : StagSetup L ell c G isRow) (t : ℝ) (htπ : |t| < tcap ell)
    (w : BondFnL2 L) (hw : SigB (WithLp.ofLp w)) (ρ : ℕ → ℕ → ℝ) :
    (inner ℝ (QfullOf G (stagCfg c t) w) (zrow G ρ) : ℝ) =
      c0 * ∑ x : PeriodicLatticeSite L, thetaOf (WithLp.ofLp w) (x, 1) * Wt ell isRow ρ (x 0).val := by
  rw [pair_levels S t htπ w hw ρ]
  obtain ⟨l0, l1, l2⟩ := lev_sums S.hell S.hdiv (thetaOf (WithLp.ofLp w)) (Hrow isRow ρ)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [l0, l1, l2]
  have hW : ∀ x : PeriodicLatticeSite L, thetaOf (WithLp.ofLp w) (x, 1) * Wt ell isRow ρ (x 0).val =
      (((ell : ℝ) ^ 0)⁻¹ * ((((ell : ℝ) ^ 2)⁻¹) ^ 0) * (Hrow isRow ρ 0 (ell ^ 0 * ((x 0).val / ell ^ 0)) * thetaOf (WithLp.ofLp w) (x, 1))) +
      (((ell : ℝ) ^ 1)⁻¹ * ((((ell : ℝ) ^ 2)⁻¹) ^ 1) * (Hrow isRow ρ 1 (ell ^ 1 * ((x 0).val / ell ^ 1)) * thetaOf (WithLp.ofLp w) (x, 1))) +
      (((ell : ℝ) ^ 2)⁻¹ * ((((ell : ℝ) ^ 2)⁻¹) ^ 2) * (Hrow isRow ρ 2 (ell ^ 2 * ((x 0).val / ell ^ 2)) * thetaOf (WithLp.ofLp w) (x, 1))) := by
    intro x
    simp only [Wt, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Hrow]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hW x), Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

#print axioms pair_Q_zrow

end AdalyFormal.CoverOmega
