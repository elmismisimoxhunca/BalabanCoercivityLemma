import GN2

/-!
# SC2 -- consumer: site coercivity of `Δ'_a(U)` (whole torus) gives `hu` and `‖G'‖ ≤ 1/c`, hence the NF5/NF6 hypotheses
with `C_G = 1/c`; and arithmetic of the resulting thresholds.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.SiteCoercivity

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SliceCoerc

variable {L : PeriodicLatticeExtent}

theorem siteMask_univ_eq_one : siteMask (Set.univ : Set (PeriodicLatticeSite L)) = 1 := by
  ext1 f
  exact siteMask_univ f

theorem unit_of_site_coercive (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (a : ℝ) {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ f : SiteL2 L, c * ‖f‖ ^ 2 ≤ ⟪f, DelpA G U a f⟫) :
    IsUnit (DelpA G U a + (1 - siteMask G.Om0)) := by
  rw [hOm, siteMask_univ_eq_one, sub_self, add_zero]
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hinj : Function.Injective (DelpA G U a) := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have h := hc f
    rw [hf, inner_zero_right] at h
    have h2 : ‖f‖ ^ 2 ≤ 0 := by nlinarith
    have : ‖f‖ = 0 := by nlinarith [norm_nonneg f]
    exact norm_eq_zero.mp this
  exact ⟨hinj, LinearMap.surjective_of_injective (f := (DelpA G U a : SiteL2 L →ₗ[ℝ] SiteL2 L)) hinj⟩

theorem Gp_norm_le_of_site_coercive (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (a : ℝ) {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ f : SiteL2 L, c * ‖f‖ ^ 2 ≤ ⟪f, DelpA G U a f⟫) (g : SiteL2 L) :
    ‖Gp G U a g‖ ≤ (1 / c) * ‖g‖ := by
  have hu := unit_of_site_coercive G hOm U a hc0 hc
  have hs := (Gp_spec G U a hu g).2
  rw [hOm, siteMask_univ_eq_one] at hs
  simp only [ContinuousLinearMap.one_apply] at hs
  have h := hc (Gp G U a g)
  rw [hs] at h
  have h2 : ⟪Gp G U a g, g⟫ ≤ ‖Gp G U a g‖ * ‖g‖ := real_inner_le_norm _ _
  have hv := norm_nonneg (Gp G U a g)
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc0]
  by_cases h0 : ‖Gp G U a g‖ = 0
  · rw [h0, zero_mul]; exact norm_nonneg g
  · have hp : 0 < ‖Gp G U a g‖ := lt_of_le_of_ne hv (Ne.symm h0)
    nlinarith


/-- elementary: the NF5 `T`-coefficient is at least `1/2` once `x = α₀ C_G ≤ 1/1200`. -/
theorem coeff_ge_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 1200) : (1 / 2 : ℝ) ≤ 1 - 384 * x ^ 2 - 544 * x := by
  nlinarith

/-- exact positivity threshold of the NF5 `T`-coefficient: `x ≤ 1/544` already makes `1 - 384x² - 544x`
nonnegative fails at `1/544` (value `-384/544² < 0`) but holds for `x ≤ 1/545`. -/
theorem coeff_pos_of_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 545) : 0 < 1 - 384 * x ^ 2 - 544 * x := by
  nlinarith

theorem coeff_not_pos_at_544 : ¬ (0 < 1 - 384 * (1 / 544 : ℝ) ^ 2 - 544 * (1 / 544 : ℝ)) := by
  norm_num

#print axioms unit_of_site_coercive
#print axioms Gp_norm_le_of_site_coercive
#print axioms coeff_ge_half
#print axioms coeff_pos_of_le

end AdalyFormal.SiteCoercivity
