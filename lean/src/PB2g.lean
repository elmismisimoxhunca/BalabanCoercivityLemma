import PB2

/-!
# PB2g -- item (2), GENERAL tower bound: site coercivity / `hu` / Poincare on `N(Q'(U))` from the nested form
`site_coercive_nested` (PSiteC7), hypotheses `frobSupBond U ≤ α/ell^k`, `frobSupBond (bgTower i) ≤ δ_i` (`i < k`), `Σ_{i<k} 6(ell-1)δ_i ≤ E`,
constant `1 - 72 α² - 4 E²` (the class bound of PB2 is the case `δ_i = ρ ell^i/ell^k`, `α = ρ`, `E = 6ρ`; this form also accepts the
tree's crude tower bound `δ_i = blkConstOf(ell)^i α/ell^k`, i.e. Small `U` alone, k-dependent).
Standard axioms only (each declaration's printed axiom line).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.PortSlice

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp Tower)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.SliceCoerc (GF fullTower_Om0)

theorem site_coercive_GF_gen (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a) (α E : ℝ)
    (hU : frobSupBond U ≤ α / (ell : ℝ) ^ k) (δ : ℕ → ℝ)
    (hδ : ∀ i, i < k → frobSupBond (bgTower (GF ell k Lu) U i) ≤ δ i)
    (hE : ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i ≤ E)
    (f : SiteL2 (scaleUp ell k Lu)) :
    (1 - 72 * α ^ 2 - 4 * E ^ 2) * ‖f‖ ^ 2
      ≤ max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 * ⟪f, DelpA (GF ell k Lu) U a f⟫ := by
  rw [GF_eq_fullGeom] at hδ ⊢
  exact AdalyFormal.SiteCoercivity.site_coercive_nested ell k hell (scaleUp_dvd ell k (by omega) Lu) U a ha α E hU δ hδ hE f

theorem hu_gen (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a) (α E : ℝ) (hpos : 72 * α ^ 2 + 4 * E ^ 2 < 1)
    (hU : frobSupBond U ≤ α / (ell : ℝ) ^ k) (δ : ℕ → ℝ)
    (hδ : ∀ i, i < k → frobSupBond (bgTower (GF ell k Lu) U i) ≤ δ i)
    (hE : ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i ≤ E) :
    IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)) := by
  have hM := mM_pos a ha ell k hell
  refine AdalyFormal.SiteCoercivity.unit_of_site_coercive (GF ell k Lu) (fullTower_Om0 ell k Lu) U a
    (c := (1 - 72 * α ^ 2 - 4 * E ^ 2) / (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2)) (by apply div_pos <;> linarith) (fun f => ?_)
  have h := site_coercive_GF_gen ell k Lu hell U a ha α E hU δ hδ hE f
  rw [div_mul_eq_mul_div, div_le_iff₀ hM]
  linarith [h]

theorem poincare_gen (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a) (α E : ℝ) (hpos : 72 * α ^ 2 + 4 * E ^ 2 < 1)
    (hU : frobSupBond U ≤ α / (ell : ℝ) ^ k) (δ : ℕ → ℝ)
    (hδ : ∀ i, i < k → frobSupBond (bgTower (GF ell k Lu) U i) ≤ δ i)
    (hE : ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i ≤ E) :
    ∀ ν ∈ NQp (GF ell k Lu) U,
      ‖ν‖ ≤ Real.sqrt (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 / (1 - 72 * α ^ 2 - 4 * E ^ 2))
        * ‖AdalyFormal.IngredientFamilyR2.gradL2 U ν‖ := by
  intro ν hν
  have hM := mM_pos a ha ell k hell
  have hden : 0 < 1 - 72 * α ^ 2 - 4 * E ^ 2 := by linarith
  have h := site_coercive_GF_gen ell k Lu hell U a ha α E hU δ hδ hE ν
  have hq : ⟪ν, DelpA (GF ell k Lu) U a ν⟫ = ‖AdalyFormal.IngredientFamilyR2.gradL2 U ν‖ ^ 2 := by
    rw [AdalyFormal.SiteCoercivity.DelpA_univ _ (fullTower_Om0 ell k Lu), inner_add_right,
      AdalyFormal.SiteCoercivity.Qpa_form_zero_of_NQp (GF ell k Lu) U a hν, add_zero, inner_lapFull]
  rw [hq] at h
  have h2 : ‖ν‖ ^ 2 ≤ (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 / (1 - 72 * α ^ 2 - 4 * E ^ 2))
      * ‖AdalyFormal.IngredientFamilyR2.gradL2 U ν‖ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    linarith [h]
  calc ‖ν‖ = Real.sqrt (‖ν‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 / (1 - 72 * α ^ 2 - 4 * E ^ 2))
          * ‖AdalyFormal.IngredientFamilyR2.gradL2 U ν‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 / (1 - 72 * α ^ 2 - 4 * E ^ 2))
          * ‖AdalyFormal.IngredientFamilyR2.gradL2 U ν‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

#print axioms site_coercive_GF_gen
#print axioms hu_gen
#print axioms poincare_gen

end AdalyFormal.PortSlice
