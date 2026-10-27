import PB2g
import ASAl2

/-!
# ASAl3 -- `hu_al`, `poincare_al`: PB2g with the tower bound on ALIGNED bonds (ASAl1/ASAl2); the proofs are PB2g's verbatim.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.AsmM0

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp Tower)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.SliceCoerc (GF fullTower_Om0)
open AdalyFormal.PortSlice

theorem site_coercive_GF_al (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a) (α E : ℝ)
    (hU : frobSupBond U ≤ α / (ell : ℝ) ^ k) (δ : ℕ → ℝ)
    (hδ : ∀ i, i < k → AlignedLinkBound (ell ^ i) (bgTower (GF ell k Lu) U i) (δ i))
    (hE : ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i ≤ E)
    (f : SiteL2 (scaleUp ell k Lu)) :
    (1 - 72 * α ^ 2 - 4 * E ^ 2) * ‖f‖ ^ 2
      ≤ max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 * ⟪f, DelpA (GF ell k Lu) U a f⟫ := by
  rw [GF_eq_fullGeom] at hδ ⊢
  exact AdalyFormal.AsmM0.site_coercive_nested_al ell k hell (scaleUp_dvd ell k (by omega) Lu) U a ha α E hU δ hδ hE f

theorem hu_al (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a) (α E : ℝ) (hpos : 72 * α ^ 2 + 4 * E ^ 2 < 1)
    (hU : frobSupBond U ≤ α / (ell : ℝ) ^ k) (δ : ℕ → ℝ)
    (hδ : ∀ i, i < k → AlignedLinkBound (ell ^ i) (bgTower (GF ell k Lu) U i) (δ i))
    (hE : ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i ≤ E) :
    IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)) := by
  have hM := mM_pos a ha ell k hell
  refine AdalyFormal.SiteCoercivity.unit_of_site_coercive (GF ell k Lu) (fullTower_Om0 ell k Lu) U a
    (c := (1 - 72 * α ^ 2 - 4 * E ^ 2) / (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2)) (by apply div_pos <;> linarith) (fun f => ?_)
  have h := site_coercive_GF_al ell k Lu hell U a ha α E hU δ hδ hE f
  rw [div_mul_eq_mul_div, div_le_iff₀ hM]
  linarith [h]

theorem poincare_al (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a) (α E : ℝ) (hpos : 72 * α ^ 2 + 4 * E ^ 2 < 1)
    (hU : frobSupBond U ≤ α / (ell : ℝ) ^ k) (δ : ℕ → ℝ)
    (hδ : ∀ i, i < k → AlignedLinkBound (ell ^ i) (bgTower (GF ell k Lu) U i) (δ i))
    (hE : ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i ≤ E) :
    ∀ ν ∈ NQp (GF ell k Lu) U,
      ‖ν‖ ≤ Real.sqrt (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 / (1 - 72 * α ^ 2 - 4 * E ^ 2))
        * ‖AdalyFormal.IngredientFamilyR2.gradL2 U ν‖ := by
  intro ν hν
  have hM := mM_pos a ha ell k hell
  have hden : 0 < 1 - 72 * α ^ 2 - 4 * E ^ 2 := by linarith
  have h := site_coercive_GF_al ell k Lu hell U a ha α E hU δ hδ hE ν
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

#print axioms site_coercive_GF_al
#print axioms hu_al
#print axioms poincare_al

end AdalyFormal.AsmM0
