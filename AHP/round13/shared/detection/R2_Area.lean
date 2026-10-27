import DrEquiv

/-! Exact alternating-area expansion of a two-color quadratic map.
This is algebra, not a nonvanishing assertion for any crossing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.Round13.Detection.Area
open AdalyFormal.IngredientFamilyR2
open Finset
variable {S X Y : Type*} [AddCommGroup S] [Module ℝ S]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- Zero pure-color terms leave a bilinear mixed term. -/
theorem mixed_bilinear (Q : X → Y) (hQ : IsQuadMap Q)
    (a b : S →ₗ[ℝ] X) (ha : ∀ f, Q (a f) = 0) (hb : ∀ g, Q (b g) = 0) :
    ∃ B : S →ₗ[ℝ] S →ₗ[ℝ] Y, ∀ f g, Q (a f + b g) = B f g := by
  obtain ⟨β, hβ⟩ := hQ
  refine ⟨β.compl₁₂ a b + β.flip.compl₁₂ a b, ?_⟩
  intro f g
  have ha' := ha f
  have hb' := hb g
  rw [hβ] at ha' hb'
  rw [hβ]
  simp only [map_add, LinearMap.add_apply, ha', hb', zero_add, add_zero,
    LinearMap.compl₁₂_apply, LinearMap.flip_apply]
  exact add_comm _ _

/-- Quarter-color rotation makes that bilinear term alternating. -/
theorem mixed_alternating (Q : X → Y) (hQ : IsQuadMap Q)
    (a b : S →ₗ[ℝ] X) (ha : ∀ f, Q (a f) = 0) (hb : ∀ g, Q (b g) = 0)
    (hrot : ∀ f g, Q (a g - b f) = Q (a f + b g)) :
    ∃ B : S →ₗ[ℝ] S →ₗ[ℝ] Y,
      (∀ f g, Q (a f + b g) = B f g) ∧ (∀ f g, B g f = -B f g) := by
  obtain ⟨B, hB⟩ := mixed_bilinear Q hQ a b ha hb
  refine ⟨B, hB, ?_⟩
  intro f g
  have h := hrot f g
  rw [sub_eq_add_neg, ← map_neg b, hB, map_neg, hB] at h
  exact neg_eq_iff_eq_neg.mp h

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The coefficient is the actual value of the mixed map on two scalar atoms. -/
theorem bilinear_matrix (B : (I → ℝ) →ₗ[ℝ] (I → ℝ) →ₗ[ℝ] Y)
    (f g : I → ℝ) :
    B f g = ∑ i : I, ∑ j : I,
      (f i * g j) • B (Pi.single i 1) (Pi.single j 1) := by
  have he (f : I → ℝ) : f = ∑ i : I, f i • Pi.single i 1 := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [he f, he g]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- Ordered-pair convention: the factor 1/2 pays for counting each pair twice. -/
theorem bilinear_area (B : (I → ℝ) →ₗ[ℝ] (I → ℝ) →ₗ[ℝ] Y)
    (hskew : ∀ f g, B g f = -B f g) (f g : I → ℝ) :
    B f g = (1 / 2 : ℝ) • ∑ i : I, ∑ j : I,
      (f i * g j - g i * f j) • B (Pi.single i 1) (Pi.single j 1) := by
  have he : (∑ i : I, ∑ j : I,
      (f i * g j - g i * f j) • B (Pi.single i 1) (Pi.single j 1)) =
      B f g - B g f := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← bilinear_matrix, ← bilinear_matrix]
  rw [he, hskew f g, sub_neg_eq_add, ← two_smul ℝ (B f g), smul_smul]
  norm_num

/-- Full finite alternating-area dictionary; it does not supply a nonzero area. -/
theorem quadratic_area (Q : X → Y) (hQ : IsQuadMap Q)
    (a b : (I → ℝ) →ₗ[ℝ] X) (ha : ∀ f, Q (a f) = 0) (hb : ∀ g, Q (b g) = 0)
    (hrot : ∀ f g, Q (a g - b f) = Q (a f + b g)) (f g : I → ℝ) :
    Q (a f + b g) = (1 / 2 : ℝ) • ∑ i : I, ∑ j : I,
      (f i * g j - g i * f j) • Q (a (Pi.single i 1) + b (Pi.single j 1)) := by
  obtain ⟨B, hB, hskew⟩ := mixed_alternating Q hQ a b ha hb hrot
  simp_rw [hB]
  exact bilinear_area B hskew f g

#print axioms mixed_bilinear
#print axioms mixed_alternating
#print axioms bilinear_matrix
#print axioms bilinear_area
#print axioms quadratic_area
end AdalyFormal.Round13.Detection.Area
