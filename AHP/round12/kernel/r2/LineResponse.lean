import DrEquiv
/-! Quadratic responses on a charged line: the unit response hull is a singleton. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.Round12.Kernel.Response
open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A quarter-turn invariant quadratic map is radial on each charged complex line. -/
theorem quadratic_on_charged_line (Q : E → F) (hQ : IsQuadMap Q)
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ x, Q (J x) = Q x)
    (u : E) (hu : J (J u) = -u) (a b : ℝ) :
    Q (a • u + b • J u) = (a^2+b^2) • Q u := by
  obtain ⟨B, hB⟩ := hQ
  have he := hJ u
  have hm := hJ (u + J u)
  rw [map_add, hu] at hm
  simp only [hB, map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply] at he hm
  have hc : B u (J u) + B (J u) u = 0 := by
    have hh : (2 : ℝ) • (B u (J u) + B (J u) u) = 0 := by
      calc
        _ = (B u u + B (J u) u + (B u (J u) + B (J u) (J u))) -
            (B (J u) (J u) + -B u (J u) + -(B (J u) u + -B u u)) := by module
        _ = 0 := sub_eq_zero.mpr hm.symm
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  simp only [hB, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  calc
    _ = (a^2) • B u u + (b^2) • B (J u) (J u) +
        (a*b) • (B u (J u) + B (J u) u) := by module
    _ = (a^2+b^2) • B u u := by rw [hc, smul_zero, add_zero, he, add_smul]

/-- The isometric quarter-turn gives the matching norm identity. -/
theorem norm_sq_on_charged_line (J : E ≃ₗᵢ[ℝ] E)
    (u : E) (hu : J (J u) = -u) (a b : ℝ) :
    ‖a • u + b • J u‖^2 = (a^2+b^2) * ‖u‖^2 := by
  have h := J.inner_map_map u (J u)
  rw [hu, inner_neg_right] at h
  have hc := real_inner_comm (J u) u
  have hz : ⟪u,J u⟫ = 0 := by linarith
  have hz' : ⟪J u,u⟫ = 0 := by linarith
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hz, hz', J.inner_map_map, real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial]
  ring

/-- A generator determines every vector response in its charged span. -/
theorem response_eq_norm_ratio (Q : E → F) (hQ : IsQuadMap Q)
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ x, Q (J x) = Q x)
    (u : E) (hu : J (J u) = -u) (hne : u ≠ 0)
    (v : E) (hv : v ∈ Submodule.span ℝ ({u,J u} : Set E)) :
    Q v = (‖v‖^2 / ‖u‖^2) • Q u := by
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hv
  rw [quadratic_on_charged_line Q hQ J hJ u hu,
    norm_sq_on_charged_line J u hu]
  rw [mul_div_cancel_right₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hne))]

/-- Every nonzero vector in this span is visible iff the generator is visible. -/
theorem response_ne_zero_iff (Q : E → F) (hQ : IsQuadMap Q)
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ x, Q (J x) = Q x)
    (u : E) (hu : J (J u) = -u) (hne : u ≠ 0)
    (v : E) (hv : v ∈ Submodule.span ℝ ({u,J u} : Set E)) (hvn : v ≠ 0) :
    Q v ≠ 0 ↔ Q u ≠ 0 := by
  rw [response_eq_norm_ratio Q hQ J hJ u hu hne v hv, smul_ne_zero_iff]
  simp [pow_ne_zero _ (norm_ne_zero_iff.mpr hvn),
    pow_ne_zero _ (norm_ne_zero_iff.mpr hne)]

/-- Unit responses of an arbitrary nonzero subspace contained in the charged line
are a SINGLE point, not merely contained in a pointed cone. -/
theorem unit_response_image (K : Submodule ℝ E) (Q : E → F) (hQ : IsQuadMap Q)
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ x, Q (J x) = Q x)
    (u : E) (hu : J (J u) = -u) (hne : u ≠ 0) (huk : u ∈ K)
    (hK : K ≤ Submodule.span ℝ ({u,J u} : Set E)) :
    Q '' {v | v ∈ K ∧ ‖v‖ = 1} = {(‖u‖^2)⁻¹ • Q u} := by
  ext w
  constructor
  · rintro ⟨v,⟨hv,hvn⟩,rfl⟩
    rw [Set.mem_singleton_iff, response_eq_norm_ratio Q hQ J hJ u hu hne v (hK hv), hvn]
    simp
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    refine ⟨‖u‖⁻¹ • u, ⟨K.smul_mem _ huk, ?_⟩, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
    · rw [hQ.smul_sq, inv_pow]

#print axioms quadratic_on_charged_line
#print axioms norm_sq_on_charged_line
#print axioms response_eq_norm_ratio
#print axioms response_ne_zero_iff
#print axioms unit_response_image
end AdalyFormal.Round12.Kernel.Response
