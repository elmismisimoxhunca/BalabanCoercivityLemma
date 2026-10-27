import CvS2b

/-!
# CvS3a -- the constrained form `⟪y, (Q A⁻¹ Q*)⁻¹ y⟫` sees `A` only on `ker (π Q)` (lane cover_strong_20261016)

Abstract linear algebra (finite-dimensional real inner product spaces).
* `mem_range_adjoint_of_perp`: `z ⊥ ker T` ⇒ `z ∈ range T*`.
* **`inv_form_congr`**: let `π` be symmetric on `F`, `A, A'` units with `N = Q A⁻¹ Q*`, `N' = Q A'⁻¹ Q*` units.  If
  `⟪x', (A' − A) x⟫ = 0` for all `x, x'` with `π (Q x) = π (Q x') = 0`, then `⟪y, N⁻¹ y⟫ = ⟪y, N'⁻¹ y⟫` for every `y` with `π y = 0`.
  (Proof: `x = A⁻¹Q*N⁻¹y` has `Q x = y`; `(A' − A) x = Q* π ν`; so `A' x = Q*(N⁻¹y + πν)`, hence `N'⁻¹ y = N⁻¹ y + π ν`, and `⟪y, πν⟫ = 0`.)
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverStrong

open scoped RealInnerProductSpace

theorem inverse_apply_of_unit {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {M : X →L[ℝ] X} (hM : IsUnit M) (z : X) : Ring.inverse M (M z) = z := by
  obtain ⟨u, rfl⟩ := hM
  rw [Ring.inverse_unit]
  exact ContinuousLinearMap.ext_iff.mp u.inv_mul z

section Abstract

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem mem_range_adjoint_of_perp (T : E →L[ℝ] F) (z : E) (hz : ∀ x, T x = 0 → ⟪x, z⟫ = 0) :
    ∃ ν : F, ContinuousLinearMap.adjoint T ν = z := by
  have h1 : z ∈ (LinearMap.ker (T : E →ₗ[ℝ] F))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    exact hz u hu
  have h2 := ContinuousLinearMap.orthogonal_ker T
  have hcl : (LinearMap.range ((ContinuousLinearMap.adjoint T : F →L[ℝ] E) : F →ₗ[ℝ] E)).topologicalClosure =
      LinearMap.range ((ContinuousLinearMap.adjoint T : F →L[ℝ] E) : F →ₗ[ℝ] E) :=
    IsClosed.submodule_topologicalClosure_eq (Submodule.closed_of_finiteDimensional _)
  have h3 : z ∈ LinearMap.range ((ContinuousLinearMap.adjoint T : F →L[ℝ] E) : F →ₗ[ℝ] E) := by
    rw [← hcl]
    have : z ∈ (LinearMap.ker (T : E →ₗ[ℝ] F))ᗮ := h1
    simpa [h2] using this
  obtain ⟨ν, hν⟩ := h3
  exact ⟨ν, hν⟩

theorem adjoint_eq_self_of_symm (π : F →L[ℝ] F) (hπ : ∀ a b, ⟪π a, b⟫ = ⟪a, π b⟫) :
    ContinuousLinearMap.adjoint π = π := by
  ext1 ν
  refine ext_inner_left ℝ (fun a => ?_)
  rw [ContinuousLinearMap.adjoint_inner_right, hπ]

/-- **the constrained form depends on `A` only through its compression to `ker (π Q)`.** -/
theorem inv_form_congr (Q : E →L[ℝ] F) (A A' : E →L[ℝ] E) (π : F →L[ℝ] F) (hπ : ∀ a b, ⟪π a, b⟫ = ⟪a, π b⟫)
    (hA : IsUnit A) (hA' : IsUnit A')
    (hN : IsUnit ((Q.comp (Ring.inverse A)).comp (ContinuousLinearMap.adjoint Q)))
    (hN' : IsUnit ((Q.comp (Ring.inverse A')).comp (ContinuousLinearMap.adjoint Q)))
    (hD : ∀ x, π (Q x) = 0 → ∀ x', π (Q x') = 0 → ⟪x', A' x - A x⟫ = 0)
    (y : F) (hy : π y = 0) :
    ⟪y, Ring.inverse ((Q.comp (Ring.inverse A)).comp (ContinuousLinearMap.adjoint Q)) y⟫ =
      ⟪y, Ring.inverse ((Q.comp (Ring.inverse A')).comp (ContinuousLinearMap.adjoint Q)) y⟫ := by
  set Qs := ContinuousLinearMap.adjoint Q with hQs
  set N := (Q.comp (Ring.inverse A)).comp Qs with hNdef
  set N' := (Q.comp (Ring.inverse A')).comp Qs with hN'def
  set lam := Ring.inverse N y with hlam
  set x := Ring.inverse A (Qs lam) with hx
  have hQx : Q x = y := apply_inverse_of_unit hN y
  have hz : ∀ x', (π.comp Q) x' = 0 → ⟪x', A' x - A x⟫ = 0 :=
    fun x' hx' => hD x (by rw [hQx]; exact hy) x' hx'
  obtain ⟨ν, hν⟩ := mem_range_adjoint_of_perp (π.comp Q) (A' x - A x) hz
  have hadj : ContinuousLinearMap.adjoint (π.comp Q) ν = Qs (π ν) := by
    rw [ContinuousLinearMap.adjoint_comp, adjoint_eq_self_of_symm π hπ]
    rfl
  have hAx : A x = Qs lam := apply_inverse_of_unit hA _
  have hA'x : A' x = Qs (lam + π ν) := by
    rw [map_add, ← hAx, ← hadj, hν]
    abel
  have hx' : Ring.inverse A' (Qs (lam + π ν)) = x := by rw [← hA'x, inverse_apply_of_unit hA']
  have hN'eq : N' (lam + π ν) = y := by
    show Q (Ring.inverse A' (Qs (lam + π ν))) = y
    rw [hx', hQx]
  have hinv : Ring.inverse N' y = lam + π ν := by rw [← hN'eq, inverse_apply_of_unit hN']
  rw [hinv, inner_add_right]
  have h0 : ⟪y, π ν⟫ = 0 := by rw [← hπ, hy, inner_zero_left]
  rw [h0, add_zero]

end Abstract

#print axioms inverse_apply_of_unit
#print axioms mem_range_adjoint_of_perp
#print axioms adjoint_eq_self_of_symm
#print axioms inv_form_congr

end AdalyFormal.CoverStrong
