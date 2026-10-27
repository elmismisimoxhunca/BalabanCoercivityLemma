import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# GCa2 -- equivariance passes to first and second Fréchet derivatives, with NO differentiability

If `f' ∘ A = A ∘ f` for a continuous linear equivalence `A`, then `f' = A ∘ f ∘ A⁻¹` and
Mathlib's `ContinuousLinearEquiv.comp_fderiv` / `comp_right_fderiv` (valid for every `f`,
differentiable or not) give
 * `fderiv f' (A x) (A a) = A (fderiv f x a)`;
 * `fderiv (fderiv f') (A x) (A a) (A b) = A (fderiv (fderiv f) x a b)`.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.GaugeCov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem conj_eq_of_equivariant (A : E ≃L[ℝ] E) (f f' : E → E) (h : ∀ x, f' (A x) = A (f x)) :
    f' = ((A : E → E) ∘ f) ∘ (A.symm : E → E) := by
  funext y
  simp only [Function.comp_apply]
  rw [← h, A.apply_symm_apply]

theorem fderiv_eq_of_equivariant (A : E ≃L[ℝ] E) (f f' : E → E) (h : ∀ x, f' (A x) = A (f x)) :
    fderiv ℝ f' = fun y => A.arrowCongr A (fderiv ℝ f (A.symm y)) := by
  funext y
  rw [conj_eq_of_equivariant A f f' h, A.symm.comp_right_fderiv, A.comp_fderiv]
  ext v
  simp

/-- **first derivative**: `D f'(A x) ∘ A = A ∘ D f(x)`. -/
theorem fderiv_equivariant (A : E ≃L[ℝ] E) (f f' : E → E) (h : ∀ x, f' (A x) = A (f x))
    (x a : E) : fderiv ℝ f' (A x) (A a) = A (fderiv ℝ f x a) := by
  rw [fderiv_eq_of_equivariant A f f' h]
  simp

/-- **second derivative**: `D² f'(A x)(A a, A b) = A (D² f(x)(a, b))`. -/
theorem fderiv2_equivariant (A : E ≃L[ℝ] E) (f f' : E → E) (h : ∀ x, f' (A x) = A (f x))
    (x a b : E) :
    fderiv ℝ (fderiv ℝ f') (A x) (A a) (A b) = A (fderiv ℝ (fderiv ℝ f) x a b) := by
  have e : fderiv ℝ f'
      = ((A.arrowCongr A : (E →L[ℝ] E) → (E →L[ℝ] E)) ∘ fderiv ℝ f) ∘ (A.symm : E → E) := by
    rw [fderiv_eq_of_equivariant A f f' h]; rfl
  rw [e, A.symm.comp_right_fderiv, (A.arrowCongr A).comp_fderiv]
  simp

#print axioms fderiv_equivariant
#print axioms fderiv2_equivariant

end AdalyFormal.GaugeCov
