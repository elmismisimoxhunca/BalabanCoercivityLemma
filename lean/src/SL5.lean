import Mathlib

/-!
# SL5 -- Young's inequality for the form-relative drift (abstract)

`young_sq`: `‖u‖² ≤ (1+t)‖v‖² + (1+1/t)‖u - v‖²` (`t > 0`), any real normed group.
`young_wsum`: the same for a nonnegatively weighted finite sum of squared norms.
These turn a local drift `‖(curl_1 - curl_U) x‖ ≤ δc‖x‖` into the form-relative bound the slice comparison needs
(the plain `|⟪x,Δ_U x⟫ - ⟪x,Δ_1 x⟫| ≤ S1 a‖x‖²` of template_route_bridge is first order in the link deviation `a`
and loses a factor `n` in the scaled norm; the `(1+t)` split costs only `a²`).
-/
set_option autoImplicit false
namespace AdalyFormal.SliceCoerc

theorem young_sq {X : Type*} [SeminormedAddCommGroup X] (u v : X) (t : ℝ) (ht : 0 < t) :
    ‖u‖ ^ 2 ≤ (1 + t) * ‖v‖ ^ 2 + (1 + 1 / t) * ‖u - v‖ ^ 2 := by
  have h1 : ‖u‖ ≤ ‖v‖ + ‖u - v‖ := by
    have := norm_add_le v (u - v); simpa using this
  have h0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hy : 2 * ‖v‖ * ‖u - v‖ ≤ t * ‖v‖ ^ 2 + (1 / t) * ‖u - v‖ ^ 2 := by
    have hq : 0 ≤ (t * ‖v‖ - ‖u - v‖) ^ 2 := sq_nonneg _
    have : 2 * ‖v‖ * ‖u - v‖ * t ≤ t * t * ‖v‖ ^ 2 + ‖u - v‖ ^ 2 := by nlinarith
    rw [div_mul_eq_mul_div, one_mul]
    have ht' : t * ‖v‖ ^ 2 + ‖u - v‖ ^ 2 / t = (t * t * ‖v‖ ^ 2 + ‖u - v‖ ^ 2) / t := by
      field_simp
    rw [ht', le_div_iff₀ ht]; linarith
  have h2 : ‖u‖ ^ 2 ≤ (‖v‖ + ‖u - v‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
  nlinarith

theorem young_wsum {ι X : Type*} [SeminormedAddCommGroup X] (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (u v : ι → X) (t : ℝ) (ht : 0 < t) :
    ∑ i ∈ s, w i * ‖u i‖ ^ 2 ≤ (1 + t) * ∑ i ∈ s, w i * ‖v i‖ ^ 2
      + (1 + 1 / t) * ∑ i ∈ s, w i * ‖u i - v i‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i hi => ?_)
  have := mul_le_mul_of_nonneg_left (young_sq (u i) (v i) t ht) (hw i hi)
  nlinarith

#print axioms young_sq
#print axioms young_wsum

end AdalyFormal.SliceCoerc
