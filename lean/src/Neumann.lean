import Mathlib

set_option autoImplicit false
namespace HConstruction.Covariance.Reproduced
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable def gOneOfNeumann (G0 P : H →L[ℝ] H) : H →L[ℝ] H :=
  G0 * Ring.inverse (1 - P * G0)

theorem gOneOfNeumann_eq_tsum (G0 P : H →L[ℝ] H) (hconv : ‖P * G0‖ < 1) :
    gOneOfNeumann G0 P = ∑' n : ℕ, G0 * (P * G0) ^ n := by
  unfold gOneOfNeumann
  rw [← geom_series_eq_inverse (P * G0) hconv]
  exact (Summable.tsum_mul_left G0 (summable_geometric_of_norm_lt_one hconv)).symm

theorem gOneOfNeumann_cancel_right (G0 P : H →L[ℝ] H) (hconv : ‖P * G0‖ < 1) :
    gOneOfNeumann G0 P * (1 - P * G0) = G0 := by
  unfold gOneOfNeumann
  rw [mul_assoc, ← geom_series_eq_inverse (P * G0) hconv, geom_series_mul_neg (P * G0) hconv,
    mul_one]

omit [CompleteSpace H] in
theorem gOneOfNeumann_zero_perturbation (G0 : H →L[ℝ] H) : gOneOfNeumann G0 0 = G0 := by
  unfold gOneOfNeumann
  simp

end HConstruction.Covariance.Reproduced
