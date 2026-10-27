import UW3

/-!
# UW4 -- SU(2) product / conjugation / commutator bounds used by the clause-2 stacking (lane unif_20261016)

All in the Frobenius norm on `M2`, for `SU2` elements (unitary invariance):
`su2_sub_rel` (`Y = k Z k'⁻¹ ⇒ |k' − k| ≤ |Y − 1| + |Z − 1|`), `prod4_sub_one`, `prod4_diff`, `conj_diff`
(`|c Y c⁻¹ − c' Y' c'⁻¹| ≤ |Y' − Y| + 2|c' − c||Y − 1|`), `comm_bound` (`|XY − YX| ≤ 2|X − 1||Y − 1|`),
`mul_diff` (`|ab − a'b'| ≤ |a − a'| + |b − b'|`).  Reusable.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.UnifLane.Z

open Matrix
open AdalyFormal.M2Glue2 (frobNorm_sub_le' frobNorm_sub_comm frobNorm_su2_mul frobNorm_mul_su2 frobNorm_mul_su2_star
  frobNorm_su2_mul_star frobNorm_mul_le su2_mul_star su2_star_mul gauge_step_two)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv coe_one)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.Bch2 (frobNorm_add_le frobNorm_nonneg frobNorm_smul)
open AdalyFormal.Balaban.RegularityGap (frobNorm_neg)

theorem mul_diff (a b a' b' : SU2) :
    frobNorm (((a * b : SU2) : M2) - ((a' * b' : SU2) : M2)) ≤ frobNorm ((a : M2) - a') + frobNorm ((b : M2) - b') := by
  rw [coe_mul, coe_mul]
  have e : (a : M2) * b - a' * b' = ((a : M2) - a') * b + (a' : M2) * ((b : M2) - b') := by noncomm_ring
  rw [e]
  refine (frobNorm_add_le _ _).trans ?_
  rw [frobNorm_mul_su2, frobNorm_su2_mul]

theorem inv_diff (a a' : SU2) : frobNorm (((a⁻¹ : SU2) : M2) - ((a'⁻¹ : SU2) : M2)) = frobNorm ((a : M2) - a') := by
  rw [coe_inv, coe_inv, ← conjTranspose_sub, AdalyFormal.M2Glue2.frobNorm_conjTranspose]

theorem prod4_diff (a b c d a' b' c' d' : SU2) :
    frobNorm (((a * b * c * d : SU2) : M2) - ((a' * b' * c' * d' : SU2) : M2))
      ≤ frobNorm ((a : M2) - a') + frobNorm ((b : M2) - b') + frobNorm ((c : M2) - c') + frobNorm ((d : M2) - d') := by
  have h1 := mul_diff (a * b * c) d (a' * b' * c') d'
  have h2 := mul_diff (a * b) c (a' * b') c'
  have h3 := mul_diff a b a' b'
  linarith

theorem prod4_sub_one (a b c d : SU2) :
    frobNorm (((a * b * c * d : SU2) : M2) - 1)
      ≤ frobNorm ((a : M2) - 1) + frobNorm ((b : M2) - 1) + frobNorm ((c : M2) - 1) + frobNorm ((d : M2) - 1) := by
  have := prod4_diff a b c d 1 1 1 1
  simpa [coe_one] using this

/-- `Y = k Z k'⁻¹ ⇒ |k' − k| ≤ |Y − 1| + |Z − 1|`. -/
theorem su2_sub_rel {Y k Z k' : SU2} (h : Y = k * Z * k'⁻¹) :
    frobNorm ((k' : M2) - k) ≤ frobNorm ((Y : M2) - 1) + frobNorm ((Z : M2) - 1) := by
  have hk : k' = Y⁻¹ * k * Z := by rw [h]; group
  rw [hk, coe_mul, coe_mul, coe_inv]
  have e : (Y : M2)ᴴ * k * Z - k = (Y : M2)ᴴ * k * ((Z : M2) - 1) + (1 - (Y : M2)) * ((Y : M2)ᴴ * k) := by
    have hy := su2_mul_star Y
    have e2 : (1 - (Y : M2)) * ((Y : M2)ᴴ * k) = (Y : M2)ᴴ * k - (Y : M2) * (Y : M2)ᴴ * k := by noncomm_ring
    rw [e2, hy]; noncomm_ring
  rw [e]
  refine (frobNorm_add_le _ _).trans ?_
  have a : frobNorm ((Y : M2)ᴴ * k * ((Z : M2) - 1)) = frobNorm ((Z : M2) - 1) := by
    rw [mul_assoc, frobNorm_su2_mul_star, frobNorm_su2_mul]
  have b : frobNorm ((1 - (Y : M2)) * ((Y : M2)ᴴ * k)) = frobNorm ((Y : M2) - 1) := by
    rw [← mul_assoc, show (1 - (Y : M2)) * (Y : M2)ᴴ * k = ((1 - (Y : M2)) * (Y : M2)ᴴ) * k from rfl,
      frobNorm_mul_su2, frobNorm_mul_su2_star, frobNorm_sub_comm]
  rw [a, b]; linarith

/-- conjugation differences. -/
theorem conj_diff (c c' Y Y' : SU2) :
    frobNorm (((c' * Y' * c'⁻¹ : SU2) : M2) - ((c * Y * c⁻¹ : SU2) : M2))
      ≤ frobNorm ((Y' : M2) - Y) + 2 * frobNorm ((c' : M2) - c) * frobNorm ((Y : M2) - 1) := by
  have h := gauge_step_two c c c' c' Y Y'
  have z : frobNorm (0 : M2) = 0 := by
    have := frobNorm_smul (0 : ℝ) (0 : M2); simpa using this
  have e1 : (c' : M2) - c' = 0 := sub_self _
  have e3 : (0 : M2) - ((c : M2) - c) = 0 := by abel
  rw [e1, e3, z] at h
  nlinarith [frobNorm_nonneg ((c' : M2) - c), frobNorm_nonneg ((Y : M2) - 1)]

/-- commutators of near-identity elements. -/
theorem comm_bound (X Y : SU2) :
    frobNorm (((X * Y : SU2) : M2) - ((Y * X : SU2) : M2)) ≤ 2 * frobNorm ((X : M2) - 1) * frobNorm ((Y : M2) - 1) := by
  rw [coe_mul, coe_mul]
  have e : (X : M2) * Y - Y * X = ((X : M2) - 1) * ((Y : M2) - 1) - ((Y : M2) - 1) * ((X : M2) - 1) := by noncomm_ring
  rw [e]
  refine (frobNorm_sub_le' _ 0 _).trans ?_
  rw [sub_zero, zero_sub, frobNorm_neg]
  have a := frobNorm_mul_le ((X : M2) - 1) ((Y : M2) - 1)
  have b := frobNorm_mul_le ((Y : M2) - 1) ((X : M2) - 1)
  linarith

theorem su2_sub_one_inv (a : SU2) : frobNorm (((a⁻¹ : SU2) : M2) - 1) = frobNorm ((a : M2) - 1) :=
  AdalyFormal.M2BallCharts.su2_inv_sub_one a

end AdalyFormal.UnifLane.Z
