import UZ5

/-!
# CG4a -- group-level plaquette estimate: `|a b c⁻¹ d⁻¹ - 1| ≤ 2 t₂ + 2 t₁²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace AdalyFormal.CoverGeom

open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.UnifLane.Z (n_conj n_inv n_mul)
open AdalyFormal.M2Glue2 (frobNorm_mul_le frobNorm_mul_su2 frobNorm_su2_mul frobNorm_sub_le' frobNorm_sub_comm)

theorem sub_one_eq (a c : SU2) : ((a * c⁻¹ : SU2) : M2) - 1 = ((a : M2) - (c : M2)) * ((c⁻¹ : SU2) : M2) := by
  have h : (c : M2) * ((c⁻¹ : SU2) : M2) = 1 := by
    rw [← Submonoid.coe_mul]; simp
  rw [sub_mul, h]; rfl

theorem norm_ratio (a c : SU2) : frobNorm (((a * c⁻¹ : SU2) : M2) - 1) = frobNorm ((a : M2) - (c : M2)) := by
  rw [sub_one_eq]; exact frobNorm_mul_su2 _ _

theorem norm_comm (c d : SU2) {t1 : ℝ} (hc : frobNorm ((c : M2) - 1) ≤ t1) (hd : frobNorm ((d : M2) - 1) ≤ t1) :
    frobNorm (((c * d * c⁻¹ * d⁻¹ : SU2) : M2) - 1) ≤ 2 * t1 ^ 2 := by
  have e : c * d * c⁻¹ * d⁻¹ = (c * d) * (d * c)⁻¹ := by group
  rw [e, norm_ratio]
  have h1 : ((c * d : SU2) : M2) - ((d * c : SU2) : M2) = ((c : M2) - 1) * ((d : M2) - 1) - ((d : M2) - 1) * ((c : M2) - 1) := by
    simp only [Submonoid.coe_mul, Subgroup.coe_mul]; noncomm_ring
  rw [h1]
  have n0 : ∀ A : M2, 0 ≤ frobNorm A := fun A => Real.sqrt_nonneg _
  have t0 : 0 ≤ t1 := le_trans (n0 _) hc
  set X : M2 := (c : M2) - 1
  set Y : M2 := (d : M2) - 1
  have hXY : frobNorm (X * Y) ≤ t1 ^ 2 := by
    refine (frobNorm_mul_le X Y).trans ?_
    nlinarith [n0 X, n0 Y]
  have hYX : frobNorm (Y * X) ≤ t1 ^ 2 := by
    refine (frobNorm_mul_le Y X).trans ?_
    nlinarith [n0 X, n0 Y]
  have := frobNorm_sub_le' (X * Y) 0 (Y * X)
  rw [sub_zero, frobNorm_sub_comm (0 : M2) (Y * X), sub_zero] at this
  linarith

theorem hol_near_one (a b c d : SU2) {t1 t2 : ℝ} (hb : frobNorm ((b : M2) - (d : M2)) ≤ t2)
    (ha : frobNorm ((a : M2) - (c : M2)) ≤ t2) (hc : frobNorm ((c : M2) - 1) ≤ t1) (hd : frobNorm ((d : M2) - 1) ≤ t1) :
    frobNorm (((a * b * c⁻¹ * d⁻¹ : SU2) : M2) - 1) ≤ 2 * t2 + 2 * t1 ^ 2 := by
  have e : a * b * c⁻¹ * d⁻¹ = (a * c⁻¹) * (c * (b * d⁻¹) * c⁻¹) * (c * d * c⁻¹ * d⁻¹) := by group
  rw [e]
  refine (n_mul _ _).trans ?_
  have h12 := n_mul (a * c⁻¹) (c * (b * d⁻¹) * c⁻¹)
  have h3 := norm_comm c d hc hd
  rw [n_conj, norm_ratio] at h12
  rw [norm_ratio] at h12
  have : frobNorm (((a * c⁻¹ : SU2) : M2) - 1) ≤ t2 := by rw [norm_ratio]; exact ha
  have h2 : frobNorm (((b * d⁻¹ : SU2) : M2) - 1) ≤ t2 := by rw [norm_ratio]; exact hb
  linarith

end AdalyFormal.CoverGeom
