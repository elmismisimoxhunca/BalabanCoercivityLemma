import QSplit
import QTransverse
import CircleGauge
import AxialHessian
import SourceCompression

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
noncomputable section
namespace HConstruction.G0Positivity
open HConstruction.Coeff HConstruction.Circle HConstruction.SmallNF
open HConstruction.Covariance HConstruction.Carrier HConstruction.G0Close HConstruction.Nonflat
open HConstruction.G0Final.Hessian HConstruction.NfRepair.Reproduced
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.DeltaKR85

/-- Axial projection on the actual coarse Hilbert carrier. -/
def coarseAxis : K →ₗ[ℝ] K :=
  (cfl2Equiv 2).symm.toLinearMap.comp
    ((LinearMap.pi fun c => axisProjection.comp (LinearMap.proj c)).comp
      (cfl2Equiv 2).toLinearMap)
def coarseTransverse : K →ₗ[ℝ] K := LinearMap.id - coarseAxis

@[simp] theorem coarseAxis_value (B : K) (c : CoarseBond witnessL (1*2)) :
    cfl2Equiv 2 (coarseAxis B) c = axisProjection (cfl2Equiv 2 B c) := rfl

@[simp] theorem coarseAxis_idempotent (B : K) : coarseAxis (coarseAxis B) = coarseAxis B := by
  apply (cfl2Equiv 2).injective
  funext c
  simp only [coarseAxis_value, axisProjection_idempotent]

theorem coarseAxis_selfAdjoint (A B : K) :
    (inner ℝ (coarseAxis A) B : ℝ) = inner ℝ A (coarseAxis B) := by
  change (∑ c, inner ℝ (axisProjection (cfl2Equiv 2 A c)) (cfl2Equiv 2 B c)) =
    ∑ c, inner ℝ (cfl2Equiv 2 A c) (axisProjection (cfl2Equiv 2 B c))
  exact Finset.sum_congr rfl (fun c _ => axisProjection_selfAdjoint _ _)

theorem coarseAxis_transverse_orthogonal (A B : K) :
    (inner ℝ (coarseAxis A) (coarseTransverse B) : ℝ) = 0 := by
  change inner ℝ (coarseAxis A) (B - coarseAxis B) = 0
  rw [inner_sub_right, ← coarseAxis_selfAdjoint, coarseAxis_idempotent, sub_self]

theorem axisProjection_half_turn (X : SuTwo) :
    axisProjection X = (1/2 : ℝ) • (X + RMap (rotElem 1) X) := by
  conv_rhs => rw [← assemble_coordinates X, rot_one_assemble]
  simp only [assemble_add, assemble_smul]
  simp only [axisProjection_apply]
  have h : assemble (0:ℝ) (axisCoord X) 0 = axisCoord X • pauliE2 := by simp [assemble]
  rw [← h]
  congr 1 <;> ring

/-- The genuine five-channel bond map commutes with both sectors. -/
theorem q124_axis_commute (A : CoarseBond witnessL 1 → SuTwo)
    (c : CoarseBond witnessL (1*2)) :
    q124Principal 1 2 chosenU (fun b => axisProjection (A b)) c =
      axisProjection (q124Principal 1 2 chosenU A c) := by
  have hf : (fun b => axisProjection (A b)) =
      (1/2 : ℝ) • (A + fun b => RMap (rotElem 1) (A b)) := by
    funext b; exact axisProjection_half_turn (A b)
  rw [hf, map_smul, map_add]
  change (1/2 : ℝ) • (q124Principal 1 2 chosenU A c +
    q124Principal 1 2 chosenU (fun b => RMap (rotElem 1) (A b)) c) = _
  rw [q124Principal_circle, axisProjection_half_turn]

theorem nativeQ_axis_commute (A : H) :
    nativeLinearQ chosenU 2 (bondAxis A) = coarseAxis (nativeLinearQ chosenU 2 A) := by
  apply (cfl2Equiv 2).injective
  funext c
  exact q124_axis_commute (fineCoordinates A) c

theorem nativeQ_transverse_commute (A : H) :
    nativeLinearQ chosenU 2 (bondTransverse A) = coarseTransverse (nativeLinearQ chosenU 2 A) := by
  change nativeLinearQ chosenU 2 (A - bondAxis A) =
    nativeLinearQ chosenU 2 A - coarseAxis (nativeLinearQ chosenU 2 A)
  rw [map_sub, nativeQ_axis_commute]

/-- Coefficient annihilation removes all four correction channels, but only axially. -/
theorem nativeQ_axis_flat (A : H) :
    nativeLinearQ chosenU 2 (bondAxis A) = nativeLinearQ (trivialU witnessL) 2 (bondAxis A) := by
  apply (cfl2Equiv 2).injective
  funext c
  change q124Principal 1 2 chosenU (fun b => axisCoord (fineCoordinates A b) • pauliE2) c =
    q124Principal 1 2 (trivialU witnessL) (fun b => axisCoord (fineCoordinates A b) • pauliE2) c
  rw [q124Principal_axis_flat, HConstruction.DRepair.q124_flat]
  rfl

theorem chosen_gaugeConstraint_axis_commute (A : H) :
    gaugeConstraintU chosenU (bondAxis A) = siteAxis (gaugeConstraintU chosenU A) :=
  gaugeConstraint_axis_commute (1/16) A

theorem gaugeConstraint_transverse_commute (A : H) :
    gaugeConstraintU chosenU (bondTransverse A) = siteTransverse (gaugeConstraintU chosenU A) := by
  change gaugeConstraintU chosenU (A - bondAxis A) =
    gaugeConstraintU chosenU A - siteAxis (gaugeConstraintU chosenU A)
  rw [map_sub, chosen_gaugeConstraint_axis_commute]

theorem gaugeConstraint_axis_flat (A : H) :
    gaugeConstraintU chosenU (bondAxis A) = gaugeConstraint (bondAxis A) := by
  change siteRU chosenU ((covGrad chosenU).adjoint (bondAxis A)) =
    siteR (flatGrad.adjoint (bondAxis A))
  unfold chosenU
  rw [covGrad_adjoint_axis_flat, flatGrad_adjoint_axis_commute, siteRU_axis_flat]

theorem gauge_energy_split (A : H) :
    ‖gaugeConstraintU chosenU A‖^2 =
      ‖gaugeConstraintU chosenU (bondAxis A)‖^2 +
      ‖gaugeConstraintU chosenU (bondTransverse A)‖^2 := by
  rw [chosen_gaugeConstraint_axis_commute, gaugeConstraint_transverse_commute]
  have h := siteAxis_transverse_orthogonal (gaugeConstraintU chosenU A) (gaugeConstraintU chosenU A)
  have he : siteAxis (gaugeConstraintU chosenU A) + siteTransverse (gaugeConstraintU chosenU A) =
      gaugeConstraintU chosenU A := by
    simp only [siteTransverse, LinearMap.sub_apply, LinearMap.id_apply]; abel
  have hn := norm_add_sq_real (siteAxis (gaugeConstraintU chosenU A)) (siteTransverse (gaugeConstraintU chosenU A))
  rw [he, h] at hn
  simpa using hn

theorem nativeQ_energy_split (A : H) :
    ‖nativeLinearQ chosenU 2 A‖^2 =
      ‖nativeLinearQ chosenU 2 (bondAxis A)‖^2 +
      ‖nativeLinearQ chosenU 2 (bondTransverse A)‖^2 := by
  rw [nativeQ_axis_commute, nativeQ_transverse_commute]
  have h := coarseAxis_transverse_orthogonal (nativeLinearQ chosenU 2 A) (nativeLinearQ chosenU 2 A)
  have he : coarseAxis (nativeLinearQ chosenU 2 A) + coarseTransverse (nativeLinearQ chosenU 2 A) =
      nativeLinearQ chosenU 2 A := by
    simp only [coarseTransverse, LinearMap.sub_apply, LinearMap.id_apply]; abel
  have hn := norm_add_sq_real (coarseAxis (nativeLinearQ chosenU 2 A)) (coarseTransverse (nativeLinearQ chosenU 2 A))
  rw [he, h] at hn
  simpa using hn

theorem flatBaseline_energy (A : H) :
    (inner ℝ A (flatBaseline A) : ℝ) = ‖flatCurl A‖^2 + ‖gaugeConstraint A‖^2 +
      8*‖nativeLinearQ (trivialU witnessL) 2 A‖^2 := by
  rw [flatBaseline_density]
  simp only [_root_.smul_apply, inner_smul_right, basePrecision_energy]
  ring

theorem bondAxis_axialH (A : H) :
    bondAxis A = axialH (fun e => axisCoord (bfl2Equiv A e)) := rfl

/-- FULL flat precision comparison on the axis, not merely curl-square. -/
theorem chosenPrecision_axis_lower (A : H) :
    (255/257 : ℝ) * (inner ℝ (bondAxis A) (flatBaseline (bondAxis A)) : ℝ) ≤
      inner ℝ (bondAxis A) (chosenPrecision (bondAxis A)) := by
  have h := deltaU_axial_lower (fun e => axisCoord (bfl2Equiv A e))
  rw [← bondAxis_axialH] at h
  have he : (inner ℝ (bondAxis A) (chosenPrecision (bondAxis A)) : ℝ) =
      inner ℝ (bondAxis A) (deltaU chosenU (bondAxis A)) +
      ‖gaugeConstraint (bondAxis A)‖^2 +
      8 * ‖nativeLinearQ (trivialU witnessL) 2 (bondAxis A)‖^2 := by
    rw [chosenPrecision, precisionU, ← gaugeU_identity]
    simp only [_root_.add_apply, _root_.smul_apply, inner_add_right, inner_smul_right,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      real_inner_self_eq_norm_sq, gaugeConstraint_axis_flat, nativeQ_axis_flat]
    ring
  rw [he, flatBaseline_energy]
  nlinarith [sq_nonneg ‖gaugeConstraint (bondAxis A)‖,
    sq_nonneg ‖nativeLinearQ (trivialU witnessL) 2 (bondAxis A)‖]

theorem chosenPrecision_axis_positive (A : H) (hA : bondAxis A ≠ 0) :
    (0 : ℝ) < inner ℝ (bondAxis A) (chosenPrecision (bondAxis A)) := by
  have h := flatBaseline_positive (bondAxis A) hA
  have hl := chosenPrecision_axis_lower A
  linarith

#print axioms nativeQ_axis_commute
#print axioms nativeQ_transverse_commute
#print axioms nativeQ_axis_flat
#print axioms gaugeConstraint_axis_flat
#print axioms gauge_energy_split
#print axioms nativeQ_energy_split
#print axioms chosenPrecision_axis_lower
#print axioms chosenPrecision_axis_positive
end HConstruction.G0Positivity
