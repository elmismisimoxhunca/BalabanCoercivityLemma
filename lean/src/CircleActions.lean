import CircleCoordinates
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
namespace HConstruction.Circle
open HConstruction.NfRepair.Reproduced
open HConstruction.SmallNF
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.DeltaKR66
open OneStep124
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)

theorem principal_loop_log (c : CoarseBond witnessL (1*2))
    (x : PeriodicLatticeSite witnessL) (hx : x ∈ stepBlockOf c.1.1 1 2) :
    principalSuTwoLog (loopVar 1 2 chosenU (c.1.1,c.2) x) =
      ((loopWord c x : ℝ) * theta) • pauliE2 := by
  rw [chosenU, loop_word]
  exact principalSuTwoLog_rotElem_zpow_small _ (loopWord_values c x hx)

theorem source_Zx (c : CoarseBond witnessL (1*2))
    (x : PeriodicLatticeSite witnessL) (hx : x ∈ stepBlockOf c.1.1 1 2) :
    (sourcePrincipalLogData 1 2 chosenU).Zx c x =
      ((loopWord c x : ℝ) * theta) • pauliE2 := principal_loop_log c x hx

/-- The source commutator has transverse complex orientation +i. -/
theorem adOp_axis_assemble (s x a z : ℝ) :
    adOp (s • pauliE2) (assemble x a z) = assemble (-2*s*z) 0 (2*s*x) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adOp, adLM, adVal, assemble, pauliE1, pauliE1Val, pauliE2, witnessM,
      pauliE3, suTwoWitness, suTwoWitnessVal, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.real_smul] <;> ring

theorem adOp_axis_coordinates (s : ℝ) (X : SuTwo) :
    axisCoord (adOp (s • pauliE2) X) = 0 ∧
    transverseCoord (adOp (s • pauliE2) X) = (2*s : ℝ) * Complex.I * transverseCoord X := by
  rw [← assemble_coordinates X, adOp_axis_assemble]
  simp only [axisCoord_assemble, transverseCoord_assemble]
  constructor
  · trivial
  · apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem RMap_rot_assemble (t x a z : ℝ) :
    RMap (rotElem t) (assemble x a z) =
      assemble ((rotA t ^ 2 - rotB t ^ 2)*x - (2*rotA t*rotB t)*z) a
        ((2*rotA t*rotB t)*x + (rotA t ^ 2 - rotB t ^ 2)*z) := by
  apply Subtype.ext
  rw [RMap_coe_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotElem_coe, rotM, assemble, pauliE1, pauliE1Val, pauliE2, witnessM,
      pauliE3, suTwoWitness, suTwoWitnessVal, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.real_smul]
    <;> apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im]
    <;> nlinarith [congrArg (fun u : ℝ => a*u) (rotA_sq_add_rotB_sq t)]

theorem RMap_rot_coordinates (t : ℝ) (X : SuTwo) :
    axisCoord (RMap (rotElem t) X) = axisCoord X ∧
    transverseCoord (RMap (rotElem t) X) =
      ((rotA t : ℂ) + (rotB t : ℂ) * Complex.I)^2 * transverseCoord X := by
  rw [← assemble_coordinates X, RMap_rot_assemble]
  simp only [axisCoord_assemble, transverseCoord_assemble]
  constructor
  · trivial
  · apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring <;> simp

theorem RMap_rot_axis (t s : ℝ) : RMap (rotElem t) (s • pauliE2) = s • pauliE2 := by
  have h := RMap_rot_assemble t 0 s 0
  simpa [assemble] using h

#print axioms RMap_rot_coordinates
#print axioms RMap_rot_axis
#print axioms principal_loop_log
#print axioms source_Zx
#print axioms adOp_axis_assemble
#print axioms adOp_axis_coordinates
#print axioms RMap_rot_assemble
end HConstruction.Circle
