import QCircle
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HConstruction.Coeff
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.DeltaKR85
open HConstruction.SmallNF
open HConstruction.Circle
open HConstruction.NfRepair.Reproduced
open OneStep124

def quarterTurn (X : SuTwo) : SuTwo :=
  assemble (-(transverseCoord X).im) 0 (transverseCoord X).re

theorem quarterTurn_as_rotations (X : SuTwo) :
    quarterTurn X = (25/24 : ℝ) • RMap (rotElem (1/2)) X - (3/8 : ℝ) • X -
      (2/3 : ℝ) • RMap (rotElem 1) X := by
  rw [← assemble_coordinates X]
  simp only [quarterTurn, transverseCoord_assemble, RMap_rot_assemble, assemble_smul, assemble_sub]
  norm_num [rotA, rotB]
  congr 1 <;> ring

theorem q124Principal_quarterTurn (A : CoarseBond witnessL 1 → SuTwo)
    (c : CoarseBond witnessL (1*2)) :
    q124Principal 1 2 chosenU (fun b => quarterTurn (A b)) c =
      quarterTurn (q124Principal 1 2 chosenU A c) := by
  have hf : (fun b => quarterTurn (A b)) =
      (25/24 : ℝ) • (fun b => RMap (rotElem (1/2)) (A b)) - (3/8 : ℝ) • A -
      (2/3 : ℝ) • (fun b => RMap (rotElem 1) (A b)) := by
    funext b; exact quarterTurn_as_rotations (A b)
  rw [hf, map_sub, map_sub, map_smul, map_smul, map_smul]
  change (25/24 : ℝ) • q124Principal 1 2 chosenU (fun b => RMap (rotElem (1/2)) (A b)) c -
    (3/8 : ℝ) • q124Principal 1 2 chosenU A c -
    (2/3 : ℝ) • q124Principal 1 2 chosenU (fun b => RMap (rotElem 1) (A b)) c = _
  rw [q124Principal_circle, q124Principal_circle, quarterTurn_as_rotations]

def transverseLift (z : ℂ) : SuTwo := assemble z.re 0 z.im

theorem transverseLift_i (z : ℂ) : transverseLift (Complex.I*z) = quarterTurn (transverseLift z) := by
  simp [transverseLift, quarterTurn, Complex.mul_re, Complex.mul_im]

theorem q124Principal_transverse (z : CoarseBond witnessL 1 → ℂ)
    (c : CoarseBond witnessL (1*2)) :
    axisCoord (q124Principal 1 2 chosenU (fun b => transverseLift (z b)) c) = 0 := by
  have h := q124Principal_quarterTurn (fun b => quarterTurn (transverseLift (z b))) c
  have hf : (fun b => quarterTurn (quarterTurn (transverseLift (z b)))) =
      -(fun b => transverseLift (z b)) := by
    funext b
    simp only [quarterTurn, transverseLift, transverseCoord_assemble, Pi.neg_apply, assemble_neg]
    congr 1 <;> simp
  rw [hf, map_neg] at h
  have ha := congrArg axisCoord h
  change axisCoord (-q124Principal 1 2 chosenU (fun b => transverseLift (z b)) c) = _ at ha
  simp only [quarterTurn, axisCoord_assemble] at ha
  change -(axisCoord (q124Principal 1 2 chosenU (fun b => transverseLift (z b)) c)) = 0 at ha
  exact neg_eq_zero.mp ha

 theorem q124Principal_complex_i (z : CoarseBond witnessL 1 → ℂ)
    (c : CoarseBond witnessL (1*2)) :
    transverseCoord (q124Principal 1 2 chosenU (fun b => transverseLift (Complex.I*z b)) c) =
      Complex.I * transverseCoord (q124Principal 1 2 chosenU (fun b => transverseLift (z b)) c) := by
  simp_rw [transverseLift_i]
  rw [q124Principal_quarterTurn]
  apply Complex.ext <;> simp [quarterTurn, Complex.mul_re, Complex.mul_im]

#print axioms q124Principal_quarterTurn
#print axioms q124Principal_transverse
#print axioms q124Principal_complex_i
end HConstruction.Coeff
