import CircleLog
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
namespace HConstruction.Circle
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner

def assemble (x a z : ℝ) : SuTwo := x • pauliE1 + a • pauliE2 + z • pauliE3

theorem assemble_inner (x a z x' a' z' : ℝ) :
    inner ℝ (assemble x a z) (assemble x' a' z') = x*x' + a*a' + z*z' := by
  rw [inner_eq_hsInner, hsInner_entries]
  simp [assemble, pauliE1, pauliE1Val, pauliE2, witnessM, pauliE3,
    suTwoWitness, suTwoWitnessVal, Complex.real_smul, Complex.mul_re, Complex.mul_im]
  <;> ring

def axisCoord (X : SuTwo) : ℝ := ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re

def transverseCoord (X : SuTwo) : ℂ :=
  ⟨((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im,
   ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im⟩

theorem assemble_coordinates (X : SuTwo) :
    assemble (transverseCoord X).re (axisCoord X) (transverseCoord X).im = X :=
  (suTwo_decompose X).symm

@[simp] theorem axisCoord_assemble (x a z : ℝ) : axisCoord (assemble x a z) = a := by
  simp [axisCoord, assemble, pauliE1, pauliE1Val, pauliE2, witnessM, pauliE3,
    suTwoWitness, suTwoWitnessVal, Complex.real_smul]

@[simp] theorem transverseCoord_assemble (x a z : ℝ) :
    transverseCoord (assemble x a z) = ⟨x,z⟩ := by
  apply Complex.ext <;> simp [transverseCoord, assemble, pauliE1, pauliE1Val, pauliE2, witnessM,
    pauliE3, suTwoWitness, suTwoWitnessVal, Complex.real_smul]

/-- Coordinate order is transverse real, axis, transverse imaginary. -/
def coordinates : SuTwo ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun X := WithLp.toLp 2 ![(transverseCoord X).re, axisCoord X, (transverseCoord X).im]
  invFun v := assemble (v 0) (v 1) (v 2)
  left_inv X := assemble_coordinates X
  right_inv v := by ext i; fin_cases i <;> simp
  map_add' X Y := by
    ext i; fin_cases i <;> simp [axisCoord, transverseCoord]
  map_smul' r X := by
    ext i; fin_cases i <;> simp [axisCoord, transverseCoord, Complex.real_smul]

theorem inner_coordinates (X Y : SuTwo) :
    inner ℝ (coordinates X) (coordinates Y) = inner ℝ X Y := by
  conv_rhs => rw [← assemble_coordinates X, ← assemble_coordinates Y, assemble_inner]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ,
    coordinates]
  <;> ring

def coordinateIsometry : SuTwo ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  coordinates.isometryOfInner inner_coordinates

theorem inner_axis_transverse (X Y : SuTwo) :
    inner ℝ X Y = axisCoord X * axisCoord Y +
      ((star (transverseCoord X)) * transverseCoord Y).re := by
  rw [← inner_coordinates]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ,
    coordinates, Complex.mul_re]
  <;> ring

#print axioms assemble_inner
#print axioms coordinateIsometry
#print axioms inner_axis_transverse
end HConstruction.Circle
