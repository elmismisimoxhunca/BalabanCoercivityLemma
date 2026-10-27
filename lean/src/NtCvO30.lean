import NtCvO29

/-!
# CvO30 -- `Ad_h` fixes exactly the sigma_3-valued fields; operators of the genuine family preserve sigma_3-valued fields (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverNested (cartan cartan_coe)
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.GaugeCov
open AdalyFormal.IngredientFamilyR2

/-- entries of `cartan (pi/2)`. -/
theorem cartan_half_entries :
    ((cartan (Real.pi / 2) : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = Complex.I ∧
    ((cartan (Real.pi / 2) : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = -Complex.I := by
  rw [cartan_coe]
  have h1 : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [show (((Real.pi / 2 : ℝ) : ℂ)) = (Real.pi : ℂ) / 2 by push_cast; ring]
    exact Complex.exp_pi_div_two_mul_I
  have h2 : Complex.exp (-(((Real.pi / 2 : ℝ) : ℂ) * Complex.I)) = -Complex.I := by
    rw [Complex.exp_neg, h1, Complex.inv_I]
  push_cast at h1 h2
  constructor <;> simp [Matrix.diagonal_apply, h1, h2]

/-- `Ad_h Y = Y` iff `Y` is diagonal (sigma_3-valued), for `h = cartan (pi/2)`. -/
theorem RMap_h_fixed_iff (Y : SuTwo) : RMap (cartan (Real.pi / 2)) Y = Y ↔ diagP Y = Y := by
  obtain ⟨e00, e11⟩ := cartan_half_entries
  have hoff : ∀ i j : Fin 2, i ≠ j → ((cartan (Real.pi / 2) : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j = 0 := by
    intro i j hij
    rw [cartan_coe]
    simp [Matrix.diagonal_apply, hij]
  constructor
  · intro h
    have hm := congrArg (fun Z : SuTwo => (Z : Matrix (Fin 2) (Fin 2) ℂ)) h
    simp only [RMap_coe_apply] at hm
    apply Subtype.ext
    rw [diagP_coe]
    ext i j
    have e01 := congrFun (congrFun hm 0) 1
    have e10 := congrFun (congrFun hm 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, hoff 0 1 (by decide), hoff 1 0 (by decide), e00, e11] at e01 e10
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]
    · have : (Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by linear_combination (-1 / 2 : ℂ) * e01 + (1 / 2 : ℂ) * ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1) * Complex.I_sq
      exact this.symm
    · have : (Y : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by linear_combination (-1 / 2 : ℂ) * e10 + (1 / 2 : ℂ) * ((Y : Matrix (Fin 2) (Fin 2) ℂ) 1 0) * Complex.I_sq
      exact this.symm
  · intro h
    rw [← h]
    exact RMap_diagP (cartan_isCartan _) Y

/-- `Ad_h` is an involution on su(2) (`h^2 = -1` is central). -/
theorem RMap_h_sq (Y : SuTwo) : RMap (cartan (Real.pi / 2)) (RMap (cartan (Real.pi / 2)) Y) = Y := by
  obtain ⟨e00, e11⟩ := cartan_half_entries
  have hoff : ∀ i j : Fin 2, i ≠ j → ((cartan (Real.pi / 2) : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j = 0 := by
    intro i j hij
    rw [cartan_coe]
    simp [Matrix.diagonal_apply, hij]
  apply Subtype.ext
  rw [RMap_coe_apply, RMap_coe_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, hoff 0 1 (by decide), hoff 1 0 (by decide), e00, e11] <;>
    ring_nf <;> simp [Complex.I_sq]

#print axioms RMap_h_fixed_iff
#print axioms RMap_h_sq

end AdalyFormal.CoverOmega
