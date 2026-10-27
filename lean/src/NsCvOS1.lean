import Mathlib

/-!
# CvOS1 -- determinant / adjugate of a continuous endomorphism of a finite-dimensional real normed space,
polynomial in the matrix entries, hence analytic in analytic families (lane omega/near2/struct)

`cdet A = det (toMatrix A)`, `cadj A` = the endomorphism with matrix `adjugate (toMatrix A)`.
Facts: `A ∘ cadj A = cdet A • 1`, `cdet (c • A) = c ^ n * cdet A`, `cadj (c • A) = c ^ (n-1) • cadj A`,
`cdet A ≠ 0 ↔ IsUnit A`, `Ring.inverse A = (cdet A)⁻¹ • cadj A` when `cdet A ≠ 0`,
analyticity of `t ↦ cdet (A t)` and `t ↦ cadj (A t)` for analytic CLM-valued `A`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega.Struct

open Matrix

section
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- the fixed basis. -/
noncomputable def bs (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    Module.Basis (Fin (Module.finrank ℝ X)) ℝ X := Module.finBasis ℝ X

/-- matrix entry as a continuous linear functional on `X →L X`. -/
noncomputable def entL (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (i j : Fin (Module.finrank ℝ X)) : (X →L[ℝ] X) →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap ((bs X).coord i)).comp (ContinuousLinearMap.apply ℝ X (bs X j))

theorem entL_apply (A : X →L[ℝ] X) (i j : Fin (Module.finrank ℝ X)) :
    entL X i j A = (bs X).repr (A (bs X j)) i := rfl

/-- the matrix of a CLM. -/
noncomputable def mat (A : X →L[ℝ] X) : Matrix (Fin (Module.finrank ℝ X)) (Fin (Module.finrank ℝ X)) ℝ :=
  LinearMap.toMatrix (bs X) (bs X) (A : X →ₗ[ℝ] X)

theorem mat_apply (A : X →L[ℝ] X) (i j : Fin (Module.finrank ℝ X)) : mat A i j = entL X i j A := by
  simp [mat, entL_apply, LinearMap.toMatrix_apply]

/-- determinant. -/
noncomputable def cdet (A : X →L[ℝ] X) : ℝ := LinearMap.det (A : X →ₗ[ℝ] X)

theorem cdet_eq (A : X →L[ℝ] X) : cdet A = (mat A).det := by
  unfold cdet mat
  exact (LinearMap.det_toMatrix (bs X) _).symm

/-- rank-one operator `x ↦ coord_j(x) • b_i`. -/
noncomputable def rk (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (i j : Fin (Module.finrank ℝ X)) : X →L[ℝ] X :=
  (LinearMap.toContinuousLinearMap ((bs X).coord j)).smulRight (bs X i)

theorem rk_apply (i j : Fin (Module.finrank ℝ X)) (x : X) : rk X i j x = ((bs X).coord j x) • bs X i := rfl

/-- adjugate endomorphism. -/
noncomputable def cadj (A : X →L[ℝ] X) : X →L[ℝ] X :=
  ∑ i, ∑ j, (mat A).adjugate i j • rk X i j

theorem cadj_basis (A : X →L[ℝ] X) (j : Fin (Module.finrank ℝ X)) :
    cadj A (bs X j) = ∑ i, (mat A).adjugate i j • bs X i := by
  simp only [cadj, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, rk_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Finset.sum_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

theorem mat_cadj (A : X →L[ℝ] X) : mat (cadj A) = (mat A).adjugate := by
  ext i j
  rw [mat_apply, entL_apply, cadj_basis]
  simp [map_sum, Module.Basis.repr_self, Finsupp.single_apply]

theorem mat_comp (A B : X →L[ℝ] X) : mat (A.comp B) = mat A * mat B := by
  unfold mat
  exact LinearMap.toMatrix_mul (bs X) _ _

theorem mat_one : mat (1 : X →L[ℝ] X) = 1 := by
  unfold mat
  exact LinearMap.toMatrix_id (bs X)

theorem mat_smul (c : ℝ) (A : X →L[ℝ] X) : mat (c • A) = c • mat A := by
  ext i j; simp [mat_apply, entL_apply]

theorem mat_injective : Function.Injective (mat : (X →L[ℝ] X) → _) := by
  intro A B h
  have : (A : X →ₗ[ℝ] X) = B := (LinearMap.toMatrix (bs X) (bs X)).injective h
  exact ContinuousLinearMap.coe_injective this

theorem comp_cadj (A : X →L[ℝ] X) : A.comp (cadj A) = cdet A • (1 : X →L[ℝ] X) := by
  apply mat_injective
  rw [mat_comp, mat_cadj, mat_smul, mat_one, cdet_eq, Matrix.mul_adjugate]

theorem cadj_comp (A : X →L[ℝ] X) : (cadj A).comp A = cdet A • (1 : X →L[ℝ] X) := by
  apply mat_injective
  rw [mat_comp, mat_cadj, mat_smul, mat_one, cdet_eq, Matrix.adjugate_mul]

theorem cdet_smul (c : ℝ) (A : X →L[ℝ] X) : cdet (c • A) = c ^ Module.finrank ℝ X * cdet A := by
  unfold cdet
  exact LinearMap.det_smul c _

theorem cadj_smul (c : ℝ) (A : X →L[ℝ] X) : cadj (c • A) = c ^ (Module.finrank ℝ X - 1) • cadj A := by
  apply mat_injective
  rw [mat_cadj, mat_smul, Matrix.adjugate_smul, mat_smul, mat_cadj]
  simp [Fintype.card_fin]

theorem cdet_comp (A B : X →L[ℝ] X) : cdet (A.comp B) = cdet A * cdet B := by
  unfold cdet
  exact LinearMap.det_comp _ _

theorem cdet_one : cdet (1 : X →L[ℝ] X) = 1 := by
  unfold cdet; simp

theorem mul_binv (A : X →L[ℝ] X) (h : cdet A ≠ 0) : A * ((cdet A)⁻¹ • cadj A) = 1 := by
  ext1 x
  have := congrArg (fun T : X →L[ℝ] X => T x) (comp_cadj A)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at this
  simp [ContinuousLinearMap.mul_apply, this, smul_smul, h]

theorem binv_mul (A : X →L[ℝ] X) (h : cdet A ≠ 0) : ((cdet A)⁻¹ • cadj A) * A = 1 := by
  ext1 x
  have := congrArg (fun T : X →L[ℝ] X => T x) (cadj_comp A)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at this
  simp [ContinuousLinearMap.mul_apply, this, smul_smul, h]

/-- the unit with value `A` and inverse `(cdet A)⁻¹ • cadj A`. -/
noncomputable def mkUnit (A : X →L[ℝ] X) (h : cdet A ≠ 0) : (X →L[ℝ] X)ˣ :=
  ⟨A, (cdet A)⁻¹ • cadj A, mul_binv A h, binv_mul A h⟩

theorem isUnit_of_cdet_ne (A : X →L[ℝ] X) (h : cdet A ≠ 0) : IsUnit A := ⟨mkUnit A h, rfl⟩

theorem cdet_ne_of_isUnit (A : X →L[ℝ] X) (h : IsUnit A) : cdet A ≠ 0 := by
  obtain ⟨u, rfl⟩ := h
  have h1 : cdet ((u : X →L[ℝ] X).comp (((u⁻¹ : (X →L[ℝ] X)ˣ)) : X →L[ℝ] X)) = 1 := by
    have : ((u : X →L[ℝ] X).comp (((u⁻¹ : (X →L[ℝ] X)ˣ)) : X →L[ℝ] X)) = 1 := by
      exact u.mul_inv
    rw [this, cdet_one]
  rw [cdet_comp] at h1
  intro h0
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

theorem isUnit_iff_cdet (A : X →L[ℝ] X) : IsUnit A ↔ cdet A ≠ 0 :=
  ⟨cdet_ne_of_isUnit A, isUnit_of_cdet_ne A⟩

theorem inverse_eq_cadj (A : X →L[ℝ] X) (h : cdet A ≠ 0) : Ring.inverse A = (cdet A)⁻¹ • cadj A := by
  have : Ring.inverse ((mkUnit A h : (X →L[ℝ] X)ˣ) : X →L[ℝ] X) = ((mkUnit A h)⁻¹ : (X →L[ℝ] X)ˣ) := Ring.inverse_unit _
  exact this

end

end AdalyFormal.CoverOmega.Struct
