import AdalyFormal.Balaban.CovariantOperators

/-!
# CvR1 -- pilot of the U(1) (colour sigma_3) reduction, lane cover_jacobi_20261016

For a CARTAN-valued SU(2) element `V` (diagonal), the adjoint action `R(V) X = V X V^dagger` fixes the diagonal part of `X`
(the `sigma_3` component of `X in su(2)`) and maps the off-diagonal part to off-diagonal.  Hence for a configuration whose
every link is Cartan-valued, the `sigma_3` component of the covariant gradient `D_U lam` is the FLAT gradient of the `sigma_3`
component of `lam`, and the covariant gradient commutes with the projection onto the `sigma_3` component.
This is the first brick of the colour-split theorem (R1); it concerns `gradValueCovariant` (pointwise) only.
NOT proved here: the L^2 / adjoint statement for `lapFull`, the curl `D_U` on bonds, `Delta`, `Q_j`, `W`, `R`, the full stack.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.LatticeOperators
open scoped Matrix

/-- a diagonal (Cartan-torus) element of SU(2). -/
def IsCartan (V : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Prop :=
  (V : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (V : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0

/-- the diagonal part of a `2x2` matrix. -/
def diagM (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun i => X i i)

theorem diagM_mem {X : Matrix (Fin 2) (Fin 2) ℂ} (h : X ∈ suTwo) : diagM X ∈ suTwo := by
  obtain ⟨h1, h2⟩ := h
  have e00 : star (X 0 0) = - X 0 0 := by
    have := congrFun (congrFun h1 0) 0
    simpa [Matrix.conjTranspose_apply] using this
  have e11 : star (X 1 1) = - X 1 1 := by
    have := congrFun (congrFun h1 1) 1
    simpa [Matrix.conjTranspose_apply] using this
  have htr : X 0 0 + X 1 1 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using h2
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [diagM, Matrix.conjTranspose_apply, e00, e11]
  · simp [diagM, Matrix.trace, Matrix.diag, Fin.sum_univ_two, htr]

/-- the projection of `su(2)` onto the `sigma_3` axis. -/
noncomputable def diagP : SuTwo →ₗ[ℝ] SuTwo where
  toFun X := ⟨diagM X.1, diagM_mem X.2⟩
  map_add' X Y := by
    apply Subtype.ext
    ext i j
    simp [diagM, Matrix.diagonal_apply]
  map_smul' c X := by
    apply Subtype.ext
    ext i j
    simp [diagM, Matrix.diagonal_apply]

theorem diagP_coe (X : SuTwo) : (diagP X : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal (fun i => (X : Matrix (Fin 2) (Fin 2) ℂ) i i) := rfl

theorem diagP_idem (X : SuTwo) : diagP (diagP X) = diagP X := by
  apply Subtype.ext
  rw [diagP_coe, diagP_coe]
  ext i j
  simp [Matrix.diagonal_apply]

/-- entries of the adjoint action of a Cartan element on the diagonal. -/
theorem cartan_conj_diag {V : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hV : IsCartan V) (X : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    ((V : Matrix (Fin 2) (Fin 2) ℂ) * X * (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) i i = X i i := by
  have hu := V.2
  rw [Matrix.mem_specialUnitaryGroup_iff] at hu
  have hU : (V : Matrix (Fin 2) (Fin 2) ℂ) * (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
    have := hu.1
    rw [Matrix.mem_unitaryGroup_iff] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  obtain ⟨h01, h10⟩ := hV
  have e0 := congrFun (congrFun hU 0) 0
  have e1 := congrFun (congrFun hU 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, h01, h10] at e0 e1
  fin_cases i
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, h01, h10, Complex.star_def]
    linear_combination X 0 0 * e0
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, h01, h10, Complex.star_def]
    linear_combination X 1 1 * e1

/-- `sigma_3` component is invariant under a Cartan adjoint action. -/
theorem diagP_RMap {V : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hV : IsCartan V) (X : SuTwo) :
    diagP (RMap V X) = diagP X := by
  apply Subtype.ext
  rw [diagP_coe, diagP_coe, RMap_coe_apply]
  ext i j
  simp only [Matrix.diagonal_apply]
  split_ifs with h
  · subst h; exact cartan_conj_diag hV _ _
  · rfl

#print axioms IsCartan
#print axioms diagM
#print axioms diagM_mem
#print axioms diagP
#print axioms diagP_coe
#print axioms diagP_idem
#print axioms cartan_conj_diag
#print axioms diagP_RMap

end AdalyFormal.CoverJacobi
