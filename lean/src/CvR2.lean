import CvR1

/-!
# CvR2 -- covariant gradient on a Cartan-valued configuration: colour split (pointwise level), lane cover_jacobi_20261016

For a link configuration `U` all of whose links are Cartan-valued (diagonal):
* `diagP (R(V) X) = diagP X` and `R(V) (diagP X) = diagP X` for every link value `V`;
* `diagP (D_U lam)(b) = diagP lam(b_+) - diagP lam(b_-)`: the `sigma_3` component of the covariant gradient is the FLAT gradient of the
  `sigma_3` component, independent of `U`;
* `D_U (diagP o lam) = diagP o (D_U lam)`: the covariant gradient commutes with the `sigma_3` projection;
* the complementary (off-diagonal) component is mapped to off-diagonal.
Pointwise statements about `gradValueCovariant`; the L^2 / adjoint level (`gradL2`, `lapFull`) is the next module.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open scoped Matrix

/-- every link value is in the Cartan torus. -/
def CartanCfg {L : PeriodicLatticeExtent} (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : Prop :=
  ∀ b, IsCartan (U b)

theorem RMap_diagP {V : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hV : IsCartan V) (X : SuTwo) :
    RMap V (diagP X) = diagP X := by
  apply Subtype.ext
  rw [RMap_coe_apply, diagP_coe]
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
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.diagonal_apply, h01, h10, Complex.star_def]
  · linear_combination ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0) * e0
  · linear_combination ((X : Matrix (Fin 2) (Fin 2) ℂ) 1 1) * e1

/-- the `sigma_3` projection commutes with every Cartan adjoint action. -/
theorem diagP_RMap_comm {V : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hV : IsCartan V) (X : SuTwo) :
    diagP (RMap V X) = RMap V (diagP X) := by
  rw [diagP_RMap hV, RMap_diagP hV]

/-- off-diagonal part is mapped to off-diagonal part (the complementary colour block is invariant). -/
theorem diagP_RMap_offdiag {V : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hV : IsCartan V) (X : SuTwo) :
    diagP (RMap V (X - diagP X)) = 0 := by
  simp only [map_sub, diagP_RMap hV, diagP_idem, sub_self]

variable {L : PeriodicLatticeExtent}

/-- **the `sigma_3` component of the covariant gradient is the flat gradient of the `sigma_3` component.** -/
theorem diagP_grad {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U)
    (lam : PeriodicLatticeSite L → SuTwo) (b : Bond L) :
    diagP (gradValueCovariant U lam b) = diagP (lam (periodicLatticeShift b.1 b.2)) - diagP (lam b.1) := by
  rw [gradValueCovariant, map_sub, diagP_RMap (hU b)]

/-- the covariant gradient commutes with the `sigma_3` projection. -/
theorem grad_diagP_comm {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U)
    (lam : PeriodicLatticeSite L → SuTwo) (b : Bond L) :
    gradValueCovariant U (fun x => diagP (lam x)) b = diagP (gradValueCovariant U lam b) := by
  rw [diagP_grad hU]
  simp only [gradValueCovariant, RMap_diagP (hU b)]

/-- the `sigma_3` block of the covariant gradient does not depend on the (Cartan) configuration. -/
theorem grad_diagP_flat {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U)
    (lam : PeriodicLatticeSite L → SuTwo) (b : Bond L) :
    gradValueCovariant U (fun x => diagP (lam x)) b =
      gradValueCovariant (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) (fun x => diagP (lam x)) b := by
  simp only [gradValueCovariant, RMap_diagP (hU b), RMap_one, LinearMap.id_apply]

/-- the flat configuration is Cartan. -/
theorem cartanCfg_one : CartanCfg (fun _ : Bond L => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  intro b
  constructor <;> simp


#print axioms CartanCfg
#print axioms RMap_diagP
#print axioms diagP_RMap_comm
#print axioms diagP_RMap_offdiag
#print axioms diagP_grad
#print axioms grad_diagP_comm
#print axioms grad_diagP_flat
#print axioms cartanCfg_one

end AdalyFormal.CoverJacobi
