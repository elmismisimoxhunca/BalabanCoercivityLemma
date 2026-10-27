import NtCvON5

/-!
# PtU1 -- abstract flat reduction: `UnitsFour` from positive definiteness of `Ginv` and injectivity of `Q*` (lane omega/near2/point)

At a flat background `Jf = 0`, so `G₁⁻¹ = Ginv` (symmetric, same form), and `G₁ = G = Ginv⁻¹`.  If the form `⟨x,Ginv x⟩` is definite on `E₀`
and `Qs` is injective, the four units `G1inv, Nmat, Ginv, Q G Q*` all hold.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmegaTwo
open AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneG

variable (P : IngrBParams)

theorem pt_J_zero (hU : P.U = flatCfg) : P.data.J = 0 := by
  have hJ : P.Jf = 0 := Jf_flat P hU
  show (pE P.G) P.Jf = 0
  rw [hJ]; exact map_zero _

theorem pt_G1inv_eq (hU : P.U = flatCfg) : P.G1inv = P.data.Ginv := by
  have hJ := pt_J_zero P hU
  refine symm_unique (P.G1inv_spec.symm) (P.data.Ginv_symm P.data_laws) (fun A => ?_)
  rw [P.G1inv_spec.form A, BaseDataS.K_eq, hJ, inner_zero_right, mul_zero, sub_zero]

theorem pt_unit_of_pd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : E →L[ℝ] E) (hpd : ∀ x : E, ⟪x, M x⟫ = 0 → x = 0) : IsUnit M := by
  have hinj : Function.Injective (M : E →ₗ[ℝ] E) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine hpd x ?_
    have : M x = 0 := hx
    rw [this, inner_zero_right]
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩

/-- the four units at a flat background, from definiteness of the `Ginv` form and injectivity of `Q*`. -/
theorem pt_unitsFour (hU : P.U = flatCfg)
    (hpd : ∀ x : ↥(bondSupp P.G), ⟪x, P.data.Ginv x⟫ = 0 → x = 0)
    (hQs : Function.Injective P.data.Qs) : UnitsFour P := by
  have hGi : IsUnit P.data.Ginv := pt_unit_of_pd _ hpd
  have hG1 : IsUnit P.G1inv := by rw [pt_G1inv_eq P hU]; exact hGi
  refine ⟨hG1, ?_, hGi, ?_⟩
  · -- Nmat
    show IsUnit ((P.data.Q.comp (P.data.G1 P.G1inv)).comp P.data.Qs)
    have hinj : Function.Injective ((((P.data.Q.comp (P.data.G1 P.G1inv)).comp P.data.Qs)) :
        FSp P.G →ₗ[ℝ] FSp P.G) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      set A : ↥(bondSupp P.G) := (P.data.G1 P.G1inv) (P.data.Qs z) with hA
      have hG1' : P.G1inv A = P.data.Qs z := by
        have := Ring.mul_inverse_cancel _ hG1
        exact ContinuousLinearMap.ext_iff.mp this (P.data.Qs z)
      have hNz : ((P.data.Q.comp (P.data.G1 P.G1inv)).comp P.data.Qs) z = P.data.Q A := rfl
      have hz' : ((P.data.Q.comp (P.data.G1 P.G1inv)).comp P.data.Qs) z = 0 := hz
      have h0 : ⟪A, P.G1inv A⟫ = 0 := by
        rw [hG1', ← P.data.Q_adj, ← hNz, hz', inner_zero_left]
      have hA0 : A = 0 := by
        refine hpd A ?_
        rw [← pt_G1inv_eq P hU]; exact h0
      have : P.data.Qs z = 0 := by rw [← hG1', hA0, map_zero]
      exact hQs (by rw [this, map_zero])
    exact (ContinuousLinearMap.isUnit_iff_bijective).mpr ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩
  · -- Q G Q*
    show IsUnit ((P.data.Q.comp P.data.G).comp P.data.Qs)
    have hinj : Function.Injective ((((P.data.Q.comp P.data.G).comp P.data.Qs)) :
        FSp P.G →ₗ[ℝ] FSp P.G) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      set A : ↥(bondSupp P.G) := P.data.G (P.data.Qs z) with hA
      have hG1' : P.data.Ginv A = P.data.Qs z := by
        have := Ring.mul_inverse_cancel _ hGi
        exact ContinuousLinearMap.ext_iff.mp this (P.data.Qs z)
      have hNz : ((P.data.Q.comp P.data.G).comp P.data.Qs) z = P.data.Q A := rfl
      have hz' : ((P.data.Q.comp P.data.G).comp P.data.Qs) z = 0 := hz
      have h0 : ⟪A, P.data.Ginv A⟫ = 0 := by
        rw [hG1', ← P.data.Q_adj, ← hNz, hz', inner_zero_left]
      have hA0 : A = 0 := hpd A h0
      have : P.data.Qs z = 0 := by rw [← hG1', hA0, map_zero]
      exact hQs (by rw [this, map_zero])
    exact (ContinuousLinearMap.isUnit_iff_bijective).mpr ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩

#print axioms pt_unitsFour

end AdalyFormal.CoverOmegaTwo
