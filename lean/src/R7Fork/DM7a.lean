import R7Fork.DM6b

/-!
# DM7a -- `IsUnit Nmat` from `IsUnit G1inv` and injectivity of `Q*` (flat `U`, any tower, `a >= 0`).
`G1inv` is symmetric with nonnegative form (sum of squares + mass), so `form A = 0` forces `G1inv A = 0`, hence `A = 0` when `G1inv` is a unit.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)

/-- a symmetric positive semidefinite operator kills every vector of zero form -/
theorem psd_kernel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (S : E →L[ℝ] E)
    (hsym : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫) (hpsd : ∀ x, 0 ≤ ⟪x, S x⟫) (x : E) (h : ⟪x, S x⟫ = 0) : S x = 0 := by
  have key : ∀ y : E, ⟪y, S x⟫ = 0 := by
    intro y
    set u := ⟪y, S x⟫ with hu
    set c := ⟪y, S y⟫ with hc
    have hc0 : 0 ≤ c := hpsd y
    have hexp : ∀ t : ℝ, ⟪x + t • y, S (x + t • y)⟫ = 2 * t * u + t ^ 2 * c := by
      intro t
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, h]
      have : ⟪x, S y⟫ = u := by rw [← hsym, real_inner_comm]
      rw [this]; ring
    by_contra hne
    have hpos : 0 < u ^ 2 := by positivity
    have := hpsd (x + (-u / (c + 1)) • y)
    rw [hexp] at this
    have hc1 : 0 < c + 1 := by linarith
    have : 2 * (-u / (c + 1)) * u + (-u / (c + 1)) ^ 2 * c < 0 := by
      have e : 2 * (-u / (c + 1)) * u + (-u / (c + 1)) ^ 2 * c = u ^ 2 * (-(c + 2)) / (c + 1) ^ 2 := by
        field_simp; ring
      rw [e]
      apply div_neg_of_neg_of_pos
      · nlinarith
      · positivity
    linarith
  have := key (S x)
  exact inner_self_eq_zero.mp this

/-- the quadratic form of `G1inv` at flat `U` (any tower) -/
theorem G1inv_form_gen (P : IngrBParams) (hU : P.U = flatCfg) (A : ↥(bondSupp P.G)) :
    ⟪A, P.G1inv A⟫ = ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn P.G.Om0)
          (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
            (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A))‖ ^ 2 +
        ‖Tfull P.G P.U (iE P.G A)‖ ^ 2 + ⟪A, P.data.Mass A⟫ := by
  have hJ : P.Jf = 0 := Jf_flat P hU
  have hJd : P.data.J = 0 := by
    show (pE P.G) P.Jf = 0
    rw [hJ]; exact map_zero _
  have hK := P.G1inv_spec.form A
  have hD : ⟪A, P.data.Dpi A⟫ = ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn P.G.Om0)
          (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
            (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A))‖ ^ 2 := by
    have : ⟪A, P.data.Dpi A⟫ = ⟪iE P.G A, DpiFull P.G P.U P.a (iE P.G A)⟫ := by
      show ⟪A, (pE P.G) (DpiFull P.G P.U P.a (iE P.G A))⟫ = _
      rw [pE_inner_right]
    rw [this, hU]
    exact inner_DpiFull_flat P.G P.a (iE P.G A)
  rw [hK]
  unfold BaseDataS.K
  rw [hJd, inner_zero_right, mul_zero, sub_zero, hD]
  rfl

theorem mass_nonneg_gen (P : IngrBParams) (ha : 0 ≤ P.a) (A : ↥(bondSupp P.G)) : 0 ≤ ⟪A, P.data.Mass A⟫ := by
  rw [mass_inner_gen]
  exact Finset.sum_nonneg (fun p _ => mul_nonneg (mul_nonneg ha (by positivity)) (sq_nonneg _))

theorem G1inv_nonneg_gen (P : IngrBParams) (hU : P.U = flatCfg) (ha : 0 ≤ P.a) (A : ↥(bondSupp P.G)) :
    0 ≤ ⟪A, P.G1inv A⟫ := by
  rw [G1inv_form_gen P hU A]
  have := mass_nonneg_gen P ha A
  positivity

/-- **`IsUnit N` from `IsUnit G1inv` and injectivity of `Q*`.** -/
theorem isUnit_Nmat_of_Qs_inj (P : IngrBParams) (hU : P.U = flatCfg) (ha : 0 ≤ P.a)
    (hG : IsUnit P.G1inv) (hQs : Function.Injective P.data.Qs) : IsUnit (GenP.Nmat P) := by
  have hinj : Function.Injective ((GenP.Nmat P) : FSp P.G →ₗ[ℝ] FSp P.G) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    set A : ↥(bondSupp P.G) := P.data.G1 P.G1inv (P.data.Qs z) with hA
    have hG1 : P.G1inv A = P.data.Qs z := by
      have := Ring.mul_inverse_cancel _ hG
      exact ContinuousLinearMap.ext_iff.mp this (P.data.Qs z)
    have hNz : GenP.Nmat P z = P.data.Q A := rfl
    have hz' : GenP.Nmat P z = 0 := hz
    have h0 : ⟪A, P.G1inv A⟫ = 0 := by
      rw [hG1, ← P.data.Q_adj, ← hNz, hz', inner_zero_left]
    have hker : P.G1inv A = 0 :=
      psd_kernel P.G1inv P.G1inv_spec.symm (G1inv_nonneg_gen P hU ha) A h0
    have hA0 : A = 0 := by
      obtain ⟨u, hu⟩ := hG
      have : (↑u⁻¹ : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G)) (P.G1inv A) = A := by
        rw [← hu]; exact ContinuousLinearMap.ext_iff.mp u.inv_mul A
      rw [hker, map_zero] at this
      exact this.symm
    have : P.data.Qs z = 0 := by rw [← hG1, hA0, map_zero]
    exact hQs (by rw [this, map_zero])
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩

#print axioms psd_kernel
#print axioms G1inv_form_gen
#print axioms isUnit_Nmat_of_Qs_inj

end AdalyFormal.DirichletMono
