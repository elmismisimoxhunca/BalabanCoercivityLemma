import NsCvO34

/-!
# CvO35 -- `Delta2 = 0` on sigma_3-valued fields of `E_0`; `G1inv = Ginv` there (lane omega)
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

/-- `Wop` preserves sigma_3-valued fields (equivariance under the constant Cartan gauge). -/
theorem Wop_sig (P : IngrBParams) (hU : CartanCfg P.U) (u : BondFnL2 P.Lf) (hu : SigB (WithLp.ofLp u)) :
    SigB (WithLp.ofLp (Wop P.G P.U P.a u)) := by
  have h := (bondEqv_hGauge P hU).W u
  rw [(adBL_hGauge_fixed_iff u).mpr hu] at h
  exact (adBL_hGauge_fixed_iff _).mp h.symm

/-- the base-data `C2` vanishes on sigma_3-valued elements of `E_0` once `C2full` vanishes on sigma_3-valued fields. -/
theorem data_C2_sig (P : IngrBParams) (hU : CartanCfg P.U) (hC : ∀ A : BondFnL2 P.Lf, SigB (WithLp.ofLp A) → P.sector.C2full A = 0)
    (u : ↥(bondSupp P.G)) (hu : SigB (WithLp.ofLp (u : BondFnL2 P.Lf))) : P.data.C2 u = 0 :=
  hC _ (Wop_sig P hU _ hu)

theorem Delta2_equivariant (P : IngrBParams) (hU : CartanCfg P.U) (x : ↥(bondSupp P.G)) :
    P.data.Delta2 P.data_laws (adEL (hGauge P.Lf) P.G x) = adEL (hGauge P.Lf) P.G (P.data.Delta2 P.data_laws x) := by
  have h := baseEqv_hGauge P hU
  have hG1 : P.G1inv = P.data.Ginv - P.data.Delta2 P.data_laws :=
    P.data.G1inv_unique P.G1inv_spec (P.data.isG1inv_sub P.data_laws)
  have e1 := h.G1inv P.G1inv_spec P.G1inv_spec x
  have e2 := h.Ginv x
  have : P.data.Delta2 P.data_laws = P.data.Ginv - P.G1inv := by rw [hG1]; abel
  rw [this]
  simp only [ContinuousLinearMap.sub_apply, e1, e2, map_sub]

/-- **`Delta2` kills sigma_3-valued fields.** -/
theorem Delta2_sig (P : IngrBParams) (hU : CartanCfg P.U) (hC : ∀ A : BondFnL2 P.Lf, SigB (WithLp.ofLp A) → P.sector.C2full A = 0)
    (x : ↥(bondSupp P.G)) (hx : SigB (WithLp.ofLp (x : BondFnL2 P.Lf))) : P.data.Delta2 P.data_laws x = 0 := by
  set AE := adEL (hGauge P.Lf) P.G with hAE
  have hxfix : AE x = x := (adEL_hGauge_fixed_iff P.G x).mpr hx
  obtain ⟨hsymm, hform⟩ := P.data.Delta2_spec P.data_laws
  -- Delta2 x is fixed
  have hfix : AE (P.data.Delta2 P.data_laws x) = P.data.Delta2 P.data_laws x := by
    rw [← Delta2_equivariant P hU, hxfix]
  -- quadratic form vanishes on fixed vectors
  have hq : ∀ u : ↥(bondSupp P.G), AE u = u → ⟪u, P.data.Delta2 P.data_laws u⟫ = 0 := by
    intro u hu
    rw [hform u]
    have : P.data.C2 u = 0 := data_C2_sig P hU hC u ((adEL_hGauge_fixed_iff P.G u).mp hu)
    rw [this]; simp
  -- pairing with a fixed w vanishes
  have hpair : ∀ w : ↥(bondSupp P.G), AE w = w → ⟪w, P.data.Delta2 P.data_laws x⟫ = 0 := by
    intro w hw
    have h1 := hq (w + x) (by rw [map_add, hw, hxfix])
    have h2 := hq w hw
    have h3 := hq x hxfix
    simp only [map_add, inner_add_left, inner_add_right] at h1
    have h4 : ⟪x, P.data.Delta2 P.data_laws w⟫ = ⟪w, P.data.Delta2 P.data_laws x⟫ := by
      rw [real_inner_comm, hsymm]
    linarith
  -- general w
  have hall : ∀ w : ↥(bondSupp P.G), ⟪w, P.data.Delta2 P.data_laws x⟫ = 0 := by
    intro w
    have hsym : AE (w + AE w) = w + AE w := by
      rw [map_add, hAE, adEL_hGauge_sq]; abel
    have h1 := hpair _ hsym
    have h2 : ⟪AE w, P.data.Delta2 P.data_laws x⟫ = ⟪w, P.data.Delta2 P.data_laws x⟫ := by
      conv_lhs => rw [← hfix]
      exact (AE.inner_map_map _ _)
    rw [inner_add_left, h2] at h1
    linarith
  exact inner_self_eq_zero.mp (hall _)

#print axioms Delta2_sig

end AdalyFormal.CoverOmega
