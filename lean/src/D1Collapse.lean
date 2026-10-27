import D1Lit

/-!
# D1Collapse -- junk collapse of `genFormS` when `Ginv` is not a unit (generalises `statement_audit_r5_opus/PXCollapse.lean` to the selector-generalised data)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

section generic
variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable (D : BaseDataS E S F)

theorem gen_G_zero (h : ¬ IsUnit D.Ginv) : D.G = 0 := Ring.inverse_non_unit _ h

theorem gen_H_zero (h : ¬ IsUnit D.Ginv) : D.H = 0 := by
  unfold BaseDataS.H
  rw [gen_G_zero D h]
  simp only [ContinuousLinearMap.zero_comp]

theorem gen_Ginv_isG1inv (hL : D.Laws) (h : ¬ IsUnit D.Ginv) : D.IsG1inv D.Ginv := by
  refine ⟨fun x y => D.Ginv_symm hL x y, fun A => ?_⟩
  rw [D.K_eq, gen_H_zero D h]
  simp

theorem gen_G1inv_eq (hL : D.Laws) (h : ¬ IsUnit D.Ginv) {G1inv : E →L[ℝ] E} (hG : D.IsG1inv G1inv) : G1inv = D.Ginv :=
  D.G1inv_unique hG (gen_Ginv_isG1inv D hL h)

theorem gen_G1_zero (hL : D.Laws) (h : ¬ IsUnit D.Ginv) {G1inv : E →L[ℝ] E} (hG : D.IsG1inv G1inv) : D.G1 G1inv = 0 := by
  unfold BaseDataS.G1
  rw [gen_G1inv_eq D hL h hG]
  exact Ring.inverse_non_unit _ h

theorem gen_H1_zero (hL : D.Laws) (h : ¬ IsUnit D.Ginv) {G1inv : E →L[ℝ] E} (hG : D.IsG1inv G1inv) : D.H1 G1inv = 0 := by
  unfold BaseDataS.H1
  rw [gen_G1_zero D hL h hG]
  simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
end generic

/-- JUNK COLLAPSE (selector-generalised): if `Ginv` of the data is not a unit, `genFormS B = -a ⟪B,B⟫`. -/
theorem genFormS_collapse (sD sJ : PlaqSel) (P : IngrBParams) (h : ¬ IsUnit (dataS sD sJ P).Ginv) (B : BondFnL2 P.Lu) :
    GenS.genFormS sD sJ P B = -P.a * ⟪B, B⟫ := by
  have hL := dataS_laws sD sJ P
  have hG := G1invS_spec sD sJ P
  have hN : GenS.NmatS sD sJ P = 0 := by
    unfold GenS.NmatS
    rw [gen_G1_zero _ hL h hG]
    simp only [ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp]
  have hH : H1inS sD sJ P = 0 := by
    unfold H1inS
    rw [gen_H1_zero _ hL h hG]
    simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  unfold GenS.genFormS GenS.firstTermS
  rw [hN, hH, Ring.inverse_zero]
  simp

/-- the literal inequality FAILS at any point where `Ginv` is not a unit, for every `γ₀ > 0`, given one admissible `B̃` of positive energy and `a ≥ 0`. -/
theorem not_InstIneqS_of_not_unit (sD sJ : PlaqSel) (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 ≤ a)
    (Lu : PeriodicLatticeExtent) (γ₀ : ℝ) (hγ : 0 < γ₀)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (hnu : ¬ IsUnit (dataS sD sJ (gparams ell k Lu hell S U a Lam)).Ginv)
    (Bt : Bond Lu → SuTwo) (h1 : OnLambdaTildeIn Lam ell Bt) (h2 : OnLambdaT Lam Bt)
    (hE : 0 < bondEnergy Bt) :
    ¬ InstIneqS sD sJ ell k hell a Lu γ₀ S Lam U := by
  intro hI
  have h := hI Bt h1 h2
  rw [genFormS_collapse sD sJ _ hnu] at h
  have hB : 0 ≤ ⟪(WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt) : BondFnL2 Lu),
      WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt)⟫ := real_inner_self_nonneg
  have : (gparams ell k Lu hell S U a Lam).a = a := rfl
  rw [this] at h
  nlinarith [mul_pos hγ hE, mul_nonneg ha hB]

#print axioms genFormS_collapse
#print axioms not_InstIneqS_of_not_unit

end AdalyFormal.D1Literal
