import GdGen8

/-!
# GdGen9 -- the guarded literal headline `P428Target8SG selAll sJ` from the localised headline and ONE residual implication.

`GuardResidual sD sJ`: at every printed-class configuration (in the regime that the headline quantifies over) at which the localised data are well defined,
`IsUnit Ginv → IsUnit G1inv` for the literal selectors.  `P428Target8SG_of_residual`: this residual (together with the proved localised headline) gives `P428Target8SG sD sJ`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)

/-- if the localised data are NOT well defined, the localised inequality forces every admissible test field to have zero energy, and then the literal inequality is trivial. -/
theorem InstIneqS_of_loc_not_wd (sD sJ : PlaqSel) {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} {a γ₀ : ℝ} (ha : 0 ≤ a) (hγ : 0 < γ₀) (Lam : Set (PeriodicLatticeSite Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (hloc : InstIneqS selIn selIn ell k hell0 a Lu γ₀ S Lam U)
    (hWD2 : ¬ WellDefAt selIn selIn (gparams ell k Lu hell0 S U a Lam)) :
    InstIneqS sD sJ ell k hell0 a Lu γ₀ S Lam U := by
  intro Bt h1 h2
  have hlocB := hloc Bt h1 h2
  have hcol := genFormS_collapse_of_not_wd selIn selIn (gparams ell k Lu hell0 S U a Lam) hWD2
    (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S U a Lam) Bt))
  rw [hcol] at hlocB
  have hB0 : (0 : ℝ) ≤ ⟪(WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S U a Lam) Bt) : BondFnL2 Lu),
      (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S U a Lam) Bt) : BondFnL2 Lu)⟫ := real_inner_self_nonneg
  have hE : bondEnergy Bt ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hA : (gparams ell k Lu hell0 S U a Lam).a = a := rfl
    rw [hA] at hlocB
    nlinarith [mul_pos hγ hpos, mul_nonneg ha hB0]
  have hBt : Bt = 0 := bondEnergy_eq_zero (le_antisymm hE (bondEnergy_nonneg Bt))
  subst hBt
  have hE0 : bondEnergy (0 : Bond Lu → SuTwo) = 0 := by
    unfold bondEnergy
    exact Finset.sum_eq_zero (fun b _ => by simp)
  rw [hE0, mul_zero]
  have hB0' : (WithLp.toLp 2 ((GenP.genC (gparams ell k Lu hell0 S U a Lam)) 0) :
      BondFnL2 (gparams ell k Lu hell0 S U a Lam).Lu) = 0 := by
    rw [map_zero]; rfl
  exact ((congrArg (GenS.genFormS sD sJ (gparams ell k Lu hell0 S U a Lam)) hB0').trans
    (genFormS_zero sD sJ (gparams ell k Lu hell0 S U a Lam))).ge

#print axioms InstIneqS_of_loc_not_wd

/-- **the residual**: at a printed-class configuration with well-defined localised data, `IsUnit Ginv → IsUnit G1inv` for the literal selectors. -/
def GuardResidual (sD sJ : PlaqSel) : Prop :=
  ∀ (ell M R k : ℕ) (Lu : PeriodicLatticeExtent) (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu)) (a α₀ : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)),
    2 ≤ ell → 1 ≤ k → 17 * ell ≤ R * M → TorusOK ell M Lu → Admissible ell M R k S → LambdaOK2 ell M R k S Lam →
    ClassCoupled ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    WellDefAt selIn selIn (gparams ell k Lu hell0 S U a Lam) →
    IsUnit (dataS sD sJ (gparams ell k Lu hell0 S U a Lam)).Ginv → IsUnit (G1invS sD sJ (gparams ell k Lu hell0 S U a Lam))

/-- **the guarded literal headline from the localised headline and the residual.** -/
theorem P428Target8SG_of_residual (sD sJ : PlaqSel)
    (hsD : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD L G)
    (hsJ : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ L G)
    (hres : GuardResidual sD sJ) : P428Target8SG sD sJ := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hmm⟩ := (pin_target8_iff.mpr AdalyFormal.M2RightInv.p428Target8 : P428Target8S selIn selIn) ell hell a ha
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hmm m hm
  refine ⟨max R₀ 18, fun R hR => ?_⟩
  obtain ⟨hside, a₀, ha₀, γ₀, hγ, hcore⟩ := hR₀ R (le_trans (le_max_left _ _) hR)
  have hR18 : 18 ≤ R := le_trans (le_max_right _ _) hR
  refine ⟨hside, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ hα hαle hT S hS Lam hL U hU => ?_⟩
  have hell0 : 0 < ell := by omega
  have hroom : 17 * ell ≤ R * ell ^ m := by
    have h1 : ell ≤ ell ^ m := by
      calc ell = ell ^ 1 := (pow_one ell).symm
        _ ≤ ell ^ m := Nat.pow_le_pow_right hell0 (le_trans hm₀ hm)
    calc 17 * ell ≤ 18 * ell ^ m := by omega
      _ ≤ R * ell ^ m := Nat.mul_le_mul_right _ hR18
  have hloc := hcore k hk Lu α₀ hα hαle hT S hS Lam hL U hU
  by_cases hWD2 : WellDefAt selIn selIn (gparams ell k Lu hell0 S U a Lam)
  · exact InstIneqSG_general sD sJ hell0 hS hk hroom ha.le hγ Lam U hsD hsJ hloc hWD2
      (hres ell (ell ^ m) R k Lu hell0 S a α₀ Lam U hell hk hroom hT hS hL hU hWD2)
  · intro _
    exact InstIneqS_of_loc_not_wd sD sJ hell0 ha.le hγ Lam U hloc hWD2

#print axioms P428Target8SG_of_residual

end AdalyFormal.D1Guarded
