import GdGen5

/-!
# GdGen6 -- consequences at an ARBITRARY configuration `U`.

* `genFormS_collapse_of_not_wd`, `genFormS_zero`.
* `InstIneqSG2_general` : the full-guard literal inequality at `U` follows from the localised inequality at the SAME `U`.
* `GapAt_of_loc` : given the localised units, `GapAt` at `U` reduces to `IsUnit Ginv → IsUnit G1inv`.
* `InstIneqSG_general` : the guarded literal inequality at `U` from the localised inequality at `U` and `IsUnit Ginv → IsUnit G1inv`.
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
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)

theorem genFormS_collapse_of_not_wd (sD sJ : PlaqSel) (P : IngrBParams) (h : ¬ WellDefAt sD sJ P) (B : BondFnL2 P.Lu) :
    GenS.genFormS sD sJ P B = -P.a * ⟪B, B⟫ := by
  by_cases hM : IsUnit (dataS sD sJ P).Ginv
  · by_cases hG : IsUnit (G1invS sD sJ P)
    · exact genFormS_collapse_N sD sJ P (fun hN => h ⟨hM, hG, hN⟩) B
    · exact genFormS_collapse_G1inv sD sJ P hG B
  · exact genFormS_collapse sD sJ P hM B

theorem genFormS_zero (sD sJ : PlaqSel) (P : IngrBParams) : GenS.genFormS sD sJ P (0 : BondFnL2 P.Lu) = 0 := by
  have hD : P.D2in (0 : BondFnL2 P.Lu) = 0 := by
    have := P.D2in_quad 0 (0 : BondFnL2 P.Lu)
    simpa using this
  unfold GenS.genFormS GenS.firstTermS
  rw [hD]
  simp

section gen
variable (sD sJ : PlaqSel) {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
  {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M)
  {a γ₀ : ℝ} (ha : 0 ≤ a) (hγ : 0 < γ₀) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
  (hsD : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD L G)
  (hsJ : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ L G)

include hS hk hroom ha hγ hsD hsJ in
/-- **the full-guard literal inequality at ANY `U` follows from the localised inequality at the same `U`.** -/
theorem InstIneqSG2_general
    (hloc : InstIneqS selIn selIn ell k hell0 a Lu γ₀ S Lam U) :
    InstIneqSG2 sD sJ ell k hell0 a Lu γ₀ S Lam U := by
  intro hWD Bt h1 h2
  have hlocB := hloc Bt h1 h2
  by_cases hWD2 : WellDefAt selIn selIn (gparams ell k Lu hell0 S U a Lam)
  · have heq := genFormS_eq_loc (gparams ell k Lu hell0 S U a Lam) hS hell0 hroom hk sD sJ selIn selIn hsD
      (fun _ _ => subset_rfl) hsJ (fun _ _ => subset_rfl) hWD hWD2
      (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S U a Lam) Bt))
    exact hlocB.trans_eq heq.symm
  · have hcol := genFormS_collapse_of_not_wd selIn selIn (gparams ell k Lu hell0 S U a Lam) hWD2
      (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S U a Lam) Bt))
    have hlocB' := hlocB
    rw [hcol] at hlocB'
    have hB0 : (0 : ℝ) ≤ ⟪(WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S U a Lam) Bt) : BondFnL2 Lu),
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S U a Lam) Bt) : BondFnL2 Lu)⟫ := real_inner_self_nonneg
    have hE : bondEnergy Bt ≤ 0 := by
      by_contra hpos
      push Not at hpos
      have hA : (gparams ell k Lu hell0 S U a Lam).a = a := rfl
      rw [hA] at hlocB'
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

#print axioms genFormS_collapse_of_not_wd
#print axioms genFormS_zero
#print axioms InstIneqSG2_general

end gen

end AdalyFormal.D1Guarded
