import GdGen4
import GdSG3

/-!
# GdGen5 -- ANY configuration `U`: `genFormS` (literal selectors) = `genFormS` (localised) under the units; the full-guard literal inequality from the localised headline;
the guard gap reduces to `IsUnit Ginv → IsUnit G1inv`.
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
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)

section gen
variable (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell0 : 0 < P.ell) (hroom : 17 * P.ell ≤ R * M)

include hS hell0 hroom in
/-- **the literal and the localised `genFormS` agree at every configuration**, once all units exist. -/
theorem genFormS_eq_loc (hk : 1 ≤ P.k) (sD sJ sD' sJ' : PlaqSel)
    (hsD : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD L G)
    (hsD' : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD' L G)
    (hsJ : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ L G)
    (hsJ' : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ' L G)
    (WD1 : WellDefAt sD sJ P) (WD2 : WellDefAt sD' sJ' P) (B : BondFnL2 P.Lu) :
    GenS.genFormS sD sJ P B = GenS.genFormS sD' sJ' P B := by
  have T := twoData_lit_loc P hS hell0 hroom sD sJ sD' sJ' hsD hsD' hsJ hsJ'
  have hL1 := dataS_laws sD sJ P
  have hL2 := dataS_laws sD' sJ' P
  have hG1 := G1invS_spec sD sJ P
  have hG2 := G1invS_spec sD' sJ' P
  have n1 : IsUnit (((dataS sD sJ P).Q.comp (dataS sD sJ P).G).comp (dataS sD sJ P).Qs) :=
    NG_unit_of_N1 (dataS sD sJ P) hL1 hG1 WD1.2.2
  have n2 : IsUnit (((dataS sD' sJ' P).Q.comp (dataS sD' sJ' P).G).comp (dataS sD' sJ' P).Qs) :=
    NG_unit_of_N1 (dataS sD' sJ' P) hL2 hG2 WD2.2.2
  have hτ : ∀ y : BondFnL2 P.Lu, ContinuousLinearMap.adjoint P.tau y ∈ Z0 P.G := fun y β hβ => adjoint_tau_level0 P hk y β hβ
  have e1 := (T.N1inv_H1_eq hL1 hL2 WD1.1 WD2.1 n1 n2 hG1 hG2 WD1.2.1 WD2.2.1 WD1.2.2 WD2.2.2 (hτ B)).1
  have hfirst : GenS.firstTermS sD sJ P B = GenS.firstTermS sD' sJ' P B :=
    congrArg (fun t => P.eta * ⟪ContinuousLinearMap.adjoint P.tau B, t⟫) e1
  have e2 := T.inner_H1_J_eq hL1 hL2 WD1.1 WD2.1 n1 n2 hG1 hG2 WD1.2.1 WD2.2.1 WD1.2.2 WD2.2.2 (hτ (P.D2in B))
  have hH : ⟪H1inS sD sJ P (P.D2in B), JfS sJ P⟫ = ⟪H1inS sD' sJ' P (P.D2in B), JfS sJ' P⟫ := by
    have a1 : ⟪H1inS sD sJ P (P.D2in B), JfS sJ P⟫ =
        ⟪(dataS sD sJ P).H1 (G1invS sD sJ P) (ContinuousLinearMap.adjoint P.tau (P.D2in B)), (dataS sD sJ P).J⟫ :=
      (pE_inner_right P.G _ (JfS sJ P)).symm
    have a2 : ⟪H1inS sD' sJ' P (P.D2in B), JfS sJ' P⟫ =
        ⟪(dataS sD' sJ' P).H1 (G1invS sD' sJ' P) (ContinuousLinearMap.adjoint P.tau (P.D2in B)), (dataS sD' sJ' P).J⟫ :=
      (pE_inner_right P.G _ (JfS sJ' P)).symm
    exact a1.trans (e2.trans a2.symm)
  exact congrArg₂ (fun u v => u - P.a * ⟪B, B⟫ - 2 * v) hfirst hH

#print axioms genFormS_eq_loc

end gen

end AdalyFormal.D1Guarded
