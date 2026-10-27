import GdGen6

/-!
# GdGen7 -- the guard gap at an ARBITRARY configuration reduces to `IsUnit Ginv → IsUnit G1inv`.
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

section gen
variable (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell0 : 0 < P.ell) (hroom : 17 * P.ell ≤ R * M)

include hS hell0 hroom in
/-- **the guard gap at `P` from the localised units**: only `IsUnit Ginv → IsUnit G1inv` remains. -/
theorem GapAt_of_loc (sD sJ : PlaqSel)
    (hsD : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD L G)
    (hsJ : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ L G)
    (WD2 : WellDefAt selIn selIn P)
    (h : IsUnit (dataS sD sJ P).Ginv → IsUnit (G1invS sD sJ P)) : GapAt sD sJ P := by
  intro hu
  have g1 := h hu
  refine ⟨g1, ?_⟩
  have T := twoData_lit_loc P hS hell0 hroom sD sJ selIn selIn hsD (fun _ _ => subset_rfl) hsJ (fun _ _ => subset_rfl)
  have hL1 := dataS_laws sD sJ P
  have hL2 := dataS_laws selIn selIn P
  have hG1 := G1invS_spec sD sJ P
  have hG2 := G1invS_spec selIn selIn P
  have n2 : IsUnit (((dataS selIn selIn P).Q.comp (dataS selIn selIn P).G).comp (dataS selIn selIn P).Qs) :=
    NG_unit_of_N1 (dataS selIn selIn P) hL2 hG2 WD2.2.2
  have hZV2 : ∀ x, (dataS selIn selIn P).Q x ∈ Z0 P.G → x ∈ V0 P.G := fun x hx => T.hZV x (by rw [T.hQ]; exact hx)
  have n1' : IsUnit (((dataS selIn selIn P).Q.comp (Ring.inverse (dataS sD sJ P).Ginv)).comp (dataS selIn selIn P).Qs) :=
    unit_transfer (Q := (dataS selIn selIn P).Q) (Qs := (dataS selIn selIn P).Qs) (V0 P.G) (Z0 P.G) hu WD2.1 n2 hZV2 T.hM
  have n1 : IsUnit (((dataS sD sJ P).Q.comp (dataS sD sJ P).G).comp (dataS sD sJ P).Qs) := by
    show IsUnit (((dataS sD sJ P).Q.comp (Ring.inverse (dataS sD sJ P).Ginv)).comp (dataS sD sJ P).Qs)
    rw [T.hQ, T.hQs]; exact n1'
  have m1' : IsUnit (((dataS selIn selIn P).Q.comp (Ring.inverse (G1invS sD sJ P))).comp (dataS selIn selIn P).Qs) :=
    unit_transfer (Q := (dataS selIn selIn P).Q) (Qs := (dataS selIn selIn P).Qs) (V0 P.G) (Z0 P.G) g1 WD2.2.1 WD2.2.2 hZV2
      (fun x hx => T.G1inv_eq_on hL1 hL2 hu WD2.1 n1 n2 hG1 hG2 hx)
  show IsUnit (((dataS sD sJ P).Q.comp (Ring.inverse (G1invS sD sJ P))).comp (dataS sD sJ P).Qs)
  rw [T.hQ, T.hQs]; exact m1'

#print axioms GapAt_of_loc

end gen

section ineq
variable (sD sJ : PlaqSel) {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
  {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M)
  {a γ₀ : ℝ} (ha : 0 ≤ a) (hγ : 0 < γ₀) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
  (hsD : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD L G)
  (hsJ : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ L G)

include hS hk hroom ha hγ hsD hsJ in
/-- **the guarded literal inequality at ANY `U`**, from the localised inequality at the same `U`, the localised units, and `IsUnit Ginv → IsUnit G1inv`. -/
theorem InstIneqSG_general (hloc : InstIneqS selIn selIn ell k hell0 a Lu γ₀ S Lam U)
    (WD2 : WellDefAt selIn selIn (gparams ell k Lu hell0 S U a Lam))
    (h : IsUnit (dataS sD sJ (gparams ell k Lu hell0 S U a Lam)).Ginv → IsUnit (G1invS sD sJ (gparams ell k Lu hell0 S U a Lam))) :
    InstIneqSG sD sJ ell k hell0 a Lu γ₀ S Lam U :=
  instIneqSG_of_gap sD sJ ell k hell0 a Lu γ₀ S Lam U
    (GapAt_of_loc (gparams ell k Lu hell0 S U a Lam) hS hell0 hroom sD sJ hsD hsJ WD2 h)
    (InstIneqSG2_general sD sJ hell0 hS hk hroom ha hγ Lam U hsD hsJ hloc)

#print axioms InstIneqSG_general

end ineq

end AdalyFormal.D1Guarded
