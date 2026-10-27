import GdR6b
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
namespace SolR6Residual
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2 AdalyFormal.D1Literal AdalyFormal.D1Guarded

-- Stronger domain for correction equality: no assumed literal G1inv unit.
theorem delta_eq_with_only_literal_Ginv (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell) (hroom : 17 * P.ell ≤ R * M)
    (sD sJ : PlaqSel)
    (hsD : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD L G)
    (hsJ : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ L G)
    (hu : IsUnit (dataS sD sJ P).Ginv) (WD : WellDefAt selIn selIn P) :
    (dataS sD sJ P).Delta2 (dataS_laws sD sJ P) =
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) := by
  have T := twoData_lit_loc P hS hell hroom sD sJ selIn selIn hsD (fun _ _ => Set.Subset.refl _) hsJ (fun _ _ => Set.Subset.refl _)
  have n2 := NG_unit_of_N1 (dataS selIn selIn P) (dataS_laws selIn selIn P) (G1invS_spec selIn selIn P) WD.2.2
  have n1 : IsUnit (((dataS sD sJ P).Q.comp (dataS sD sJ P).G).comp (dataS sD sJ P).Qs) := by
    have hQ := T.hQ
    have hQs := T.hQs
    have nn : IsUnit (((dataS sD sJ P).Q.comp (dataS selIn selIn P).G).comp (dataS sD sJ P).Qs) := by
      rw [hQ, hQs]; exact n2
    exact unit_transfer (V0 P.G) (Z0 P.G) hu WD.1 nn T.hZV T.hM
  exact T.Delta2_eq (dataS_laws sD sJ P) (dataS_laws selIn selIn P) hu WD.1 n1 n2
#print axioms delta_eq_with_only_literal_Ginv
end SolR6Residual
