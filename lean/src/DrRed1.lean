import GdR6b

/-!
# DrRed1 -- exact reduction of the guard residual to a linear-algebra pencil.

For a configuration `P` at which the literal `Ginv` is a unit and the localised data are well defined (`WellDefAt selIn selIn P`),
`G1inv_lit = Ginv_lit - Delta2_loc` as operators, with `Delta2_loc` the correction of the LOCALISED data (the same operator for every
exterior/shell value that leaves the localised data unchanged).  So at such a `P`, `IsUnit G1inv_lit` is the statement that the
pencil `Ginv_lit - Delta2_loc` is invertible.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Residual

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.D1Guarded
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

section red
variable (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell0 : 0 < P.ell) (hroom : 17 * P.ell ≤ R * M)

include hS hell0 hroom in
/-- the literal `Delta2` equals the localised `Delta2` as soon as the literal `Ginv` is a unit and the localised data are well defined
(no unit hypothesis on the literal `G1inv`; this is the statement of Sol round 6, `delta_eq_with_only_literal_Ginv`, re-proved here). -/
theorem Delta2_lit_eq_loc (hu : IsUnit (dataS selAll selAll P).Ginv) (WD : WellDefAt selIn selIn P) :
    (dataS selAll selAll P).Delta2 (dataS_laws selAll selAll P) =
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) := by
  have T := twoData_lit_loc P hS hell0 hroom selAll selAll selIn selIn (fun _ _ => Set.subset_univ _)
    (fun _ _ => Set.Subset.refl _) (fun _ _ => Set.subset_univ _) (fun _ _ => Set.Subset.refl _)
  have n2 := NG_unit_of_N1 (dataS selIn selIn P) (dataS_laws selIn selIn P) (G1invS_spec selIn selIn P) WD.2.2
  have n1 : IsUnit (((dataS selAll selAll P).Q.comp (dataS selAll selAll P).G).comp (dataS selAll selAll P).Qs) := by
    have hQ := T.hQ
    have hQs := T.hQs
    have nn : IsUnit (((dataS selAll selAll P).Q.comp (dataS selIn selIn P).G).comp (dataS selAll selAll P).Qs) := by
      rw [hQ, hQs]; exact n2
    exact unit_transfer (V0 P.G) (Z0 P.G) hu WD.1 nn T.hZV T.hM
  exact T.Delta2_eq (dataS_laws selAll selAll P) (dataS_laws selIn selIn P) hu WD.1 n1 n2

include hS hell0 hroom in
/-- **the pencil identity**: at `P` with `IsUnit Ginv_lit` and the localised data well defined, `G1inv_lit = Ginv_lit - Delta2_loc`. -/
theorem G1inv_lit_eq_pencil (hu : IsUnit (dataS selAll selAll P).Ginv) (WD : WellDefAt selIn selIn P) :
    G1invS selAll selAll P = (dataS selAll selAll P).Ginv - (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) := by
  have e1 : G1invS selAll selAll P = (dataS selAll selAll P).Ginv - (dataS selAll selAll P).Delta2 (dataS_laws selAll selAll P) :=
    (dataS selAll selAll P).G1inv_unique (G1invS_spec selAll selAll P) ((dataS selAll selAll P).isG1inv_sub (dataS_laws selAll selAll P))
  rw [e1, Delta2_lit_eq_loc P hS hell0 hroom hu WD]

include hS hell0 hroom in
/-- the guard question at `P`: with `Ginv_lit` a unit and the localised data well defined, `IsUnit G1inv_lit` is `IsUnit (Ginv_lit - Delta2_loc)`. -/
theorem isUnit_G1inv_lit_iff_pencil (hu : IsUnit (dataS selAll selAll P).Ginv) (WD : WellDefAt selIn selIn P) :
    IsUnit (G1invS selAll selAll P) ↔
      IsUnit ((dataS selAll selAll P).Ginv - (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) := by
  rw [G1inv_lit_eq_pencil P hS hell0 hroom hu WD]

end red

#print axioms Delta2_lit_eq_loc
#print axioms G1inv_lit_eq_pencil
#print axioms isUnit_G1inv_lit_iff_pencil

end AdalyFormal.D1Residual
