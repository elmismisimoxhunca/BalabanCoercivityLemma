import DrRed1
import DrBracket

/-!
# DrMargin -- where the guard residual is automatic: a coercivity margin of `Ginv_lit` over `‖Delta2_loc‖`.

If `Ginv_lit` is coercive with constant `c` and the localised correction has operator norm `ε < c` (and the localised data are well defined), then `G1inv_lit` is a unit.
Contrapositive: at a configuration with `IsUnit Ginv_lit` and `not IsUnit G1inv_lit`, every coercivity constant `c` of `Ginv_lit` (if it has one) satisfies `c ≤ ‖Delta2_loc‖`:
the residual can only fail inside the window where `Ginv_lit` is within `‖Delta2_loc‖` of singular.
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

section margin
variable (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell0 : 0 < P.ell) (hroom : 17 * P.ell ≤ R * M)

include hS hell0 hroom in
/-- a coercivity margin of `Ginv_lit` over `‖Delta2_loc‖` makes `G1inv_lit` a unit. -/
theorem G1inv_lit_isUnit_of_margin {c ε : ℝ} (hc : 0 < c)
    (hco : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, (dataS selAll selAll P).Ginv x⟫)
    (hε : ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ ≤ ε) (hεc : ε < c)
    (WD : WellDefAt selIn selIn P) : IsUnit (G1invS selAll selAll P) := by
  have hu : IsUnit (dataS selAll selAll P).Ginv := isUnit_of_coercive _ hc hco
  rw [G1inv_lit_eq_pencil P hS hell0 hroom hu WD]
  refine isUnit_of_coercive _ (sub_pos.mpr hεc) (fun x => ?_)
  have h1 := hco x
  have h2 : ⟪x, (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x⟫ ≤ ε * ‖x‖ ^ 2 := by
    calc ⟪x, (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x⟫
        ≤ ‖x‖ * ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * ‖x‖) := by
          gcongr; exact (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ ‖x‖ * (ε * ‖x‖) := by gcongr
      _ = ε * ‖x‖ ^ 2 := by ring
  simp only [ContinuousLinearMap.sub_apply, inner_sub_right]
  nlinarith

include hS hell0 hroom in
/-- **window**: if `G1inv_lit` is not a unit (localised data well defined), no coercivity constant of `Ginv_lit` exceeds `‖Delta2_loc‖`
(a coercive `Ginv_lit` is automatically a unit). -/
theorem coercivity_le_Delta2_of_gap (WD : WellDefAt selIn selIn P)
    (hn : ¬ IsUnit (G1invS selAll selAll P)) {c : ℝ} (hc : 0 < c)
    (hco : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, (dataS selAll selAll P).Ginv x⟫) :
    c ≤ ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ := by
  by_contra h
  push Not at h
  exact hn (G1inv_lit_isUnit_of_margin P hS hell0 hroom hc hco le_rfl h WD)

end margin

#print axioms G1inv_lit_isUnit_of_margin
#print axioms coercivity_le_Delta2_of_gap

end AdalyFormal.D1Residual
