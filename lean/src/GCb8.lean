import GCb7

/-!
# GCb8 -- the unit-torus background `Ū^k|_{unit}` is gauge covariant with the restricted gauge `u = γ ∘ embY`
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2

theorem scaleUp_succ_b (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (μ : Fin 3) :
    scaleUp ell k Lu μ + 1 = (Lu μ + 1) * ell ^ k := by
  unfold scaleUp
  have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

/-- the embedded unit lattice is stable under the stride-`ell^k` coarse shift and matches the unit shift. -/
theorem coarseShift_embY (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (y : PeriodicLatticeSite Lu) (μ : Fin 3) :
    coarseShift (embY ell k Lu hell y) (ell ^ k) μ = embY ell k Lu hell (periodicLatticeShift y μ) := by
  funext ν
  apply Fin.ext
  by_cases h : ν = μ
  · subst h
    rw [coarseShift_val_eq, embY_val, embY_val]
    have e1 : ((periodicLatticeShift y ν) ν).val = ((y ν).val + 1) % (Lu ν + 1) := by
      unfold periodicLatticeShift
      rw [Function.update_self, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
    rw [e1, scaleUp_succ_b ell k Lu hell]
    have e2 : ell ^ k * ((y ν).val) + ell ^ k = ell ^ k * ((y ν).val + 1) := by ring
    rw [e2, mul_comm (Lu ν + 1), Nat.mul_mod_mul_left]
  · rw [coarseShift_apply_ne _ _ _ _ h, embY_val, embY_val]
    unfold periodicLatticeShift
    rw [Function.update_of_ne h]

theorem unitBg_gauge_b (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (γ : GaugeFn (scaleUp ell k Lu)) (Ubar : PeriodicLinkConfiguration SU2g (scaleUp ell k Lu)) :
    unitBg ell k Lu hell (AdalyFormal.Balaban.QjComposite.coarseGaugeTransform (ell ^ k) γ Ubar)
      = periodicGaugeTransform (fun y => γ (embY ell k Lu hell y)) (unitBg ell k Lu hell Ubar) := by
  funext e
  show γ (embY ell k Lu hell e.1) * Ubar (embY ell k Lu hell e.1, e.2)
      * (γ (coarseShift (embY ell k Lu hell e.1) (ell ^ k) e.2))⁻¹
    = γ (embY ell k Lu hell e.1) * Ubar (embY ell k Lu hell e.1, e.2)
      * (γ (embY ell k Lu hell (periodicLatticeShift e.1 e.2)))⁻¹
  rw [coarseShift_embY]

#print axioms coarseShift_embY
#print axioms unitBg_gauge_b

end AdalyFormal.GaugeCov
