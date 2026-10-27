import GCa5
import ZXR2Wire2

/-!
# GCa6 -- bridge to the Wire2 usage `Q1 := Q1jet ell unitBgU`

* `embY_coarseShift` : the stride-`ell^k` fine shift of an embedded unit site is the embedding of
  the unit shift;
* `unitBg_gauge`     : `unitBg (coarseGaugeTransform (ell^k) γ V) = periodicGaugeTransform (γ ∘ embY) (unitBg V)`;
* `unitBgU_gauge`, `Q1_gauge`, `C2tildeU_gauge` : for `IngrBParams P`, gauging the fine `U` by `γ`
  gauges the unit background by `γ ∘ embY`, and `Q1`, `C̃⁽²⁾` are equivariant with that unit gauge.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.GaugeCov

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (coarseGaugeTransform)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2

theorem scaleUp_succ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (μ : Fin 3) :
    scaleUp ell k Lu μ + 1 = (Lu μ + 1) * ell ^ k := by
  unfold scaleUp
  have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

theorem embY_coarseShift (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (y : PeriodicLatticeSite Lu) (μ : Fin 3) :
    coarseShift (embY ell k Lu hell y) (ell ^ k) μ = embY ell k Lu hell (periodicLatticeShift y μ) := by
  funext ν
  apply Fin.ext
  by_cases h : ν = μ
  · subst h
    rw [coarseShift_val_eq, embY_val, embY_val, scaleUp_succ ell k Lu hell]
    have hy : ((periodicLatticeShift y ν) ν).val = ((y ν).val + 1) % (Lu ν + 1) := by
      simp only [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one']
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [hy, show ell ^ k * (y ν).val + ell ^ k = ell ^ k * ((y ν).val + 1) by ring,
      mul_comm (Lu ν + 1) (ell ^ k), Nat.mul_mod_mul_left]
  · rw [coarseShift_apply_ne _ _ _ _ h, embY_val, embY_val]
    simp [periodicLatticeShift, Function.update_of_ne h]

theorem unitBg_gauge (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (γ : GaugeFn (scaleUp ell k Lu)) (V : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)) :
    unitBg ell k Lu hell (coarseGaugeTransform (ell ^ k) γ V)
      = periodicGaugeTransform (fun y => γ (embY ell k Lu hell y)) (unitBg ell k Lu hell V) := by
  funext e
  simp only [unitBg, coarseGaugeTransform, periodicGaugeTransform]
  rw [embY_coarseShift]

theorem unitBgU_gauge (P : IngrBParams) (γ : GaugeFn P.Lf) :
    unitBg P.ell P.k P.Lu P.hell (bgTower P.G (periodicGaugeTransform γ P.U) P.k)
      = periodicGaugeTransform (fun y => γ (embY P.ell P.k P.Lu P.hell y)) P.unitBgU := by
  rw [bgTower_gauge]
  exact unitBg_gauge P.ell P.k P.Lu P.hell γ _

/-- `Q₁` of the gauged parameters, with the induced unit gauge `γ ∘ embY`. -/
theorem Q1_gauge (P : IngrBParams) (γ : GaugeFn P.Lf) (B : Bond P.Lu → SuTwo) :
    Q1jet P.ell (unitBg P.ell P.k P.Lu P.hell (bgTower P.G (periodicGaugeTransform γ P.U) P.k))
        (gaugeActA (fun y => γ (embY P.ell P.k P.Lu P.hell y)) B)
      = adC (fun y => γ (embY P.ell P.k P.Lu P.hell y)) P.ell (P.Q1 B) := by
  rw [unitBgU_gauge]
  exact Q1jet_gauge P.ell _ P.unitBgU B

theorem C2tildeU_gauge (P : IngrBParams) (γ : GaugeFn P.Lf) (B : Bond P.Lu → SuTwo) :
    C2tilde P.ell (unitBg P.ell P.k P.Lu P.hell (bgTower P.G (periodicGaugeTransform γ P.U) P.k))
        (gaugeActA (fun y => γ (embY P.ell P.k P.Lu P.hell y)) B)
      = adC (fun y => γ (embY P.ell P.k P.Lu P.hell y)) P.ell (C2tilde P.ell P.unitBgU B) := by
  rw [unitBgU_gauge]
  exact C2tilde_gauge P.ell _ P.unitBgU B

#print axioms embY_coarseShift
#print axioms unitBg_gauge
#print axioms unitBgU_gauge
#print axioms Q1_gauge
#print axioms C2tildeU_gauge

end AdalyFormal.GaugeCov
