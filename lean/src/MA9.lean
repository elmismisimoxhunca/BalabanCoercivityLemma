import MA8
import GCz3
import GW1

/-!
# MA9 -- gauge transfer of the stratified D-layer `hJ` clause (lane m1_assembly_20261014)
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.M1Assembly

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower scaleUp OnLambdaTildeIn)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneG (gparams GenP.genC)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply gaugeInv)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

theorem gaugeAct_cancel {L : PeriodicLatticeExtent} (γ : GaugeFn L) (A : Bond L → SuTwo) :
    gaugeActA γ (gaugeActA (gaugeInv γ) A) = A := by
  funext b
  simp only [gaugeActA_apply, gaugeInv]
  exact AdalyFormal.Balaban.CovariantHjMinimizer.RMap_apply_inv_cancel (γ b.1) (A b)

/-- `hJ` at `U` gives `hJ` at `U^gamma`. -/
theorem hJ_gauge {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (γ : GaugeFn (scaleUp ell k Lu)) (εJ : ℝ)
    (hJ : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      |⟪(gparams ell k Lu hell S U a Lam).H1in ((gparams ell k Lu hell S U a Lam).D2in
          (WithLp.toLp 2 (Cop Lam (gparams ell k Lu hell S U a Lam).Q1 Bt))), (gparams ell k Lu hell S U a Lam).Jf⟫|
        ≤ εJ * ‖(WithLp.toLp 2 (Cop Lam (gparams ell k Lu hell S U a Lam).Q1 Bt) : BondFnL2 Lu)‖ ^ 2) :
    ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      |⟪(gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).H1in
          ((gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).D2in
            (WithLp.toLp 2 (Cop Lam (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).Q1 Bt))),
          (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).Jf⟫|
        ≤ εJ * ‖(WithLp.toLp 2 (Cop Lam (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).Q1 Bt) : BondFnL2 Lu)‖ ^ 2 := by
  intro Bt' h1 h2
  set P := gparams ell k Lu hell S U a Lam with hP
  set u := uOf ell k Lu hell γ with hu
  set Bt := gaugeActA (gaugeInv u) Bt' with hBt
  have hBt1 : OnLambdaTildeIn Lam ell Bt := (onLambdaTildeIn_gauge (gaugeInv u) Lam ell Bt').mpr h1
  have hBt2 : OnLambdaT Lam Bt := (onLambdaT_gauge (gaugeInv u) Lam Bt').mpr h2
  have hcancel : gaugeActA u Bt = Bt' := gaugeAct_cancel u Bt'
  have H := hJ Bt hBt1 hBt2
  have hhyp := genFormHyps_gauge P γ
  have hC := genC_gauge P γ Bt
  rw [hcancel] at hC
  -- hC : genC (gaugeP P γ) Bt' = gaugeActA u (genC P Bt)
  have hC' : Cop Lam (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).Q1 Bt'
      = gaugeActA u (Cop Lam P.Q1 Bt) := hC
  have hto : (WithLp.toLp 2 (gaugeActA u (Cop Lam P.Q1 Bt)) : BondFnL2 Lu)
      = adBL u (WithLp.toLp 2 (Cop Lam P.Q1 Bt)) := rfl
  rw [hC', hto]
  have hd2 := hhyp.D2 (WithLp.toLp 2 (Cop Lam P.Q1 Bt))
  have hh1 := hhyp.H1in (P.D2in (WithLp.toLp 2 (Cop Lam P.Q1 Bt)))
  have hj := hhyp.base.J
  show |⟪({ P with U := periodicGaugeTransform γ P.U } : IngrBParams).H1in
        (({ P with U := periodicGaugeTransform γ P.U } : IngrBParams).D2in (adBL u (WithLp.toLp 2 (Cop Lam P.Q1 Bt)))),
        ({ P with U := periodicGaugeTransform γ P.U } : IngrBParams).Jf⟫| ≤ _
  rw [hd2, hh1, hj, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map]
  exact H

end AdalyFormal.M1Assembly

#print axioms AdalyFormal.M1Assembly.hJ_gauge
