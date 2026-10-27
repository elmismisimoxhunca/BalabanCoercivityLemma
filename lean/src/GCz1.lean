import GCb9
import GCa4
import GCa6
import GCg4

/-!
# GCz1 -- the plugged theorem: `genForm` of the genuine family is gauge INVARIANT, unconditionally.
For `P : IngrBParams` (tower `S`, background `U`, mass `a`, region `Λ`), any fine gauge `γ` (ALL sites of the fine torus; no condition on the cube boundary),
`P' = {P with U := U^γ}`, `u = γ ∘ embY` (unit-torus gauge): `genForm P' (Ad_u B) = genForm P B`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply gaugeInv)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.StatementLane (scaleUp Tower)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

/-- the gauge-transformed parameter point. -/
@[reducible] def gaugeP (P : IngrBParams) (γ : GaugeFn P.Lf) : IngrBParams :=
  { P with U := periodicGaugeTransform γ P.U }

theorem Q1_gauge_pt (P : IngrBParams) (γ : GaugeFn P.Lf) (B : Bond P.Lu → SuTwo) (c : CoarseBond P.Lu P.ell) :
    (gaugeP P γ).Q1 (gaugeActA (uOf P.ell P.k P.Lu P.hell γ) B) c
      = RMap (uOf P.ell P.k P.Lu P.hell γ c.1.1) (P.Q1 B c) :=
  congrFun (Q1_gauge P γ B) c

theorem C2tilde_gauge_pt (P : IngrBParams) (γ : GaugeFn P.Lf) (B : Bond P.Lu → SuTwo) (c : CoarseBond P.Lu P.ell) :
    C2tilde P.ell (gaugeP P γ).unitBgU (gaugeActA (uOf P.ell P.k P.Lu P.hell γ) B) c
      = RMap (uOf P.ell P.k P.Lu P.hell γ c.1.1) (C2tilde P.ell P.unitBgU B c) :=
  congrFun (C2tildeU_gauge P γ B) c

theorem bondEqv_gauge (P : IngrBParams) (γ : GaugeFn P.Lf) :
    BondEqv γ P.G P.U (periodicGaugeTransform γ P.U) P.a P.sector (gaugeP P γ).sector P.Jf (gaugeP P γ).Jf where
  W x := Wop_gauge P.G γ P.U P.a x
  D x := Delta_gauge P.G γ P.U x
  T x := Tfull_gauge P.G γ P.U x
  Q x := QfullOf_gauge P.G P.U γ x
  C x := C2fullOf_gauge P.G P.U γ x
  J := Jf_gauge P γ

/-- **MAIN: `genForm` is gauge invariant.** -/
theorem genForm_gauge_main (P : IngrBParams) (γ : GaugeFn P.Lf) (B : BondFnL2 P.Lu) :
    GenP.genForm (gaugeP P γ) (adBL (uOf P.ell P.k P.Lu P.hell γ) B) = GenP.genForm P B :=
  genForm_gauge P γ (bondEqv_gauge P γ) (fun B c => Q1_gauge_pt P γ B c) (fun B c => C2tilde_gauge_pt P γ B c) B

#print axioms bondEqv_gauge
#print axioms genForm_gauge_main

end AdalyFormal.GaugeCov
