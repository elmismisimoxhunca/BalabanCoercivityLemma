import NtCvO28

/-!
# CvO29 -- `Ad_h`-equivariance of the genuine ingredient family at a Cartan `U`; sigma_3-valued = `Ad_h`-fixed (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverNested (cartan)
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.GaugeCov
open AdalyFormal.IngredientFamilyR2

theorem bondEqv_hGauge (P : IngrBParams) (hU : CartanCfg P.U) :
    BondEqv (hGauge P.Lf) P.G P.U P.U P.a P.sector P.sector P.Jf P.Jf where
  W x := by
    have := Wop_gauge P.G (hGauge P.Lf) P.U P.a x
    rwa [gaugeTransform_hGauge hU] at this
  D x := by
    have := Delta_gauge P.G (hGauge P.Lf) P.U x
    rwa [gaugeTransform_hGauge hU] at this
  T x := by
    have := Tfull_gauge P.G (hGauge P.Lf) P.U x
    rwa [gaugeTransform_hGauge hU] at this
  Q x := by
    have := QfullOf_gauge P.G P.U (hGauge P.Lf) x
    rwa [gaugeTransform_hGauge hU] at this
  C x := by
    have := C2fullOf_gauge P.G P.U (hGauge P.Lf) x
    rwa [gaugeTransform_hGauge hU] at this
  J := by
    have := Jf_gauge P (hGauge P.Lf)
    rw [gaugeTransform_hGauge hU] at this
    exact this

theorem baseEqv_hGauge (P : IngrBParams) (hU : CartanCfg P.U) :
    BaseEqv (adEL (hGauge P.Lf) P.G) (adSL (hGauge P.Lf)) (adFL (hGauge P.Lf) P.G) P.data P.data :=
  (bondEqv_hGauge P hU).baseEqv

#print axioms bondEqv_hGauge
#print axioms baseEqv_hGauge

end AdalyFormal.CoverOmega
