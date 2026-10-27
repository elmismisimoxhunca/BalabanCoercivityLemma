import OG11
import OG15

/-!
# OG12 -- `target8_of_ballCharts` (lane m2_onegap_20261015)
`BallCharts` (OG1) plus `Residual` (the operator layer `OpLayer` verbatim from SK1, `Q*`-injectivity when a level-0 row ball leaves `Ω_0`, the headline on thin tori)
give the frozen r8 headline `P428Target8`.
-/
set_option autoImplicit false
namespace AdalyFormal.OneGap

theorem target8_of_ballCharts (hB : BallCharts) (R2 : Residual) : AdalyFormal.StatementLaneG.P428Target8 :=
  fun ell hell a ha =>
    AdalyFormal.M2Skel.class_coreK (fun ell hell a ha => fieldsK_of_ball hB hell a ha) R2 hell ha

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.target8_of_ballCharts
