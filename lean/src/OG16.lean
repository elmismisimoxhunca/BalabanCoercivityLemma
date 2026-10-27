import OG12
import BallCharts

/-!
# OG16 -- `target8_of_ballChartsG` (lane m2_onegap_20261015)
The GChart form `BallChartsG` of the residual statement, plus `Residual`, gives the frozen r8 headline.
-/
set_option autoImplicit false
namespace AdalyFormal.OneGap

theorem target8_of_ballChartsG (hG : BallChartsG) (R2 : Residual) : AdalyFormal.StatementLaneG.P428Target8 :=
  target8_of_ballCharts (ballCharts_of_G hG) R2

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.target8_of_ballChartsG
