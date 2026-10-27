import UW12
import CG5
import CG7

/-!
# UW13 -- **`BallChartsGU` and `ZT5A.P428Target8Unif`, unconditional** (lane unif_20261016)

The two COVER_GEOM interface statements are discharged by the cover_geom lane's theorems
`AdalyFormal.CoverGeom.coverGeomU` (`CG5`) and `AdalyFormal.CoverGeom.coverGeomBoxU` (`CG7`, `R₁ = 24ℓ + 25`).
-/
set_option autoImplicit false

namespace AdalyFormal.UnifLane.Z

open AdalyFormal.StatementLaneG (P428Target8Unif)
open AdalyFormal.UnifLane (BallChartsGU)

/-- **the residual `BallChartsGU`, proved.** -/
theorem ballChartsGU_proved : BallChartsGU :=
  ballChartsGU_of_cover AdalyFormal.CoverGeom.coverGeomU AdalyFormal.CoverGeom.coverGeomBoxU

/-- **`ZT5A.P428Target8Unif` (a₀, γ₀ uniform in `M` and `R`), proved.** -/
theorem p428Target8Unif_proved : P428Target8Unif :=
  unif_of_cover AdalyFormal.CoverGeom.coverGeomU AdalyFormal.CoverGeom.coverGeomBoxU

end AdalyFormal.UnifLane.Z
