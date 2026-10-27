import OG8
import AC_OG7

/-!
# AC_OG8 -- `FieldsKAtAC`: OG8 `FieldsKAt` with the interface-chart conjunct replaced by `PatchCharts` (lane allc_20261016)

Identical to OG8 `FieldsKAt` except conjunct (F4): `InterfaceCharts` (down-case patches only) becomes `PatchCharts` (all patches; produced from `BallChartsAt` by
`AC_OG7.patchCharts_of_ballAC`).  No cube factor appears.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.OneGap

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK pdist)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1Site AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar)
open AdalyFormal.M2Skel (SiteS1 RowBound alpha1)

/-- the F1-F4 content of the K-shifted fields at one configuration (F4 = all patch charts) -/
def FieldsKAtAC (ell : ℕ) (hell : 0 < ell) (a : ℝ) (df M R k : ℕ) (Lu : PeriodicLatticeExtent) (K : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) : Prop :=
  AdalyFormal.M2Skel.SiteS1 ell k S U a (csOf a (AdalyFormal.M1GaugeW4.rhoT ell 12 M (alpha1 ell (K * α₀)))) ∧
  AdalyFormal.M2Skel.RowBound ell k S U a (gamC ell a (AdalyFormal.M1GaugeW4.rhoT ell 12 M (alpha1 ell (K * α₀)))
    (AdalyFormal.M1GaugeW4.epsXnum ell (R * M * ell) a (AdalyFormal.M1GaugeW4.rhoT ell 12 M (alpha1 ell (K * α₀))))) ∧
  MassComm ell M k 1 5 S U a (CMcStar ell M 1 5 a (SstarM ell 12 M (alpha1 ell (K * α₀)))) ∧
  (∀ d : ℕ, df ≤ d → d + 64 * ell ^ 2 + 2 ≤ M →
    AdalyFormal.M2Route.PatchCharts ell M k 1 5 d S U ((ell : ℝ) ^ k)⁻¹ (((12 : ℕ) : ℝ) * M * (K * α₀))) ∧
  (ExitFree ell k Lu S → Function.Injective (gparams ell k Lu hell S U a Lam).data.Qs)

end AdalyFormal.OneGap
