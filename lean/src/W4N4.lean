import W4N3
import MI33

/-!
# W4N4 -- `wellDef_M1_final`, `hb_M1_of_small` (lane m1_w4num_20261014)

`wellDef_M1_final`: `GW9.wellDef_M1_patched` with `W4Num`, `QsNum` and the linear smallness hypotheses discharged by one threshold
`12 M α₀ ≤ aS`.  Remaining named inputs: `hD2` (with `ε₂' < cwW4`) and `hb`.

`hb_M1_of_small`: `hb` at `U` from `hb_of_small` at `U^g` for ANY gauge `g` whose level-`k` unit background is `e0`-small.
(`M1Regular` is NOT used: `GW4.ramp_not_hV` shows that the unit background of the `M1Regular` witness `(1, χσ₃)` of the ramp has a link `-1`.)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1W4Num

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.M1GaugeW4
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar delStar rho1_nonneg)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams GenP.WellDef)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.NonflatJet (r0)
open AdalyFormal.M1 (M1Bounds)
open AdalyFormal.M1NonFlat (epsNF PkA thetaN)

/-- **`hb` at `U` from per-link smallness of the level-`k` unit background of `U^g`, for any gauge `g`** (gauge invariance of `hb`
+ `hb_of_small`).  The hypotheses `hle`, `hr` are `k`-free numeric conditions on `e0`. -/
theorem hb_M1_of_small {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (g : PeriodicLatticeSite (scaleUp ell k Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hd : ∀ μ, ell ∣ Lu μ + 1) (e0 : ℝ) (he0 : 0 ≤ e0) (hle : e0 ≤ 1 / (1000 * (ell : ℝ) ^ 4))
    (hr : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * e0) < r0)
    (hV : ∀ e, frobNorm (((gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam).unitBgU e : M2) - 1) ≤ e0) :
    Function.Bijective (H0 (gparams ell k Lu hell0 S U a Lam).Lam (gparams ell k Lu hell0 S U a Lam).Q1) :=
  (hb_gauge_iff hell0 S a Lam U g).1
    (AdalyFormal.M0Finish.R7.hb_of_small (gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam) hd e0 he0 hle hr hV)

end AdalyFormal.M1W4Num

#print axioms AdalyFormal.M1W4Num.hb_M1_of_small
