import HB1
import W4N5

/-!
# HB2 -- `wellDef_M1_final_hb` (lane m1_hb_20261014)

`W4N5.wellDef_M1_final` with the named input `hb` DISCHARGED by `HB1.hb_M1'`.  Added hypotheses (both are hypotheses of the frozen headline's
`CoercG8At`): `TorusOK ell M Lu`, `LambdaOK2 ell M R k S Lam`.  The threshold is `aS' = min aS (beta0 ell)` (depends on `ell` and `a` only).
Remaining named input: `hD2` (with `ε₂' < cwW4`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1HB

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.M1GaugeW4
open AdalyFormal.M1W4Num
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar delStar rho1_nonneg)
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLaneG (gparams GenP.WellDef LambdaOK2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.M1NonFlat (epsNF PkA thetaN)
open AdalyFormal.M1DK (beta0 beta0_pos)

/-- **W5 at `U ∈ M1Regular` with `hb` discharged** (`W = R·M·ell`).  Remaining named input: `hD2` with `ε₂' < cwW4`. -/
theorem wellDef_M1_final_hb {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ D : ℕ, 12 * ell + 10 ≤ D ∧
    (∀ d, D ≤ d → epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2) ∧
    ∃ Wmin : ℕ, 1 ≤ Wmin ∧ ∃ ε1 : ℝ, 0 < ε1 ∧ ∃ aS : ℝ, 0 < aS ∧
    ∀ {M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
      {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hR1 : 1 ≤ R)
      (hR4 : (c + 4) * κ * ell ≤ R) (hc : 5 ≤ c) (hroom : 17 * ell ≤ R * M) {d : ℕ} (hdD : D ≤ d)
      (hdM : d + 64 * ell ^ 2 ≤ κ * M) (hRW : Wmin ≤ R) (hLu5 : ∀ μ, 5 ≤ Lu μ + 1)
      (hT : TorusOK ell M Lu)
      (U : LinkCfg (scaleUp ell k Lu)) {α₀ : ℝ}
      (hreg : AdalyFormal.M1.M1Regular ell M 12 k S α₀ (((ell : ℝ) ^ k)⁻¹) U) (hα0 : 0 < α₀)
      (hsmall : (12 : ℝ) * M * α₀ ≤ aS)
      (Lam : Set (PeriodicLatticeSite Lu)) (hL : LambdaOK2 ell M R k S Lam) (ε2 : ℝ) (hε2 : 0 < ε2) (ε2' : ℝ)
      (hlt : ε2' < cwW4 ell M κ c (R * M * ell) a (rhoT ell 12 M α₀) (rho1 12 M α₀) ε1 ε2
          (cPnf ell (R * M * ell) d a cW α₀ ε1 12 M)
          (epsXnum ell (R * M * ell) a (rhoT ell 12 M α₀)) (CMcStar ell M κ c a (SstarM ell 12 M α₀)))
      (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G),
        |⟪A, (gparams ell k Lu hell0 S U a Lam).data.Delta2 (gparams ell k Lu hell0 S U a Lam).data_laws A⟫|
          ≤ ε2' * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))),
      GenP.WellDef (gparams ell k Lu hell0 S U a Lam) := by
  obtain ⟨cW, hcW, a₀, ha₀, D, hD, hall, Wmin, hW, ε1, hε1, aS, haS, H⟩ := wellDef_M1_final hell ha
  refine ⟨cW, hcW, a₀, ha₀, D, hD, hall, Wmin, hW, ε1, hε1, min aS (beta0 ell),
    lt_min haS (beta0_pos ell (by omega)), ?_⟩
  intro M R k κ c Lu hell0 S hS hκ hM hR1 hR4 hc hroom d hdD hdM hRW hLu5 hT U α₀ hreg hα0 hsmall Lam hL ε2 hε2 ε2' hlt hD2
  exact H hell0 hS hκ hM hR1 hR4 hc hroom hdD hdM hRW hLu5 U hreg hα0 (hsmall.trans (min_le_left _ _)) Lam ε2 hε2 ε2' hlt hD2
    (hb_M1' ell M R k Lu hell0 S U a Lam α₀ hS hell hroom hT hL hreg hα0.le (hsmall.trans (min_le_right _ _)))

end AdalyFormal.M1HB

#print axioms AdalyFormal.M1HB.wellDef_M1_final_hb
