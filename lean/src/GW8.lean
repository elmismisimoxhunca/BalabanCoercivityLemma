import GW7

/-!
# GW8 -- W4 and W5 at `U` from the `M1Regular` hypothesis itself (M1 gauge lane, 2026-10-14)
`w4_of_M1Regular` / `wellDef_of_M1Regular` : the `M1Regular` existential `(g, A)` is destructed and `GW5.w4_M1`, `GW7.wellDef_M1` applied.
Retained inputs: `PatchCoercive`, `hD2` (`ε₂' < cwW4`), `hb`, structural sizes, and the `k`-free numerics `W4Num`, `QsNum`.
No `RegTower`/`TowerClass`/`hV`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1GaugeW4

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar delStar massComm_M1 qs_injective_M1 rho1_nonneg)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams GenP.WellDef)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.M1 (M1Bounds)

section main
variable {ell M R k f κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c) {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
  (hroom : 17 * ell ≤ R * M) (hLu5 : ∀ μ, 5 ≤ Lu μ + 1)
  (U : LinkCfg (scaleUp ell k Lu)) {α₀ η : ℝ}
  (hreg : AdalyFormal.M1.M1Regular ell M f k S α₀ η U) (hη : 0 < η) (hα0 : 0 ≤ α₀)
  (ha1 : (f : ℝ) * M * α₀ ≤ 1)
  (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 f M α₀ ≤ 1)
  (hsmA : (1 + 3 * Real.pi) * rho1 f M α₀ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
  (hrr : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 f M α₀))
      < AdalyFormal.NonflatJet.r0)
include hell0 hS hκ hM hell hR1 hR hc hW hWR hroom hLu5 hreg hη hα0 ha1 hsm4 hsmA hrr

/-- **W4 at `U` from `M1Regular ell M f k S α₀ η U`** (the existential witness `(g, A)` is destructed). -/
theorem w4_of_M1Regular (a : ℝ) (ha : 0 < a) (Lam : Set (PeriodicLatticeSite Lu))
    (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2) (hN : W4Num ell M f W a α₀ ε1)
    (cP : ℝ) (hP : PatchCoercive ell M k κ c Lu hell0 S U a Lam cP)
    (A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G)) :
    cwW4 ell M κ c W a (rhoT ell f M α₀) (rho1 f M α₀) ε1 ε2 cP (epsXnum ell W a (rhoT ell f M α₀))
        (CMcStar ell M κ c a (SstarM ell f M α₀))
      * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ := by
  obtain ⟨g, A0, hUg, hB⟩ := hreg
  exact w4_M1 hell0 hS hκ hM hell hR1 hR hc hW hWR hroom hLu5 U g A0 hUg hB hη hα0 ha1 hsm4 hsmA hrr a ha Lam ε1 ε2
    hε1 hε2 hN cP hP A

/-- **W5 at `U` from `M1Regular ell M f k S α₀ η U`**. -/
theorem wellDef_of_M1Regular (a : ℝ) (ha : 0 < a) (Lam : Set (PeriodicLatticeSite Lu))
    (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2) (hN : W4Num ell M f W a α₀ ε1) (hQN : QsNum ell f M α₀)
    (cP : ℝ) (hP : PatchCoercive ell M k κ c Lu hell0 S U a Lam cP)
    (ε2' : ℝ)
    (hlt : ε2' < cwW4 ell M κ c W a (rhoT ell f M α₀) (rho1 f M α₀) ε1 ε2 cP (epsXnum ell W a (rhoT ell f M α₀))
        (CMcStar ell M κ c a (SstarM ell f M α₀)))
    (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G),
      |⟪A, (gparams ell k Lu hell0 S U a Lam).data.Delta2 (gparams ell k Lu hell0 S U a Lam).data_laws A⟫|
        ≤ ε2' * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
    (hb : Function.Bijective (H0 (gparams ell k Lu hell0 S U a Lam).Lam (gparams ell k Lu hell0 S U a Lam).Q1)) :
    GenP.WellDef (gparams ell k Lu hell0 S U a Lam) := by
  obtain ⟨g, A0, hUg, hB⟩ := hreg
  exact wellDef_M1 hell0 hS hκ hM hell hR1 hR hc hW hWR hroom hLu5 U g A0 hUg hB hη hα0 ha1 hsm4 hsmA hrr a ha Lam ε1 ε2
    hε1 hε2 hN hQN cP hP ε2' hlt hD2 hb

end main

end AdalyFormal.M1GaugeW4

#print axioms AdalyFormal.M1GaugeW4.w4_of_M1Regular
#print axioms AdalyFormal.M1GaugeW4.wellDef_of_M1Regular
