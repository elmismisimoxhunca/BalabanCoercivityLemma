import GCa3L

/-!
# GCa4 -- A4: the bond sector `QfullOf`, `C2fullOf` (ZXR2Sector) is gauge-equivariant

`QfullOf G U' (adBL γ A) = adFL γ G (QfullOf G U A)` and the same for `C2fullOf`, `U' = U^γ`,
every `A : BondFnL2 L`, no regularity hypothesis.  Frame of `p : BIdx G` is `γ p.2.1.1`, the base
site of the level-`j` bond `p.2.1`; this is the frame carried by the output of `QlinB` at bond
`p.2.1` (`suCoordInv_AdX`, `AdX_apply`).
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.GaugeCov

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

theorem QlinB_gauge (G : TowerGeom L) (U : Cfg L) (γ : GaugeFn L) (j : ℕ) (A : BondFnL2 L) :
    QlinB G (periodicGaugeTransform γ U) j (adBL γ A) = adBL γ (QlinB G U j A) := by
  rw [QlinB_apply, QlinB_apply, suCoord_adBL,
    QlinCompL_gauge G.ell (bgTower G U) _ γ (bgTower_gauge G U γ), suCoordInv_AdX]

theorem C2rawB_gauge (G : TowerGeom L) (U : Cfg L) (γ : GaugeFn L) (j : ℕ) (A : BondFnL2 L) :
    C2rawB G (periodicGaugeTransform γ U) j (adBL γ A) = adBL γ (C2rawB G U j A) := by
  rw [C2rawB_eq, C2rawB_eq, suCoord_adBL,
    C2CompL_gauge G.ell (bgTower G U) _ γ (bgTower_gauge G U γ), suCoordInv_AdX]

/-- **A4 (first order).** -/
theorem QfullOf_gauge (G : TowerGeom L) (U : Cfg L) (γ : GaugeFn L) (A : BondFnL2 L) :
    QfullOf G (periodicGaugeTransform γ U) (adBL γ A) = adFL γ G (QfullOf G U A) := by
  refine PiLp.ext (fun p => ?_)
  rw [adFL_apply]
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) •
        (WithLp.ofLp (QlinB G (periodicGaugeTransform γ U) p.1 (adBL γ A))) p.2.1
      = RMap (γ p.2.1.1) ((((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G U p.1 A)) p.2.1)
  rw [QlinB_gauge, map_smul]
  rfl

/-- **A4 (second order).** -/
theorem C2fullOf_gauge (G : TowerGeom L) (U : Cfg L) (γ : GaugeFn L) (A : BondFnL2 L) :
    C2fullOf G (periodicGaugeTransform γ U) (adBL γ A) = adFL γ G (C2fullOf G U A) := by
  refine PiLp.ext (fun p => ?_)
  rw [adFL_apply]
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) •
        (WithLp.ofLp (C2rawB G (periodicGaugeTransform γ U) p.1 (adBL γ A))) p.2.1
      = RMap (γ p.2.1.1) ((((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (C2rawB G U p.1 A)) p.2.1)
  rw [C2rawB_gauge, map_smul]
  rfl

#print axioms QlinB_gauge
#print axioms C2rawB_gauge
#print axioms QfullOf_gauge
#print axioms C2fullOf_gauge

end AdalyFormal.GaugeCov
