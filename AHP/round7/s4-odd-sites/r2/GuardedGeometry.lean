import SoA3
import SoPar

/-!
# Round 7 S-4: the genuine odd-scale sites-only cell

The local body below is copied verbatim from CaT2d, with only the namespace
changed. `body_eq_frozen` checks the identity. All goals retain WellDefG as
an antecedent, NOT as a conclusion and NOT merely the Ginv guard.
Goal2 is pointwise failure at every odd scale, stronger than `¬ Goal1`.
Goal4 is pointwise failure at ell = 13, stronger than `¬ Goal3`.
These are targets, not asserted theorems.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.Round7.S4OddSites

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.CoverStrong (InstIneqWDH)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open MXQ.AllC
open NcwdhFam

/-- Verbatim body from frozen CaT2d.lean. -/
def FamilyTorusSitesConstAt (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            CovSitesF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S ∧
              PerCubeRegularF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneqWDH ell k (by omega) a Lu γ₀ S Lam U

theorem body_eq_frozen (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) :
    FamilyTorusSitesConstAt c ell hell a =
      CovAssume.FamilyTorusSitesConstAt c ell hell a := rfl

/-- Positive, every odd ell >= 3, every factor c >= 10, every a > 0. -/
def Goal1 : Prop :=
  ∀ (c ell : ℕ), 10 ≤ c → (hell : 3 ≤ ell) → ell % 2 = 1 →
    ∀ (a : ℝ), 0 < a → FamilyTorusSitesConstAt c ell (by omega) a

/-- Negative at each parameter triple; not just the negation of Goal1. -/
def Goal2 : Prop :=
  ∀ (c ell : ℕ), 10 ≤ c → (hell : 3 ≤ ell) → ell % 2 = 1 →
    ∀ (a : ℝ), 0 < a → ¬ FamilyTorusSitesConstAt c ell (by omega) a

/-- Fixed odd scale in the recorded CMP109 range, still every c >= 10, a > 0. -/
def Goal3 : Prop :=
  ∀ (c : ℕ), 10 ≤ c → ∀ (a : ℝ), 0 < a →
    FamilyTorusSitesConstAt c 13 (by norm_num) a

/-- Negative counterpart at ell = 13; no divisibility or width restriction. -/
def Goal4 : Prop :=
  ∀ (c : ℕ), 10 ≤ c → ∀ (a : ℝ), 0 < a →
    ¬ FamilyTorusSitesConstAt c 13 (by norm_num) a

theorem goal1_implies_goal3 : Goal1 → Goal3 := by
  intro h c hc a ha
  exact h c 13 hc (by norm_num) (by norm_num) a ha

theorem goal2_implies_goal4 : Goal2 → Goal4 := by
  intro h c hc a ha
  exact h c 13 hc (by norm_num) (by norm_num) a ha

theorem goal3_goal4_incompatible : Goal3 → Goal4 → False := by
  intro hp hn
  exact hn 10 (by norm_num) 1 (by norm_num) (hp 10 (by norm_num) 1 (by norm_num))

theorem goal1_goal2_incompatible : Goal1 → Goal2 → False := by
  intro hp hn
  exact goal3_goal4_incompatible (goal1_implies_goal3 hp) (goal2_implies_goal4 hn)

#check Goal1
#check Goal2
#check Goal3
#check Goal4
#check CovAssume.FamilyTorusSitesConstAt
#check NcwdhFam.CovSitesF
#check NcwdhFam.PerCubeRegularF
#check AdalyFormal.CoverStrong.InstIneqWDH
#check AdalyFormal.SitesOnly.main_neg_S
#check AdalyFormal.SitesOnly.sites_not_imp_plaq_S
#check AdalyFormal.SitesOnly.no_uniform_step_blockzero_odd
#print axioms FamilyTorusSitesConstAt
#print axioms body_eq_frozen
#print axioms Goal1
#print axioms Goal2
#print axioms Goal3
#print axioms Goal4
#print axioms goal1_implies_goal3
#print axioms goal2_implies_goal4
#print axioms goal3_goal4_incompatible
#print axioms goal1_goal2_incompatible

end AdalyFormal.Round7.S4OddSites

namespace AdalyFormal.Round7.S4OddSites.R2Geometry

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SitesOnly
open AdalyFormal.NcwdhTwo
open AdalyFormal.NoCover (perCube_one)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open MXQ.AllC
open NcwdhFam

/-- Frozen flat-member inverse argument, specialized directly to flatCfg. -/
theorem flat_wellDefG [CfData] {ell M R : ℕ} (hell : 2 ≤ ell)
    (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) {a : ℝ} (ha : 0 < a) :
    GenP.WellDefG (gparams ell 2 (neLu M R) (by omega) (neS ell M R)
      flatCfg a (neLam M R)) := by
  let P := gparams ell 2 (neLu M R) (by omega) (neS ell M R)
    flatCfg a (neLam M R)
  have hunitBg : P.unitBgU = flatCfg := by
    unfold IngrBParams.unitBgU
    rw [show bgTower P.G P.U P.k = flatCfg by exact Ubar_flat ell 2]
    rfl
  have hH : Function.Bijective (H0 P.Lam P.Q1) := by
    unfold IngrBParams.Q1
    rw [hunitBg]
    exact H0_flat_bijective (by omega) (unit_hdiv hdvd hM) (neLam M R)
  have hu : UnitsFour P := by
    have hz : (flatCfg : LinkCfg (scaleUp ell 2 (neLu M R))) = stag0Cfg 0 0 := by
      rw [stag0Cfg_zero]
      rfl
    dsimp [P]
    rw [hz]
    exact SitesOnly.unitsFour_flat_two hell hdvd hM hR a ha
  have hd : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)) :=
    delpA_unit (geomOf ell 2 (neS ell M R)) flatCfg ha hell
      (out_nested_two hell hM hR)
  exact ⟨⟨hH, hu.1, hu.2.1⟩, hd, hu.2.2.1, hu.2.2.2⟩

/-- Same proposed shortcut as round 1; no coercivity conclusion is encoded. -/
def EventualGuardedCoverageUpgrade (ell c : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=
  ∃ m₁ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R →
      ∀ k : ℕ, 1 ≤ k → ∀ Lu : PeriodicLatticeExtent,
        TorusOK ell (ell ^ m) Lu →
        ∀ S : Tower (scaleUp ell k Lu), Admissible ell (ell ^ m) R k S →
        ∀ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 ell (ell ^ m) R k S Lam →
        ∀ α₀ : ℝ, 0 < α₀ → (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
        ∀ U : LinkCfg (scaleUp ell k Lu),
          CovSitesF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S →
          PerCubeRegularF ell (ell ^ m) (constFam c (scaleUp ell k Lu))
            k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
          GenP.WellDefG (gparams ell k Lu (by omega) S U a Lam) →
          CovPlaqF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S

/-- Large thresholds, positive smallness and all inverse guards do not recover
plaquette coverage from sites. The witness is flat, so this is NOT a refutation
of the quadratic inequality. No parity premise is needed. -/
theorem no_eventual_guarded_coverage_upgrade (ell : ℕ) (hell : 3 ≤ ell)
    (a : ℝ) (ha : 0 < a) :
    ¬ EventualGuardedCoverageUpgrade ell (9 * ell + 1) (by omega) a := by
  rintro ⟨m₁, R₁, a₀, ha₀, h⟩
  letI : CfData := ⟨19, by norm_num⟩
  let m := max m₁ 1
  let R := max R₁ (9 * ell + 1)
  have hm : m₁ ≤ m := le_max_left _ _
  have hm1 : 1 ≤ m := le_max_right _ _
  have hRR : R₁ ≤ R := le_max_left _ _
  have hRc : 9 * ell + 1 ≤ R := le_max_right _ _
  have hR : 1 ≤ R := by omega
  have hell2 : 2 ≤ ell := by omega
  have hell0 : 0 < ell := by omega
  have hM : 0 < ell ^ m := pow_pos hell0 _
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega)
  have hc : 10 ≤ 9 * ell + 1 := by omega
  have hrel : SoRel ell (9 * ell + 1) := by
    change ell * (19 - 1) = 2 * ((9 * ell + 1) - 1)
    simp only [Nat.add_sub_cancel, show (19 : ℕ) - 1 = 18 by norm_num]
    ring
  obtain ⟨hcs, hnp⟩ := sites_not_imp_plaq_S hell2 hM hR hrel hc hRc
  have hcR : (0 : ℝ) < ((9 * ell + 1 : ℕ) : ℝ) := by positivity
  have hMR : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by exact_mod_cast hM
  let α₀ := a₀ / (((9 * ell + 1 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ))
  have hα : 0 < α₀ := by positivity
  have hcap : ((9 * ell + 1 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by
    dsimp [α₀]
    rw [mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]
  have hη : (0 : ℝ) < ((ell : ℝ) ^ 2)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  have hreg : PerCubeRegularF ell (ell ^ m)
      (constFam (9 * ell + 1) (scaleUp ell 2 (neLu (ell ^ m) R)))
      2 (neS ell (ell ^ m) R) α₀ ((ell : ℝ) ^ 2)⁻¹ flatCfg :=
    perCubeRegularF_constFam_iff.mpr (perCube_one hell0 hM (by omega) hα hη)
  exact hnp (h m hm R hRR 2 (by norm_num) (neLu (ell ^ m) R)
    (torusOK_ne_two hell2 hdvd hM) (neS ell (ell ^ m) R)
    (ne_admissible_two hell2 hM hR) (neLam (ell ^ m) R)
    (lambdaOK2_ne_two hell2 hdvd hM hR) α₀ hα hcap flatCfg hcs hreg
    (flat_wellDefG hell2 hdvd hM hR ha))

/-- Scale 13 lies in the recorded later source range; the factor here is 118. -/
theorem no_eventual_guarded_coverage_upgrade_thirteen (a : ℝ) (ha : 0 < a) :
    ¬ EventualGuardedCoverageUpgrade 13 118 (by norm_num) a := by
  simpa using no_eventual_guarded_coverage_upgrade 13 (by norm_num) a ha

#print axioms flat_wellDefG
#print axioms EventualGuardedCoverageUpgrade
#print axioms no_eventual_guarded_coverage_upgrade
#print axioms no_eventual_guarded_coverage_upgrade_thirteen

end AdalyFormal.Round7.S4OddSites.R2Geometry
