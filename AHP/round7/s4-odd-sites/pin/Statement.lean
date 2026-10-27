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
