import NJ20b

/-!
# NJ20c -- volume-free `L²` main-term drift.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov (unitToCoarseCov)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem sum_x2 {ell : ℕ} (hell : 0 < ell) (A : CoarseBond L 1 → SuTwo) :
    ∑ c : CoarseBond L (1 * ell), ((1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N2 ell A c u.1) ^ 2
      ≤ 3 * l1 (gA A) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have h := sum_family hell A ell (fun d _ => d) (fun _ μ => List.replicate ell μ) (fun _ _ μ => by simp)
  have c2 : ((ell : ℝ) / (ell : ℝ) ^ 5) * (3 * (ell : ℝ) ^ 3 * ell * l1 (gA A)) = 3 * l1 (gA A) := by
    field_simp
  exact h.trans (le_of_eq c2)

/-- **VOLUME-FREE `L²` main-term drift.** -/
theorem T1_drift_l2 {ell : ℕ} (hell : 0 < ell) (V : PeriodicLinkConfiguration SU2 L)
    (ε0 : ℝ) (hε0 : 0 ≤ ε0) (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0)
    (A : CoarseBond L 1 → SuTwo) :
    ∑ c : CoarseBond L (1 * ell),
        ‖unitToCoarseCov 1 ell V A c - unitToCoarseCov 1 ell (trivialU L) A c‖ ^ 2
      ≤ 192 * (ell * ε0) ^ 2 * l1 (gA A) := by
  have hrow : ∀ c : CoarseBond L (1 * ell),
      ‖unitToCoarseCov 1 ell V A c - unitToCoarseCov 1 ell (trivialU L) A c‖ ^ 2
        ≤ (8 * ell * ε0) ^ 2 *
          ((1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N2 ell A c u.1) ^ 2 := by
    intro c
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (T1_drift_row hell V ε0 hε0 hV A c) 2
  refine le_trans (Finset.sum_le_sum (fun c _ => hrow c)) ?_
  rw [← Finset.mul_sum]
  calc (8 * (ell : ℝ) * ε0) ^ 2 * _ ≤ (8 * (ell : ℝ) * ε0) ^ 2 * (3 * l1 (gA A)) :=
        mul_le_mul_of_nonneg_left (sum_x2 hell A) (sq_nonneg _)
    _ = 192 * (ell * ε0) ^ 2 * l1 (gA A) := by ring

#print axioms T1_drift_l2

end AdalyFormal.NonflatJet
