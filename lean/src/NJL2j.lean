import NJL2i

/-!
# NJL2j -- the four sums over rows: `Σ_c x_i(c)² ≤ C_i · ‖g‖₁`  (`g = |A|²`), volume free.
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
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

/-- `g = |A|²`. -/
def gA (A : CoarseBond L 1 → SuTwo) : PeriodicLatticeEdge L → ℝ := fun e => fA A e ^ 2

theorem gA_nonneg (A : CoarseBond L 1 → SuTwo) (e : PeriodicLatticeEdge L) : 0 ≤ gA A e := sq_nonneg _

theorem card_unitSites_le {ell : ℕ} (hell : 0 < ell) (y : PeriodicLatticeSite L) :
    ((unitSitesOf 1 (1 * ell) y).card : ℝ) ≤ (ell : ℝ) ^ 3 := by
  have := unitSitesOf_card_le (L := L) (m := ell) (ell := 1) (by norm_num) y (mem_coarseLattice_one y)
  exact_mod_cast this

/-- THE FAMILY SQUARE-SUM BOUND: `Σ_c ((1/ell⁴) Σ_u pathSum f_A (c₋ + a(d_u,μ)) (q(d_u,μ)))² ≤ (3 m²/ell²) ‖g_A‖₁`. -/
theorem sum_family {ell : ℕ} (hell : 0 < ell) (A : CoarseBond L 1 → SuTwo) (m : ℕ)
    (a : PeriodicLatticeSite L → Fin 3 → PeriodicLatticeSite L)
    (q : PeriodicLatticeSite L → Fin 3 → List (Fin 3))
    (hq : ∀ d ∈ Doff L ell, ∀ μ, (q d μ).length ≤ m) :
    ∑ c : CoarseBond L (1 * ell),
        ((1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
          pathSum (fA A) (c.1.1 + a (u.1 - c.1.1) c.2) (q (u.1 - c.1.1) c.2)) ^ 2
      ≤ (m / (ell : ℝ) ^ 5) * (3 * (ell : ℝ) ^ 3 * m * l1 (gA A)) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hrow : ∀ c : CoarseBond L (1 * ell),
      ((1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
          pathSum (fA A) (c.1.1 + a (u.1 - c.1.1) c.2) (q (u.1 - c.1.1) c.2)) ^ 2
        ≤ (m / (ell : ℝ) ^ 5) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
          pathSum (gA A) (c.1.1 + a (u.1 - c.1.1) c.2) (q (u.1 - c.1.1) c.2) := by
    intro c
    refine cs_block hell _ (card_unitSites_le hell c.1.1)
      (fun u => pathSum (fA A) (c.1.1 + a (u.1 - c.1.1) c.2) (q (u.1 - c.1.1) c.2))
      (fun u => pathSum (gA A) (c.1.1 + a (u.1 - c.1.1) c.2) (q (u.1 - c.1.1) c.2)) m hm
      (fun u hu => ?_) (fun u => pathSum_nonneg _ (gA_nonneg A) _ _)
    refine le_trans (pathSum_sq_le (fA A) _ _) ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hq _ (sub_mem_Doff c.1.1 u hu) _)
      (pathSum_nonneg _ (gA_nonneg A) _ _)
  refine le_trans (Finset.sum_le_sum (fun c _ => hrow c)) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact fam_bound (gA A) (gA_nonneg A) m a q hq

#print axioms sum_family

end AdalyFormal.NonflatJet
