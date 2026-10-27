import PW1
import ZGU1B
import ZXR2Flat6

/-!
# PW4 -- flat closed forms on the patch (M1 lane D, node W3)

* `qfull_flat` : at `U = 1`, a constraint row `(i, b)` of ANY tower geometry with `G.ell = ell` reads the
  `ell^i`-block line average `lineCoarseRestrictSuTwo (ell^i)` of the field (from `Qcomp_closed`, ZGU1B).
* `lcr_succ` : for `0 < n`, `0 < ell`, `n ell ∣ L μ + 1` and `c` on the `n`-lattice:
  `LCR_{n ell}(c) = ell^{-4} Σ_{x ∈ stepBlock(c)} Σ_{s<ell} [x + s n e_μ on the n-lattice] LCR_n(x + s n e_μ)` (the tree's `tower_law`;
  the guard always holds on such tori, `pathSite_mul_coarse`).
* `lcr_succ_sq` : Cauchy–Schwarz form `‖LCR_{n ell}(c)‖² ≤ ell^{-4} Σ Σ ‖LCR_n(·)‖²`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1Patch

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1 (Qcomp_closed sum_unitSites)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2 M2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond coarseLattice_mem_fits)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf card_stepBlockOf)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.ThirdLevelArrows (unitToCoarse unitSitesOf pathSite_mul_coarse tower_law)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo lineCoarseRestrictCovLM
  lineCoarseRestrictCov_trivialU lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

variable {L : PeriodicLatticeExtent}

theorem suCoordFInv_suCoord (A : BondFnL2 L) : suCoordFInv (suCoord A) = WithLp.ofLp A := by
  funext b
  apply Subtype.ext
  show toM2 (fromM2 ((WithLp.ofLp A b : SuTwo) : M2)) = _
  exact toM2_fromM2 (WithLp.ofLp A b).2

theorem bg_flat (G : TowerGeom L) (j : ℕ) :
    bgTower G (flatCfg : PeriodicLinkConfiguration SU2 L) j = flatCfg := Ubar_flat G.ell j

/-- **flat constraint rows are block line averages** (any tower geometry). -/
theorem qfull_flat (G : TowerGeom L) (hell : 0 < G.ell) (hdvd : ∀ μ, G.ell ^ G.k ∣ L μ + 1) (A : BondFnL2 L)
    (p : BIdx G) (hc : p.2.1.1 ∈ CoarseLattice L (G.ell ^ (p.1 : ℕ))) :
    (QfullOf G (flatCfg : PeriodicLinkConfiguration SU2 L) A).ofLp p
      = lineCoarseRestrictSuTwo (G.ell ^ (p.1 : ℕ)) (WithLp.ofLp A) (⟨p.2.1.1, hc⟩, p.2.1.2) := by
  have hi : (p.1 : ℕ) ≤ G.k := Nat.lt_succ_iff.mp p.1.isLt
  have hbg : ∀ j, bgTower G (flatCfg : PeriodicLinkConfiguration SU2 L) j = flatCfg := bg_flat G
  have hreg : RegTower G.ell (bgTower G (flatCfg : PeriodicLinkConfiguration SU2 L)) G.k :=
    fun j _ => by rw [hbg j]; exact RegBg_flat _ _
  have hcl := Qcomp_closed G.ell hell (bgTower G (flatCfg : PeriodicLinkConfiguration SU2 L)) hbg G.k hdvd
    (suCoord A) (p.1 : ℕ) hi (G.ell ^ (p.1 : ℕ)) rfl (⟨p.2.1.1, hc⟩, p.2.1.2)
  rw [suCoordFInv_suCoord] at hcl
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G flatCfg p.1 A)) p.2.1 = _
  rw [QlinB_apply, QlinCompL_eq_QlinCompX G.ell _ G.k hreg _ hi]
  have h2 : (WithLp.ofLp (suCoordInv (QlinCompX G.ell (bgTower G flatCfg) (p.1 : ℕ) (suCoord A)))) p.2.1
      = suCoordFInv (QlinCompX G.ell (bgTower G flatCfg) (p.1 : ℕ) (suCoord A)) (p.2.1.1, p.2.1.2) := rfl
  rw [h2, hcl, smul_smul]
  have hne : ((G.ell : ℝ) ^ (p.1 : ℕ)) ≠ 0 := by
    have : (0 : ℝ) < G.ell := by exact_mod_cast hell
    positivity
  push_cast
  rw [inv_mul_cancel₀ hne, one_smul]

/-- the tower law as an explicit average over `ell^4` level-`n` line averages. -/
theorem lcr_succ {n ell : ℕ} (hn : 0 < n) (hell : 0 < ell) (hdvd : ∀ μ, n * ell ∣ L μ + 1)
    (v : Bond L → SuTwo) (c : CoarseBond L (n * ell)) (hcn : c.1.1 ∈ CoarseLattice L n) :
    lineCoarseRestrictSuTwo (n * ell) v c
      = (1 / (ell : ℝ) ^ 4) • ∑ x ∈ stepBlockOf c.1.1 n ell, ∑ i ∈ Finset.range ell,
          (if h : pathSite x c.2 (i * n) ∈ CoarseLattice L n then
            lineCoarseRestrictSuTwo n v (⟨pathSite x c.2 (i * n), h⟩, c.2) else 0) := by
  have hdn : ∀ μ, n ∣ L μ + 1 := fun μ => dvd_trans (dvd_mul_right n ell) (hdvd μ)
  have htl := congrFun (tower_law (L := L) hn hell hdn v) c
  rw [lineCoarseRestrictCovLM_apply, lineCoarseRestrictCov_trivialU] at htl
  rw [← htl]
  unfold unitToCoarse
  congr 1
  rw [sum_unitSites n ell hcn (fun x => ∑ i ∈ Finset.range ell,
      (if h : pathSite x c.2 (i * n) ∈ CoarseLattice L n then
        lineCoarseRestrictCovLM (trivialU L) n v (⟨pathSite x c.2 (i * n), h⟩, c.2) else 0))]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun i _ => ?_))
  split_ifs
  · rw [lineCoarseRestrictCovLM_apply, lineCoarseRestrictCov_trivialU]
  · rfl

/-- Cauchy–Schwarz on a finite sum of vectors. -/
theorem norm_sum_sq_le {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (s : Finset ι) (f : ι → V) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
  have h2 : (∑ i ∈ s, ‖f i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
    simpa using hcs
  calc ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem lcr_succ_sq {n ell : ℕ} (hn : 0 < n) (hell : 0 < ell) (hdvd : ∀ μ, n * ell ∣ L μ + 1)
    (v : Bond L → SuTwo) (c : CoarseBond L (n * ell)) (hcn : c.1.1 ∈ CoarseLattice L n) :
    ‖lineCoarseRestrictSuTwo (n * ell) v c‖ ^ 2
      ≤ (1 / (ell : ℝ) ^ 4) * ∑ x ∈ stepBlockOf c.1.1 n ell, ∑ i ∈ Finset.range ell,
          ‖(if h : pathSite x c.2 (i * n) ∈ CoarseLattice L n then
            lineCoarseRestrictSuTwo n v (⟨pathSite x c.2 (i * n), h⟩, c.2) else 0)‖ ^ 2 := by
  rw [lcr_succ hn hell hdvd v c hcn, norm_smul, mul_pow]
  have hfit : ∀ μ, (c.1.1 μ).val + n * ell ≤ L μ + 1 := coarseLattice_mem_fits hdvd c.1.2
  have hcard : (stepBlockOf c.1.1 n ell).card = ell ^ 3 := card_stepBlockOf c.1.1 n ell hn hfit
  rw [← Finset.sum_product']
  have hcs := norm_sum_sq_le ((stepBlockOf c.1.1 n ell) ×ˢ Finset.range ell)
    (fun q : PeriodicLatticeSite L × ℕ => (if h : pathSite q.1 c.2 (q.2 * n) ∈ CoarseLattice L n then
            lineCoarseRestrictSuTwo n v (⟨pathSite q.1 c.2 (q.2 * n), h⟩, c.2) else 0))
  rw [Finset.card_product, hcard, Finset.card_range] at hcs
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hn1 : ‖(1 / (ell : ℝ) ^ 4)‖ ^ 2 = (1 / (ell : ℝ) ^ 4) * (1 / (ell : ℝ) ^ 4) := by
    rw [Real.norm_of_nonneg (by positivity)]; ring
  rw [hn1, ← Finset.sum_product' (f := fun x i => ‖(if h : pathSite x c.2 (i * n) ∈ CoarseLattice L n then
            lineCoarseRestrictSuTwo n v (⟨pathSite x c.2 (i * n), h⟩, c.2) else 0)‖ ^ 2)]
  have hS0 : 0 ≤ ∑ q ∈ (stepBlockOf c.1.1 n ell) ×ˢ Finset.range ell,
      ‖(if h : pathSite q.1 c.2 (q.2 * n) ∈ CoarseLattice L n then
            lineCoarseRestrictSuTwo n v (⟨pathSite q.1 c.2 (q.2 * n), h⟩, c.2) else 0)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hk : ((ell ^ 3 * ell : ℕ) : ℝ) = (ell : ℝ) ^ 4 := by push_cast; ring
  rw [hk] at hcs
  calc (1 / (ell : ℝ) ^ 4) * (1 / (ell : ℝ) ^ 4) * ‖∑ q ∈ (stepBlockOf c.1.1 n ell) ×ˢ Finset.range ell, _‖ ^ 2
      ≤ (1 / (ell : ℝ) ^ 4) * (1 / (ell : ℝ) ^ 4) * ((ell : ℝ) ^ 4 * _) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by field_simp

#print axioms qfull_flat
#print axioms lcr_succ
#print axioms lcr_succ_sq

end AdalyFormal.M1Patch
