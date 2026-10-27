import NtPtB

/-!
# PtC -- the flat row formula `Q_j = lineCoarseRestrictSuTwo` for an arbitrary tower geometry, and its cube-sum form (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.QOne (pathSite)

variable {L : PeriodicLatticeExtent}

/-- the flat tower of a flat background is flat. -/
theorem bgTower_flat (G : TowerGeom L) (j : ℕ) :
    bgTower G (flatCfg : Cfg L) j = flatCfg := by
  unfold bgTower
  exact Ubar_flat _ j

/-- **every row of `Q` at a flat background is the `ell^j`-block line average.** -/
theorem Qfull_flat_row (G : TowerGeom L) (hell : 0 < G.ell) (J : ℕ) (hdvdJ : ∀ ν, G.ell ^ J ∣ L ν + 1)
    (p : BIdx G) (hpJ : (p.1 : ℕ) ≤ J) (hc : p.2.1.1 ∈ CoarseLattice L (G.ell ^ (p.1 : ℕ))) (A : BondFnL2 L) :
    (QfullOf G (flatCfg : Cfg L) A) p
      = lineCoarseRestrictSuTwo (G.ell ^ (p.1 : ℕ)) (WithLp.ofLp A) ⟨⟨p.2.1.1, hc⟩, p.2.1.2⟩ := by
  have hell' : (G.ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have key := Qcomp_closed G.ell hell (bgTower G (flatCfg : Cfg L)) (bgTower_flat G) J hdvdJ
    (suCoordF (WithLp.ofLp A)) (p.1 : ℕ) hpJ (G.ell ^ (p.1 : ℕ)) rfl ⟨⟨p.2.1.1, hc⟩, p.2.1.2⟩
  rw [suCoordFInv_suCoordF] at key
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G (flatCfg : Cfg L) (p.1 : ℕ) A)) p.2.1 = _
  have hQ : (WithLp.ofLp (QlinB G (flatCfg : Cfg L) (p.1 : ℕ) A)) p.2.1
      = suCoordFInv (QlinCompX G.ell (bgTower G (flatCfg : Cfg L)) (p.1 : ℕ) (suCoordF (WithLp.ofLp A)))
        (p.2.1.1, p.2.1.2) := by
    have hb := QlinCompL_eq_QlinCompX G.ell (bgTower G (flatCfg : Cfg L)) J
      (fun j _ => by rw [bgTower_flat]; exact RegBg_flat _ _) (p.1 : ℕ) hpJ
    rw [← hb]; rfl
  rw [hQ]
  have key' : suCoordFInv (QlinCompX G.ell (bgTower G (flatCfg : Cfg L)) (p.1 : ℕ) (suCoordF (WithLp.ofLp A)))
        (p.2.1.1, p.2.1.2) = (((G.ell ^ (p.1 : ℕ) : ℕ) : ℝ)) • lineCoarseRestrictSuTwo (G.ell ^ (p.1 : ℕ)) (WithLp.ofLp A)
          ⟨⟨p.2.1.1, hc⟩, p.2.1.2⟩ := key
  rw [key', smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (pow_ne_zero _ hell'), one_smul]

#print axioms Qfull_flat_row

/-- the telescoped cube sum: `lcr` of a field that is the discrete gradient of `ξ'` on the row's support, direction `0`. -/
theorem lcr_dir0 (A : Bond L → SuTwo) (ξ' : ℕ → ℕ → ℕ → SuTwo) (Y : PeriodicLatticeSite L) (n : ℕ)
    (hfit : ∀ μ, (Y μ).val + n ≤ L μ + 1) (hc : Y ∈ CoarseLattice L n)
    (hrel : ∀ a b c, (Y 0).val ≤ a → a < (Y 0).val + 2 * n → (Y 1).val ≤ b → b < (Y 1).val + n →
      (Y 2).val ≤ c → c < (Y 2).val + n → A (mkS L a b c, 0) = ξ' (a + 1) b c - ξ' a b c) :
    lineCoarseRestrictSuTwo n A ⟨⟨Y, hc⟩, 0⟩
      = (1 / (n : ℝ) ^ 4) • (cube ξ' n ((Y 0).val + n) (Y 1).val (Y 2).val - cube ξ' n (Y 0).val (Y 1).val (Y 2).val) := by
  unfold lineCoarseRestrictSuTwo
  congr 1
  rw [sum_block_eq_cube Y n hfit (fun x => ∑ i ∈ range n, A (pathSite x 0 i, 0))]
  unfold cube
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun c hc' => ?_)
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  have hc'' := Finset.mem_range.mp hc'
  simp only [pathSite_mkS0]
  have : ∀ i ∈ range n, A (mkS L ((Y 0).val + a + i) ((Y 1).val + b) ((Y 2).val + c), 0)
      = ξ' ((Y 0).val + a + i + 1) ((Y 1).val + b) ((Y 2).val + c) - ξ' ((Y 0).val + a + i) ((Y 1).val + b) ((Y 2).val + c) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact hrel _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have e1 : ∑ i ∈ range n, A (mkS L ((Y 0).val + a + i) ((Y 1).val + b) ((Y 2).val + c), 0)
      = ∑ i ∈ range n, (ξ' ((Y 0).val + a + (i + 1)) ((Y 1).val + b) ((Y 2).val + c)
          - ξ' ((Y 0).val + a + i) ((Y 1).val + b) ((Y 2).val + c)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [this i hi, add_assoc ((Y 0).val + a) i 1, add_comm i 1]
  rw [e1, Finset.sum_range_sub (fun i => ξ' ((Y 0).val + a + i) ((Y 1).val + b) ((Y 2).val + c)) n]
  have e2 : (Y 0).val + a + n = (Y 0).val + n + a := by ring
  simp only [e2, add_zero]


theorem lcr_dir1 (A : Bond L → SuTwo) (ξ' : ℕ → ℕ → ℕ → SuTwo) (Y : PeriodicLatticeSite L) (n : ℕ)
    (hfit : ∀ μ, (Y μ).val + n ≤ L μ + 1) (hc : Y ∈ CoarseLattice L n)
    (hrel : ∀ a b c, (Y 0).val ≤ a → a < (Y 0).val + n → (Y 1).val ≤ b → b < (Y 1).val + 2 * n →
      (Y 2).val ≤ c → c < (Y 2).val + n → A (mkS L a b c, 1) = ξ' a (b + 1) c - ξ' a b c) :
    lineCoarseRestrictSuTwo n A ⟨⟨Y, hc⟩, 1⟩
      = (1 / (n : ℝ) ^ 4) • (cube ξ' n (Y 0).val ((Y 1).val + n) (Y 2).val - cube ξ' n (Y 0).val (Y 1).val (Y 2).val) := by
  unfold lineCoarseRestrictSuTwo
  congr 1
  rw [sum_block_eq_cube Y n hfit (fun x => ∑ i ∈ range n, A (pathSite x 1 i, 1))]
  unfold cube
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun c hc' => ?_)
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  have hc'' := Finset.mem_range.mp hc'
  simp only [pathSite_mkS1]
  have : ∀ i ∈ range n, A (mkS L ((Y 0).val + a) ((Y 1).val + b + i) ((Y 2).val + c), 1)
      = ξ' ((Y 0).val + a) ((Y 1).val + b + i + 1) ((Y 2).val + c) - ξ' ((Y 0).val + a) ((Y 1).val + b + i) ((Y 2).val + c) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact hrel _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have e1 : ∑ i ∈ range n, A (mkS L ((Y 0).val + a) ((Y 1).val + b + i) ((Y 2).val + c), 1)
      = ∑ i ∈ range n, (ξ' ((Y 0).val + a) ((Y 1).val + b + (i + 1)) ((Y 2).val + c)
          - ξ' ((Y 0).val + a) ((Y 1).val + b + i) ((Y 2).val + c)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [this i hi, add_assoc ((Y 1).val + b) i 1, add_comm i 1]
  rw [e1, Finset.sum_range_sub (fun i => ξ' ((Y 0).val + a) ((Y 1).val + b + i) ((Y 2).val + c)) n]
  have e2 : (Y 1).val + b + n = (Y 1).val + n + b := by ring
  simp only [e2, add_zero]

theorem lcr_dir2 (A : Bond L → SuTwo) (ξ' : ℕ → ℕ → ℕ → SuTwo) (Y : PeriodicLatticeSite L) (n : ℕ)
    (hfit : ∀ μ, (Y μ).val + n ≤ L μ + 1) (hc : Y ∈ CoarseLattice L n)
    (hrel : ∀ a b c, (Y 0).val ≤ a → a < (Y 0).val + n → (Y 1).val ≤ b → b < (Y 1).val + n →
      (Y 2).val ≤ c → c < (Y 2).val + 2 * n → A (mkS L a b c, 2) = ξ' a b (c + 1) - ξ' a b c) :
    lineCoarseRestrictSuTwo n A ⟨⟨Y, hc⟩, 2⟩
      = (1 / (n : ℝ) ^ 4) • (cube ξ' n (Y 0).val (Y 1).val ((Y 2).val + n) - cube ξ' n (Y 0).val (Y 1).val (Y 2).val) := by
  unfold lineCoarseRestrictSuTwo
  congr 1
  rw [sum_block_eq_cube Y n hfit (fun x => ∑ i ∈ range n, A (pathSite x 2 i, 2))]
  unfold cube
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun c hc' => ?_)
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  have hc'' := Finset.mem_range.mp hc'
  simp only [pathSite_mkS2]
  have : ∀ i ∈ range n, A (mkS L ((Y 0).val + a) ((Y 1).val + b) ((Y 2).val + c + i), 2)
      = ξ' ((Y 0).val + a) ((Y 1).val + b) ((Y 2).val + c + i + 1) - ξ' ((Y 0).val + a) ((Y 1).val + b) ((Y 2).val + c + i) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact hrel _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have e1 : ∑ i ∈ range n, A (mkS L ((Y 0).val + a) ((Y 1).val + b) ((Y 2).val + c + i), 2)
      = ∑ i ∈ range n, (ξ' ((Y 0).val + a) ((Y 1).val + b) ((Y 2).val + c + (i + 1))
          - ξ' ((Y 0).val + a) ((Y 1).val + b) ((Y 2).val + c + i)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [this i hi, add_assoc ((Y 2).val + c) i 1, add_comm i 1]
  rw [e1, Finset.sum_range_sub (fun i => ξ' ((Y 0).val + a) ((Y 1).val + b) ((Y 2).val + c + i)) n]
  have e2 : (Y 2).val + c + n = (Y 2).val + n + c := by ring
  simp only [e2, add_zero]

end AdalyFormal.CoverOmega
