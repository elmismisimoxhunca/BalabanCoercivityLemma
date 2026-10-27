import NtOdd6b

/-!
# NsOdd7 -- the staggered tower for ODD `ell ≥ 3`: levels 0 and 1 are Cartan and regular for `|t| < 33/20` (lane ncwdh_strong_20261017)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq UbarTower UbarTower_succ UbarTower_zero)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

theorem regBg2_cartanOf_of_loops {s ell : ℕ} {θ : PeriodicLatticeEdge L → ℝ}
    (h : ∀ cc : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf cc.1 s ell, |loopAngG s ell θ cc.1 cc.2 x| < Real.pi) :
    RegBg2 s ell (cartanOf θ) := by
  apply regBg2_of_ne_negOne
  intro cc x hx
  obtain ⟨y, μ⟩ := cc
  rw [loopVar_cartanOf]
  exact cartan_ne_negOne _ (h (y, μ) x hx)

/-- the level-0 loops (stride 1) for odd `ell`: `|angle| ≤ |t| < π`. -/
theorem stag_hphi0_odd (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi) :
    ∀ cc : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf cc.1 1 ell, |loopAngG 1 ell (stagφ c t) cc.1 cc.2 x| < Real.pi := by
  intro cc x hx
  rw [loopAngG_stagφ_odd hN hO]
  exact lt_of_le_of_lt (stagPhiO_abs_le hO c t cc.2 cc.1 x hx) htπ

theorem bg1_eq_odd (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi)
    (hc1 : ell ≤ c) (hc2 : c + ell ≤ L 0 + 1) :
    stridedBlockedGauge su2LogExp 1 ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) = cartanOf (phi1o L c ell t) := by
  funext e
  obtain ⟨z, μ⟩ := e
  rw [stagCfg_eq, sbg_cartanOf 1 ell (stagφ c t) z μ (fun x hx => stag_hphi0_odd hN hO c t htπ (z, μ) x hx),
    blockAng_stag_odd hN hO c t hc1 hc2 z μ]
  rfl

theorem Bell_le {ell : ℕ} (h3 : 3 ≤ ell) : 1 + 2 * ((ell : ℝ) - 1) * (2 / (ell : ℝ) ^ 2) ≤ 17 / 9 := by
  have hl : (3 : ℝ) ≤ ell := by exact_mod_cast h3
  have hl0 : (0 : ℝ) < (ell : ℝ) ^ 2 := by positivity
  have : 2 * ((ell : ℝ) - 1) * (2 / (ell : ℝ) ^ 2) = 4 * ((ell : ℝ) - 1) / (ell : ℝ) ^ 2 := by ring
  rw [this]
  have h2 : 4 * ((ell : ℝ) - 1) / (ell : ℝ) ^ 2 ≤ 8 / 9 := by
    rw [div_le_div_iff₀ hl0 (by norm_num)]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 * (ell : ℝ) - 3 by linarith) (show (0 : ℝ) ≤ (ell : ℝ) - 3 by linarith)]
  linarith

/-- numeric: `(17/9)(33/20) < π`. -/
theorem Bell_T0_lt_pi {ell : ℕ} (h3 : 3 ≤ ell) {t : ℝ} (ht : |t| < 33 / 20) :
    (1 + 2 * ((ell : ℝ) - 1) * (2 / (ell : ℝ) ^ 2)) * |t| < Real.pi := by
  have hB := Bell_le h3
  have hpi := Real.pi_gt_d2
  calc (1 + 2 * ((ell : ℝ) - 1) * (2 / (ell : ℝ) ^ 2)) * |t| ≤ (17 / 9) * |t| := by
        exact mul_le_mul_of_nonneg_right hB (abs_nonneg t)
    _ < (17 / 9) * (33 / 20) := by
        apply mul_lt_mul_of_pos_left ht (by norm_num)
    _ < Real.pi := by norm_num at hpi ⊢; linarith

theorem phi1o_loop_lt_pi (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (h3 : 3 ≤ ell) (hbig : ell * ell + ell < L 1 + 1)
    (c : ℕ) (hc3 : c + ell * ell < L 0 + 1) (t : ℝ) (ht : |t| < 33 / 20) :
    ∀ cc : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf cc.1 ell ell, |loopAngG ell ell (phi1o L c ell t) cc.1 cc.2 x| < Real.pi := by
  intro cc x hx
  obtain ⟨y, μ⟩ := cc
  have h2 : 2 ≤ ell := by omega
  refine lt_of_le_of_lt ?_ (Bell_T0_lt_pi h3 ht)
  fin_cases μ
  · exact loop_phi1o_dir0_bound hN hO h2 hbig c hc3 t y x hx
  · exact loop_phi1o_dir1_bound hN hO h3 hbig c t y x hx
  · exact loop_phi1o_dir2_bound hN hO h2 hbig c t y x hx

/-- **regularity of the two lowest levels of the staggered tower, odd `ell ≥ 3`.** -/
theorem stag_regTower_odd (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (h3 : 3 ≤ ell) (hbig : ell * ell + ell < L 1 + 1)
    (c : ℕ) (hc1 : ell ≤ c) (hc2 : c + ell ≤ L 0 + 1) (hc3 : c + ell * ell < L 0 + 1) (t : ℝ) (ht : |t| < 33 / 20) :
    RegTower2 ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 2 := by
  have htπ : |t| < Real.pi := lt_trans ht (by have := Real.pi_gt_d2; norm_num at this ⊢; linarith)
  intro j hj
  have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl
  · simp only [UbarTower_zero, pow_zero]
    rw [stagCfg_eq]
    exact regBg2_cartanOf_of_loops (stag_hphi0_odd hN hO c t htπ)
  · simp only [UbarTower_succ, UbarTower_zero, pow_zero, pow_one]
    rw [bg1_eq_odd hN hO c t htπ hc1 hc2]
    exact regBg2_cartanOf_of_loops (phi1o_loop_lt_pi hN hO h3 hbig c hc3 t ht)

#print axioms bg1_eq_odd
#print axioms phi1o_loop_lt_pi
#print axioms stag_regTower_odd

end AdalyFormal.CoverOmega
