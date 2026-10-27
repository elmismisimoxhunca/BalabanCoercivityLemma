import NtOdd9c

/-!
# NsOdd10 -- the unified (even / odd `ell`) interface of the staggered tower (lane ncwdh_strong_20261017)

* `StagPar L ell`: `2 ∣ ell`, or `ell` odd `≥ 3` with the odd-block geometry `ell² + ell < L₁ + 1`.
* `StagOK ell`: `2 ∣ ell`, or `ell` odd `≥ 3` (so `StagOK ell` holds for every `ell ≥ 3`; fork of ncwdh_strong where this was `≥ 5`).
* `tcap ell`: the half-width of the parameter interval on which the tower is proven regular (`π` for even, `33/20` for odd; was `8/5` in ncwdh_strong).
* `phiU`: the angle field of the first blocked level (`phi1` for even, `phi1o` for odd).
* `bg1_eq_u`, `stag_hphi0_u`, `stag_hphi1_u`, `stag_regTower_u`: the facts the rest of the chain uses, for both parities.
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

/-- parity geometry on the fine torus. -/
def StagPar (L : PeriodicLatticeExtent) (ell : ℕ) : Prop :=
  2 ∣ ell ∨ (ell % 2 = 1 ∧ 3 ≤ ell ∧ ell * ell + ell < L 1 + 1)

/-- parity condition on the block size. -/
def StagOK (ell : ℕ) : Prop := 2 ∣ ell ∨ (ell % 2 = 1 ∧ 3 ≤ ell)

/-- half-width of the parameter interval of proven regularity. -/
noncomputable def tcap (ell : ℕ) : ℝ := if ell % 2 = 0 then Real.pi else 33 / 20

/-- the angle field of the first blocked level. -/
noncomputable def phiU {L : PeriodicLatticeExtent} (ell c : ℕ) (t : ℝ) : PeriodicLatticeEdge L → ℝ :=
  if ell % 2 = 0 then (phi1 ell c t : PeriodicLatticeEdge L → ℝ) else phi1o L c ell t

theorem StagPar.ok {ell : ℕ} (h : StagPar L ell) : StagOK ell := by
  rcases h with h | ⟨h1, h2, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2⟩

theorem StagOK.pos {ell : ℕ} (h : StagOK ell) (hell3 : 3 ≤ ell) : 0 < ell := by omega

theorem tcap_even {ell : ℕ} (h : 2 ∣ ell) : tcap ell = Real.pi := by
  unfold tcap; rw [if_pos (by omega)]

theorem tcap_odd {ell : ℕ} (h : ell % 2 = 1) : tcap ell = 33 / 20 := by
  unfold tcap; rw [if_neg (by omega)]

theorem pi_gt_33_20 : (33 / 20 : ℝ) < Real.pi := by
  have := Real.pi_gt_d2; norm_num at this ⊢; linarith

theorem tcap_le_pi (ell : ℕ) : tcap ell ≤ Real.pi := by
  unfold tcap; split_ifs
  · exact le_rfl
  · exact pi_gt_33_20.le

theorem tcap_pos (ell : ℕ) : 0 < tcap ell := by
  unfold tcap; split_ifs
  · exact Real.pi_pos
  · norm_num

theorem abs_lt_pi_of_tcap {ell : ℕ} {t : ℝ} (h : |t| < tcap ell) : |t| < Real.pi := lt_of_lt_of_le h (tcap_le_pi ell)

/-- `cos(33/20) < -1/14`. -/
theorem cos_33_20_lt : Real.cos (33 / 20) < -(1 / 14 : ℝ) := by
  have hpi1 := Real.pi_lt_d2
  have hpi2 := Real.pi_gt_d2
  have hx0 : 0 < (33 / 20 : ℝ) - Real.pi / 2 := by norm_num at hpi1 hpi2 ⊢; linarith
  have hx1 : (33 / 20 : ℝ) - Real.pi / 2 ≤ 1 := by norm_num at hpi1 hpi2 ⊢; linarith
  have hsin := Real.sin_gt_sub_cube hx0 hx1
  have hc : Real.cos (33 / 20) = - Real.sin ((33 / 20 : ℝ) - Real.pi / 2) := by
    have := Real.cos_add_pi_div_two ((33 / 20 : ℝ) - Real.pi / 2)
    rw [show (33 / 20 : ℝ) - Real.pi / 2 + Real.pi / 2 = 33 / 20 by ring] at this
    exact this
  rw [hc]
  set x : ℝ := (33 / 20 : ℝ) - Real.pi / 2 with hx
  have hxl : (3 / 40 : ℝ) < x := by rw [hx]; norm_num at hpi1 hpi2 ⊢; linarith
  have hxu : x < (1 / 10 : ℝ) := by rw [hx]; norm_num at hpi1 hpi2 ⊢; linarith
  have hx3 : x ^ 3 ≤ x / 100 := by nlinarith [sq_nonneg x, mul_pos hx0 hx0]
  nlinarith

theorem le_mul_self_c {ell c : ℕ} (hL : c + ell * ell < L 0 + 1) : c + ell ≤ L 0 + 1 := by
  have : ell ≤ ell * ell := Nat.le_mul_self ell
  omega

/-- the level-0 loops (stride 1) of the staggered layer: `|angle| < π`. -/
theorem stag_hphi0_u (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : StagPar L ell) (c : ℕ) (t : ℝ) (htπ : |t| < tcap ell) :
    ∀ cc : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf cc.1 1 ell, |loopAngG 1 ell (stagφ c t) cc.1 cc.2 x| < Real.pi := by
  rcases hE with hE | ⟨hO, -, -⟩
  · exact stag_hphi0 hN hE c t (abs_lt_pi_of_tcap htπ)
  · exact stag_hphi0_odd hN hO c t (abs_lt_pi_of_tcap htπ)

/-- the first blocked level is `cartanOf (phiU ..)`. -/
theorem bg1_eq_u (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : StagPar L ell) (hell : 0 < ell) (c : ℕ) (t : ℝ) (htπ : |t| < tcap ell)
    (hc1 : ell ≤ c) (hc2 : c + ell * ell < L 0 + 1) :
    stridedBlockedGauge su2LogExp 1 ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) = cartanOf (phiU ell c t : PeriodicLatticeEdge L → ℝ) := by
  rcases hE with hE | ⟨hO, -, -⟩
  · have hev : ell % 2 = 0 := Nat.mod_eq_zero_of_dvd hE
    unfold phiU; rw [if_pos hev]
    exact bg1_eq hN hE hell c t (abs_lt_pi_of_tcap htπ) hc1 (le_mul_self_c hc2)
  · have hev : ¬ ell % 2 = 0 := by omega
    unfold phiU; rw [if_neg hev]
    exact bg1_eq_odd hN hO c t (abs_lt_pi_of_tcap htπ) hc1 (le_mul_self_c hc2)

/-- the level-1 loops (stride `ell`) of the staggered layer: `|angle| < π`. -/
theorem stag_hphi1_u (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : StagPar L ell) (hell : 0 < ell) (c : ℕ) (t : ℝ) (htπ : |t| < tcap ell)
    (hc2 : c + ell * ell < L 0 + 1) :
    ∀ cc : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf cc.1 ell ell, |loopAngG ell ell (phiU ell c t : PeriodicLatticeEdge L → ℝ) cc.1 cc.2 x| < Real.pi := by
  rcases hE with hE | ⟨hO, h3, hbig⟩
  · have hev : ell % 2 = 0 := Nat.mod_eq_zero_of_dvd hE
    unfold phiU; rw [if_pos hev]
    exact stag_hphi1 hN hell c t (abs_lt_pi_of_tcap htπ)
  · have hev : ¬ ell % 2 = 0 := by omega
    unfold phiU; rw [if_neg hev]
    rw [tcap_odd hO] at htπ
    exact phi1o_loop_lt_pi hN hO h3 hbig c hc2 t htπ

/-- **regularity of the two lowest levels of the tower**, both parities. -/
theorem stag_regTower_u (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : StagPar L ell) (hell : 0 < ell) (c : ℕ) (t : ℝ) (htπ : |t| < tcap ell)
    (hc1 : ell ≤ c) (hc2 : c + ell * ell < L 0 + 1) :
    RegTower2 ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 2 := by
  rcases hE with hE | ⟨hO, h3, hbig⟩
  · exact stag_regTower_gen hN hE hell c t (abs_lt_pi_of_tcap htπ) hc1 (le_mul_self_c hc2)
  · rw [tcap_odd hO] at htπ
    exact stag_regTower_odd hN hO h3 hbig c hc1 (le_mul_self_c hc2) hc2 t htπ

#print axioms bg1_eq_u
#print axioms stag_hphi1_u
#print axioms stag_regTower_u

end AdalyFormal.CoverOmega
