import NsOdd9b

/-!
# NsOdd9c -- the unit-level background of the odd staggered tower is `cartanOf (unitFld ...)`, hence regular (lane ncwdh_strong_20261017)
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
open AdalyFormal.IngredientFamilyR2 (unitBg embY embY_val)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq UbarTower UbarTower_succ UbarTower_zero)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {ell : ℕ} {Lu : PeriodicLatticeExtent}

theorem sgnNat_mul_odd {k : ℕ} (hk : k % 2 = 1) (v : ℕ) : sgnNat (k * v) = sgnNat v := by
  unfold sgnNat
  have : (k * v) % 2 = v % 2 := by rw [Nat.mul_mod, hk]; simp
  rw [this]

theorem phiu_eq_unitFld (hell : 0 < ell) {c : ℕ} (G : OddGeo (scaleUp ell 2 Lu) ell c) (cu : ℕ) (hcu : c = ell * ell * cu) (t : ℝ) :
    (fun e : PeriodicLatticeEdge Lu => blockAngG ell ell (phi1o (scaleUp ell 2 Lu) c ell t) (embY ell 2 Lu hell e.1) e.2) =
      (unitFld t (b2 ell) (d2 ell) cu : PeriodicLatticeEdge Lu → ℝ) := by
  have hY : ∀ y : PeriodicLatticeSite Lu, ∀ μ, ell * ell ∣ ((embY ell 2 Lu hell y) μ).val := by
    intro y μ; rw [embY_val, pow_two]; exact dvd_mul_right _ _
  have hsq : ell * ell % 2 = 1 := by rw [Nat.mul_mod, G.hO]
  have hN0 : scaleUp ell 2 Lu 0 + 1 = ell * ell * (Lu 0 + 1) := by
    rw [scaleUp_succ ell 2 Lu hell, pow_two]; ring
  have hpos : 0 < ell * ell := Nat.mul_pos hell hell
  have hind : ∀ v : ℕ, (ell * ell * v = c) ↔ (v = cu) := by
    intro v; rw [hcu]; exact Nat.mul_left_cancel_iff hpos
  have hemb : ∀ (y : PeriodicLatticeSite Lu) (μ : Fin 3), ((embY ell 2 Lu hell y) μ).val = ell * ell * (y μ).val := by
    intro y μ; rw [embY_val, pow_two]
  have H0 : ∀ y : PeriodicLatticeSite Lu, blockAngG ell ell (phi1o (scaleUp ell 2 Lu) c ell t) (embY ell 2 Lu hell y) 0 =
      (unitFld t (b2 ell) (d2 ell) cu : PeriodicLatticeEdge Lu → ℝ) (y, 0) := by
    intro y
    rw [phi2_dir0 G t _ (hY y)]
    unfold unitFld shapeFld fld
    dsimp only
    rw [if_pos rfl]
    simp only [hemb, hN0, sgnNat_mul_odd hsq, hind]
    have : (ell * ell * (y 0).val + ell * ell) % (ell * ell * (Lu 0 + 1)) = ell * ell * (((y 0).val + 1) % (Lu 0 + 1)) := by
      rw [show ell * ell * (y 0).val + ell * ell = ell * ell * ((y 0).val + 1) by ring, Nat.mul_mod_mul_left]
    rw [this]; simp only [hind]
    unfold Dfun
    ring
  have H1 : ∀ y : PeriodicLatticeSite Lu, blockAngG ell ell (phi1o (scaleUp ell 2 Lu) c ell t) (embY ell 2 Lu hell y) 1 =
      (unitFld t (b2 ell) (d2 ell) cu : PeriodicLatticeEdge Lu → ℝ) (y, 1) := by
    intro y
    rw [phi2_dir1 G t _ (hY y)]
    unfold unitFld shapeFld fld
    dsimp only
    rw [if_neg (show ¬ ((1 : Fin 3) = 0) by decide), if_pos rfl]
    simp only [hemb, sgnNat_mul_odd hsq, hind]
    ring
  have H2 : ∀ y : PeriodicLatticeSite Lu, blockAngG ell ell (phi1o (scaleUp ell 2 Lu) c ell t) (embY ell 2 Lu hell y) 2 =
      (unitFld t (b2 ell) (d2 ell) cu : PeriodicLatticeEdge Lu → ℝ) (y, 2) := by
    intro y
    rw [phi2_dir2 G t _ (hY y)]
    unfold unitFld shapeFld fld
    dsimp only
    rw [if_neg (show ¬ ((2 : Fin 3) = 0) by decide), if_neg (show ¬ ((2 : Fin 3) = 1) by decide)]
  funext ⟨y, μ⟩
  fin_cases μ
  · exact H0 y
  · exact H1 y
  · exact H2 y


theorem two_dvd_unit (hO : ell % 2 = 1) (h : 2 ∣ scaleUp ell 2 Lu 1 + 1) : 2 ∣ Lu 1 + 1 := by
  have hell : 0 < ell := by omega
  rw [scaleUp_succ ell 2 Lu hell] at h
  have hc : Nat.Coprime 2 (ell ^ 2) := by
    apply Nat.Coprime.pow_right
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  exact hc.dvd_of_dvd_mul_right h

theorem unitBg_eq_cartan (hell : 0 < ell) {c : ℕ} (G : OddGeo (scaleUp ell 2 Lu) ell c) (t : ℝ) (ht : |t| < 8 / 5) :
    unitBg ell 2 Lu hell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 (scaleUp ell 2 Lu)) 2) =
      cartanOf (fun e : PeriodicLatticeEdge Lu => blockAngG ell ell (phi1o (scaleUp ell 2 Lu) c ell t) (embY ell 2 Lu hell e.1) e.2) := by
  have htπ : |t| < Real.pi := lt_trans ht (by have := Real.pi_gt_d2; norm_num at this ⊢; linarith)
  funext ⟨y, μ⟩
  unfold unitBg
  simp only [UbarTower_succ, UbarTower_zero, pow_zero, pow_one]
  show stridedBlockedGauge su2LogExp ell ell (stridedBlockedGauge su2LogExp 1 ell (stagCfg c t : PeriodicLinkConfiguration SU2 (scaleUp ell 2 Lu))) (embY ell 2 Lu hell y, μ) = _
  rw [bg1_eq_odd G.hN G.hO c t htπ G.hc1 G.hc2]
  rw [sbg_cartanOf ell ell _ (embY ell 2 Lu hell y) μ
    (fun x hx => phi1o_loop_lt_pi G.hN G.hO G.h5 G.hbig c G.hc3 t ht (embY ell 2 Lu hell y, μ) x hx)]
  rfl

theorem unit_regBg2_odd (hell : 0 < ell) {c : ℕ} (G : OddGeo (scaleUp ell 2 Lu) ell c) (cu : ℕ) (hcu : c = ell * ell * cu)
    (t : ℝ) (ht : |t| < 8 / 5) :
    RegBg2 1 ell (unitBg ell 2 Lu hell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 (scaleUp ell 2 Lu)) 2)) := by
  rw [unitBg_eq_cartan hell G t ht, phiu_eq_unitFld hell G cu hcu t]
  have hN := two_dvd_unit G.hO G.hN
  have hb := b2_range G.h5
  have hd := d2_range G.h5
  apply regBg2_cartanOf_of_loops
  intro cc x hx
  refine lt_of_le_of_lt (unitFld_loop_le hN G.hO cu t (b2 ell) (d2 ell) hb hd cc x hx) (lt_trans ht ?_)
  have := Real.pi_gt_d2; norm_num at this ⊢; linarith

#print axioms phiu_eq_unitFld
#print axioms unitBg_eq_cartan
#print axioms unit_regBg2_odd

end AdalyFormal.CoverOmega
