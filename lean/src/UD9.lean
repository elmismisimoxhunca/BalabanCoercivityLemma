import UD8

/-!
# UD9 -- `hb_of_row_gauges`: `H0(Q₁(Ū))` is bijective if every row `c` touching `Λ'` has ITS OWN gauge `g_c` making `Ū^{g_c}` small on `Ball(c₋, 4ℓ)` (lane m2_unitcharts_20261014)

No relation between the gauges of different rows is assumed.  Row `d` of `H0` is compared (via `Q1jet_gauge` at the row's own gauge, the cut `Vcut1` of the gauged background to the
row's ball, and `Q1_drift_local`) with `ℓ⁻³ · RMap(g_d(c₋)⁻¹ g_d(b₀₋)) w(d)`; the rotations are isometries, so `H0_bij_of_rot_drift` applies with the same `ℓ¹` drift
`192(8ℓκ + 8 e2Majorant(rhoOf ℓ κ))` as the one-gauge route (`HB1.hb_near`).
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2UnitCharts

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (CRowIn)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt QlinStepL_congr_bg suCoordFInv_apply_congr)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA)
open AdalyFormal.IngredientFamilyR2 (RegBg Q1jet H0 Dset iotaD QlinStepL suCoordF suCoordFInv flatCfg Q1jet_flat H0_q1SU2_apply)
open AdalyFormal.NonflatJet (rhoOf r0)
open EstimatesLayer.E1E3 (e2Majorant e2Majorant_nonneg)
open AdalyFormal.DLayer (Q1_drift_local VisStep sum_vis_le sum_one_mul iotaD_l1)
open AdalyFormal.BondComposite (sum_le_of_injective sum_edge_eq_coarse1)

variable {Lu : PeriodicLatticeExtent}

open Classical in
/-- the background cut to the ball read by ONE row `c`. -/
noncomputable def Vcut1 (ell : ℕ) (c : CoarseBond Lu ell) (W : PeriodicLinkConfiguration SU2 Lu) :
    PeriodicLinkConfiguration SU2 Lu :=
  fun e => if e.1 ∈ Ball c.1.1 (4 * (1 * ell)) then W e else 1

theorem Vcut1_agree (ell : ℕ) (c : CoarseBond Lu ell) (W : PeriodicLinkConfiguration SU2 Lu) :
    AgreeAt (Ball c.1.1 (4 * (1 * ell))) W (Vcut1 ell c W) := by
  intro z hz μ
  show W (z, μ) = Vcut1 ell c W (z, μ)
  unfold Vcut1
  rw [if_pos hz]

theorem Q1jet_cut1 (ell : ℕ) (c : CoarseBond Lu ell) (W : PeriodicLinkConfiguration SU2 Lu) (B : Bond Lu → SuTwo) :
    Q1jet ell W B c = Q1jet ell (Vcut1 ell c W) B c := by
  have hrow : QlinStepL 1 ell W (suCoordF B) (c.1.1, c.2) = QlinStepL 1 ell (Vcut1 ell c W) (suCoordF B) (c.1.1, c.2) :=
    QlinStepL_congr_bg 1 ell one_pos (c.1.1, c.2) (Vcut1_agree ell c W) _
  show ((ell : ℝ)⁻¹) • (suCoordFInv (QlinStepL 1 ell W (suCoordF B))) (c.1.1, c.2)
    = ((ell : ℝ)⁻¹) • (suCoordFInv (QlinStepL 1 ell (Vcut1 ell c W) (suCoordF B))) (c.1.1, c.2)
  rw [suCoordFInv_apply_congr hrow]

theorem Vcut1_small (ell : ℕ) (c : CoarseBond Lu ell) (W : PeriodicLinkConfiguration SU2 Lu) (κ : ℝ) (hκ : 0 ≤ κ)
    (hnear : ∀ z ∈ Ball c.1.1 (4 * (1 * ell)), ∀ μ : Fin 3, frobNorm (((W (z, μ) : SU2) : M2) - 1) ≤ κ)
    (e : PeriodicLatticeEdge Lu) : frobNorm (((Vcut1 ell c W e : SU2) : M2) - 1) ≤ κ := by
  unfold Vcut1
  split_ifs with h
  · exact hnear e.1 h e.2
  · have : frobNorm (((1 : SU2) : M2) - 1) = 0 := by
      simp [AdalyFormal.Balaban.RMapLipschitz.frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]
    rw [this]; exact hκ

open Classical in
theorem hb_of_row_gauges {ell : ℕ} (hell : 0 < ell) (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (Lu μ + 1))
    (Lam : Set (PeriodicLatticeSite Lu)) (Wbg : PeriodicLinkConfiguration SU2 Lu) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (u1 : κ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
    (u2 : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * κ) < r0)
    (hKDc : 192 * (8 * (ell : ℝ) * κ + 8 * e2Majorant (rhoOf ell κ)) ≤ 1 / (2 * (ell : ℝ) ^ 3))
    (hrow : ∀ c : CoarseBond Lu ell, CRowIn ell Lam c → ∃ g : GaugeFn Lu,
      ∀ z ∈ Ball c.1.1 (4 * (1 * ell)), ∀ μ : Fin 3,
        frobNorm (((periodicGaugeTransform g Wbg (z, μ) : SU2) : M2) - 1) ≤ κ) :
    Function.Bijective (H0 Lam (Q1jet ell Wbg)) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hns := AdalyFormal.NonflatJet.numeric_small hell κ hκ0 u1
  have hgc : ∀ d : Dset Lu ell Lam, ∃ g : GaugeFn Lu, ∀ z ∈ Ball d.1.1.1 (4 * (1 * ell)), ∀ μ : Fin 3,
      frobNorm (((periodicGaugeTransform g Wbg (z, μ) : SU2) : M2) - 1) ≤ κ := fun d => hrow d.1 d.2
  choose gc hgc using hgc
  set κ' : ℝ := 8 * ell * κ + 8 * e2Majorant (rhoOf ell κ) with hκ'
  have hκ'0 : 0 ≤ κ' := by
    have : 0 ≤ e2Majorant (rhoOf ell κ) := e2Majorant_nonneg (by unfold rhoOf; positivity)
    rw [hκ']; positivity
  have hδlt : 192 * κ' < 1 / (ell : ℝ) ^ 3 := by
    have : 1 / (2 * (ell : ℝ) ^ 3) < 1 / (ell : ℝ) ^ 3 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_pos hellR 3]
    linarith
  -- the rotations
  let O : Dset Lu ell Lam → SuTwo → SuTwo := fun d x =>
    RMap ((gc d d.1.1.1)⁻¹ * gc d (AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell d.1).1) x
  refine H0_bij_of_rot_drift hell Lam _ (192 * κ') hδlt O (fun d x => norm_RMap _ x) (fun w => ?_)
  set ι := iotaD ell Lam w with hι
  -- row estimate
  have hrowb : ∀ d : Dset Lu ell Lam,
      ‖H0 Lam (Q1jet ell Wbg) w d - ((1 : ℝ) / (ell : ℝ) ^ 3) • O d (w d)‖
        ≤ κ' * ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (d.1.1.1, d.1.2) e), ‖ι e‖ := by
    intro d
    set g := gc d with hg
    set c := d.1 with hc
    set W := periodicGaugeTransform g Wbg with hW
    set ι' := gaugeActA g ι with hι'
    have hVs : ∀ e, frobNorm (((Vcut1 ell c W e : SU2) : M2) - 1) ≤ κ :=
      Vcut1_small ell c W κ hκ0 (hgc d) 
    have hreg1 : RegBg 1 ell (Vcut1 ell c W) := AdalyFormal.NonflatJet.regBg_of_small Nat.one_pos _ κ hκ0 hVs u2
    have hloc := Q1_drift_local hell hdvd (Vcut1 ell c W) κ hκ0 hVs hns.1 hreg1 ι' c
    -- gauge covariance at the row
    have hcov : Q1jet ell W ι' c = RMap (g c.1.1) (Q1jet ell Wbg ι c) := by
      have := AdalyFormal.GaugeCov.Q1jet_gauge ell g Wbg ι
      exact congrFun this c
    -- flat part
    have hι'eq : ι' = iotaD ell Lam (fun d' => RMap (g (AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell d'.1).1) (w d')) :=
      gaugeAct_iotaD Lam g w
    have hflat : Q1jet ell flatCfg ι' c
        = ((1 : ℝ) / (ell : ℝ) ^ 3) • RMap (g (AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell c).1) (w d) := by
      have h1 := H0_q1SU2_apply hell hdvd Lam
        (fun d' => RMap (g (AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell d'.1).1) (w d')) d
      rw [Q1jet_flat ell hell hdvd ι' c, hι'eq]
      exact h1
    have hnorm : ∀ e, ‖ι' e‖ = ‖ι e‖ := by
      intro e
      show ‖RMap (g e.1) (ι e)‖ = _
      exact norm_RMap _ _
    have hrot : RMap (g c.1.1) (H0 Lam (Q1jet ell Wbg) w d - ((1 : ℝ) / (ell : ℝ) ^ 3) • O d (w d))
        = Q1jet ell (Vcut1 ell c W) ι' c - Q1jet ell flatCfg ι' c := by
      have hOid : RMap (g c.1.1) (O d (w d)) = RMap (g (AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell c).1) (w d) := by
        show RMap (g c.1.1) (RMap ((gc d c.1.1)⁻¹ * gc d (AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell c).1) (w d)) = _
        rw [AdalyFormal.Balaban.CovariantOperators.RMap_mul_apply (gc d c.1.1)
          ((gc d c.1.1)⁻¹ * gc d (AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell c).1) (w d)]
        simp only [mul_inv_cancel_left]
        rfl
      rw [← Q1jet_cut1 ell c W ι', hflat, hcov, map_sub, map_smul, hOid]
      rfl
    calc ‖H0 Lam (Q1jet ell Wbg) w d - ((1 : ℝ) / (ell : ℝ) ^ 3) • O d (w d)‖
        = ‖RMap (g c.1.1) (H0 Lam (Q1jet ell Wbg) w d - ((1 : ℝ) / (ell : ℝ) ^ 3) • O d (w d))‖ := (norm_RMap _ _).symm
      _ = ‖Q1jet ell (Vcut1 ell c W) ι' c - Q1jet ell flatCfg ι' c‖ := by rw [hrot]
      _ ≤ κ' * ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (c.1.1, c.2) e), ‖ι' e‖ := hloc
      _ = _ := by simp only [hnorm]
  -- sum
  set F : CoarseBond Lu ell → ℝ := fun c =>
    κ' * ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (c.1.1, c.2) e), ‖ι e‖ with hF
  have hF0 : ∀ c, 0 ≤ F c := fun c => mul_nonneg hκ'0 (Finset.sum_nonneg (fun e _ => norm_nonneg _))
  have h1 : ∑ d : Dset Lu ell Lam, F d.1 ≤ ∑ c : CoarseBond Lu ell, F c :=
    sum_le_of_injective (fun d : Dset Lu ell Lam => d.1) Subtype.val_injective F hF0
  refine (Finset.sum_le_sum (fun d _ => hrowb d)).trans (h1.trans ?_)
  rw [hF, ← Finset.mul_sum]
  have hn : ∀ ν, 1 * ell ∣ Lu ν + 1 := fun ν => by rw [one_mul]; exact hdvd ν
  have h3 := sum_vis_le 1 ell Nat.one_pos hell hn (fun e => ‖ι e‖) (fun e => norm_nonneg _)
  have h4 := sum_one_mul (Lq := Lu) ell (fun y μ => ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (y, μ) e), ‖ι e‖)
  have h5 : ∑ e : CoarseBond Lu 1, ‖ι (e.1.1, e.2)‖ = ∑ e : Bond Lu, ‖ι e‖ :=
    (sum_edge_eq_coarse1 (fun e => ‖ι e‖)).symm
  have h6 := iotaD_l1 Lam w
  rw [h4]
  have h7 : ∑ c : CoarseBond Lu (1 * ell), ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (c.1.1, c.2) e), ‖ι e‖
      ≤ 192 * ∑ d : Dset Lu ell Lam, ‖w d‖ := by
    refine h3.trans ?_
    rw [h5]
    exact mul_le_mul_of_nonneg_left h6 (by norm_num)
  have := mul_le_mul_of_nonneg_left h7 hκ'0
  linarith

end AdalyFormal.M2UnitCharts

#print axioms AdalyFormal.M2UnitCharts.hb_of_row_gauges
