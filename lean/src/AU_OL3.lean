import OL3
import AU_UD4
import AU_DK2
import AU_CUT

/-! AU copy of OL3 (c-free): `rowGauges_classU`, `hKD_classU` take a `BallChartsAt` instance. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2OpLayer


open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist TorusOK CRowIn)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt AgreeX rhoT pdist_comm pdist_triangle pdist_coarseShift_le lamPrime_sub Ball_sub
  QlinStepL_congr_bg C2StepL_congr_bg C2StepL_congr_in suCoordFInv_apply_congr)
open AdalyFormal.IngredientFamilyR2 (embY embY_val H0 H0inv hLift rhoD iotaD Dset RegBg Q1jet QlinStepL suCoordF suCoordFInv
  flatCfg Q1jet_flat H0_q1SU2_apply H0_H0inv C2tilde)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.NonflatJet (rhoOf r0)
open EstimatesLayer.E1E3 (e2Majorant e2Majorant_nonneg)
open AdalyFormal.DLayer (Q1_drift_local VisStep sum_vis_le sum_one_mul iotaD_l1 KDfree K2s C2tilde_l1)
open AdalyFormal.BondComposite (sum_le_of_injective sum_edge_eq_coarse1)
open AdalyFormal.M1DK (kapM1 qM1 KDsmall)
open AdalyFormal.M2Unit (agree_gauge unitBgU_chart_small)
open AdalyFormal.M2UnitCharts (chart_of_ballU scaleUp_succ pdist_embY norm_RMap Vcut1 Vcut1_agree Vcut1_small Q1jet_cut1
  gaugeAct_iotaD)

section
variable {Lu : PeriodicLatticeExtent}

open Classical in
end

theorem rowGauges_classU {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell)
    (hT : TorusOK ell M Lu) (hMb : 4 * ell + 141 ≤ 4 * M) (hRM : 5 * ell + 17 ≤ R * M) (hR6 : 6 * ell ≤ R) (hk1 : 1 ≤ k)
    (hthick : ∀ σ : Fin 3, 12 * (M * ell ^ k) ≤ scaleUp ell k Lu σ + 1)
    (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S)
    (Lam : Set (PeriodicLatticeSite Lu)) (hL : LambdaOK2 ell M R k S Lam)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (αb : ℝ) (hα : 0 < αb) {C : ℝ} (hC : 1 ≤ C)
    (hBall : AdalyFormal.OneGap.BallChartsAt ell M k S U C αb ((ell : ℝ) ^ k)⁻¹)
    (α₁ : ℝ) (hα1 : (ell : ℝ) ^ 3 * (2 * (C * αb)) ≤ α₁) (hsm : KDsmall ell (12 * M * α₁)) :
    ∀ c : CoarseBond Lu ell, CRowIn ell Lam c → ∃ g : GaugeFn Lu, ∀ z ∈ Ball c.1.1 (4 * (1 * ell)), ∀ μ : Fin 3,
      frobNorm (((periodicGaugeTransform g (gparams ell k Lu (by omega) S U a Lam).unitBgU (z, μ) : SU2) : M2) - 1)
        ≤ kapM1 (12 * M * α₁) := by
  have hell : 0 < ell := by omega
  have hn : 0 < ell ^ k := pow_pos hell k
  have hLu : ∀ σ : Fin 3, 1 ≤ scaleUp ell k Lu σ := by
    intro σ
    have h1 := scaleUp_succ ell k Lu hell σ
    have h2 := hT.2.1 σ
    have : 3 ≤ Lu σ + 1 := by omega
    have h3 : (Lu σ + 1) * 1 ≤ (Lu σ + 1) * ell ^ k := Nat.mul_le_mul_left _ hn
    omega
  have hT3 : ∀ μ, 3 ≤ Lu μ + 1 := fun μ => by have := hT.2.1 μ; omega
  have hα1pos : 0 < α₁ := lt_of_lt_of_le (by have := lt_of_lt_of_le one_pos hC; positivity) hα1
  have hβ0 : 0 ≤ 12 * (M : ℝ) * α₁ := by positivity
  have hL1 := hL.1
  set P := gparams ell k Lu hell S U a Lam with hP
  have hrho := AdalyFormal.StatementLaneR8.rhoT_le ell hell2 k
  intro c hc
  -- a point of Λ within ℓ of c₋
  obtain ⟨y0, hy0, hyc⟩ : ∃ y ∈ Lam, pdist y c.1.1 ≤ ell := by
    rcases hc with h | h
    · exact ⟨c.1.1, lamPrime_sub hell h, by rw [AdalyFormal.StatementLane.pdist_self]; exact Nat.zero_le _⟩
    · refine ⟨coarseShift c.1.1 ell c.2, lamPrime_sub hell h, ?_⟩
      rw [pdist_comm]; exact pdist_coarseShift_le _ _ _
  have hrad : (ell ^ k * (4 * ell) + 8 * ell ^ k) + 64 * ell ^ k + 5 ≤ 6 * (M * ell ^ k) - 1 := by
    have h1 : ell ^ k * (4 * ell + 141) ≤ ell ^ k * (4 * M) := Nat.mul_le_mul_left _ hMb
    have e1 : ell ^ k * (4 * ell + 141) = ell ^ k * (4 * ell) + 141 * ell ^ k := by ring
    have e2 : ell ^ k * (4 * M) = 4 * (M * ell ^ k) := by ring
    omega
  obtain ⟨γ, V, hV, hag⟩ := chart_of_ballU hell (by omega : 0 < M) hk1 hS hL1 hthick hR6 hy0 c.1.1 (by omega)
    (ell ^ k * (4 * ell) + 8 * ell ^ k) hrad hC hα hBall
  replace hV := AdalyFormal.AllU.M1RegularU.mono (by positivity) hα1 hV
  obtain ⟨g, A, hgA, hB⟩ := hV
  obtain ⟨hlk, hpl⟩ := AdalyFormal.M1DK.chart_boundsU ell M k hell S α₁ V g A _ rfl hgA hB hα1pos.le hsm.h1
  refine ⟨fun w => (g (embY ell k Lu hell w)) * (γ (embY ell k Lu hell w)), fun z hz μ => ?_⟩
  set γ' : GaugeFn (scaleUp ell k Lu) := fun x => g x * γ x with hγ'
  have hcomp : periodicGaugeTransform γ' U = periodicGaugeTransform g (periodicGaugeTransform γ U) :=
    (AdalyFormal.Lattice.Witness.periodicGaugeTransform_comp g γ U).symm
  have hag' : AgreeAt (Ball (embY ell k Lu hell c.1.1) (ell ^ k * (4 * ell) + 8 * ell ^ k)) (periodicGaugeTransform γ' U)
      (periodicGaugeTransform g V) := by
    rw [hcomp]; exact agree_gauge hag g
  have hz' : pdist c.1.1 z ≤ 4 * (1 * ell) := hz
  have hsub : AgreeAt (Ball (embY ell k Lu hell z) (rhoT ell k)) (periodicGaugeTransform γ' U) (periodicGaugeTransform g V) := by
    refine hag'.mono (Ball_sub (d := ell ^ k * (4 * ell)) ?_ (by omega))
    rw [pdist_embY hell]
    exact Nat.mul_le_mul_left _ (by omega)
  have hnear : pdist y0 z + 17 ≤ R * M := by
    have := pdist_triangle y0 c.1.1 z
    omega
  have := unitBgU_chart_small hell hell2 S hS Lam hL hT3 U a γ' (periodicGaugeTransform g V) (12 * M * α₁)
    (qM1 (12 * M * α₁)) (AdalyFormal.M1DK.qM1_nonneg hβ0) hlk hpl hsm.hcb z hsub hy0 hnear μ
  unfold kapM1; exact this


section rest
variable {Lu : PeriodicLatticeExtent}

open Classical in
open Classical in
/-- **`hKD` at the printed class** (per-row gauges; no global gauge) -/
theorem hKD_classU {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell)
    (hT : TorusOK ell M Lu) (hMb : 4 * ell + 141 ≤ 4 * M) (hRM : 5 * ell + 17 ≤ R * M) (hR6 : 6 * ell ≤ R) (hk1 : 1 ≤ k)
    (hthick : ∀ σ : Fin 3, 12 * (M * ell ^ k) ≤ scaleUp ell k Lu σ + 1)
    (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S)
    (Lam : Set (PeriodicLatticeSite Lu)) (hL : LambdaOK2 ell M R k S Lam)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (αb : ℝ) (hα : 0 < αb) {C : ℝ} (hC : 1 ≤ C)
    (hBall : AdalyFormal.OneGap.BallChartsAt ell M k S U C αb ((ell : ℝ) ^ k)⁻¹)
    (α₁ : ℝ) (hα1 : (ell : ℝ) ^ 3 * (2 * (C * αb)) ≤ α₁) (hsm : KDsmall ell (12 * M * α₁))
    (B : BondFnL2 Lu) :
    ∑ e, ‖((gparams ell k Lu (by omega) S U a Lam).D2in B) e‖ ≤ 2187 * KDfree ell * ‖B‖ ^ 2 := by
  classical
  have hell : 0 < ell := by omega
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set P := gparams ell k Lu (by omega) S U a Lam with hP
  have hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1 := hT.1
  have hα1pos : 0 < α₁ := lt_of_lt_of_le (by have := lt_of_lt_of_le one_pos hC; positivity) hα1
  have hβ0 : 0 ≤ 12 * (M : ℝ) * α₁ := by positivity
  set κ : ℝ := kapM1 (12 * M * α₁) with hκ
  have hκ0 : 0 ≤ κ := AdalyFormal.M1DK.kapM1_nonneg hβ0
  have hrows := rowGauges_classU hell2 hT hMb hRM hR6 hk1 hthick S hS Lam hL U a αb hα hC hBall α₁ hα1 hsm
  obtain ⟨O, hO, hdrift⟩ := rot_drift_of_row_gauges hell hell2 hd Lam P.unitBgU κ hκ0 hsm.u1 hsm.u2 hsm.kd hrows
  set δ : ℝ := 192 * (8 * ell * κ + 8 * e2Majorant (rhoOf ell κ)) with hδ
  have hδlt : δ < 1 / (ell : ℝ) ^ 3 := by
    have h := hsm.kd
    have : 1 / (2 * (ell : ℝ) ^ 3) < 1 / (ell : ℝ) ^ 3 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_pos hellR 3]
    linarith
  have hb : Function.Bijective (H0 Lam (Q1jet ell P.unitBgU)) :=
    AdalyFormal.M2UnitCharts.H0_bij_of_rot_drift hell Lam _ δ hδlt O hO hdrift
  have hloop : 8 * (ell : ℝ) * κ ≤ 1 / 16 := by
    have h1 := hsm.u1
    have hl2 : (2 : ℝ) ≤ ell := by exact_mod_cast hell2
    have hl3 : (8 : ℝ) * ell ≤ 8 * (ell : ℝ) ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hl2 3]
    have h5 : 8 * (ell : ℝ) * κ ≤ 8 * (ell : ℝ) ^ 4 * (1 / (1000 * (ell : ℝ) ^ 4)) := by
      have := mul_le_mul hl3 h1 hκ0 (by positivity); linarith
    have h6 : 8 * (ell : ℝ) ^ 4 * (1 / (1000 * (ell : ℝ) ^ 4)) = 8 / 1000 := by field_simp
    linarith
  set f : CoarseBond Lu ell → SuTwo := C2tilde ell P.unitBgU (WithLp.ofLp B) with hf
  have hL1 := hLift_l1_rot hell Lam (Q1jet ell P.unitBgU) δ hδlt O hO hdrift hb f
  -- rows of `C̃⁽²⁾` touching `Λ'`
  have hrow : ∀ d : Dset Lu ell Lam, ‖f d.1‖
      ≤ K2s ell * ∑ b : Bond Lu, if b.1 ∈ Ball d.1.1.1 (4 * (1 * ell)) then ‖(WithLp.ofLp B) b‖ ^ 2 else 0 := by
    intro d
    obtain ⟨g, hg⟩ := hrows d.1 d.2
    exact C2tilde_row hell hd P.unitBgU d.1 g κ hκ0 hg hsm.u2 hloop (WithLp.ofLp B)
  have hK0 : 0 ≤ K2s ell := by unfold K2s; positivity
  set F : CoarseBond Lu ell → ℝ := fun c =>
    K2s ell * ∑ b : Bond Lu, if b.1 ∈ Ball c.1.1 (4 * (1 * ell)) then ‖(WithLp.ofLp B) b‖ ^ 2 else 0 with hF
  have hF0 : ∀ c, 0 ≤ F c := fun c => mul_nonneg hK0 (Finset.sum_nonneg (fun b _ => by split_ifs <;> positivity))
  have hS1 : ∑ d : Dset Lu ell Lam, ‖f d.1‖ ≤ 2187 * K2s ell * ‖B‖ ^ 2 := by
    have h1 : ∑ d : Dset Lu ell Lam, ‖f d.1‖ ≤ ∑ d : Dset Lu ell Lam, F d.1 := Finset.sum_le_sum (fun d _ => hrow d)
    have h2 : ∑ d : Dset Lu ell Lam, F d.1 ≤ ∑ c : CoarseBond Lu ell, F c :=
      sum_le_of_injective (fun d : Dset Lu ell Lam => d.1) Subtype.val_injective F hF0
    have h3 := ball_count_unit hell hd (fun b => ‖(WithLp.ofLp B) b‖ ^ 2) (fun b => by positivity)
    have hB2 : ∑ b : Bond Lu, ‖(WithLp.ofLp B) b‖ ^ 2 = ‖B‖ ^ 2 := by rw [PiLp.norm_sq_eq_of_L2]
    have h4 : ∑ c : CoarseBond Lu ell, F c ≤ K2s ell * (2187 * ‖B‖ ^ 2) := by
      rw [hF, ← Finset.mul_sum, ← hB2]
      exact mul_le_mul_of_nonneg_left h3 hK0
    linarith
  have hpos : 0 < 1 / (ell : ℝ) ^ 3 - δ := by linarith
  have hinv : 1 / (1 / (ell : ℝ) ^ 3 - δ) ≤ 2 * (ell : ℝ) ^ 3 := by
    rw [div_le_iff₀ hpos]
    have : 1 / (ell : ℝ) ^ 3 - δ ≥ 1 / (2 * (ell : ℝ) ^ 3) := by
      have e1 : 1 / (ell : ℝ) ^ 3 = 2 * (1 / (2 * (ell : ℝ) ^ 3)) := by field_simp
      have := hsm.kd
      linarith
    have e2 : 2 * (ell : ℝ) ^ 3 * (1 / (2 * (ell : ℝ) ^ 3)) = 1 := by field_simp
    nlinarith [pow_pos hellR 3]
  have hpt : ∀ e', ‖(P.D2in B) e'‖ = (ell : ℝ)⁻¹ * ‖hLift Lam (Q1jet ell P.unitBgU) f e'‖ := by
    intro e'
    show ‖((ell : ℝ)⁻¹ • hLift Lam P.Q1 (C2tilde ell P.unitBgU (WithLp.ofLp B))) e'‖ = _
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
    rfl
  rw [Finset.sum_congr rfl fun e' _ => hpt e', ← Finset.mul_sum]
  have hSd0 : 0 ≤ ∑ d : Dset Lu ell Lam, ‖f d.1‖ := Finset.sum_nonneg (fun d _ => norm_nonneg _)
  have hL' : ∑ b : Bond Lu, ‖hLift Lam (Q1jet ell P.unitBgU) f b‖ ≤ 2 * (ell : ℝ) ^ 3 * (2187 * K2s ell * ‖B‖ ^ 2) := by
    refine hL1.trans ?_
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul hinv hS1 hSd0 (by positivity)
  calc (ell : ℝ)⁻¹ * ∑ b : Bond Lu, ‖hLift Lam (Q1jet ell P.unitBgU) f b‖
      ≤ (ell : ℝ)⁻¹ * (2 * (ell : ℝ) ^ 3 * (2187 * K2s ell * ‖B‖ ^ 2)) := mul_le_mul_of_nonneg_left hL' (by positivity)
    _ = 2187 * KDfree ell * ‖B‖ ^ 2 := by unfold KDfree; field_simp

end rest

end AdalyFormal.M2OpLayer

