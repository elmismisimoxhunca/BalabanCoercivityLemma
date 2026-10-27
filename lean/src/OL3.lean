import OL2

/-!
# OL3 -- `hKD` at the printed class, with one gauge PER ROW (lane m2_oplayer_20261015)

* `rowGauges_class` : UD10 `hb_class` (text copy, conclusion = its per-row gauge family): every row `c` touching `Λ'` has a unit
  gauge with `‖(Ū^g)(z,μ) − 1‖ ≤ κ` on `Ball(c₋, 4ℓ)`, `κ = kapM1(12 M α₁)`, `α₁ = ℓ³ 2α₀` (ClassCoupled only).
* `rot_drift_of_row_gauges` : UD9 `hb_of_row_gauges` (text copy, conclusion = its rotation drift): isometries `O d` with
  `Σ_d ‖H₀ w d − ℓ⁻³ O_d(w d)‖ ≤ 192 κ' Σ_d ‖w d‖`.
* `H0inv_l1_rot`, `hLift_l1_rot` : the `ℓ¹` inverse bound from the rotation drift (DLR75 `H0inv_l1` / `hLift_l1` with the
  flat comparison replaced by the rotated one).
* `C2tilde_row` : one row of `C̃⁽²⁾` from its own gauge: `‖C̃⁽²⁾_W(B)(c)‖ ≤ K2s ℓ Σ_{b₋ ∈ Ball(c₋,4ℓ)} ‖B b‖²`.
* `ball_count_unit` : `Σ_c Σ_{b₋ ∈ Ball(c₋,4ℓ)} f b ≤ 2187 Σ_b f b`.
* **`hKD_class`** : `Σ_e ‖D̃⁽²⁾(B) e‖ ≤ 2187 · KDfree ℓ · ‖B‖²` at every printed-class configuration with `KDsmall ℓ (12 M α₁)`.
-/
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
open AdalyFormal.M2UnitCharts (chart_of_class scaleUp_succ pdist_embY norm_RMap Vcut1 Vcut1_agree Vcut1_small Q1jet_cut1
  gaugeAct_iotaD)

section
variable {Lu : PeriodicLatticeExtent}

open Classical in
theorem rot_drift_of_row_gauges {ell : ℕ} (hell : 0 < ell) (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (Lu μ + 1))
    (Lam : Set (PeriodicLatticeSite Lu)) (Wbg : PeriodicLinkConfiguration SU2 Lu) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (u1 : κ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
    (u2 : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * κ) < r0)
    (hKDc : 192 * (8 * (ell : ℝ) * κ + 8 * e2Majorant (rhoOf ell κ)) ≤ 1 / (2 * (ell : ℝ) ^ 3))
    (hrow : ∀ c : CoarseBond Lu ell, CRowIn ell Lam c → ∃ g : GaugeFn Lu,
      ∀ z ∈ Ball c.1.1 (4 * (1 * ell)), ∀ μ : Fin 3,
        frobNorm (((periodicGaugeTransform g Wbg (z, μ) : SU2) : M2) - 1) ≤ κ) :
    ∃ O : Dset Lu ell Lam → SuTwo → SuTwo, (∀ d x, ‖O d x‖ = ‖x‖) ∧ ∀ w : Dset Lu ell Lam → SuTwo,
      ∑ d, ‖H0 Lam (Q1jet ell Wbg) w d - ((1 : ℝ) / (ell : ℝ) ^ 3) • O d (w d)‖
        ≤ (192 * (8 * ell * κ + 8 * e2Majorant (rhoOf ell κ))) * ∑ d, ‖w d‖ := by
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
  refine ⟨O, fun d x => norm_RMap _ x, fun w => ?_⟩
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


end

theorem rowGauges_class {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell)
    (hT : TorusOK ell M Lu) (hMb : 4 * ell + 141 ≤ 5 * M) (hRM : 21 * M + 2 * ell + 12 ≤ R * M)
    (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S)
    (Lam : Set (PeriodicLatticeSite Lu)) (hL : LambdaOK2 ell M R k S Lam)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (α₀ : ℝ) (hα : 0 < α₀)
    (hU : ClassCoupled ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (α₁ : ℝ) (hα1 : α₁ = (ell : ℝ) ^ 3 * (2 * α₀)) (hsm : KDsmall ell (12 * M * α₁)) :
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
  have hα1pos : 0 < α₁ := by rw [hα1]; positivity
  have hβ0 : 0 ≤ 12 * (M : ℝ) * α₁ := by positivity
  have hreg := hU.2
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
  have hrad : (ell ^ k * (4 * ell) + 8 * ell ^ k) + 128 * ell ^ k + 5 ≤ 5 * (M * ell ^ k) := by
    have h1 : ell ^ k * (4 * ell + 141) ≤ ell ^ k * (5 * M) := Nat.mul_le_mul_left _ hMb
    have e1 : ell ^ k * (4 * ell + 141) = ell ^ k * (4 * ell) + 141 * ell ^ k := by ring
    have e2 : ell ^ k * (5 * M) = 5 * (M * ell ^ k) := by ring
    omega
  obtain ⟨γ, V, hV, hag⟩ := chart_of_class hell (by omega : 0 < M) hS hL1 hy0 c.1.1 (by omega)
    (ell ^ k * (4 * ell) + 8 * ell ^ k) hrad hLu hα hreg
  rw [← hα1] at hV
  obtain ⟨g, A, hgA, hB⟩ := hV
  obtain ⟨hlk, hpl⟩ := AdalyFormal.M1DK.chart_bounds ell M k hell S α₁ V g A _ rfl hgA hB hα1pos.le hsm.h1
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

/-- the `ℓ¹` inverse bound of `H₀` from a ROTATED drift -/
theorem H0inv_l1_rot {ell : ℕ} (hell : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu))
    (Q : (Bond Lu → SuTwo) →ₗ[ℝ] (CoarseBond Lu ell → SuTwo)) (δ : ℝ) (hδ : δ < 1 / (ell : ℝ) ^ 3)
    (O : Dset Lu ell Lam → SuTwo → SuTwo) (hO : ∀ d x, ‖O d x‖ = ‖x‖)
    (hdrift : ∀ w : Dset Lu ell Lam → SuTwo,
      ∑ d, ‖H0 Lam Q w d - ((1 : ℝ) / (ell : ℝ) ^ 3) • O d (w d)‖ ≤ δ * ∑ d, ‖w d‖)
    (hb : Function.Bijective (H0 Lam Q)) (v : Dset Lu ell Lam → SuTwo) :
    ∑ d, ‖H0inv Lam Q v d‖ ≤ (∑ d, ‖v d‖) / (1 / (ell : ℝ) ^ 3 - δ) := by
  set u := H0inv Lam Q v with hu
  have hHu : H0 Lam Q u = v := H0_H0inv Lam _ hb v
  have hpt : ∀ d, ((1 : ℝ) / (ell : ℝ) ^ 3) * ‖u d‖
      ≤ ‖v d‖ + ‖H0 Lam Q u d - ((1 : ℝ) / (ell : ℝ) ^ 3) • O d (u d)‖ := by
    intro d
    have e1 : ((1 : ℝ) / (ell : ℝ) ^ 3) • O d (u d)
        = v d - (H0 Lam Q u d - ((1 : ℝ) / (ell : ℝ) ^ 3) • O d (u d)) := by
      rw [← hHu]; abel
    have e2 : ‖((1 : ℝ) / (ell : ℝ) ^ 3) • O d (u d)‖ = ((1 : ℝ) / (ell : ℝ) ^ 3) * ‖u d‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity), hO]
    have h3 := norm_sub_le (v d) (H0 Lam Q u d - ((1 : ℝ) / (ell : ℝ) ^ 3) • O d (u d))
    rw [← e1, e2] at h3
    exact h3
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) => hpt d)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hdr := hdrift u
  have hpos : 0 < 1 / (ell : ℝ) ^ 3 - δ := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith

/-- `‖h f‖₁ ≤ Σ_{d ∈ Λ'} ‖f d‖ / (ℓ⁻³ − δ)` from a rotated drift -/
theorem hLift_l1_rot {ell : ℕ} (hell : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu))
    (Q : (Bond Lu → SuTwo) →ₗ[ℝ] (CoarseBond Lu ell → SuTwo)) (δ : ℝ) (hδ : δ < 1 / (ell : ℝ) ^ 3)
    (O : Dset Lu ell Lam → SuTwo → SuTwo) (hO : ∀ d x, ‖O d x‖ = ‖x‖)
    (hdrift : ∀ w : Dset Lu ell Lam → SuTwo,
      ∑ d, ‖H0 Lam Q w d - ((1 : ℝ) / (ell : ℝ) ^ 3) • O d (w d)‖ ≤ δ * ∑ d, ‖w d‖)
    (hb : Function.Bijective (H0 Lam Q)) (f : CoarseBond Lu ell → SuTwo) :
    ∑ b : Bond Lu, ‖hLift Lam Q f b‖ ≤ (∑ d : Dset Lu ell Lam, ‖f d.1‖) / (1 / (ell : ℝ) ^ 3 - δ) := by
  have h1 := iotaD_l1 Lam (H0inv Lam Q (rhoD ell Lam f))
  have h2 := H0inv_l1_rot hell Lam Q δ hδ O hO hdrift hb (rhoD ell Lam f)
  calc ∑ b : Bond Lu, ‖hLift Lam Q f b‖
      = ∑ b : Bond Lu, ‖iotaD ell Lam (H0inv Lam Q (rhoD ell Lam f)) b‖ := rfl
    _ ≤ _ := h1
    _ ≤ _ := h2
    _ = (∑ d : Dset Lu ell Lam, ‖f d.1‖) / (1 / (ell : ℝ) ^ 3 - δ) := rfl

open Classical in
/-- one row of `C̃⁽²⁾` from its own gauge -/
theorem C2tilde_row {ell : ℕ} (hell : 0 < ell) (hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1)
    (W : PeriodicLinkConfiguration SU2 Lu) (c : CoarseBond Lu ell) (g : GaugeFn Lu) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hsmall : ∀ z ∈ Ball c.1.1 (4 * (1 * ell)), ∀ μ : Fin 3,
      frobNorm (((periodicGaugeTransform g W (z, μ) : SU2) : M2) - 1) ≤ κ)
    (u2 : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * κ) < r0)
    (hloop : 8 * (ell : ℝ) * κ ≤ 1 / 16) (B : Bond Lu → SuTwo) :
    ‖C2tilde ell W B c‖ ≤ K2s ell * ∑ b : Bond Lu, if b.1 ∈ Ball c.1.1 (4 * (1 * ell)) then ‖B b‖ ^ 2 else 0 := by
  classical
  set W' := periodicGaugeTransform g W with hW'
  set Vc := Vcut1 ell c W' with hVc
  have hVs : ∀ e, frobNorm (((Vc e : SU2) : M2) - 1) ≤ κ := Vcut1_small ell c W' κ hκ0 hsmall
  have hreg1 : RegBg 1 ell Vc := AdalyFormal.NonflatJet.regBg_of_small Nat.one_pos _ κ hκ0 hVs u2
  set B' := gaugeActA g B with hB'
  set Bm : Bond Lu → SuTwo := fun b => if b.1 ∈ Ball c.1.1 (4 * (1 * ell)) then B' b else 0 with hBm
  have e1 : ‖C2tilde ell W B c‖ = ‖C2tilde ell W' B' c‖ := by
    have h := congrFun (AdalyFormal.GaugeCov.C2tilde_gauge ell g W B) c
    rw [h]
    show ‖C2tilde ell W B c‖ = ‖RMap (g c.1.1) (C2tilde ell W B c)‖
    rw [norm_RMap]
  have e2 : C2tilde ell W' B' c = C2tilde ell Vc B' c := by
    have hrow : AdalyFormal.IngredientFamilyR2.C2StepL 1 ell W' (suCoordF B') (c.1.1, c.2)
        = AdalyFormal.IngredientFamilyR2.C2StepL 1 ell Vc (suCoordF B') (c.1.1, c.2) :=
      C2StepL_congr_bg 1 ell one_pos (c.1.1, c.2) (Vcut1_agree ell c W') _
    show (suCoordFInv (AdalyFormal.IngredientFamilyR2.C2StepL 1 ell W' (suCoordF B'))) (c.1.1, c.2)
      = (suCoordFInv (AdalyFormal.IngredientFamilyR2.C2StepL 1 ell Vc (suCoordF B'))) (c.1.1, c.2)
    rw [suCoordFInv_apply_congr hrow]
  have e3 : C2tilde ell Vc B' c = C2tilde ell Vc Bm c := by
    have hag : AgreeX (Ball c.1.1 (4 * (1 * ell))) (suCoordF B') (suCoordF Bm) := by
      intro e he
      have hb : Bm e = B' e := by simp only [hBm]; rw [if_pos he]
      show AdalyFormal.IngredientFamilyR2.fromM2 ((B' e : SuTwo) : M2)
        = AdalyFormal.IngredientFamilyR2.fromM2 ((Bm e : SuTwo) : M2)
      rw [hb]
    have hrow : AdalyFormal.IngredientFamilyR2.C2StepL 1 ell Vc (suCoordF B') (c.1.1, c.2)
        = AdalyFormal.IngredientFamilyR2.C2StepL 1 ell Vc (suCoordF Bm) (c.1.1, c.2) :=
      C2StepL_congr_in 1 ell one_pos Vc (c.1.1, c.2) hag
    show (suCoordFInv (AdalyFormal.IngredientFamilyR2.C2StepL 1 ell Vc (suCoordF B'))) (c.1.1, c.2)
      = (suCoordFInv (AdalyFormal.IngredientFamilyR2.C2StepL 1 ell Vc (suCoordF Bm))) (c.1.1, c.2)
    rw [suCoordFInv_apply_congr hrow]
  have hC := C2tilde_l1 hell hd Vc hreg1 κ hκ0 hVs hloop Bm
  have hone : ‖C2tilde ell Vc Bm c‖ ≤ ∑ c', ‖C2tilde ell Vc Bm c'‖ :=
    Finset.single_le_sum (f := fun c' => ‖C2tilde ell Vc Bm c'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ c)
  have hm : ∑ b : Bond Lu, ‖Bm b‖ ^ 2
      = ∑ b : Bond Lu, if b.1 ∈ Ball c.1.1 (4 * (1 * ell)) then ‖B b‖ ^ 2 else 0 := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [hBm]
    split_ifs
    · show ‖RMap (g b.1) (B b)‖ ^ 2 = _
      rw [norm_RMap]
    · simp
  rw [e1, e2, e3]
  calc ‖C2tilde ell Vc Bm c‖ ≤ ∑ c', ‖C2tilde ell Vc Bm c'‖ := hone
    _ ≤ K2s ell * ∑ b : Bond Lu, ‖Bm b‖ ^ 2 := hC
    _ = _ := by rw [hm]

open Classical in
/-- unit-level multiplicity: every bond lies in the read balls of at most `2187` coarse bonds -/
theorem ball_count_unit {ell : ℕ} (hell : 0 < ell) (hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1) (f : Bond Lu → ℝ)
    (hf : ∀ b, 0 ≤ f b) :
    ∑ c : CoarseBond Lu ell, ∑ b : Bond Lu, (if b.1 ∈ Ball c.1.1 (4 * (1 * ell)) then f b else 0)
      ≤ 2187 * ∑ b : Bond Lu, f b := by
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun b _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ.filter (fun c : CoarseBond Lu ell => b.1 ∈ Ball c.1.1 (4 * (1 * ell)))).card : ℝ) ≤ 2187 := by
    have h1 : (Finset.univ.filter (fun c : CoarseBond Lu ell => b.1 ∈ Ball c.1.1 (4 * (1 * ell)))).card
        ≤ ((Finset.univ.filter (fun y : PeriodicLatticeSite Lu => (∀ ν, ell ∣ (y ν).val) ∧ pdist y b.1 ≤ 4 * (1 * ell)))
            ×ˢ (Finset.univ : Finset (Fin 3))).card := by
      refine Finset.card_le_card_of_injOn (fun c => (c.1.1, c.2)) ?_ ?_
      · intro c hc
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hc
        simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod, Set.mem_setOf_eq,
          Finset.coe_univ, Set.mem_univ, and_true]
        refine ⟨fun ν => Nat.dvd_of_mod_eq_zero ((AdalyFormal.Balaban.AdmissibleSubspace.mem_CoarseLattice.mp c.1.2) ν), ?_⟩
        exact hc
      · intro c _ c' _ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Subtype.ext h.1) h.2
    have h2 := AdalyFormal.M1DStrat.card_ball_coarse_le ell hell hd (4 * (1 * ell)) b.1
    have h3 : 2 * (4 * (1 * ell)) / ell + 1 = 9 := by
      rw [show 2 * (4 * (1 * ell)) = 8 * ell by ring, Nat.mul_div_cancel _ hell]
    rw [h3] at h2
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h1
    have : (Finset.univ.filter (fun c : CoarseBond Lu ell => b.1 ∈ Ball c.1.1 (4 * (1 * ell)))).card ≤ 2187 := by
      have := Nat.mul_le_mul_right 3 h2
      omega
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right hcard (hf b)

/-- **`hKD` at the printed class** (per-row gauges; no global gauge) -/
theorem hKD_class {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell)
    (hT : TorusOK ell M Lu) (hMb : 4 * ell + 141 ≤ 5 * M) (hRM : 21 * M + 2 * ell + 12 ≤ R * M)
    (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S)
    (Lam : Set (PeriodicLatticeSite Lu)) (hL : LambdaOK2 ell M R k S Lam)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (α₀ : ℝ) (hα : 0 < α₀)
    (hU : ClassCoupled ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (α₁ : ℝ) (hα1 : α₁ = (ell : ℝ) ^ 3 * (2 * α₀)) (hsm : KDsmall ell (12 * M * α₁))
    (B : BondFnL2 Lu) :
    ∑ e, ‖((gparams ell k Lu (by omega) S U a Lam).D2in B) e‖ ≤ 2187 * KDfree ell * ‖B‖ ^ 2 := by
  classical
  have hell : 0 < ell := by omega
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set P := gparams ell k Lu (by omega) S U a Lam with hP
  have hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1 := hT.1
  have hα1pos : 0 < α₁ := by rw [hα1]; positivity
  have hβ0 : 0 ≤ 12 * (M : ℝ) * α₁ := by positivity
  set κ : ℝ := kapM1 (12 * M * α₁) with hκ
  have hκ0 : 0 ≤ κ := AdalyFormal.M1DK.kapM1_nonneg hβ0
  have hrows := rowGauges_class hell2 hT hMb hRM S hS Lam hL U a α₀ hα hU α₁ hα1 hsm
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

#print axioms AdalyFormal.M2OpLayer.rot_drift_of_row_gauges
#print axioms AdalyFormal.M2OpLayer.rowGauges_class
#print axioms AdalyFormal.M2OpLayer.H0inv_l1_rot
#print axioms AdalyFormal.M2OpLayer.hLift_l1_rot
#print axioms AdalyFormal.M2OpLayer.C2tilde_row
#print axioms AdalyFormal.M2OpLayer.ball_count_unit
#print axioms AdalyFormal.M2OpLayer.hKD_class
