import MXQ_A
import MXQ_Orig
import MXQ_Z
import MXQ_AC_SK3
import MXQ_AU_SK3
import MXQ_AC_SK6a
import MXQ_AC_MZ5
import MXQ_AC_OL8
import MXQ_AC_OL10
import MXQ_AC_MR5
import MXQ_Base
import TT_B

/-!
# TT_B -- the field chain, cube-factor-FREE and uniform in `m, R` (lane total_20261017)

Text copy of `UnifMax.UMB` (lane unif_20261016) with (i) the AllC lane's c-free substitutions of `AU_SV3b` (`AU_SK3.w4_classU`, `AU_OL3`-based `hKD_classU`
with the region/ball-chart hypothesis, threshold WITHOUT `3 fc`, `beta0 ell/(2K)`, extra conjunct `BallChartsAt .. C ..` and constant `C ≤ K` in `FieldsKT`);
(ii) the cube factor `fc ≥ 10` quantified AFTER the constants (shapes of `TT_A`), not a section parameter.  Bodies after the choices are unchanged otherwise.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false

namespace MXQ.Total
open MXQ.AllC (CF CubeFamOK)
open AdalyFormal.Total
open AdalyFormal.AllC MXQ.AllC
section t1
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK pdist HT CubeBond)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log)
open AdalyFormal.M2Glue2 (GChart chA chA_HT chA_exp frobNorm_chA chA_sub log_le log_lip)
open AdalyFormal.Balaban.Bch2 (frobNorm_smul)
open AdalyFormal.Balaban.RegularityGap (frobNorm_negI_smul)
open AdalyFormal.OneGap
theorem ballChartsT_of_G (hG : BallChartsGT) : BallChartsT := by
  intro ell hell
  obtain ⟨m₁, R₁, C, s, hs, hfU⟩ := hG ell hell
  have hC : 1 ≤ C := (hfU (MXQ.AllC.famC 10) (MXQ.AllC.famC_ok' le_rfl) m₁ le_rfl R₁ le_rfl).1
  have hpi := Real.pi_pos
  have hC0 : 0 < C := by linarith
  refine ⟨m₁, R₁, (Real.pi / 2) * C + 1, min s (1 / C), lt_min hs (by positivity), fun Fm hFm m hm1 R hR1 => ⟨by nlinarith, ?_⟩⟩
  obtain ⟨-, hf⟩ := hfU Fm hFm m hm1 R hR1
  intro k hk Lu α₀ hα hsα hT S hS Lam hLam U hcc hU1 j hjk w hw r hr7 hnw hin hout hsm
  have hs1 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s := hsα.trans (min_le_left _ _)
  have hs2 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ 1 / C := hsα.trans (min_le_right _ _)
  obtain ⟨g, hg⟩ := hf k hk Lu α₀ hα hs1 hT S hS Lam hLam U hcc hU1 j hjk w hw r hr7 hnw hin hout hsm
  have hell0 : 0 < ell := by omega
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  set a0 : ℝ := ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ with ha0
  have ha0pos : 0 < a0 := by
    have : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by
      have : 0 < ell ^ m := pow_pos hell0 m
      exact_mod_cast this
    rw [ha0]; positivity
  have hX : ((ell : ℝ) ^ (j - 1))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by exact_mod_cast hell0)
  have hX0 : 0 < ((ell : ℝ) ^ (j - 1))⁻¹ := by positivity
  have hCa : C * a0 ≤ 1 := by
    have : a0 ≤ 1 / C := by
      rw [ha0]
      have e : ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ = (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ := by norm_num
      rw [e]; exact hs2
    rw [le_div_iff₀ hC0] at this; linarith
  refine regionChart_of_gchart (f := 12) (α := ((Real.pi / 2) * C + 1) * α₀) hell0 hη ?_ hg ?_ ?_
  · calc C * (a0 * ((ell : ℝ) ^ (j - 1))⁻¹) ≤ C * (a0 * 1) := by gcongr
      _ ≤ 1 := by linarith
  · have e : (12 : ℕ) * ((ell ^ m : ℕ) : ℝ) * (((Real.pi / 2) * C + 1) * α₀)
        = ((Real.pi / 2) * C + 1) * a0 := by rw [ha0]; ring
    rw [e]
    have : 0 < a0 * ((ell : ℝ) ^ (j - 1))⁻¹ := by positivity
    nlinarith
  · have e : (12 : ℕ) * ((ell ^ m : ℕ) : ℝ) * (((Real.pi / 2) * C + 1) * α₀)
        = ((Real.pi / 2) * C + 1) * a0 := by rw [ha0]; ring
    rw [e]
    have : 0 < a0 * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 := by positivity
    nlinarith


end t1

section t2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK pdist)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1Site AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar)
open AdalyFormal.M2Skel (SiteS1 RowBound alpha1)
open AdalyFormal.OneGap
theorem fieldsKT_of_ball (hB : BallChartsT) {ell : ℕ} (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) : FieldsKT ell (by omega) a := by
  obtain ⟨m₁B, R₁B, C, sB, hsB, hBU⟩ := hB ell hell
  have hC1 : 1 ≤ C := (hBU (MXQ.AllC.famC 10) (MXQ.AllC.famC_ok' le_rfl) m₁B le_rfl R₁B le_rfl).1
  obtain ⟨s0, hs0, hwin⟩ := AdalyFormal.M2F123.window ell hell
  obtain ⟨W₀, hW₀, ε1, hε1, a₁, ha₁, hN⟩ := AdalyFormal.M1W4Num.w4Num_exists ell hell a ha
  obtain ⟨ρ1, hρ1, hq6⟩ := qsInj_exitfree ell hell
  have hell0 : 0 < ell := by omega
  have hC3 : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  have hC3' : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hell0)
  have hCpos : (0 : ℝ) < C := by linarith
  have hKpos : (0 : ℝ) < (ell : ℝ) ^ 3 * C := by positivity
  have hK1 : (1 : ℝ) ≤ (ell : ℝ) ^ 3 * C := by nlinarith
  have hpi := Real.pi_pos
  refine ⟨0, max m₁B 11, max R₁B (max (max 26 (1000 * ell)) (max (max (17 * ell) W₀) (37 * ell ^ 2))),
    (ell : ℝ) ^ 3 * C, hK1, C, hC1, (by nlinarith [hC3', hCpos]), min sB (min (min s0 (a₁ / (2 * (ell : ℝ) ^ 3)) / ((ell : ℝ) ^ 3 * C))
      (ρ1 / ((4 * Real.pi + 4) * C))),
    lt_min hsB (lt_min (div_pos (lt_min hs0 (by positivity)) hKpos) (div_pos hρ1 (by positivity))), fun Fm hFm m hm R hR => ?_⟩
  haveI : CubeFamOK Fm := hFm
  have hmB : m₁B ≤ m := le_trans (le_max_left _ _) hm
  have hm9 : 11 ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨-, hBf⟩ := hBU Fm hFm m hmB R (le_trans (le_max_left _ _) hR)
  have hR26 : 26 ≤ R := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hR
  have hR37 : 37 * ell ^ 2 ≤ R := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hR
  have hR1000 : 1000 * ell ≤ R := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hR
  have hR17 : 17 * ell ≤ R := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) (le_max_right _ _))) hR
  have hRW : W₀ ≤ R := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) (le_max_right _ _))) hR
  have hM := AdalyFormal.M2F123.pow_ge (ell := ell) hell (by omega : 6 ≤ m)
  have hM0 : 0 < ell ^ m := by omega
  have hM300 : 2002 ≤ ell ^ m := by
    have h1 : 2 ^ 11 ≤ ell ^ 11 := Nat.pow_le_pow_left hell 11
    have h2 : ell ^ 11 ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm9
    omega
  have hRM1000 : 1000 * ell ≤ R * ell ^ m := le_trans hR1000 (Nat.le_mul_of_pos_right R hM0)
  intro k hk Lu α₀ hα hsα hT S hS hthick Lam hLam U hcc hU1
  have hsB' : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sB := le_trans hsα (min_le_left _ _)
  have hs2 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ min s0 (a₁ / (2 * (ell : ℝ) ^ 3)) / ((ell : ℝ) ^ 3 * C) :=
    le_trans hsα (le_trans (min_le_right _ _) (min_le_left _ _))
  have hs6 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ ρ1 / ((4 * Real.pi + 4) * C) :=
    le_trans hsα (le_trans (min_le_right _ _) (min_le_right _ _))
  have hs3 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * ((ell : ℝ) ^ 3 * (C * α₀)) ≤ min s0 (a₁ / (2 * (ell : ℝ) ^ 3)) := by
    have := (le_div_iff₀ hKpos).1 hs2
    calc (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * ((ell : ℝ) ^ 3 * (C * α₀))
        = (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * ((ell : ℝ) ^ 3 * C) := by ring
      _ ≤ _ := this
  have hBat := hBf k hk Lu α₀ hα hsB' hT S hS Lam hLam U hcc hU1
  have hKα : ((ell : ℝ) ^ 3 * C) * α₀ = (ell : ℝ) ^ 3 * (C * α₀) := by ring
  set β : ℝ := (ell : ℝ) ^ 3 * (C * α₀) with hβ
  have hβpos : 0 < β := by rw [hβ]; positivity
  refine ⟨?_, hBat⟩
  unfold FieldsKAtAC
  rw [hKα]
  obtain ⟨h5, hL⟩ := AdalyFormal.M2F123.torus_facts (k := k) hell (by omega) hT
  have hs0' : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * β ≤ s0 := le_trans hs3 (min_le_left _ _)
  have hs1' : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * β ≤ a₁ / (2 * (ell : ℝ) ^ 3) := le_trans hs3 (min_le_right _ _)
  obtain ⟨ha1, hsm4, hsmA, hrr⟩ := hwin (ell ^ m) β hβpos.le hs0'
  have hRM : 18 ≤ R * ell ^ m := by nlinarith
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hR1 : 1 ≤ R := by omega
  have hbc := blockCharts_ball hell hS hM300 hRM1000 hL hC1 hα hη hBat
  have hrc := rowCharts_ball hell hS hM300 hRM1000 hL hC1 hα hη hBat
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact AdalyFormal.OneGap12.siteS1_of_charts12 hell hS hRM (AdalyFormal.M1GaugeW4.hbig_of ell k Lu h5) hL hη hβpos.le ha1 hsm4 U hbc a ha
  · have ha2 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * (alpha1 ell β) ≤ a₁ := by
      unfold alpha1
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (ell : ℝ) ^ 3)).1 hs1'
      nlinarith
    obtain ⟨-, -, hW4⟩ := hN (ell ^ m) R hM0 hRW (alpha1 ell β) (by unfold alpha1; positivity) ha2
    exact AdalyFormal.OneGap12.rowBound_of_charts12 hell hS hRM (AdalyFormal.M1GaugeW4.hbig_of ell k Lu h5) hL hR1 (by omega) hη
      hβpos.le ha1 hsm4 a ha ε1 hW4 U hbc
  · have hroom : 17 * ell ≤ R * ell ^ m := le_trans hR17 (Nat.le_mul_of_pos_right R hM0)
    exact AdalyFormal.OneGap12.massComm_of_charts12 hell hS hM0 (by omega) (by omega) hroom (fun μ => by have := h5 μ; omega)
      hη hβpos ha1 hsm4 hsmA hrr a ha.le U hrc
  · intro d _ hdM
    have hLthick : ∀ σ : Fin 3, 13 * (ell ^ m * ell ^ k) ≤ scaleUp ell k Lu σ + 1 := by
      intro σ
      rw [AdalyFormal.M2UnitCharts.scaleUp_succ ell k Lu hell0 σ]
      have := Nat.mul_le_mul_right (ell ^ k) (hthick σ)
      calc 13 * (ell ^ m * ell ^ k) = 13 * ell ^ m * ell ^ k := by ring
        _ ≤ _ := this
    refine patchCharts_monoAC hη ?_ (patchCharts_of_ballAC hS hM0 hell (by omega) (by omega) hdM hLthick hBat)
    have hMr : (0 : ℝ) ≤ ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) := by positivity
    have : C * α₀ ≤ (ell : ℝ) ^ 3 * (C * α₀) := by
      have : 0 ≤ C * α₀ := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_left this hMr
  · intro hex
    have hM73 : 73 * ell + 2 ≤ ell ^ m := by
      have h1 : ell ^ 11 ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm9
      have h2 : ell ^ 11 = ell * ell ^ 10 := by ring
      have h3 : 2 ^ 10 ≤ ell ^ 10 := Nat.pow_le_pow_left hell 10
      nlinarith
    have hT3 : ∀ μ, 3 ≤ Lu μ + 1 := fun μ => by have := h5 μ; omega
    refine hq6 hS hM73 hR37 (by omega) (le_trans hR17 (Nat.le_mul_of_pos_right R hM0)) hex hT3 hC1 hα hη ?_ hBat a Lam
    have hCpos' : (0 : ℝ) < (4 * Real.pi + 4) * C := by positivity
    have := (le_div_iff₀ hCpos').1 hs6
    have e : (4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * (C * α₀))
        = 12 * ((ell ^ m : ℕ) : ℝ) * α₀ * ((4 * Real.pi + 4) * C) := by push_cast; ring
    rw [e]
    exact this


end t2

section t3
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.NonflatJet (rhoOf r0)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.BondComposite (thetaOf rr)
open AdalyFormal.TowerLoc (delStar Ctheta)
open AdalyFormal.W6 (nD nD_nonneg CE CE_pos)
open AdalyFormal.M2W6 (mult0 EU EU_mem Tlin Tlin_apply)
open AdalyFormal.M1DStrat (gradWU)
open AdalyFormal.OneGap (BallChartsAt epsC SstarC numerics_epsC epsC_nonneg)
open AdalyFormal.M2RightInv
theorem classRightInvCovT (hB : BallChartsGT) : ClassRightInvCovT := by
  intro ell hell2 a ha
  have hell0 : 0 < ell := by omega
  have hpi := Real.pi_pos
  obtain ⟨m₁B, R₁B, C, sB, hsB, hBU⟩ := ballChartsT_of_G hB ell hell2
  have hC1 : 1 ≤ C := (hBU (MXQ.AllC.famC 10) (MXQ.AllC.famC_ok' le_rfl) m₁B le_rfl R₁B le_rfl).1
  obtain ⟨ρs, hρs, hnum⟩ := num_RI ell hell2
  have hCpos : (0 : ℝ) < C := by linarith
  have hq : (0 : ℝ) < (4 * Real.pi + 4) * C := by positivity
  refine ⟨m₁B + 8, cWR ell, cGR ell, cWR_nonneg ell, cGR_nonneg ell,
    R₁B + 37 * ell ^ 2 + 45 * ell + 4, min sB (ρs / ((4 * Real.pi + 4) * C)), lt_min hsB (div_pos hρs hq),
    fun Fm hFm m hm R hR => ?_⟩
  haveI : CubeFamOK Fm := hFm
  set M : ℕ := ell ^ m with hMdef
  have hM73 : 73 * ell + 2 ≤ M := by
    have h1 : 2 ^ 7 ≤ ell ^ 7 := Nat.pow_le_pow_left hell2 7
    have h2 : ell ^ 8 ≤ ell ^ m := Nat.pow_le_pow_right hell0 (by omega)
    have h3 : ell ^ 8 = ell * ell ^ 7 := by ring
    have h4 : ell * 2 ^ 7 ≤ ell * ell ^ 7 := Nat.mul_le_mul_left ell h1
    rw [hMdef]; omega
  have hM1 : 1 ≤ M := by omega
  obtain ⟨-, hBf⟩ := hBU Fm hFm m (by omega) R (by omega)
  intro k hk Lu α₀ hα hsα hT S hS hthick Lam hL U hU hloc u
  have hsB' : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sB := hsα.trans (min_le_left _ _)
  have hsρ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ ρs / ((4 * Real.pi + 4) * C) := hsα.trans (min_le_right _ _)
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hBat := hBf k hk Lu α₀ hα hsB' hT S hS Lam hL U hU hloc
  have hR37 : 37 * ell ^ 2 ≤ R := by omega
  have hR8 : 8 * ell ≤ R := by nlinarith
  have hRM : 45 * ell + 4 ≤ R * M := le_trans (by omega) (Nat.le_mul_of_pos_right R (by omega))
  have hroom : 17 * ell ≤ R * M := le_trans (by omega) hRM
  have hT3 : ∀ μ, 3 ≤ Lu μ + 1 := fun μ => by have := hthick μ; omega
  have hρ : (4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀)) ≤ ρs := by
    have e : (4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀))
        = ((4 * Real.pi + 4) * C) * ((12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀) := by rw [hMdef]; push_cast; ring
    rw [e]
    have := (le_div_iff₀' hq).1 hsρ
    linarith
  have hρ1 := (hnum _ (by positivity) hρ).1
  have ha1 : ((12 : ℕ) : ℝ) * M * (C * α₀) ≤ 1 := by
    have h4 : (1 : ℝ) ≤ 4 * Real.pi + 4 := by linarith
    have h0 : 0 ≤ ((12 : ℕ) : ℝ) * M * (C * α₀) := by positivity
    nlinarith
  exact rightInv_cfg hell2 hS hM73 hR37 hR8 hroom hRM (by omega) hT3 hη (by positivity) ha1 hBat ρs hnum hρ a Lam u


end t3

section t4
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1IMS AdalyFormal.M1GaugeW4 AdalyFormal.TowerLoc
open AdalyFormal.M1Site
open AdalyFormal.M1DStrat (gradWU etaS hext_of_rightinv_cov)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.M2Skel (SiteS1 alpha1)
open AdalyFormal.M2OpLayer
theorem classRightInvT_of_cov (hB : BallChartsGT) (hcov : ClassRightInvCovT) : ClassRightInvT := by
  intro ell hell2 a ha
  have hell0 : 0 < ell := by omega
  have hell1 : 1 ≤ ell := by omega
  have hlR : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have hpi := Real.pi_pos
  obtain ⟨m₁B, R₁B, C, sB, hsB, hBU⟩ := ballChartsT_of_G hB ell hell2
  have hC1 : 1 ≤ C := (hBU (MXQ.AllC.famC 10) (MXQ.AllC.famC_ok' le_rfl) m₁B le_rfl R₁B le_rfl).1
  obtain ⟨m₁c, cW, cG, hcW, hcG, R₁c, sc, hsc, hcU⟩ := hcov ell hell2 a ha
  obtain ⟨s0, hs0, hwin⟩ := AdalyFormal.M2F123.window ell hell2
  obtain ⟨W₀, hW₀, ε1, hε1, a₁, ha₁, hN⟩ := AdalyFormal.M1W4Num.w4Num_exists ell hell2 a ha
  set cb : ℝ := (1 / 2) / max 6 (16 / (3 * a)) with hcbdef
  have hmx : (0 : ℝ) < max 6 (16 / (3 * a)) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hcb : 0 < cb := by rw [hcbdef]; positivity
  set ηb : ℝ := etaB ell cb with hηb
  set νb : ℝ := 2 * ((17 / Real.sqrt 2) * 12 * (1 * (ell : ℝ) ^ 4)) with hνb
  have hηb0 : 0 ≤ ηb := by
    rw [hηb]; unfold etaB
    have : 0 ≤ Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell) - 1 := by
      have : 0 ≤ 2 * (ell : ℝ) ^ 2 * Real.log ell := by have := Real.log_nonneg hlR; positivity
      linarith [Real.add_one_le_exp (2 * (ell : ℝ) ^ 2 * Real.log ell)]
    positivity
  have hνb0 : 0 ≤ νb := by rw [hνb]; positivity
  have hCpos : (0 : ℝ) < C := by linarith
  set K : ℝ := (ell : ℝ) ^ 3 * C with hKdef
  have hKpos : 0 < K := by positivity
  set c₁ : ℝ := (4 * Real.pi + 4) * (2 * (ell : ℝ) ^ 3 * K) with hc₁
  set c₂ : ℝ := 30 * ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) with hc₂
  have hc₁0 : 0 < c₁ := by positivity
  have hc₂0 : 0 < c₂ := by positivity
  refine ⟨m₁B + m₁c + 11, (1 + ηb) * (45 * cG) / a + νb * cW / a + (1 + ηb), add_pos_of_nonneg_of_pos (add_nonneg
    (div_nonneg (mul_nonneg (by linarith) (by positivity)) ha.le) (div_nonneg (mul_nonneg hνb0 hcW) ha.le)) (by linarith),
    R₁B + R₁c + W₀ + 1000 * ell + 17 * ell,
    min sc (min sB (min (s0 / K) (min (a₁ / (2 * (ell : ℝ) ^ 3 * K)) (1 / (c₂ * c₁))))),
    lt_min hsc (lt_min hsB (lt_min (by positivity) (lt_min (by positivity) (by positivity)))),
    fun Fm hFm m hm R hR => ?_⟩
  haveI : CubeFamOK Fm := hFm
  have hm11 : 11 ≤ m := by omega
  set M : ℕ := ell ^ m with hMdef
  have hM2002 : 2002 ≤ M := by
    have h1 : 2 ^ 11 ≤ ell ^ 11 := Nat.pow_le_pow_left hell2 11
    have h2 : ell ^ 11 ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm11
    omega
  have hM0 : 0 < M := by omega
  have hM1 : 1 ≤ M := by omega
  have hR1 : 1 ≤ R := by omega
  have hR8 : 8 * ell ≤ R := by omega
  have hRW : W₀ ≤ R := by omega
  have hR1000 : 1000 * ell ≤ R := by omega
  obtain ⟨-, hBf⟩ := hBU Fm hFm m (by omega) R (by omega)
  have hcf := hcU Fm hFm m (by omega) R (by omega)
  have hRM1000 : 1000 * ell ≤ R * M := le_trans hR1000 (Nat.le_mul_of_pos_right R hM0)
  have hRM18 : 18 ≤ R * M := by omega
  intro k hk Lu α₀ hα hsα hT S hS hthick Lam hL U hU hloc
  set t : ℝ := (12 : ℝ) * (M : ℝ) * α₀ with htdef
  have hsα0 : t ≤ min sc (min sB (min (s0 / K) (min (a₁ / (2 * (ell : ℝ) ^ 3 * K)) (1 / (c₂ * c₁))))) := hsα
  have ht0 : 0 ≤ t := by positivity
  have hsc' : t ≤ sc := hsα0.trans (min_le_left _ _)
  have hsB' : t ≤ sB := hsα0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs3 : t ≤ s0 / K := hsα0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs4 : t ≤ a₁ / (2 * (ell : ℝ) ^ 3 * K) :=
    hsα0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hs5 : t ≤ 1 / (c₂ * c₁) :=
    hsα0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  set β : ℝ := (ell : ℝ) ^ 3 * (C * α₀) with hβdef
  have hβpos : 0 < β := by positivity
  have hβK : β = K * α₀ := by rw [hβdef, hKdef]; ring
  have htβ : (12 : ℝ) * M * β = K * t := by rw [hβK, htdef]; ring
  set α1 : ℝ := alpha1 ell β with hα1def
  have hα1pos : 0 < α1 := by rw [hα1def]; unfold alpha1; positivity
  have htα1 : (12 : ℝ) * M * α1 = 2 * (ell : ℝ) ^ 3 * K * t := by
    rw [hα1def]; unfold alpha1; rw [hβK, htdef]; ring
  have hβs0 : (12 : ℝ) * M * β ≤ s0 := by
    rw [htβ]; have := (le_div_iff₀ hKpos).1 hs3; linarith
  have hα1a₁ : (12 : ℝ) * M * α1 ≤ a₁ := by
    rw [htα1]; have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (ell : ℝ) ^ 3 * K)).1 hs4; linarith
  have hr_eq : rho1 12 M α1 = c₁ * t := by
    unfold rho1; rw [hc₁]; push_cast; rw [show (12 : ℝ) * M * α1 = 2 * (ell : ℝ) ^ 3 * K * t from htα1]; ring
  have hr0 : 0 ≤ rho1 12 M α1 := rho1_nonneg 12 M α1 hα1pos.le
  have hct : c₁ * t ≤ 1 / c₂ := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < c₂ * c₁)).1 hs5
    rw [le_div_iff₀ hc₂0]; nlinarith
  have hc₂1 : (1 : ℝ) ≤ c₂ := by
    rw [hc₂]; have : (1 : ℝ) ≤ ell := hlR; nlinarith [sq_nonneg (ell : ℝ)]
  have hr1 : rho1 12 M α1 ≤ 1 := by
    rw [hr_eq]; refine hct.trans ?_; rw [div_le_one hc₂0]; exact hc₂1
  have hrT : rhoT ell 12 M α1 ≤ 1 / 30 := by
    unfold rhoT
    rw [hr_eq]
    have e : ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * (c₁ * t) = c₂ * (c₁ * t) / 30 := by rw [hc₂]; ring
    rw [e, div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 30)]
    have := mul_le_mul_of_nonneg_left hct hc₂0.le
    rw [mul_one_div_cancel hc₂0.ne'] at this
    linarith
  have hrT0 : 0 ≤ rhoT ell 12 M α1 := rhoT_nonneg ell 12 M α1 hα1pos.le
  have hcs : cb ≤ csOf a (rhoT ell 12 M α1) := by
    unfold csOf
    rw [hcbdef]
    apply div_le_div_of_nonneg_right _ hmx.le
    have : rhoT ell 12 M α1 ^ 2 ≤ (1 / 30) ^ 2 := pow_le_pow_left₀ hrT0 hrT 2
    nlinarith
  obtain ⟨h5, hLs⟩ := AdalyFormal.M2F123.torus_facts (k := k) hell2 (by omega : 6 ≤ m) hT
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hBat := hBf k hk Lu α₀ hα hsB' hT S hS Lam hL U hU hloc
  obtain ⟨ha1w, hsm4, -, -⟩ := hwin M β hβpos.le hβs0
  have hbc := AdalyFormal.OneGap.blockCharts_ball hell2 hS hM2002 hRM1000 hLs hC1 hα hη hBat
  obtain ⟨-, -, hNum⟩ := hN M R hM0 hRW α1 hα1pos.le hα1a₁
  have hHc : SiteS1 ell k S U a (csOf a (rhoT ell 12 M α1)) :=
    AdalyFormal.OneGap12.siteS1_of_charts12 hell2 hS hRM18 (AdalyFormal.M1GaugeW4.hbig_of ell k Lu h5) hLs hη
      hβpos.le ha1w hsm4 U hbc a ha
  have h216 := (rhoT_smalls ell 12 M α1 hα1pos.le hell1 hsm4).1
  have hW1 : 1 ≤ R * M * ell := by
    have : 1 ≤ R * M := by nlinarith
    nlinarith
  have hp := AdalyFormal.M2Skel.hatPack_of_S1 (W := R * M * ell) hell1 ha hNum h216 hHc
  have hK1 : (1 : ℝ) ≤ K := by
    have : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ hlR
    rw [hKdef]; nlinarith
  have hαβ : α₀ ≤ β := by rw [hβK]; nlinarith
  have hUb := hU.mono hη.le hαβ
  have hb1 : ((12 : ℕ) : ℝ) * M * β ≤ 1 := by
    have h1 : (12 : ℝ) * M * β ≤ 12 * M * ((ell : ℝ) ^ 3 * (2 * β)) := by
      have : β ≤ (ell : ℝ) ^ 3 * (2 * β) := by
        have : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ hlR
        nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have := h1.trans ha1w
    simpa using this
  have hreg : HolRegime S ell k U (rho1 12 M α1) := MXQ.M2Skel.holRegime_rho1ACΦ hell1 hS hη hβpos.le hb1 hUb
  have hR := hcf k hk Lu α₀ hα hsc' hT S hS hthick Lam hL U hU hloc
  intro v
  obtain ⟨g, hg, hE⟩ := hext_of_rightinv_cov hS hell2 hR1 hM1 hW1 le_rfl hell0 U a _ hp (rho1 12 M α1) hr0 hreg 1
    one_pos Lam cW cG hcW hcG hR v
  refine ⟨g, hg, hE.trans ?_⟩
  have hηle := etaS_le_etaB ell (R * M * ell) hell1 hW1 hcb hcs hr0 hr1
  have hνle : 2 * ((17 / Real.sqrt 2) * 12 * (rho1 12 M α1 * (ell : ℝ) ^ 4)) ≤ νb := by
    rw [hνb]; gcongr
  have hN0 : 0 ≤ ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v‖ ^ 2 := sq_nonneg _
  refine mul_le_mul_of_nonneg_right ?_ hN0
  have h1 : (1 + etaS ell (R * M * ell) (csOf a (rhoT ell 12 M α1)) (rho1 12 M α1) 1) * (45 * cG) / a
      ≤ (1 + ηb) * (45 * cG) / a := by
    apply div_le_div_of_nonneg_right _ ha.le
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h2 : 2 * ((17 / Real.sqrt 2) * 12 * (rho1 12 M α1 * (ell : ℝ) ^ 4)) * cW / a ≤ νb * cW / a := by
    apply div_le_div_of_nonneg_right _ ha.le
    exact mul_le_mul_of_nonneg_right hνle hcW
  linarith


end t4

section t5
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1IMS AdalyFormal.M1GaugeW4 AdalyFormal.TowerLoc
open AdalyFormal.M1Site
open AdalyFormal.M1DStrat
open AdalyFormal.M1DStrat.DQ (DQSmall K2strat dqSmall_exists K2strat_mono)
open AdalyFormal.M1DK (KDsmall beta0 beta0_pos KDsmall_of_le)
open AdalyFormal.M1Assembly (cwW4_lower KG_small)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.M2Skel (SiteS1 RowBound alpha1)
open AdalyFormal.M2DLayer (Ageo)
open AdalyFormal.M2OpLayer
theorem opLayerThickT_of (hB : BallChartsGT) (hRI : ClassRightInvT) : OpLayerThickT := by
  intro ell hell2 a ha
  have hell0 : 0 < ell := by omega
  have hell1 : 1 ≤ ell := by omega
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell0
  have hlR : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have hlg : 0 ≤ Real.log ell := Real.log_nonneg hlR
  have hpi := Real.pi_pos
  -- (ℓ, a)-constants
  obtain ⟨m₁B, R₁B, C, sB, hsB, hBU⟩ := ballChartsT_of_G hB ell hell2
  have hC1 : 1 ≤ C := (hBU (MXQ.AllC.famC 10) (MXQ.AllC.famC_ok' le_rfl) m₁B le_rfl R₁B le_rfl).1
  obtain ⟨m₁R, bN, hbN, R₁R, sR, hsR, hRU⟩ := hRI ell hell2 a ha
  obtain ⟨s0, hs0, hwin⟩ := AdalyFormal.M2F123.window ell hell2
  obtain ⟨W₀, hW₀, ε1, hε1, a₁, ha₁, hN⟩ := AdalyFormal.M1W4Num.w4Num_exists ell hell2 a ha
  obtain ⟨cW, hcW, a0P, ha0P, D, hD, hDle, hw4⟩ := MXQ.M2Skel.w4_classUΦ hell2 ha
  have hε1' : ε1 < 1 := by
    obtain ⟨-, -, h0⟩ := hN 1 W₀ one_pos le_rfl 0 le_rfl (by simpa using ha₁.le)
    have h := h0.hη
    have hr : rho1 12 1 0 = 0 := by simp [rho1]
    rw [hr] at h
    unfold etaC nuC at h
    simpa using h
  obtain ⟨δc, hδc, c1, hc1, hU1⟩ := AdalyFormal.M1Num.cw_uniform ell hell0 a ε1 1 (min a (cW / 2)) ha hε1 hε1' one_pos
    (lt_min ha (by linarith))
  obtain ⟨β₀, hβ₀, hDQall⟩ := dqSmall_exists ell hell2
  obtain ⟨M₁, hM₁⟩ := KG_small ell δc hδc
  obtain ⟨CHb, hCHb, CWb, hCWb, KWb, hKWb, CH1b, hCH1b, CHB, hCHB, CH1B, hCH1B, δ, hδ, hball⟩ :=
    num_ballB hell2 ha hc1 hbN
  set θ : ℝ := δ / 2 with hθdef
  have hθ : 0 < θ := by positivity
  set Bθ : ℝ := max (2 * (ell : ℝ) ^ 2 * Real.log ell / δ)
    (max (3 * (ell : ℝ) * Real.log ell / δ) (Real.log (2 * (ell : ℝ) ^ 3) / θ)) with hBθ
  have hCpos : (0 : ℝ) < C := by linarith
  set K : ℝ := (ell : ℝ) ^ 3 * C with hKdef
  have hKpos : 0 < K := by positivity
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ hlR
    nlinarith
  -- the constants
  set KH : ℝ := CHB * Real.sqrt (a * ell) with hKHdef
  set KH1 : ℝ := CH1B * Real.sqrt (a * ell) with hKH1def
  have hKH : 0 ≤ KH := by positivity
  have hKH1 : 0 ≤ KH1 := by positivity
  have hDQ0 := hDQall β₀ hβ₀.le le_rfl
  have hK2s0 : 0 ≤ K2strat ell β₀ := by
    unfold K2strat
    have := AdalyFormal.M1DStrat.DQ.K2free_nonneg ell ((1 + 3 * Real.pi) * AdalyFormal.M1DStrat.DQ.alphaQ ell β₀)
      (AdalyFormal.M1DStrat.DQ.thetaK2_lt_of ell _ hDQ0.hK2c)
    positivity
  set K2c : ℝ := 44217 * K2strat ell β₀ with hK2cdef
  have hK2c : 0 ≤ K2c := by positivity
  set CW : ℝ := (ell : ℝ) ^ 2 * CWb with hCWdef
  set KD : ℝ := 2187 * AdalyFormal.DLayer.KDfree ell with hKDdef
  have hKD0 : 0 ≤ KD := by
    unfold AdalyFormal.DLayer.KDfree AdalyFormal.DLayer.K2s at hKDdef; rw [hKDdef]; positivity
  set Cδ : ℝ := 2 * (Real.sqrt (Ageo ell θ) * KH) * (400 * (ell : ℝ) ^ 3) * K2c * Real.exp (2 * (32 * θ * ell))
      * 44217 * ((ell : ℝ) ^ 2 * KWb) with hCδdef
  have hCδ0 : 0 ≤ Cδ := by positivity
  set s : ℝ := min sB (min sR (min (s0 / K) (min (a₁ / (2 * (ell : ℝ) ^ 3 * K)) (min (a0P / K)
    (min (δc / (4 * (ell : ℝ) ^ 3 * K)) (min (δ / (4 * (4 * Real.pi + 4) * (ell : ℝ) ^ 3 * K))
    (min (δ / (2 * (Cδ + 1))) (min (β₀ / (2 * (ell : ℝ) ^ 3 * K)) (min (beta0 ell / (2 * K)) (1 / 4)))))))))) with hsdef
  have hspos : 0 < s := by
    have hb0 := beta0_pos ell hell0
    refine lt_min hsB (lt_min hsR (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by norm_num))))))))))
  refine ⟨m₁B + m₁R + 11 + (D + 64 * ell ^ 2 + 2) + M₁, R₁B + R₁R + 26 + 1000 * ell + 17 * ell + W₀ + 37 * ell ^ 2 + (Nat.ceil Bθ + 1) + (Nat.ceil (1 / δc) + 1), (θ, KH, KH1, K2c, CW, KD), s, hspos, fun Fm hFm m hm R hR => ?_⟩
  haveI : CubeFamOK Fm := hFm
  have hmB : m₁B ≤ m := by omega
  have hmR : m₁R ≤ m := by omega
  have hm11 : 11 ≤ m := by omega
  have hmM : m < ell ^ m := Nat.lt_pow_self (by omega)
  set M : ℕ := ell ^ m with hMdef
  have hM2002 : 2002 ≤ M := by
    have h1 : 2 ^ 11 ≤ ell ^ 11 := Nat.pow_le_pow_left hell2 11
    have h2 : ell ^ 11 ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm11
    omega
  have hM0 : 0 < M := by omega
  have hM1 : 1 ≤ M := by omega
  have hMge : ell ≤ M := by
    calc ell = ell ^ 1 := (pow_one ell).symm
      _ ≤ ell ^ m := Nat.pow_le_pow_right hell0 (by omega)
  have hdM : D + 64 * ell ^ 2 + 2 ≤ M := by omega
  have hKG : AdalyFormal.M1IMS.KG ell M 1 5 < δc := hM₁ M (by omega)
  have hRB' : R₁B ≤ R := by omega
  have hRR' : R₁R ≤ R := by omega
  have hR26 : 26 ≤ R := by omega
  have hR1000 : 1000 * ell ≤ R := by omega
  have hR17 : 17 * ell ≤ R := by omega
  have hRW : W₀ ≤ R := by omega
  have hR1 : 1 ≤ R := by omega
  have hR8 : 8 * ell ≤ R := by omega
  have hRB1 : Nat.ceil Bθ + 1 ≤ R := by omega
  have hRc : Nat.ceil (1 / δc) + 1 ≤ R := by omega
  obtain ⟨-, hBf⟩ := hBU Fm hFm m hmB R hRB'
  have hRf := hRU Fm hFm m hmR R hRR'
  -- room facts
  have hRM1000 : 1000 * ell ≤ R * M := le_trans hR1000 (Nat.le_mul_of_pos_right R hM0)
  have hroom17 : 17 * ell ≤ R * M := by omega
  have hroom18 : 18 * ell ≤ R * M := by omega
  have hRM18 : 18 ≤ R * M := by omega
  have hRMge : (R : ℝ) ≤ (R : ℝ) * M := le_mul_of_one_le_right (by positivity) (by exact_mod_cast hM1)
  have hRBθ : Bθ < (R : ℝ) := by
    have h1 := Nat.le_ceil Bθ
    have h2 : ((Nat.ceil Bθ + 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hRB1
    push_cast at h2
    linarith
  have hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2 := by
    refine exp_tail ell hell1 θ hθ _ ?_
    have h1 : Real.log (2 * (ell : ℝ) ^ 3) / θ ≤ Bθ := (le_max_right _ _).trans (le_max_right _ _)
    linarith
  have hW1 : 1 ≤ R * M * ell := by
    have : 1 ≤ R * M := by nlinarith
    nlinarith
  have hWpos : (0 : ℝ) < ((R * M * ell : ℕ) : ℝ) := by exact_mod_cast (show 0 < R * M * ell by omega)
  have hWge : (R : ℝ) ≤ ((R * M * ell : ℕ) : ℝ) := by
    have e : ((R * M * ell : ℕ) : ℝ) = (R : ℝ) * M * ell := by push_cast; ring
    rw [e]
    calc (R : ℝ) ≤ (R : ℝ) * M := hRMge
      _ ≤ (R : ℝ) * M * ell := le_mul_of_one_le_right (by positivity) hlR
  have hpδ : 2 * (ell : ℝ) ^ 2 * Real.log ell / ((R * M * ell : ℕ) : ℝ) < δ := by
    rw [div_lt_iff₀ hWpos]
    have h1 : 2 * (ell : ℝ) ^ 2 * Real.log ell / δ < ((R * M * ell : ℕ) : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hRBθ hWge)
    rw [div_lt_iff₀ hδ] at h1; linarith
  have hqδ : 3 * (ell : ℝ) * Real.log ell / ((R * M * ell : ℕ) : ℝ) < δ := by
    rw [div_lt_iff₀ hWpos]
    have h1 : 3 * (ell : ℝ) * Real.log ell / δ < ((R * M * ell : ℕ) : ℝ) :=
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) (lt_of_lt_of_le hRBθ hWge)
    rw [div_lt_iff₀ hδ] at h1; linarith
  have hp0 : 0 ≤ 2 * (ell : ℝ) ^ 2 * Real.log ell / ((R * M * ell : ℕ) : ℝ) := by positivity
  have hq0 : 0 ≤ 3 * (ell : ℝ) * Real.log ell / ((R * M * ell : ℕ) : ℝ) := by positivity
  have hxδ' : |((R * M * ell : ℕ) : ℝ)⁻¹| < δc := by
    rw [abs_of_nonneg (inv_nonneg.mpr hWpos.le)]
    have h1 : 1 / δc < (R : ℝ) := by
      have := Nat.lt_of_ceil_lt (by omega : ⌈1 / δc⌉₊ < R)
      exact_mod_cast this
    rw [inv_eq_one_div, div_lt_iff₀ hWpos]
    rw [div_lt_iff₀ hδc] at h1
    nlinarith
  have hKδ : |AdalyFormal.M1IMS.KG ell M 1 5| < δc := by
    rw [abs_of_nonneg (AdalyFormal.M1IMS.KG_nonneg ell M 1 5)]; exact hKG
  refine ⟨⟨hθ, hq, hKH, hKH1, hK2c, by positivity, hKD0⟩, ?_⟩
  intro k hk Lu α₀ hα hsα hT S hS Lam hL U hU hloc hthick
  -- smallness unpacked (t := 12 M α₀)
  set t : ℝ := (12 : ℝ) * (M : ℝ) * α₀ with htdef
  have ht0 : 0 ≤ t := by positivity
  have hsα0 : t ≤ s := hsα
  have hMR : ((ell ^ m : ℕ) : ℝ) = (M : ℝ) := rfl
  have hsB' : t ≤ sB := hsα0.trans (min_le_left _ _)
  have hsR' : t ≤ sR := hsα0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs3 : t ≤ s0 / K := hsα0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs4 : t ≤ a₁ / (2 * (ell : ℝ) ^ 3 * K) := hsα0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hs5 : t ≤ a0P / K := hsα0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hs6 : t ≤ δc / (4 * (ell : ℝ) ^ 3 * K) := hsα0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
  have hs7 : t ≤ δ / (4 * (4 * Real.pi + 4) * (ell : ℝ) ^ 3 * K) := hsα0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))))))
  have hs8 : t ≤ δ / (2 * (Cδ + 1)) := hsα0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))))))
  have hs9 : t ≤ β₀ / (2 * (ell : ℝ) ^ 3 * K) := hsα0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))))))
  have hs10 : t ≤ beta0 ell / (2 * K) := hsα0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))))))
  have hs11 : t ≤ 1 / 4 := hsα0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))))))
  -- β = K α₀, α1 = alpha1 ℓ β
  set β : ℝ := (ell : ℝ) ^ 3 * (C * α₀) with hβdef
  have hβpos : 0 < β := by positivity
  have hβK : β = K * α₀ := by rw [hβdef, hKdef]; ring
  have htβ : (12 : ℝ) * M * β = K * t := by rw [hβK, htdef]; ring
  set α1 : ℝ := alpha1 ell β with hα1def
  have hα1pos : 0 < α1 := by rw [hα1def]; unfold alpha1; positivity
  have htα1 : (12 : ℝ) * M * α1 = 2 * (ell : ℝ) ^ 3 * K * t := by
    rw [hα1def]; unfold alpha1; rw [hβK, htdef]; ring
  have hl3 : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  have hβs0 : (12 : ℝ) * M * β ≤ s0 := by
    rw [htβ]; have := (le_div_iff₀ hKpos).1 hs3; linarith
  have hα1a₁ : (12 : ℝ) * M * α1 ≤ a₁ := by
    rw [htα1]; have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (ell : ℝ) ^ 3 * K)).1 hs4; linarith
  have hβa0P : (12 : ℝ) * M * β ≤ a0P := by
    rw [htβ]; have := (le_div_iff₀ hKpos).1 hs5; linarith
  have hα1δc : |((12 : ℕ) : ℝ) * M * α1| < δc := by
    have e : ((12 : ℕ) : ℝ) * M * α1 = (12 : ℝ) * M * α1 := by norm_num
    rw [e, abs_of_nonneg (by positivity), htα1]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (ell : ℝ) ^ 3 * K)).1 hs6
    nlinarith
  have hr1 : rho1 12 M α1 < δ := by
    have e : rho1 12 M α1 = (4 * Real.pi + 4) * ((12 : ℝ) * M * α1) := by unfold rho1; push_cast; ring
    rw [e, htα1]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (4 * Real.pi + 4) * (ell : ℝ) ^ 3 * K)).1 hs7
    nlinarith
  have hr0 : 0 ≤ rho1 12 M α1 := rho1_nonneg 12 M α1 hα1pos.le
  have hα1β₀ : (12 : ℝ) * M * α1 ≤ β₀ := by
    rw [htα1]; have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (ell : ℝ) ^ 3 * K)).1 hs9; linarith
  have hKDs : KDsmall ell (12 * M * ((ell : ℝ) ^ 3 * (2 * (C * α₀)))) := by
    refine KDsmall_of_le ell hell0 _ (by positivity) ?_
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * K)).1 hs10
    have e : (12 : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * (C * α₀))) = t * (2 * K) := by rw [htdef, hKdef]; ring
    rw [e]; exact this
  have hsm4α : 4 * ((12 : ℝ) * M * α₀) ≤ 1 := by
    have e : (12 : ℝ) * M * α₀ = t := by rw [htdef]
    rw [e]; linarith
  -- torus facts
  obtain ⟨h5, hLs⟩ := AdalyFormal.M2F123.torus_facts (k := k) hell2 (by omega : 6 ≤ m) hT
  have hT3 : ∀ μ, 3 ≤ Lu μ + 1 := fun μ => by have := h5 μ; omega
  have hLu' : ∀ μ, ell < Lu μ + 1 := fun μ => by have := hthick μ; omega
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  -- the class statements at this configuration
  have hBat := hBf k hk Lu α₀ hα hsB' hT S hS Lam hL U hU hloc
  have hext := hRf k hk Lu α₀ hα hsR' hT S hS hthick Lam hL U hU hloc
  -- F1-F4 at β (OG9)
  obtain ⟨ha1w, hsm4, hsmA, hrr⟩ := hwin M β hβpos.le hβs0
  have hbc := AdalyFormal.OneGap.blockCharts_ball hell2 hS hM2002 hRM1000 hLs hC1 hα hη hBat
  have hrc := AdalyFormal.OneGap.rowCharts_ball hell2 hS hM2002 hRM1000 hLs hC1 hα hη hBat
  obtain ⟨-, -, hNum⟩ := hN M R hM0 hRW α1 hα1pos.le hα1a₁
  have hHc : SiteS1 ell k S U a (csOf a (rhoT ell 12 M α1)) :=
    AdalyFormal.OneGap12.siteS1_of_charts12 hell2 hS hRM18 (AdalyFormal.M1GaugeW4.hbig_of ell k Lu h5) hLs hη
      hβpos.le ha1w hsm4 U hbc a ha
  have hGc : RowBound ell k S U a (gamC ell a (rhoT ell 12 M α1) (epsXnum ell (R * M * ell) a (rhoT ell 12 M α1))) :=
    AdalyFormal.OneGap12.rowBound_of_charts12 hell2 hS hRM18 (AdalyFormal.M1GaugeW4.hbig_of ell k Lu h5) hLs hR1
      (by omega) hη hβpos.le ha1w hsm4 a ha ε1 hNum U hbc
  have hCc := AdalyFormal.OneGap12.massComm_of_charts12 hell2 hS hM0 hR1 hR8 hroom17 hT3 hη hβpos ha1w hsm4 hsmA hrr
    a ha.le U hrc
  have hLthick : ∀ σ : Fin 3, 13 * (M * ell ^ k) ≤ scaleUp ell k Lu σ + 1 := by
    intro σ
    rw [AdalyFormal.M2UnitCharts.scaleUp_succ ell k Lu hell0 σ]
    have := Nat.mul_le_mul_right (ell ^ k) (hthick σ)
    calc 13 * (M * ell ^ k) = 13 * M * ell ^ k := by ring
      _ ≤ _ := this
  have hIc : AdalyFormal.M2Route.PatchCharts ell M k 1 5 D S U ((ell : ℝ) ^ k)⁻¹ (((12 : ℕ) : ℝ) * M * β) := by
    refine AdalyFormal.OneGap.patchCharts_monoAC hη ?_
      (AdalyFormal.OneGap.patchCharts_of_ballAC hS hM0 hell2 (by omega) (by omega) hdM hLthick hBat)
    have hMr : (0 : ℝ) ≤ ((12 : ℕ) : ℝ) * M := by positivity
    have : C * α₀ ≤ (ell : ℝ) ^ 3 * (C * α₀) := by
      have : 0 ≤ C * α₀ := by positivity
      have : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ hlR
      nlinarith
    exact mul_le_mul_of_nonneg_left this hMr
  -- the class at β
  have hαβ : α₀ ≤ β := by rw [hβK]; nlinarith
  have hUb := hU.mono hη.le hαβ
  have hb1 : ((12 : ℕ) : ℝ) * M * β ≤ 1 := by
    have h1 : (12 : ℝ) * M * β ≤ 12 * M * ((ell : ℝ) ^ 3 * (2 * β)) := by
      have : β ≤ (ell : ℝ) ^ 3 * (2 * β) := by
        have : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ hlR
        nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have := h1.trans ha1w
    simpa using this
  have h216 := (rhoT_smalls ell 12 M α1 hα1pos.le hell1 hsm4).1
  have hcs : 0 < csOf a (rhoT ell 12 M α1) := by
    unfold csOf
    exact div_pos (by linarith) (lt_max_of_lt_left (by norm_num))
  -- W4 at U with the constant c1
  have cw1 := cwW4_lower (ell := ell) (M := M) (R := R) (d := D) (a := a) (cW := cW) (α₀ := α1) hε1 hα1pos.le
    (hDle D le_rfl) hcs hNum.hη (fun s x K hs hx hK => hU1 s x K hs hx hK) hα1δc hxδ' hKδ
  have hW4 : ∀ A : ↥(bondSupp (geomOf ell k S)),
      c1 * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ := by
    intro A
    have h := hw4 hell0 hS hM0 hR1 (by omega) (by omega) hroom17 le_rfl hdM hW1 le_rfl U hβpos hβa0P hUb hb1
      Lam ε1 1 hε1 one_pos hNum h216 hHc hGc hCc hIc A
    exact le_trans (mul_le_mul_of_nonneg_right cw1 (AdalyFormal.M1DStrat.wnormSq_nonneg' S _)) h
  -- the numeric point
  set W : ℕ := R * M * ell with hWdef
  set x : ℝ × ℝ × ℝ × ℝ := (θ, rho1 12 M α1, 2 * (ell : ℝ) ^ 2 * Real.log ell / ((R * M * ell : ℕ) : ℝ),
    3 * (ell : ℝ) * Real.log ell / ((R * M * ell : ℕ) : ℝ)) with hxdef
  have hdx : ∀ d0 d1 : ℝ, |d0| < δ → |d1| < δ → dist ((x, (d0, d1)) : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)) 0 < δ := by
    intro d0 d1 h0 h1
    rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
    simp only [hxdef, Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero]
    rw [abs_of_pos hθ, abs_of_nonneg hr0, abs_of_nonneg hp0, abs_of_nonneg hq0]
    exact max_lt (max_lt (by rw [hθdef]; linarith) (max_lt hr1 (max_lt hpδ hqδ))) (max_lt h0 h1)
  obtain ⟨⟨⟨N1, N2, N3, N4, N5, N6, N7, N8, N9, N10, N11, N12, N13, N14, N15, N16⟩, NkW, -, -, -, -⟩, B1, B2, -, -⟩ :=
    hball _ (hdx 0 0 (by simpa using hδ) (by simpa using hδ))
  -- the CTBase at U
  obtain ⟨Gi, hG1, hG2⟩ := AdalyFormal.M2Skel.gi_of_rowBound (geomOf ell k S) (show 1 ≤ (geomOf ell k S).ell from hell1)
    U a _ hGc
  have hp := AdalyFormal.M2Skel.hatPack_of_S1 (W := W) hell1 ha hNum h216 hHc
  have hγ0 : 0 < gamC ell a (rhoT ell 12 M α1) (epsXnum ell W a (rhoT ell 12 M α1)) := by
    have hden := sub_pos.mpr N5
    unfold gamC
    have hnum : 0 < (ell : ℝ) * (Real.sqrt (max a 1) * ((1 + 12 * rhoT ell 12 M α1) ^ 2
        + (512 * rhoT ell 12 M α1 ^ 2 + 4704) / a)) := by
      have : 0 < Real.sqrt (max a 1) := Real.sqrt_pos.mpr (lt_max_of_lt_right one_pos)
      positivity
    exact div_pos hnum hden
  let B : CTBase ell M R k S W :=
    { hS := hS, hW := hW1, hell := hell2, hR := hR1, hM := hM1, hWR := le_rfl, U := U, a := a,
      cs := csOf a (rhoT ell 12 M α1), hp := hp, θ := θ, hθ := hθ, Θ := ThN ell W θ, Δ := DeN ell W θ,
      hΘ := le_rfl, hΔ := le_rfl, hsm := N3.le, hsmD := N4.le, Gi := Gi, hG1 := hG1, hG2 := hG2,
      γ := gamC ell a (rhoT ell 12 M α1) (epsXnum ell W a (rhoT ell 12 M α1)), hγ0 := hγ0, hγ := hGc }
  have hreg : HolRegime S ell k B.U (rho1 12 M α1) := MXQ.M2Skel.holRegime_rho1ACΦ hell1 hS hη hβpos.le hb1 hUb
  have hεγ : ∀ c, (B.toCT c).epsG * B.γ ≤ 1 := fun c => N11.le
  have hcG : ∀ c, 0 < (B.toCT c).cG := fun c => N12
  have Dr : ∀ p : BIdx (geomOf ell k S), AdalyFormal.M2F123.RowQ ell k Lu S B.U (SstarM ell 12 M α1) p := by
    intro p
    by_cases h1 : 1 ≤ (p.1 : ℕ)
    · exact AdalyFormal.OneGap12.rowQ_of_chart12 hell2 hS hroom17 hT3 hη hβpos.le ha1w hsm4 hsmA hrr U p (hrc p h1)
    · exact AdalyFormal.OneGap12.rowQ_level012 hell2 hS hroom17 hM0 hT3 hη hβpos ha1w hsm4 hsmA hrr U p (by omega)
  -- (1) the weighted columns of `H`
  have hHL2 := hHL2_cfg B hell0 Lam (rho1 12 M α1) hr0 hreg hεγ hcG c1 hc1 hW4 hR8 (SstarM ell 12 M α1) Dr bN hbN hext
    CHB hCHB N13 B1 B2.le
  -- (2) the `C2` bound at the class
  have hC : ∀ z, ∑ q, ‖C2fullOf (geomOf ell k S) B.U z q‖ ≤ K2c * AdalyFormal.M1.wnormSq S ell k z := by
    intro z
    have hDQ1 : DQSmall ell (12 * M * ((ell : ℝ) ^ 3 * (2 * ((ell : ℝ) ^ 3 * (C * α₀))))) :=
      hDQall _ (by positivity) hα1β₀
    have h1 := hC2_class hell2 hS hM2002 hRM1000 hLs hLu' hC1 hα hBat hDQ1 z
    have hmono : K2strat ell (12 * M * ((ell : ℝ) ^ 3 * (2 * ((ell : ℝ) ^ 3 * (C * α₀))))) ≤ K2strat ell β₀ :=
      K2strat_mono ell hell1 (by positivity) hα1β₀ hDQ0
    have hw0 := AdalyFormal.M1DStrat.wnormSq_nonneg' S (ell := ell) (k := k) z
    refine h1.trans ?_
    rw [hK2cdef]
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 44217)) hw0
    linarith
  -- (3) the two `Δ⁽²⁾` constants
  set kW : ℝ := kWcN ell a (csOf a (rhoT ell 12 M α1)) (ThN ell W θ) (DeN ell W θ)
    (gamC ell a (rhoT ell 12 M α1) (epsXnum ell W a (rhoT ell 12 M α1))) with hkWdef
  have hkW2 : kW ^ 2 < KWb := NkW
  set δ0 : ℝ := 2 * ((Real.sqrt (Ageo ell θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2c
      * Real.exp (2 * 0) * 44217 * ((ell : ℝ) * kW) ^ 2 with hδ0def
  set δ1 : ℝ := 2 * ((Real.sqrt (Ageo ell θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2c
      * Real.exp (2 * (32 * θ * ell)) * 44217 * ((ell : ℝ) * kW) ^ 2 with hδ1def
  have hδ00 : 0 ≤ δ0 := by rw [hδ0def]; positivity
  have hδ10 : 0 ≤ δ1 := by rw [hδ1def]; positivity
  have hδ01 : δ0 ≤ δ1 := by
    rw [hδ0def, hδ1def]
    have he : Real.exp (2 * 0) ≤ Real.exp (2 * (32 * θ * ell)) := Real.exp_le_exp.mpr (by
      have : 0 ≤ 32 * θ * ell := by positivity
      linarith)
    have hA : 0 ≤ 2 * ((Real.sqrt (Ageo ell θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2c := by positivity
    have hB : 0 ≤ 44217 * ((ell : ℝ) * kW) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left he hA
    nlinarith
  have hδ1C : δ1 ≤ Cδ * t := by
    rw [hδ1def, hCδdef]
    have hkk : ((ell : ℝ) * kW) ^ 2 ≤ (ell : ℝ) ^ 2 * KWb := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hkW2.le (by positivity)
    have hA : 0 ≤ 2 * ((Real.sqrt (Ageo ell θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2c
        * Real.exp (2 * (32 * θ * ell)) * 44217 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hkk hA
    have e : 2 * (Real.sqrt (Ageo ell θ) * KH) * (400 * (ell : ℝ) ^ 3) * K2c * Real.exp (2 * (32 * θ * ell))
        * 44217 * ((ell : ℝ) ^ 2 * KWb) * t
        = 2 * ((Real.sqrt (Ageo ell θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2c
          * Real.exp (2 * (32 * θ * ell)) * 44217 * ((ell : ℝ) ^ 2 * KWb) := by rw [htdef]; ring
    rw [e]; exact h1
  have hδ1δ : δ1 < δ := by
    have h1 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Cδ + 1))).1 hs8
    have h2 : Cδ * t ≤ (Cδ + 1) * t := by nlinarith
    nlinarith
  obtain ⟨⟨-, -, hcw2, hk1, -, -⟩, -, -, B3, B4⟩ := hball _ (hdx δ0 δ1 (by rw [abs_of_nonneg hδ00]; linarith)
    (by rw [abs_of_nonneg hδ10]; exact hδ1δ))
  have hlt2 : δ0 < c1 := by have : δ0 < c1 / 2 := hcw2
                            linarith
  -- (4) the weighted columns of `H₁`
  have hH1L2 := MXQ.M2OpLayer.hH1L2_cfgACΦ B hell0 Lam (rho1 12 M α1) hr0 hreg hεγ hcG c1 hc1 hW4 hR8 (SstarM ell 12 M α1) Dr bN hbN hext
    hell2 hroom18 hU hα.le hsm4α hq KH hKH hHL2 K2c hK2c hC CH1B hCH1B hlt2 hk1 B3 B4.le
  -- (5) the `W` bound
  have hW : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G),
      AdalyFormal.M1.wnormSq (gparams ell k Lu hell0 S U a Lam).S (gparams ell k Lu hell0 S U a Lam).ell
          (gparams ell k Lu hell0 S U a Lam).k
          (Wop (gparams ell k Lu hell0 S U a Lam).G (gparams ell k Lu hell0 S U a Lam).U
            (gparams ell k Lu hell0 S U a Lam).a (iE (gparams ell k Lu hell0 S U a Lam).G A))
        ≤ CW * AdalyFormal.M1.wnormSq (gparams ell k Lu hell0 S U a Lam).S (gparams ell k Lu hell0 S U a Lam).ell
          (gparams ell k Lu hell0 S U a Lam).k (A : BondFnL2 (gparams ell k Lu hell0 S U a Lam).Lf) := by
    intro A
    have h := hW_of_fields hS hW1 hell2 hR1 hM1 le_rfl U a ha hNum h216 hHc _ hγ0.le hGc Lam A
    refine h.trans ?_
    have hw0 := AdalyFormal.M1DStrat.wnormSq_nonneg' S (ell := ell) (k := k) (A : BondFnL2 (scaleUp ell k Lu))
    have hc : (ell : ℝ) ^ 2 * CWcN ell W a (csOf a (rhoT ell 12 M α1))
        (gamC ell a (rhoT ell 12 M α1) (epsXnum ell W a (rhoT ell 12 M α1))) ^ 2 ≤ CW := by
      rw [hCWdef]; exact mul_le_mul_of_nonneg_left N16.le (by positivity)
    exact mul_le_mul_of_nonneg_right hc hw0
  -- (6) the `D̃⁽²⁾` bound
  have hMb : 4 * ell + 141 ≤ 4 * M := by omega
  have hthick12 : ∀ σ : Fin 3, 12 * (M * ell ^ k) ≤ scaleUp ell k Lu σ + 1 := by
    intro σ
    rw [AdalyFormal.M2UnitCharts.scaleUp_succ ell k Lu hell0 σ]
    have := Nat.mul_le_mul_right (ell ^ k) (hthick σ)
    have e : 13 * M * ell ^ k = 12 * (M * ell ^ k) + M * ell ^ k := by ring
    omega
  have hKD := hKD_classU hell2 hT hMb (by omega : 5 * ell + 17 ≤ R * M) (by omega : 6 * ell ≤ R) hk hthick12 S hS Lam hL U a α₀ hα hC1 hBat ((ell : ℝ) ^ 3 * (2 * (C * α₀))) le_rfl hKDs
  exact ⟨hHL2, hH1L2, hC, hW, hKD⟩


end t5

end MXQ.Total
