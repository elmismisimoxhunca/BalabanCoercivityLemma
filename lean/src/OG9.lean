import OG8

/-!
# OG9 -- `fieldsK_of_ball : BallCharts → FieldsK ell a` (lane m2_onegap_20261015)
F1 (S1), F2 (row bound), F3 (mass commutator) from the anchor charts of `BallChartsAt` at the chart constant `ℓ³ (C α₀)`;
F4 (interface charts) from `interfaceCharts_of_ball`, enlarged to the constant `12 M (K α₀)`, `K = ℓ³ C`.
All thresholds `s` are divided by `K`.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.OneGap

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK pdist)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1Site AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar)
open AdalyFormal.M2Skel (SiteS1 RowBound alpha1)

theorem interfaceCharts_mono {L : PeriodicLatticeExtent} {ell M k d : ℕ} {S : Tower L} {U : LinkCfg L} {η a' b' : ℝ}
    (hη : 0 < η) (hab : a' ≤ b') (h : AdalyFormal.M2Route.InterfaceCharts ell M k d S U η a') :
    AdalyFormal.M2Route.InterfaceCharts ell M k d S U η b' := by
  intro j w hp hj hB hc
  exact (h j w hp hj hB hc).mono_const hη hab

theorem fieldsK_of_ball (hB : BallCharts) {ell : ℕ} (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) : FieldsK ell (by omega) a := by
  obtain ⟨m₁B, hBm⟩ := hB ell hell
  obtain ⟨s0, hs0, hwin⟩ := AdalyFormal.M2F123.window ell hell
  obtain ⟨W₀, hW₀, ε1, hε1, a₁, ha₁, hN⟩ := AdalyFormal.M1W4Num.w4Num_exists ell hell a ha
  obtain ⟨ρ1, hρ1, hq6⟩ := qsInj_exitfree ell hell
  have hell0 : 0 < ell := by omega
  have hC3 : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  have hC3' : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hell0)
  refine ⟨0, max m₁B 11, fun m hm => ?_⟩
  have hmB : m₁B ≤ m := le_trans (le_max_left _ _) hm
  have hm9 : 11 ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨R₁B, hRB⟩ := hBm m hmB
  refine ⟨max R₁B (max (max 26 (1000 * ell)) (max (max (17 * ell) W₀) (37 * ell ^ 2))), fun R hR => ?_⟩
  obtain ⟨C, hC1, sB, hsB, hBf⟩ := hRB R (le_trans (le_max_left _ _) hR)
  have hR26 : 26 ≤ R := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hR
  have hR37 : 37 * ell ^ 2 ≤ R := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hR
  have hR1000 : 1000 * ell ≤ R := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hR
  have hR17 : 17 * ell ≤ R := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) (le_max_right _ _))) hR
  have hRW : W₀ ≤ R := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) (le_max_right _ _))) hR
  have hCpos : (0 : ℝ) < C := by linarith
  have hKpos : (0 : ℝ) < (ell : ℝ) ^ 3 * C := by positivity
  have hK1 : (1 : ℝ) ≤ (ell : ℝ) ^ 3 * C := by nlinarith
  have hM := AdalyFormal.M2F123.pow_ge (ell := ell) hell (by omega : 6 ≤ m)
  have hM0 : 0 < ell ^ m := by omega
  have hM300 : 2002 ≤ ell ^ m := by
    have h1 : 2 ^ 11 ≤ ell ^ 11 := Nat.pow_le_pow_left hell 11
    have h2 : ell ^ 11 ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm9
    omega
  have hRM1000 : 1000 * ell ≤ R * ell ^ m := le_trans hR1000 (Nat.le_mul_of_pos_right R hM0)
  have hpi := Real.pi_pos
  refine ⟨(ell : ℝ) ^ 3 * C, hK1, min sB (min (min s0 (a₁ / (2 * (ell : ℝ) ^ 3)) / ((ell : ℝ) ^ 3 * C))
      (ρ1 / ((4 * Real.pi + 4) * C))),
    lt_min hsB (lt_min (div_pos (lt_min hs0 (by positivity)) hKpos) (div_pos hρ1 (by positivity))), ?_⟩
  intro k hk Lu α₀ hα hsα hT S hS hthick Lam hLam hLne U hcc hU1
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
  have hBat := hBf k hk Lu α₀ hα hsB' hT S hS Lam hLam U hcc hU1 hLne
  have hKα : ((ell : ℝ) ^ 3 * C) * α₀ = (ell : ℝ) ^ 3 * (C * α₀) := by ring
  set β : ℝ := (ell : ℝ) ^ 3 * (C * α₀) with hβ
  have hβpos : 0 < β := by rw [hβ]; positivity
  unfold FieldsKAt
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
    refine interfaceCharts_mono hη ?_ (interfaceCharts_of_ball hS hM0 hell (by omega) hdM hLthick hBat)
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

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.fieldsK_of_ball
