import ASC5

/-!
# ASC6 -- `ginv_coercive_M0` (headline).  See ASC5 header.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.AsmM0

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.ClassPropagationUbar (blkConstOf)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.SliceCoerc
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.NonflatJet (r0)
open AdalyFormal.FlatExt (aFE bFE)

theorem ginv_coercive_M0 (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
    (R : M0Regime ell k Lu U a t e q0) (Lam : Set (PeriodicLatticeSite Lu)) (x : ↥(bondSupp (GF ell k Lu))) :
    ‖x‖ ^ 2 ≤ ((ell : ℝ) ^ k) ^ 2 * KhatM0 ell a t (rhoM0 ell k e q0) *
      ⟪x, (IngrBParams.data ⟨ell, k, Lu, (by have := R.hell; omega : 0 < ell), fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫ := by
  have hell := R.hell
  have ha := R.ha
  have ht := R.ht
  have hell0 : 0 < ell := by omega
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hnpos : 0 < n := by positivity
  set ρ : ℝ := rhoM0 ell k e q0 with hρdef
  set η : ℝ := e + 3 * Real.pi * (n * q0) with hηdef
  have hρ : ρ = n * η := rfl
  have hpi := Real.pi_pos
  have hηnn : 0 ≤ η := by rw [hηdef]; have := R.he0; have := R.hq0; positivity
  have hρnn : 0 ≤ ρ := by rw [hρ]; positivity
  have h8000 : ρ ≤ 1 / 8000 := R.h1000.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hellR 3])
  have hden : 0 < 1 - 162 * ρ := by linarith
  have h216 := R.h216
  -- constants
  set nsq : ℝ := (ell : ℝ) ^ (2 * k) with hnsq
  have hnsq2 : nsq = n ^ 2 := by rw [hnsq, hn, ← pow_mul, mul_comm]
  set c1 : ℝ := min a 1 / 1000 with hc1
  set θ : ℝ := 272 * (q0 / (4 * Real.sqrt 2)) with hθ
  set δm : ℝ := Real.sqrt a * phiC ell (3600 * (ell : ℝ) * ρ) / n with hδm
  set e' : ℝ := (1 + t) * θ + (1 + 1 / t) * ((4 * Real.sqrt 2 * (ρ / n)) ^ 2 + δm ^ 2) with he'
  set P : ℝ := Real.sqrt (max 6 (16 / (3 * a)) * n ^ 2) with hP
  set PU : ℝ := Real.sqrt (max 6 (16 / (3 * a)) * n ^ 2 / (1 - 216 * ρ ^ 2)) with hPU
  set δ : ℝ := Real.sqrt 12 * (ρ / n) with hδ
  set q : ℝ := Real.sqrt (1 / n ^ 3) with hq
  set ε0 : ℝ := 6 * ρ * q with hε0
  -- n * S = Stil
  have hS : n * Sexp ell k δ P q ε0 = Stil (Real.sqrt 3) (Real.sqrt (Mc a)) ρ := by
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    unfold Sexp
    refine S_scaling n (Real.sqrt n) (Real.sqrt 3) (Real.sqrt (Mc a)) ρ hs (Real.sq_sqrt hnpos.le).symm hden
      (aFE ell k) (bFE ell k) q δ P ε0 (aFE_eq ell k) (bFE_eq ell k) (q_eq ell k hell0) ?_ ?_ rfl
    · rw [hδ, sqrt12_eq]; ring
    · exact P_eq a n hnpos.le
  have hSq : nsq * Sexp ell k δ P q ε0 ^ 2 = Stil (Real.sqrt 3) (Real.sqrt (Mc a)) ρ ^ 2 := by
    rw [hnsq2, ← hS]; ring
  -- n² e' ≤ the k-free quantity
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hθb : n ^ 2 * θ ≤ 272 * (ρ / (3 * Real.pi)) / (4 * Real.sqrt 2) := by
    have h := theta_n2 n q0 η ρ e hnpos R.hq0 hηdef R.he0 hρ
    calc n ^ 2 * θ = 272 * (n ^ 2 * q0) / (4 * Real.sqrt 2) := by rw [hθ]; ring
      _ ≤ 272 * (ρ / (3 * Real.pi)) / (4 * Real.sqrt 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [h]
  have hδm2 : n ^ 2 * δm ^ 2 = a * phiC ell (3600 * (ell : ℝ) * ρ) ^ 2 := by
    rw [hδm, div_pow, mul_pow, Real.sq_sqrt ha.le]; field_simp
  have h32 : n ^ 2 * (4 * Real.sqrt 2 * (ρ / n)) ^ 2 = 32 * ρ ^ 2 := by
    rw [mul_pow, mul_pow, h2]; field_simp; ring
  have hne' : nsq * e' ≤ (1 + t) * (272 * (ρ / (3 * Real.pi)) / (4 * Real.sqrt 2))
      + (1 + 1 / t) * (32 * ρ ^ 2 + a * phiC ell (3600 * (ell : ℝ) * ρ) ^ 2) := by
    rw [hnsq2, he']
    have e1 : n ^ 2 * ((1 + t) * θ + (1 + 1 / t) * ((4 * Real.sqrt 2 * (ρ / n)) ^ 2 + δm ^ 2))
        = (1 + t) * (n ^ 2 * θ) + (1 + 1 / t) * (n ^ 2 * (4 * Real.sqrt 2 * (ρ / n)) ^ 2 + n ^ 2 * δm ^ 2) := by ring
    rw [e1, h32, hδm2]
    have : 0 ≤ 1 + t := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hθb this]
  have hTh : nsq * Sexp ell k δ P q ε0 ^ 2 + nsq * e' ≤ ThetaM0 ell a t ρ := by
    unfold ThetaM0; rw [hSq]; linarith
  have hsmall : nsq * Sexp ell k δ P q ε0 ^ 2 + nsq * e' < c1 := lt_of_le_of_lt hTh R.hsmallU
  have hmain := ginv_coercive_M0_pinned ell k Lu hell U a ha Lam t ht e q0 R.he0 R.hq0 R.hN R.hlinks R.hplaq R.hcb
    η ρ hηdef hρ h216 R.h1000 R.hregthr nsq c1 θ δm e' P PU δ q ε0 hnsq hc1 hθ hδm he' hP hPU hδ hq hε0 hsmall x
  -- scale the constant
  set G : ℝ := ⟪x, (IngrBParams.data ⟨ell, k, Lu, hell0, fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫ with hG
  set Δ : ℝ := c1 - ThetaM0 ell a t ρ with hΔ
  have hΔpos : 0 < Δ := by rw [hΔ]; linarith [R.hsmallU]
  set D : ℝ := c1 - nsq * Sexp ell k δ P q ε0 ^ 2 - nsq * e' with hD
  have hDΔ : Δ ≤ D := by rw [hD, hΔ]; linarith
  have hDpos : 0 < D := lt_of_lt_of_le hΔpos hDΔ
  have hnsqpos : 0 < nsq := by rw [hnsq2]; positivity
  have hT1 : 2 / (D / (1 + t) / nsq) = 2 * (1 + t) * n ^ 2 / D := by
    rw [hnsq2]; have : (1 + t) ≠ 0 := by linarith
    field_simp
  have hT1le : 2 / (D / (1 + t) / nsq) ≤ n ^ 2 * (2 * (1 + t) / Δ) := by
    rw [hT1]
    have : 2 * (1 + t) * n ^ 2 / D ≤ 2 * (1 + t) * n ^ 2 / Δ :=
      div_le_div_of_nonneg_left (by positivity) hΔpos hDΔ
    calc _ ≤ 2 * (1 + t) * n ^ 2 / Δ := this
      _ = _ := by ring
  have hden216 : 0 < 1 - 216 * ρ ^ 2 := by linarith
  have hT2 : 2 * PU ^ 2 = n ^ 2 * (2 * Mc a / (1 - 216 * ρ ^ 2)) := by
    rw [hPU, Real.sq_sqrt (div_nonneg (mul_nonneg (le_trans (by norm_num) (le_max_left _ _)) (sq_nonneg _)) hden216.le)]
    unfold Mc; ring
  have hKle : max (2 / (D / (1 + t) / nsq)) (2 * PU ^ 2) ≤ n ^ 2 * KhatM0 ell a t ρ := by
    refine max_le ?_ ?_
    · refine hT1le.trans ?_
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    · rw [hT2]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have hT1pos : 0 < 2 / (D / (1 + t) / nsq) := by
    have : 0 < 1 + t := by linarith
    positivity
  have hKpos : 0 < max (2 / (D / (1 + t) / nsq)) (2 * PU ^ 2) := lt_of_lt_of_le hT1pos (le_max_left _ _)
  have hGnn : 0 ≤ G := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_pos_of_neg hKpos hneg
    have h0 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
    linarith [hmain]
  calc ‖x‖ ^ 2 ≤ max (2 / (D / (1 + t) / nsq)) (2 * PU ^ 2) * G := hmain
    _ ≤ n ^ 2 * KhatM0 ell a t ρ * G := mul_le_mul_of_nonneg_right hKle hGnn

#print axioms ginv_coercive_M0

end AdalyFormal.AsmM0
