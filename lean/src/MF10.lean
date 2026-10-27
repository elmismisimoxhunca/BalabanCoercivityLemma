import MF8
import ASW1

/-!
# MF10 -- the constant is POSITIVE at curved backgrounds, every `k` (non-vacuity of the conclusion constant).

* `witness_M0_small k`: on the RKW2 one-bond family scaled down by `1/1000` (`UK k (epsK k / 1000)`, `ell = 2`, `Lu = (3,3,3)`):
  `M0RegimeR ∧ KUSmall ∧ UnitSmall ∧ ρ ≤ 1e-14 ∧ ∃ plaquette with dv > 0` (curved), every `k`.
* `gam0M0_pos`: for `ell = 2, a = t = 1`, `0 ≤ ρ ≤ 1e-14`, `0 ≤ ε2s ≤ 1e-10`, `0 ≤ εJ ≤ 1e-6`:
  `9e-5 ≤ gam0M0 2 1 1 ρ ε2s εJ (dCM0 2 ρ) (cBM0 2 ρ)` (and `ε2s K̂ < 1`).
So along that curved family, IF the D-layer premises hold with `ε2s ≤ 1e-10`, `εJ ≤ 1e-6`, MF7 gives `InstIneq` with `γ₀ ≥ 9·10⁻⁵`, every `k`.
(The D-layer premises themselves are NOT proved; this module only shows the conclusion constant is not vacuous in the regime.)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M0Finish

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.AsmM0
open AdalyFormal.AsmM0 (Lu3 Mc_one Stil_le Stil_nn phiC_two_le phiC_two_nn Theta_num)
open AdalyFormal.CurvBlock (dv plaq_of_pw_one)
open AdalyFormal.RegBgKU (KUSmall kapHat Kc Kc_pos epsB epsB_pos epsB_le1 epsB_le2 Kc_two_le UK epsK rho_family_le
  KU_of_le UK_link UK_plaq UK_nonflat oK)
open AdalyFormal.NonflatJet (rhoOf r0 r0_pos)
open SmallnessBridge.Assemble (loopFactorBound)
open EstimatesLayer.E1E3

theorem rhoM0_smul (ell k : ℕ) (c e q0 : ℝ) : rhoM0 ell k (e * c) (q0 * c) = rhoM0 ell k e q0 * c := by
  unfold rhoM0; ring

theorem KhatM0_le (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1e-14) : KhatM0 2 1 1 ρ ≤ 4001 := by
  have hpi := Real.pi_gt_three
  have hS := Stil_le ρ h0 (by linarith)
  have hS0 := Stil_nn ρ h0 (by linarith)
  have hφ := phiC_two_le ρ h0 (by linarith)
  have hφ0 := phiC_two_nn ρ h0
  have hs2 : (1.4 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hΘ : ThetaM0 2 1 1 ρ ≤ 1e-10 := by
    unfold ThetaM0
    have e1 : Stil (Real.sqrt 3) (Real.sqrt (Mc 1)) ρ ^ 2 ≤ (9e8 * ρ) ^ 2 := pow_le_pow_left₀ hS0 hS 2
    have e2 : 272 * (ρ / (3 * Real.pi)) / (4 * Real.sqrt 2) ≤ 272 * ρ := by
      have : ρ / (3 * Real.pi) ≤ ρ := div_le_self h0 (by linarith)
      have h4 : (1 : ℝ) ≤ 4 * Real.sqrt 2 := by linarith
      calc 272 * (ρ / (3 * Real.pi)) / (4 * Real.sqrt 2) ≤ 272 * (ρ / (3 * Real.pi)) := div_le_self (by positivity) h4
        _ ≤ 272 * ρ := by linarith
    have e3 : phiC 2 (3600 * ((2 : ℕ) : ℝ) * ρ) ^ 2 ≤ (1e-6) ^ 2 := pow_le_pow_left₀ hφ0 hφ 2
    norm_num at e1 e3 ⊢
    nlinarith
  unfold KhatM0
  rw [Mc_one]
  apply max_le
  · rw [div_le_iff₀ (by norm_num; linarith)]; norm_num; linarith
  · rw [div_le_iff₀ (by nlinarith)]; nlinarith

theorem KhatM0_pos' (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1e-14) : 0 < KhatM0 2 1 1 ρ :=
  KhatM0_pos 2 1 1 ρ one_pos (by nlinarith)

theorem dCM0_two_le (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1e-14) : dCM0 2 ρ ≤ 2e-5 := by
  have hκ := kapHat_two_le ρ h0 (by linarith)
  have hκ0 : 0 ≤ kapHat 2 ρ := by unfold kapHat; have := Kc_pos 2 le_rfl; positivity
  set κ := kapHat 2 ρ with hκdef
  have hκs : κ ≤ 4.5e-10 := by linarith
  have hrl := AdalyFormal.NonflatJet.rhoOf_le (ell := 2) κ hκ0
  push_cast at hrl
  have hrho : rhoOf 2 κ ≤ 1 / 10 := by linarith
  have hrho0 : 0 ≤ rhoOf 2 κ := by unfold AdalyFormal.NonflatJet.rhoOf; positivity
  have he2 : e2Majorant (rhoOf 2 κ) ≤ 12 * rhoOf 2 κ := AdalyFormal.NonflatJet.e2Majorant_le_twelve hrho0 hrho
  have he20 : 0 ≤ e2Majorant (rhoOf 2 κ) := e2Majorant_nonneg hrho0
  have hrad : 384 * ((2 : ℝ) * κ) ^ 2 + 480 * (e2Majorant (rhoOf 2 κ)) ^ 2 ≤ (5100 * κ) ^ 2 := by
    have h1' : e2Majorant (rhoOf 2 κ) ≤ 12 * (8 * 2 * (6 / 5 * κ)) := le_trans he2 (by linarith)
    have h2 : (e2Majorant (rhoOf 2 κ)) ^ 2 ≤ (12 * (8 * 2 * (6 / 5 * κ))) ^ 2 := pow_le_pow_left₀ he20 h1' 2
    nlinarith
  unfold dCM0
  rw [← hκdef]
  have hs : Real.sqrt (384 * ((2 : ℕ) * κ) ^ 2 + 480 * (e2Majorant (rhoOf 2 κ)) ^ 2) ≤ 5100 * κ := by
    push_cast
    rw [Real.sqrt_le_left (by positivity)]
    exact hrad
  calc ((2 : ℕ) : ℝ) ^ 3 * Real.sqrt (384 * ((2 : ℕ) * κ) ^ 2 + 480 * (e2Majorant (rhoOf 2 κ)) ^ 2)
      ≤ ((2 : ℕ) : ℝ) ^ 3 * (5100 * κ) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ 2e-5 := by push_cast; nlinarith

theorem dCM0_nn (ell : ℕ) (ρ : ℝ) : 0 ≤ dCM0 ell ρ := by unfold dCM0; positivity

theorem cBM0_two_le (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1e-14) : 0 ≤ cBM0 2 ρ ∧ cBM0 2 ρ ≤ 4 := by
  have hd := dCM0_two_le ρ h0 h1
  have hd0 := dCM0_nn 2 ρ
  have hs : Real.sqrt (1 / ((2 : ℕ) : ℝ) ^ 3) ≤ 0.36 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt (1 / ((2 : ℕ) : ℝ) ^ 3) := Real.sqrt_nonneg _
  unfold cBM0
  have hden : 0 < 1 - dCM0 2 ρ := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hden]
  push_cast at hs ⊢
  nlinarith

theorem EbarM0_two_le (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1e-14) : 0 ≤ EbarM0 2 1 1 ρ ∧ EbarM0 2 1 1 ρ ≤ 6e-7 := by
  have hpi := Real.pi_gt_three
  have hK := KhatM0_le ρ h0 h1
  have hK0 := KhatM0_pos' ρ h0 h1
  have hφ := phiC_two_le ρ h0 (by linarith)
  have hφ0 := phiC_two_nn ρ h0
  have hs2 : (1.4 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have e2 : 272 * (ρ / (3 * Real.pi)) / (4 * Real.sqrt 2) ≤ 272 * ρ := by
    have : ρ / (3 * Real.pi) ≤ ρ := div_le_self h0 (by linarith)
    have h4 : (1 : ℝ) ≤ 4 * Real.sqrt 2 := by linarith
    calc 272 * (ρ / (3 * Real.pi)) / (4 * Real.sqrt 2) ≤ 272 * (ρ / (3 * Real.pi)) := div_le_self (by positivity) h4
      _ ≤ 272 * ρ := by linarith
  have e3 : phiC 2 (3600 * ((2 : ℕ) : ℝ) * ρ) ^ 2 ≤ (1e-6) ^ 2 := pow_le_pow_left₀ hφ0 hφ 2
  have hin0 : 0 ≤ 4 * (272 * (ρ / (3 * Real.pi)) / (4 * Real.sqrt 2)) + 128 * ρ ^ 2
      + 128 * phiC 2 (3600 * ((2 : ℕ) : ℝ) * ρ) ^ 2 := by positivity
  have hin : 4 * (272 * (ρ / (3 * Real.pi)) / (4 * Real.sqrt 2)) + 128 * ρ ^ 2
      + 128 * phiC 2 (3600 * ((2 : ℕ) : ℝ) * ρ) ^ 2 ≤ 1.4e-10 := by
    norm_num at e3 ⊢; nlinarith
  unfold EbarM0
  refine ⟨mul_nonneg hin0 hK0.le, ?_⟩
  calc _ ≤ 1.4e-10 * KhatM0 2 1 1 ρ := mul_le_mul_of_nonneg_right hin hK0.le
    _ ≤ 1.4e-10 * 4001 := by linarith
    _ ≤ 6e-7 := by norm_num

/-- the arithmetic of `gam0Form` in the small regime -/
theorem gam0Form_pos (ε' εJ Et dC cB : ℝ) (h1 : 0 ≤ ε') (h2 : ε' ≤ 5e-7) (h3 : 0 ≤ εJ) (h4 : εJ ≤ 1e-6)
    (h5 : 0 ≤ Et) (h6 : Et ≤ 6e-7) (h7 : 0 ≤ dC) (h8 : dC ≤ 2e-5) (h9 : 0 ≤ cB) (h10 : cB ≤ 4) :
    9e-5 ≤ gam0Form ((1 / 54) * (1 / ((2 : ℕ) : ℝ) ^ 5)) 1 ε' εJ Et dC cB := by
  unfold gam0Form
  push_cast
  have hcB2 : cB ^ 2 ≤ 16 := by nlinarith
  have hdC2 : dC ^ 2 ≤ 4e-10 := by nlinarith
  have hX : 5.6e-4 ≤ 1 / 54 * (1 / 2 ^ 5) - (Et * 1 + 128 * dC ^ 2) * cB ^ 2 := by
    have : (Et * 1 + 128 * dC ^ 2) * cB ^ 2 ≤ (6e-7 + 128 * 4e-10) * 16 := by
      have hA : Et * 1 + 128 * dC ^ 2 ≤ 6e-7 + 128 * 4e-10 := by linarith
      have hA0 : 0 ≤ Et * 1 + 128 * dC ^ 2 := by positivity
      calc (Et * 1 + 128 * dC ^ 2) * cB ^ 2 ≤ (6e-7 + 128 * 4e-10) * cB ^ 2 :=
            mul_le_mul_of_nonneg_right hA (sq_nonneg _)
        _ ≤ (6e-7 + 128 * 4e-10) * 16 := mul_le_mul_of_nonneg_left hcB2 (by norm_num)
    norm_num at this ⊢; linarith
  have hY : 1.39e-4 ≤ (1 - ε') * (1 / 54 * (1 / 2 ^ 5) - (Et * 1 + 128 * dC ^ 2) * cB ^ 2) / (4 + Et) := by
    rw [le_div_iff₀ (by linarith)]
    have : ((1 : ℝ) - 5e-7) * 5.6e-4 ≤ (1 - ε') * (1 / 54 * (1 / 2 ^ 5) - (Et * 1 + 128 * dC ^ 2) * cB ^ 2) := by
      have hX0 : (0 : ℝ) ≤ 5.6e-4 := by norm_num
      exact mul_le_mul (by linarith) hX hX0 (by linarith)
    nlinarith
  have hZ : (ε' * 1 + 2 * εJ) * cB ^ 2 ≤ (5e-7 + 2e-6) * 16 := by
    have hA : ε' * 1 + 2 * εJ ≤ 5e-7 + 2e-6 := by linarith
    have hA0 : 0 ≤ ε' * 1 + 2 * εJ := by positivity
    calc (ε' * 1 + 2 * εJ) * cB ^ 2 ≤ (5e-7 + 2e-6) * cB ^ 2 := mul_le_mul_of_nonneg_right hA (sq_nonneg _)
      _ ≤ (5e-7 + 2e-6) * 16 := mul_le_mul_of_nonneg_left hcB2 (by norm_num)
  norm_num at hZ hY ⊢
  linarith

/-- **the M0 constant is positive in an explicit curved regime** -/
theorem gam0M0_pos (ρ ε2s εJ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1e-14) (he0 : 0 ≤ ε2s) (he1 : ε2s ≤ 1e-10)
    (hj0 : 0 ≤ εJ) (hj1 : εJ ≤ 1e-6) :
    9e-5 ≤ gam0M0 2 1 1 ρ ε2s εJ (dCM0 2 ρ) (cBM0 2 ρ) ∧ ε2s * KhatM0 2 1 1 ρ < 1 := by
  have hK := KhatM0_le ρ h0 h1
  have hK0 := KhatM0_pos' ρ h0 h1
  obtain ⟨hE0, hE⟩ := EbarM0_two_le ρ h0 h1
  obtain ⟨hc0, hc⟩ := cBM0_two_le ρ h0 h1
  have hε' : ε2s * KhatM0 2 1 1 ρ ≤ 5e-7 := by
    calc ε2s * KhatM0 2 1 1 ρ ≤ 1e-10 * 4001 := mul_le_mul he1 hK hK0.le (by norm_num)
      _ ≤ 5e-7 := by norm_num
  refine ⟨?_, by linarith⟩
  unfold gam0M0
  exact gam0Form_pos _ εJ _ _ _ (mul_nonneg he0 hK0.le) hε' hj0 hj1 hE0 hE (dCM0_nn 2 ρ) (dCM0_two_le ρ h0 h1) hc0 hc

/-- **curved, every `k`, all non-D hypotheses, and `ρ ≤ 1e-14`** (RKW2 family scaled by `1/1000`). -/
theorem witness_M0_small (k : ℕ) :
    M0RegimeR 2 k Lu3 (UK k (epsK k / 1000)) 1 1 (Real.sqrt 2 * (epsK k / 1000)) (4 * Real.sqrt 2 * (epsK k / 1000)) ∧
    KUSmall 2 (rhoM0 2 k (Real.sqrt 2 * (epsK k / 1000)) (4 * Real.sqrt 2 * (epsK k / 1000))) ∧
    UnitSmall 2 (rhoM0 2 k (Real.sqrt 2 * (epsK k / 1000)) (4 * Real.sqrt 2 * (epsK k / 1000))) ∧
    rhoM0 2 k (Real.sqrt 2 * (epsK k / 1000)) (4 * Real.sqrt 2 * (epsK k / 1000)) ≤ 1e-14 ∧
    ∃ p : PeriodicLatticePlaquette (scaleUp 2 k Lu3),
      0 < dv (periodicPlaquetteHolonomy (UK k (epsK k / 1000)) p) := by
  have hε := epsB_pos
  have hε1 := epsB_le1
  have hs2 : Real.sqrt 2 ≤ 1.5 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hs2' : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hek : 0 < epsK k / 1000 := by unfold epsK; positivity
  have hek1 : epsK k / 1000 ≤ epsB / 1000 := by
    unfold epsK; exact div_le_div_of_nonneg_right (div_le_self hε.le (one_le_pow₀ (by norm_num))) (by norm_num)
  set ρ := rhoM0 2 k (Real.sqrt 2 * (epsK k / 1000)) (4 * Real.sqrt 2 * (epsK k / 1000)) with hρdef
  have hρeq : ρ = rhoM0 2 k (Real.sqrt 2 * epsK k) (4 * Real.sqrt 2 * epsK k) * (1 / 1000) := by
    rw [hρdef, ← rhoM0_smul]; congr 1 <;> ring
  have hρ : ρ ≤ 59 * epsB / 1000 := by
    rw [hρeq]; have := rho_family_le k; nlinarith
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; unfold rhoM0; positivity
  have hρs : ρ ≤ 3e-11 := hρ.trans (by nlinarith)
  have hρ14 : ρ ≤ 1e-14 := hρ.trans (by nlinarith)
  refine ⟨⟨le_refl _, one_pos, one_pos, by positivity, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    KU_of_le _ hρ0 (hρ.trans (by nlinarith)), ?_, hρ14, ?_⟩
  · intro _; show 2 * 2 ^ k < (3 + 1) * 2 ^ k - 1 + 1
    have := Nat.one_le_two_pow (n := k); omega
  · intro b; exact UK_link k (epsK k / 1000) hek.le b
  · exact plaq_of_pw_one (UK k (epsK k / 1000)) _ (UK_plaq k (epsK k / 1000) hek.le)
  · have e1 : ((2 : ℝ) ^ 2) ^ k * (4 * Real.sqrt 2 * (epsK k / 1000)) = 4 * Real.sqrt 2 * epsB / 1000 := by
      unfold epsK; rw [show ((2 : ℝ) ^ 2) = 4 by norm_num]; field_simp
    push_cast
    rw [e1]; nlinarith
  · nlinarith
  · refine hρs.trans ?_; push_cast; norm_num
  · exact Theta_num _ hρ0 hρs
  · -- UnitSmall at ρ ≤ 1e-14
    have hκ := kapHat_two_le ρ hρ0 (by linarith)
    have hκ0 : 0 ≤ kapHat 2 ρ := by unfold kapHat; have := Kc_pos 2 le_rfl; positivity
    have hLFB : (loopFactorBound 2 : ℝ) = 10 := by norm_num [loopFactorBound]
    have hr0 := r0_pos
    have hε2 := epsB_le2
    refine ⟨?_, ?_, ?_⟩
    · have : kapHat 2 ρ ≤ 4.5e-10 := by linarith
      norm_num; linarith
    · rw [hLFB]
      have hκB : kapHat 2 ρ ≤ 45000 * (59 * epsB / 1000) := by nlinarith
      have : (45000 : ℝ) * (59 * epsB / 1000) ≤ 45000 * (59 * (r0 / 10 ^ 10) / 1000) := by nlinarith
      nlinarith [Real.pi_lt_d2]
    · have := dCM0_two_le ρ hρ0 hρ14; linarith
  · refine ⟨(oK k, ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩), ?_⟩
    exact UK_nonflat k (epsK k / 1000) hek (by have := Real.pi_gt_three; nlinarith)

#print axioms rhoM0_smul
#print axioms KhatM0_le
#print axioms dCM0_two_le
#print axioms cBM0_two_le
#print axioms EbarM0_two_le
#print axioms gam0Form_pos
#print axioms gam0M0_pos
#print axioms witness_M0_small

end AdalyFormal.M0Finish
