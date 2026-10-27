import MF7
import RKW2

/-!
# MF8 -- controls for `instIneq_M0_kuniform`.

* `delta2_flat_zero`, `instIneq_M0_flat` (MUST-NOT-FIRE / consistency): at `U = 1` every hypothesis of `instIneq_M0_kuniform` holds with
  `e = q0 = 0`, `ε2s = εJ = 0`, and the constant is `γ₀ = (1/54) ell⁻⁵ / 4` (`gam0M0_flat`): the conditional theorem is jointly satisfiable
  and yields a positive constant (weaker by the Young factor 4 than the flat theorem FE14).
* `witness_M0_nonD k` (non-vacuity of every NON-D hypothesis at a CURVED `U`, every `k`): on the RKW2 family `UK k (epsK k)`
  (`ell = 2`, `Lu = (3,3,3)`, one bond of angle `epsB/4^k`): `M0RegimeR ∧ KUSmall ∧ UnitSmall ∧ ∃ plaquette with dv > 0`.
  The D-layer premises `hD2`, `hJ` are NOT witnessed at a curved `U` (they are the open input).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M0Finish

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG (LamBlockSum InstIneq)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.AsmM0
open AdalyFormal.AsmM0 (Lu3)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.CurvBlock (dv dv_one)
open AdalyFormal.RegBgKU (KUSmall kapHat Kc Kc_pos epsB epsB_pos epsB_le1 epsB_le2 Kc_two_le UK epsK rho_family_le
  witnessKU_family)
open AdalyFormal.NonflatJet (rhoOf r0 r0_pos)
open SmallnessBridge.Assemble (loopFactorBound)
open EstimatesLayer.E1E3

/-- `Δ⁽²⁾ = 0` when the source vanishes. -/
theorem delta2_zero_of_J {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : BaseDataS E S F) (hL : D.Laws) (hJ : D.J = 0) : D.Delta2 hL = 0 := by
  obtain ⟨hs, hf⟩ := D.Delta2_spec hL
  refine symm_unique hs (fun x y => by simp) (fun A => ?_)
  rw [hf A, hJ, inner_zero_right]; simp

theorem rhoM0_zero (ell k : ℕ) : rhoM0 ell k 0 0 = 0 := by unfold rhoM0; simp

theorem kapHat_zero (ell : ℕ) : kapHat ell 0 = 0 := by unfold kapHat; simp

theorem dCM0_zero (ell : ℕ) : dCM0 ell 0 = 0 := by
  unfold dCM0
  rw [kapHat_zero, AdalyFormal.NonflatJet.rhoOf_zero, AdalyFormal.NonflatJet.e2Majorant_zero]; simp

theorem phiC_zero (ell : ℕ) : phiC ell (3600 * (ell : ℝ) * 0) = 0 := by unfold phiC; simp

theorem EbarM0_zero (ell : ℕ) (a t : ℝ) : EbarM0 ell a t 0 = 0 := by
  unfold EbarM0; rw [phiC_zero]; simp

theorem gam0M0_flat (ell : ℕ) (a t : ℝ) :
    gam0M0 ell a t 0 0 0 (dCM0 ell 0) (cBM0 ell 0) = (1 / 54) * (1 / (ell : ℝ) ^ 5) / 4 := by
  unfold gam0M0
  rw [dCM0_zero, EbarM0_zero, zero_mul]
  exact gam0Form_flat _ _ _

theorem ThetaM0_zero (ell : ℕ) (a t : ℝ) : ThetaM0 ell a t 0 = 0 := by
  unfold ThetaM0 Stil Vc Wc
  rw [phiC_zero]; simp

/-- **flat consistency (must-not-fire)**: every hypothesis holds at `U = 1`, constant `(1/54) ell⁻⁵/4`. -/
theorem instIneq_M0_flat (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell2 : 2 ≤ ell) (a t : ℝ) (ha : 0 < a) (ht : 0 < t)
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam) :
    InstIneq ell k (by omega) a Lu ((1 / 54) * (1 / (ell : ℝ) ^ 5) / 4) (fullTower ell k Lu) Lam flatCfg := by
  have hell : 0 < ell := by omega
  have hr0 := r0_pos
  have hpi := Real.pi_pos
  have R : M0RegimeR ell k Lu flatCfg a t 0 0 := by
    refine ⟨hell2, ha, ht, le_rfl, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ρ'
      have h1 : scaleUp ell k Lu ρ' + 1 = (Lu ρ' + 1) * ell ^ k := scaleUp_succ ell k Lu hell ρ'
      have h2 : 3 ≤ Lu ρ' + 1 := by have := hstrict ρ'; omega
      have h3 := Nat.mul_le_mul_right (ell ^ k) h2
      have h4 : 0 < ell ^ k := pow_pos hell k
      omega
    · intro b; simp [flatCfg, dv_one]
    · intro p
      have : periodicPlaquetteHolonomy (flatCfg : PeriodicLinkConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) p = 1 := by
        simp [periodicPlaquetteHolonomy, flatCfg]
      rw [this, dv_one]
    · simp
    · rw [rhoM0_zero]; norm_num
    · rw [rhoM0_zero]; positivity
    · rw [rhoM0_zero, ThetaM0_zero]; positivity
  have H : KUSmall ell (rhoM0 ell k 0 0) := by
    rw [rhoM0_zero]
    refine ⟨?_, ?_, ?_⟩
    · rw [kapHat_zero, mul_zero]; positivity
    · simp
    · rw [kapHat_zero, mul_zero]; exact hr0
  have HU : UnitSmall ell (rhoM0 ell k 0 0) := by
    rw [rhoM0_zero]
    refine ⟨?_, ?_, ?_⟩
    · rw [kapHat_zero]; positivity
    · rw [kapHat_zero, mul_zero, mul_zero]; exact hr0
    · rw [dCM0_zero]; norm_num
  have hJf : (PU ell k Lu hell flatCfg a Lam).Jf = 0 := Jf_flat _ rfl
  have hD2 : ‖(PU ell k Lu hell flatCfg a Lam).data.Delta2 (PU ell k Lu hell flatCfg a Lam).data_laws‖
      ≤ 0 / ((ell : ℝ) ^ k) ^ 2 := by
    have hJd : (PU ell k Lu hell flatCfg a Lam).data.J = 0 := by
      show (pE _) (PU ell k Lu hell flatCfg a Lam).Jf = 0
      rw [hJf]; exact map_zero _
    rw [delta2_zero_of_J _ _ hJd, zero_div]
    refine ContinuousLinearMap.opNorm_le_bound _ le_rfl (fun x => ?_)
    rw [ContinuousLinearMap.zero_apply, zero_mul]
    exact le_of_eq norm_zero
  have hJ : ∀ Bt : AdalyFormal.Balaban.AdmissibleSubspace.Bond Lu → SuTwo,
      AdalyFormal.StatementLane.OnLambdaTildeIn Lam ell Bt → AdalyFormal.StatementLane2.OnLambdaT Lam Bt →
      |⟪(PU ell k Lu hell flatCfg a Lam).H1in ((PU ell k Lu hell flatCfg a Lam).D2in
          (WithLp.toLp 2 (Cop Lam (PU ell k Lu hell flatCfg a Lam).Q1 Bt))),
        (PU ell k Lu hell flatCfg a Lam).Jf⟫|
        ≤ 0 * ‖(WithLp.toLp 2 (Cop Lam (PU ell k Lu hell flatCfg a Lam).Q1 Bt) : BondFnL2 Lu)‖ ^ 2 := by
    intro Bt _ _; rw [hJf, inner_zero_right, abs_zero, zero_mul]
  have h := instIneq_M0_kuniform ell k Lu hell flatCfg a t 0 0 R H HU hstrict hd Lam hLB 0 0 le_rfl le_rfl
    (by rw [zero_mul]; norm_num) hD2 hJ
  rw [rhoM0_zero, gam0M0_flat] at h
  exact h

/-- `kapHat 2 ρ ≤ 44500 ρ` for `0 ≤ ρ ≤ 1/1000`. -/
theorem kapHat_two_le (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 1000) : kapHat 2 ρ ≤ 45000 * ρ := by
  unfold kapHat
  have hK := Kc_two_le
  have hK0 := Kc_pos 2 le_rfl
  have hpi := Real.pi_gt_three
  have e1 : ρ / (3 * Real.pi) ≤ ρ / 9 := div_le_div_of_nonneg_left h0 (by norm_num) (by linarith)
  have e2 : ρ / (3 * Real.pi) + ρ ^ 2 ≤ ρ / 9 + ρ / 1000 := by nlinarith
  have e3 : Kc 2 * (ρ / (3 * Real.pi) + ρ ^ 2) ≤ 400000 * (ρ / 9 + ρ / 1000) := by
    have hp : 0 ≤ ρ / (3 * Real.pi) + ρ ^ 2 := by positivity
    calc Kc 2 * (ρ / (3 * Real.pi) + ρ ^ 2) ≤ 400000 * (ρ / (3 * Real.pi) + ρ ^ 2) :=
          mul_le_mul_of_nonneg_right hK hp
      _ ≤ 400000 * (ρ / 9 + ρ / 1000) := by nlinarith
  push_cast
  nlinarith

/-- **non-vacuity of every NON-D hypothesis at a curved background, every `k`.** -/
theorem witness_M0_nonD (k : ℕ) :
    M0RegimeR 2 k Lu3 (UK k (epsK k)) 1 1 (Real.sqrt 2 * epsK k) (4 * Real.sqrt 2 * epsK k) ∧
    KUSmall 2 (rhoM0 2 k (Real.sqrt 2 * epsK k) (4 * Real.sqrt 2 * epsK k)) ∧
    UnitSmall 2 (rhoM0 2 k (Real.sqrt 2 * epsK k) (4 * Real.sqrt 2 * epsK k)) ∧
    ∃ p : PeriodicLatticePlaquette (scaleUp 2 k Lu3), 0 < dv (periodicPlaquetteHolonomy (UK k (epsK k)) p) := by
  obtain ⟨hR, hKU, hc⟩ := witnessKU_family k
  refine ⟨hR, hKU, ?_, hc⟩
  set ρ := rhoM0 2 k (Real.sqrt 2 * epsK k) (4 * Real.sqrt 2 * epsK k) with hρ
  have hε := epsB_pos
  have hε1 := epsB_le1
  have hε2 := epsB_le2
  have hr0 := r0_pos
  have hρ59 : ρ ≤ 59 * epsB := rho_family_le k
  have hρ0 : 0 ≤ ρ := by
    have := (AdalyFormal.RegBgKU.class_bounds 2 k (by norm_num) (Real.sqrt 2 * epsK k) (4 * Real.sqrt 2 * epsK k)
      (by unfold epsK; positivity) (by unfold epsK; positivity)).1
    exact le_trans (by unfold epsK; positivity) this
  have hρs : ρ ≤ 1 / 1000 := by
    have : (59 : ℝ) * epsB ≤ 59 * (1 / 10 ^ 13) := by linarith
    linarith [show (59 : ℝ) * (1 / 10 ^ 13) ≤ 1 / 1000 by norm_num]
  have hκ := kapHat_two_le ρ hρ0 hρs
  have hκ0 : 0 ≤ kapHat 2 ρ := by unfold kapHat; have := Kc_pos 2 le_rfl; positivity
  have hκB : kapHat 2 ρ ≤ 2655000 * epsB := by nlinarith
  have hLFB : (loopFactorBound 2 : ℝ) = 10 := by norm_num [loopFactorBound]
  refine ⟨?_, ?_, ?_⟩
  · have : (2655000 : ℝ) * epsB ≤ 2655000 * (1 / 10 ^ 13) := by linarith
    have h2 : (2655000 : ℝ) * (1 / 10 ^ 13) ≤ 1 / (1000 * ((2 : ℕ) : ℝ) ^ 4) := by norm_num
    linarith
  · rw [hLFB]
    have hpi := Real.pi_lt_d2
    have : (2655000 : ℝ) * epsB ≤ 2655000 * (r0 / 10 ^ 10) := by linarith
    nlinarith
  · -- dCM0 2 ρ ≤ 8 * 5100 * κ < 1
    set κ := kapHat 2 ρ with hκdef
    have hrho : rhoOf 2 κ ≤ 1 / 10 := by
      have := AdalyFormal.NonflatJet.rhoOf_le (ell := 2) κ hκ0
      have h3 : κ ≤ 2655000 * (1 / 10 ^ 13) := by linarith
      push_cast at this
      nlinarith
    have hrho0 : 0 ≤ rhoOf 2 κ := by unfold AdalyFormal.NonflatJet.rhoOf; positivity
    have he2 : e2Majorant (rhoOf 2 κ) ≤ 12 * rhoOf 2 κ := AdalyFormal.NonflatJet.e2Majorant_le_twelve hrho0 hrho
    have he20 : 0 ≤ e2Majorant (rhoOf 2 κ) := e2Majorant_nonneg hrho0
    have hrl := AdalyFormal.NonflatJet.rhoOf_le (ell := 2) κ hκ0
    push_cast at hrl
    have hrad : 384 * ((2 : ℝ) * κ) ^ 2 + 480 * (e2Majorant (rhoOf 2 κ)) ^ 2 ≤ (5100 * κ) ^ 2 := by
      have h1 : e2Majorant (rhoOf 2 κ) ≤ 12 * (8 * 2 * (6 / 5 * κ)) := le_trans he2 (by linarith)
      have h2 : (e2Majorant (rhoOf 2 κ)) ^ 2 ≤ (12 * (8 * 2 * (6 / 5 * κ))) ^ 2 := pow_le_pow_left₀ he20 h1 2
      nlinarith
    unfold dCM0
    rw [← hκdef]
    have hs : Real.sqrt (384 * ((2 : ℕ) * κ) ^ 2 + 480 * (e2Majorant (rhoOf 2 κ)) ^ 2) ≤ 5100 * κ := by
      push_cast
      rw [Real.sqrt_le_left (by positivity)]
      exact hrad
    have : ((2 : ℕ) : ℝ) ^ 3 * (5100 * κ) < 1 := by
      have h3 : κ ≤ 2655000 * (1 / 10 ^ 13) := by linarith
      push_cast; nlinarith
    calc ((2 : ℕ) : ℝ) ^ 3 * Real.sqrt (384 * ((2 : ℕ) * κ) ^ 2 + 480 * (e2Majorant (rhoOf 2 κ)) ^ 2)
        ≤ ((2 : ℕ) : ℝ) ^ 3 * (5100 * κ) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ < 1 := this

#print axioms delta2_zero_of_J
#print axioms gam0M0_flat
#print axioms instIneq_M0_flat
#print axioms kapHat_two_le
#print axioms witness_M0_nonD

end AdalyFormal.M0Finish
