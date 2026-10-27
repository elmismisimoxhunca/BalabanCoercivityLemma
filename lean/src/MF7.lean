import MF5e
import MF6g

/-!
# MF7 -- `instIneq_M0_kuniform`: the frozen `InstIneq` at milestone M0 with an explicit `γ₀`, every `ell ≥ 2`.

Setting: full tower (`Ω₀ = ` torus), `U` in ONE gauge with `M0RegimeR` + `KUSmall` (RKF) + the unit-level smallness `UnitSmall`
(three conditions on `(ell, ρ)` only; `ρ = rhoM0 ell k e q0`), torus `ell < Lu μ + 1`, `ell ∣ Lu μ + 1`, `Λ = B(Λ')` (`LamBlockSum`).
DERIVED here (no premise): `IsUnit G₁⁻¹`, `IsUnit N` (MF5e; `Q*` injective by the flat bond right inverse + bond drift), the
`C`-perturbation bounds (MF6g, unit background `Ū^k` small by RKN2 `dv_bg_le`), everything of MF4.
REMAINING PREMISES (the D-layer, both SUP quantities, NOT proved): `hD2 : n² ‖Δ⁽²⁾_U‖ ≤ ε2s` and
`hJ : ∀ B̃ ∈ Λ̃ (touching), |⟨H₁ D̃⁽²⁾ (C_U B̃), J⟩| ≤ εJ ‖C_U B̃‖²`, with `ε2s K̂ < 1`.
`γ₀ = gam0M0 ell a t ρ ε2s εJ (dCM0 ell ρ) (cBM0 ell ρ)` -- no `k`, no `Lu`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M0Finish

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp OnLambdaTildeIn)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneG (LamBlockSum InstIneq GenP.Nmat)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily (q1SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy frobSupBond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.AsmM0
open AdalyFormal.SliceCoerc
open AdalyFormal.BondComposite
open AdalyFormal.CurvBlock (dv pw pw_one_of_plaq)
open AdalyFormal.RegBgKU (KUSmall kapHat Kc Kc_pos kap Bnd TowerSmall towerSmall_of_KU class_bounds dv_bg_le
  ginv_coercive_M0_kuniform)
open AdalyFormal.NonflatJet (rhoOf r0)
open SmallnessBridge.Assemble (loopFactorBound)
open EstimatesLayer.E1E3

/-- the `C`-perturbation constant (k-free) -/
noncomputable def dCM0 (ell : ℕ) (ρ : ℝ) : ℝ :=
  (ell : ℝ) ^ 3 * Real.sqrt (384 * ((ell : ℝ) * kapHat ell ρ) ^ 2 + 480 * (e2Majorant (rhoOf ell (kapHat ell ρ))) ^ 2)

/-- the bound on `‖C_U‖` (k-free) -/
noncomputable def cBM0 (ell : ℕ) (ρ : ℝ) : ℝ :=
  (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) / (1 - dCM0 ell ρ)

/-- unit-level smallness of the blocked background `Ū^k` (three conditions on `(ell, ρ)` only). -/
structure UnitSmall (ell : ℕ) (ρ : ℝ) : Prop where
  u1 : kapHat ell ρ ≤ 1 / (1000 * (ell : ℝ) ^ 4)
  u2 : Real.pi / 2 * ((loopFactorBound ell : ℝ) * kapHat ell ρ) < r0
  u3 : dCM0 ell ρ < 1

theorem kap_le_kapHat (ell k : ℕ) (hell : 2 ≤ ell) (e q0 : ℝ) (he0 : 0 ≤ e) (hq0 : 0 ≤ q0) :
    kap ell e q0 k ≤ kapHat ell (rhoM0 ell k e q0) := by
  obtain ⟨b1, -, b3⟩ := class_bounds ell k (by omega) e q0 he0 hq0
  have hKc := Kc_pos ell hell
  unfold kap Bnd kapHat
  have := mul_le_mul_of_nonneg_left b3 hKc.le
  linarith

/-- the bond drift of the M0 class (re-derived as in ASC4/MF4). -/
theorem hC1_M0 (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
    (R : M0RegimeR ell k Lu U a t e q0) (H : KUSmall ell (rhoM0 ell k e q0)) :
    ∀ x : BondFnL2 (scaleUp ell k Lu),
      ∑ p : BIdx (GF ell k Lu), a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p - (bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2
        ≤ (Real.sqrt a * phiC ell (3600 * (ell : ℝ) * rhoM0 ell k e q0) / (ell : ℝ) ^ k) ^ 2 * ‖x‖ ^ 2 := by
  have hell2 : 2 ≤ ell := R.hell
  have hell0 : 0 < ell := by omega
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell2
  have hellpos : (0 : ℝ) < ell := by linarith
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hnpos : 0 < n := by positivity
  have hpi := Real.pi_pos
  have ha := R.ha
  have he0 := R.he0
  have hq0 := R.hq0
  set ρ := rhoM0 ell k e q0 with hρdef
  set η := e + 3 * Real.pi * (n * q0) with hη
  have hρ : ρ = n * η := by rw [hρdef]; unfold rhoM0; rfl
  have hηnn : 0 ≤ η := by rw [hη]; positivity
  have hρnn : 0 ≤ ρ := by rw [hρ]; positivity
  have hηρ : η = ρ / n := by rw [hρ]; field_simp
  have hρ1000 := R.h1000
  set ε : ℕ → ℝ := fun j => (ell : ℝ) ^ j * e + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ j * q0) with hεdef
  have hεnn : ∀ j, 0 ≤ ε j := fun j => by simp only [hεdef]; positivity
  have hεη : ∀ j, j < k → ε j ≤ (ell : ℝ) ^ j * η := fun j hj => by
    have := eps_class_le ell k (by omega) e q0 hq0 j hj.le
    rw [hη]; exact this
  have hεs : ∀ j, j < k → ε j ≤ 1 / (1000 * (ell : ℝ) ^ 4) := by
    intro j hj
    have h1 : (ell : ℝ) ^ j * ell ≤ n := by
      rw [hn, ← pow_succ]; exact pow_le_pow_right₀ (by linarith) hj
    have h2 : (ell : ℝ) ^ j * η ≤ ρ / ell := by
      rw [hηρ, mul_div_assoc', div_le_div_iff₀ hnpos hellpos]
      nlinarith [mul_le_mul_of_nonneg_left h1 hρnn]
    have h3 : ρ / ell ≤ 1 / (1000 * (ell : ℝ) ^ 4) := by
      calc ρ / ell ≤ (1 / (1000 * (ell : ℝ) ^ 3)) / ell := div_le_div_of_nonneg_right hρ1000 hellpos.le
        _ = 1 / (1000 * (ell : ℝ) ^ 4) := by field_simp
    exact (hεη j hj).trans (h2.trans h3)
  have h0 := pw_one_of_plaq U q0 hq0 R.hplaq
  have hcl : TowerClass ell k Lu U ε :=
    towerClass_of_blocking ell k Lu hell2 U q0 e hq0 h0 R.hlinks R.hN R.hcb
  have hreg : RegTower ell (bgTower (GF ell k Lu) U) k :=
    AdalyFormal.RegBgKU.regTower_M0_kuniform ell k Lu hell2 U e q0 he0 hq0 R.hlinks R.hplaq H
  have hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2 :=
    fun j hj => hsm_of_le ell hell0 (ε j) (hεnn j) (hεs j hj)
  have hmraw := fun x => hm_of_tower ell k Lu hell0 U a ha.le ε hreg hcl (fun j _ => hεnn j) hsm x
  set δm := Real.sqrt a * phiC ell (3600 * (ell : ℝ) * ρ) / n with hδm
  have hdM : deltaM ell k a ε ≤ δm := by
    have h := class_n_deltaM_bound ell k hell2 a ha.le e q0 he0 hq0 (fun j hj => hεs j hj)
    have h' : n * deltaM ell k a ε ≤ Real.sqrt a * phiC ell (3600 * (ell : ℝ) * ρ) := by
      have e1 : ρ = n * (e + 3 * Real.pi * (n * q0)) := by rw [hρ, hη]
      unfold phiC
      rw [e1]
      exact h
    rw [hδm, le_div_iff₀ hnpos, mul_comm]
    exact h'
  intro x
  exact (hmraw x).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (deltaM_nonneg ell k hell0 a ha.le ε (fun j _ => hεnn j)) hdM 2) (sq_nonneg _))

/-- `φ² < 1/1000` from the chain's own smallness `hsmallU`. -/
theorem phi_sq_small (ell : ℕ) (a t ρ : ℝ) (ha : 0 < a) (ht : 0 < t) (hρ : 0 ≤ ρ)
    (hs : ThetaM0 ell a t ρ < min a 1 / 1000) : phiC ell (3600 * (ell : ℝ) * ρ) ^ 2 < 1 / 1000 := by
  unfold ThetaM0 at hs
  have hpi := Real.pi_pos
  have h1 : 0 ≤ Stil (Real.sqrt 3) (Real.sqrt (Mc a)) ρ ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (1 + t) * (272 * (ρ / (3 * Real.pi)) / (4 * Real.sqrt 2)) := by positivity
  have h3 : 0 ≤ 32 * ρ ^ 2 := by positivity
  have hφ := sq_nonneg (phiC ell (3600 * (ell : ℝ) * ρ))
  have h4 : a * phiC ell (3600 * (ell : ℝ) * ρ) ^ 2 ≤ (1 + 1 / t) * (32 * ρ ^ 2 + a * phiC ell (3600 * (ell : ℝ) * ρ) ^ 2) := by
    have : 1 ≤ 1 + 1 / t := by have := one_div_pos.mpr ht; linarith
    nlinarith [mul_nonneg ha.le hφ]
  have h5 : min a 1 / 1000 ≤ a / 1000 := div_le_div_of_nonneg_right (min_le_left a 1) (by norm_num)
  have h6 : a * phiC ell (3600 * (ell : ℝ) * ρ) ^ 2 < a / 1000 := by linarith
  have h7 : a * phiC ell (3600 * (ell : ℝ) * ρ) ^ 2 < a * (1 / 1000) := by linarith
  exact lt_of_mul_lt_mul_left h7 ha.le

/-- **`InstIneq` at M0 with explicit k- and volume-free `γ₀`, conditional ONLY on the D-layer (`hD2`, `hJ`).** -/
theorem instIneq_M0_kuniform (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0) (H : KUSmall ell (rhoM0 ell k e q0))
    (HU : UnitSmall ell (rhoM0 ell k e q0))
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam)
    (ε2s εJ : ℝ) (hε2s : 0 ≤ ε2s) (hεJ : 0 ≤ εJ)
    (hε' : ε2s * KhatM0 ell a t (rhoM0 ell k e q0) < 1)
    (hD2 : ‖(PU ell k Lu hell U a Lam).data.Delta2 (PU ell k Lu hell U a Lam).data_laws‖
      ≤ ε2s / ((ell : ℝ) ^ k) ^ 2)
    (hJ : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
        |⟪(PU ell k Lu hell U a Lam).H1in ((PU ell k Lu hell U a Lam).D2in
            (WithLp.toLp 2 (Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt))), (PU ell k Lu hell U a Lam).Jf⟫|
          ≤ εJ * ‖(WithLp.toLp 2 (Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt) : BondFnL2 Lu)‖ ^ 2) :
    InstIneq ell k hell a Lu
      (gam0M0 ell a t (rhoM0 ell k e q0) ε2s εJ (dCM0 ell (rhoM0 ell k e q0)) (cBM0 ell (rhoM0 ell k e q0)))
      (fullTower ell k Lu) Lam U := by
  have hell2 : 2 ≤ ell := R.hell
  set ρ := rhoM0 ell k e q0 with hρdef
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hnpos : 0 < n := pow_pos (by exact_mod_cast hell) k
  have ha := R.ha
  have hρnn : 0 ≤ ρ := le_trans (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) k) R.he0)
    (class_bounds ell k (by omega) e q0 R.he0 R.hq0).1
  set Kh := KhatM0 ell a t ρ with hKh
  have hKhpos : 0 < Kh := KhatM0_pos ell a t ρ ha R.h216
  -- Q* injective
  have hC1 := hC1_M0 ell k Lu U a t e q0 R H
  have hφ := phi_sq_small ell a t ρ ha R.ht hρnn R.hsmallU
  have hsm : 16 * n ^ 2 * (Real.sqrt a * phiC ell (3600 * (ell : ℝ) * ρ) / n) ^ 2 < a := by
    rw [div_pow, mul_pow, Real.sq_sqrt ha.le]
    have e1 : 16 * n ^ 2 * (a * phiC ell (3600 * (ell : ℝ) * ρ) ^ 2 / n ^ 2)
        = a * (16 * phiC ell (3600 * (ell : ℝ) * ρ) ^ 2) := by field_simp
    rw [e1]
    have : 16 * phiC ell (3600 * (ell : ℝ) * ρ) ^ 2 < 1 := by linarith
    nlinarith
  have hQs := qs_injective_PU ell k Lu hell U a ha Lam _ hC1 hsm
  -- units
  have hcoer : ∀ y : ↥(bondSupp (PU ell k Lu hell U a Lam).G),
      ‖y‖ ^ 2 ≤ n ^ 2 * Kh * ⟪y, (PU ell k Lu hell U a Lam).data.Ginv y⟫ :=
    fun y => ginv_coercive_M0_kuniform ell k Lu U a t e q0 R H Lam y
  have hC0 : 0 < n ^ 2 * Kh := by positivity
  have hε2C : ε2s / n ^ 2 * (n ^ 2 * Kh) < 1 := by
    rw [show ε2s / n ^ 2 * (n ^ 2 * Kh) = ε2s * Kh by field_simp]; exact hε'
  obtain ⟨hG, hN⟩ := units_PU ell k Lu hell U a Lam (n ^ 2 * Kh) (ε2s / n ^ 2) hC0 hε2C hcoer hD2 hQs
  -- the unit background
  set P := PU ell k Lu hell U a Lam with hP
  have hκ0 : 0 ≤ kapHat ell ρ := by unfold kapHat; have := Kc_pos ell hell2; positivity
  obtain ⟨S, -⟩ := towerSmall_of_KU ell k hell2 e q0 R.he0 R.hq0 H
  have hV : ∀ e', frobNorm ((P.unitBgU e' : M2) - 1) ≤ kapHat ell ρ := by
    intro e'
    have h1 := dv_bg_le ell k hell2 U e q0 R.he0 R.hq0 R.hlinks (pw_one_of_plaq U q0 R.hq0 R.hplaq) S k le_rfl
      (embY ell k Lu hell e'.1, e'.2)
    exact h1.trans (kap_le_kapHat ell k hell2 e q0 R.he0 R.hq0)
  have hns := AdalyFormal.NonflatJet.numeric_small hell (kapHat ell ρ) hκ0 HU.u1
  have hreg1 : RegBg 1 ell P.unitBgU :=
    AdalyFormal.NonflatJet.regBg_of_small Nat.one_pos P.unitBgU (kapHat ell ρ) hκ0 hV HU.u2
  have hbV : Function.Bijective (H0 Lam (Q1jet ell P.unitBgU)) :=
    AdalyFormal.M0Finish.R7.hb_of_small P hd (kapHat ell ρ) hκ0 HU.u1 HU.u2 hV
  have hdC0 : 0 ≤ dCM0 ell ρ := by unfold dCM0; positivity
  have hcB : 0 ≤ cBM0 ell ρ := by
    unfold cBM0
    have : 0 < 1 - dCM0 ell ρ := by linarith [HU.u3]
    positivity
  have hC : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      ∑ b : Bond Lu, ‖Cop Lam P.Q1 Bt b - Cop Lam (q1SU2 ell) Bt b‖ ^ 2
          ≤ dCM0 ell ρ ^ 2 * ∑ b : Bond Lu, ‖Cop Lam P.Q1 Bt b‖ ^ 2 ∧
      ∑ b : Bond Lu, ‖Cop Lam P.Q1 Bt b‖ ^ 2 ≤ cBM0 ell ρ ^ 2 * bondEnergy Bt := by
    intro Bt _ _
    have h := AdalyFormal.M0Finish.R7.cop_bounds hell hd Lam P.unitBgU (kapHat ell ρ) hκ0 hV hns.1 hreg1 hbV
      (dCM0 ell ρ) rfl HU.u3 Bt
    refine ⟨h.1, ?_⟩
    have e1 : cBM0 ell ρ ^ 2 = ((1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) / (1 - dCM0 ell ρ)) ^ 2 := rfl
    rw [e1]; exact h.2
  exact instIneq_M0_cond ell k Lu hell U a t e q0 R H hstrict hd Lam hLB hG hN ε2s εJ (dCM0 ell ρ) (cBM0 ell ρ)
    hε2s hεJ hcB hε'.le hD2 hJ hC

#print axioms dCM0
#print axioms cBM0
#print axioms kap_le_kapHat
#print axioms hC1_M0
#print axioms phi_sq_small
#print axioms instIneq_M0_kuniform

end AdalyFormal.M0Finish
