import DLR3

/-!
# DL4 -- `InstIneq` at M0 with the D-layer premise in FORM shape (copies of MF4 `instIneq_M0_cond`, MF7 `instIneq_M0_kuniform`)

`gam0M0f ell a t ρ ε' εJ dC cB := gam0Form γ a ε' εJ (EbarM0 ell a t ρ) dC cB` with `γ = (1/54) ell⁻⁵`; MF4's `gam0M0 .. ε2s ..` is the case
`ε' = ε2s · K̂` (`gam0M0_eq_f`, by `rfl`).  Proof bodies are TEXT COPIES with only the ε2s·K̂ → ε' bookkeeping and the calls to the
form-shaped `u_side_f` / `units_PU_f` (DL3) changed.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp OnLambdaTildeIn)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneG (LamBlockSum InstIneq gparams GenP.genForm GenP.genC GenP.Nmat pe tauAdj_apply)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily (q1SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy frobSupBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.AsmM0
open AdalyFormal.SliceCoerc
open AdalyFormal.PortSlice
open AdalyFormal.BondComposite
open AdalyFormal.CurvBlock (dv pw pw_one_of_plaq)
open AdalyFormal.RegBgKU (KUSmall kapHat Kc Kc_pos kap Bnd TowerSmall towerSmall_of_KU class_bounds dv_bg_le
  regTower_M0_kuniform ginv_coercive_M0_kuniform)
open AdalyFormal.NonflatJet (rhoOf r0)
open SmallnessBridge.Assemble (loopFactorBound)
open EstimatesLayer.E1E3
open AdalyFormal.M0Finish

/-- the explicit M0 constant with the FORM-shaped D-layer constant `ε'` -/
noncomputable def gam0M0f (ell : ℕ) (a t ρ ε' εJ dC cB : ℝ) : ℝ :=
  gam0Form ((1 / 54) * (1 / (ell : ℝ) ^ 5)) a ε' εJ (EbarM0 ell a t ρ) dC cB

theorem gam0M0_eq_f (ell : ℕ) (a t ρ ε2s εJ dC cB : ℝ) :
    gam0M0 ell a t ρ ε2s εJ dC cB = gam0M0f ell a t ρ (ε2s * KhatM0 ell a t ρ) εJ dC cB := rfl

/-- **`InstIneq` at M0, conditional on the D-layer (`hD2`, `hJ`), the units and the `C`-perturbation.** -/
theorem instIneq_M0_cond_f (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0) (H : KUSmall ell (rhoM0 ell k e q0))
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam)
    (hG : IsUnit (PU ell k Lu hell U a Lam).G1inv) (hN : IsUnit (GenP.Nmat (PU ell k Lu hell U a Lam)))
    (ε' εJ dC cB : ℝ) (hε'0 : 0 ≤ ε') (hεJ : 0 ≤ εJ) (hcB : 0 ≤ cB)
    (hε' : ε' ≤ 1)
    (hD2f : ∀ A : ↥(bondSupp (PU ell k Lu hell U a Lam).G),
      |⟪A, (PU ell k Lu hell U a Lam).data.Delta2 (PU ell k Lu hell U a Lam).data_laws A⟫|
        ≤ ε' * ⟪A, (PU ell k Lu hell U a Lam).data.Ginv A⟫)
    (hJ : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
        |⟪(PU ell k Lu hell U a Lam).H1in ((PU ell k Lu hell U a Lam).D2in
            (WithLp.toLp 2 (Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt))), (PU ell k Lu hell U a Lam).Jf⟫|
          ≤ εJ * ‖(WithLp.toLp 2 (Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt) : BondFnL2 Lu)‖ ^ 2)
    (hC : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
        ∑ b : Bond Lu, ‖Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt b - Cop Lam (q1SU2 ell) Bt b‖ ^ 2
            ≤ dC ^ 2 * ∑ b : Bond Lu, ‖Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt b‖ ^ 2 ∧
        ∑ b : Bond Lu, ‖Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt b‖ ^ 2 ≤ cB ^ 2 * bondEnergy Bt) :
    InstIneq ell k hell a Lu (gam0M0f ell a t (rhoM0 ell k e q0) ε' εJ dC cB) (fullTower ell k Lu) Lam U := by
  -- ===== constants and the M0 derivations (as in ASC4, RegTower from RKF) =====
  have hell2 : 2 ≤ ell := R.hell
  have hell0 : 0 < ell := hell
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
  have hρ216 := R.h216
  set Kh := KhatM0 ell a t ρ with hKh
  have hKhpos : 0 < Kh := KhatM0_pos ell a t ρ ha hρ216
  -- class
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
  have hU : frobSupBond U ≤ ρ / n := by
    refine (frobSupBond_le_of U R.hlinks).trans ?_
    rw [← hηρ, hη]
    nlinarith [mul_nonneg hnpos.le hq0, hpi]
  have hAl : ∀ i, i < k → AlignedLinkBound (ell ^ i) (bgTower (GF ell k Lu) U i) (ρ * (ell : ℝ) ^ i / n) := by
    intro i hi z hz μ
    refine (hcl i hi z hz μ).trans ?_
    refine (hεη i hi).trans (le_of_eq ?_)
    rw [hηρ]; ring
  have hpos : 72 * ρ ^ 2 + 4 * (6 * ρ) ^ 2 < 1 := by nlinarith
  have hE := AdalyFormal.SiteCoercivity.geom_tower_sum ell k hell2 ρ hρnn
  have hu := hu_al ell k Lu hell2 U a ha ρ (6 * ρ) hpos hU (fun i => ρ * (ell : ℝ) ^ i / n) hAl hE
  have hreg : RegTower ell (bgTower (GF ell k Lu) U) k :=
    regTower_M0_kuniform ell k Lu hell2 U e q0 he0 hq0 R.hlinks R.hplaq H
  have hB0 := B0_fullTower ell k Lu hell0 U hreg
  have hsm : ∀ j, j < k → AdalyFormal.NonflatJet.rhoOf ell (ε j) < Real.pi / 2 :=
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
  have hC1 : ∀ x : BondFnL2 (scaleUp ell k Lu),
      ∑ p : BIdx (GF ell k Lu), a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p - (bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2
        ≤ δm ^ 2 * ‖x‖ ^ 2 := fun x =>
    (hmraw x).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (deltaM_nonneg ell k hell0 a ha.le ε (fun j _ => hεnn j)) hdM 2) (sq_nonneg _))
  have hα₀ : 0 ≤ q0 / (4 * Real.sqrt 2) := by positivity
  have hpl : AdalyFormal.NonflatHunit.PlaqDef (q0 / (4 * Real.sqrt 2)) U := by
    intro p
    have h := R.hplaq p
    have e1 : 4 * Real.sqrt 2 * (q0 / (4 * Real.sqrt 2)) = q0 := by
      have : Real.sqrt 2 ≠ 0 := by positivity
      field_simp
    rw [e1]; exact h
  set θ := 272 * (q0 / (4 * Real.sqrt 2)) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  set δc := 4 * Real.sqrt 2 * (ρ / n) with hδc
  set dq := δm / Real.sqrt (a * n) with hdq
  -- coercivity on E₀ (C0 = n² K̂)
  have hcoer : ∀ y : ↥(bondSupp (PU ell k Lu hell U a Lam).G),
      ‖y‖ ^ 2 ≤ n ^ 2 * Kh * ⟪y, (PU ell k Lu hell U a Lam).data.Ginv y⟫ :=
    fun y => ginv_coercive_M0_kuniform ell k Lu U a t e q0 R H Lam y
  -- ===== the inequality =====
  intro Bt hBt hBT
  set P := PU ell k Lu hell U a Lam with hP
  have hFS : P.FullSupp := fullTower_fullSupp ell k Lu hell U a Lam
  set BU : Bond Lu → SuTwo := Cop Lam P.Q1 Bt with hBU
  set B : BondFnL2 Lu := WithLp.toLp 2 BU with hB
  show _ ≤ GenP.genForm P B
  have hC0 : 0 < n ^ 2 * Kh := by positivity
  obtain ⟨x, hQx, hcx, hgen⟩ := u_side_f ell k Lu hell U a Lam hu hB0 hG hN (n ^ 2 * Kh) ε' εJ hC0 hε'0
    hε' hcoer hD2f B (hJ Bt hBt hBT)
  -- the flat top restriction of x
  set Bf : Bond Lu → SuTwo :=
    AdalyFormal.GenuineU1.unitField ell k Lu hell (lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp x)) with hBf
  set B1 : Bond Lu → SuTwo := Cop Lam (q1SU2 ell) Bt with hB1
  -- curl norms
  set c1v := AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GF ell k Lu).Om0)
      (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (trivialU _) x) with hc1v
  set cUv := AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GF ell k Lu).Om0)
      (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U x) with hcUv
  set X := ⟪x, Delta P.G U x⟫ with hX
  -- h2 : ‖cU‖² ≤ X + θ‖x‖²
  have hXdec : X = ‖cUv‖ ^ 2 + AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn (GF ell k Lu).Om0) x x := by
    rw [hX]
    show ⟪x, AdalyFormal.StatementLaneR6.deltaKLocCLM U (plaqIn P.G.Om0) x⟫ = _
    rw [AdalyFormal.StatementLaneR6.inner_deltaKLocCLM, real_inner_self_eq_norm_sq]
  have hdp := theta_ported ell k Lu U hα₀ hpl x
  have h2 : ‖cUv‖ ^ 2 ≤ X + θ * ‖x‖ ^ 2 := by
    rw [hXdec]
    have := neg_abs_le (AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn (GF ell k Lu).Om0) x x)
    rw [hθ]; linarith
  -- h3 : ‖c1‖² ≤ 2‖cU‖² + 2δc²‖x‖²
  have hcd : ‖c1v - cUv‖ ≤ δc * ‖x‖ := by
    refine le_trans (hc_of_frobSup U _ x) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hU (by positivity)) (norm_nonneg _)
  have h3 : ‖c1v‖ ^ 2 ≤ 2 * ‖cUv‖ ^ 2 + 2 * δc ^ 2 * ‖x‖ ^ 2 := by
    have e : c1v = cUv + (c1v - cUv) := by abel
    have h := norm_add_le cUv (c1v - cUv)
    rw [← e] at h
    have h' : ‖c1v‖ ≤ ‖cUv‖ + δc * ‖x‖ := by linarith
    have hn0 := norm_nonneg c1v
    nlinarith [sq_nonneg (‖cUv‖ - δc * ‖x‖), norm_nonneg cUv, mul_nonneg (by positivity : (0:ℝ) ≤ δc) (norm_nonneg x)]
  -- h4 : Stokes, n Kq ≤ ‖c1‖²
  have hS := stokes_full hell (fun ρ' => by have := hstrict ρ'; omega) (WithLp.ofLp x)
  have hc1sum : ‖c1v‖ ^ 2 = ∑ p : PeriodicLatticePlaquette (scaleUp ell k Lu), ‖flatCurlValue (WithLp.ofLp x) p‖ ^ 2 := by
    have hm := AdalyFormal.FlatEllGeneral.masked_curl_norm_sq (plaqIn (GF ell k Lu).Om0) x
    have hOm : (GF ell k Lu).Om0 = Set.univ := fullTower_Om0 ell k Lu
    rw [hOm, AdalyFormal.StatementLaneG.plaqIn_univ] at hm
    rw [hc1v, hOm, AdalyFormal.StatementLaneG.plaqIn_univ]
    rw [show (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (trivialU (scaleUp ell k Lu)) x)
        = (AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2
            (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) x) from rfl, hm]
    simp
  have hnn : ((ell ^ k : ℕ) : ℝ) = n := by rw [hn, Nat.cast_pow]
  rw [hnn] at hS
  -- flat floor
  have hb1 : Function.Bijective (H0 Lam (q1SU2 ell)) := by
    have h := IngrBParams.hb_flat (PU ell k Lu hell flatCfg a Lam) rfl hd
    rw [AdalyFormal.StatementLaneG.Q1_eq_q1SU2 (PU ell k Lu hell flatCfg a Lam) rfl hd] at h
    exact h
  have hfl := flat_floor_pert hell2 hstrict hd hLB hb1 Bt hBt hBT Bf
  -- h7 : dd ≤ 2 dC² β² + 2 dq² ‖x‖²
  have hCU := hC Bt hBt hBT
  have hβsq : ‖B‖ ^ 2 = ∑ b : Bond Lu, ‖BU b‖ ^ 2 := by
    rw [hB, PiLp.norm_sq_eq_of_L2]
  have hdrift : ∑ e' : Bond Lu, ‖Bf e' - BU e'‖ ^ 2 ≤ dq ^ 2 * ‖x‖ ^ 2 := by
    have hmem := fun e' => IngrBParams.mem_of_fullSupp P hFS e'
    have hpt : ∀ e' : Bond Lu, Bf e' - BU e'
        = (bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x (pe P e' (hmem e'))
          - (bondSectorOf (GF ell k Lu) U).Qfull x (pe P e' (hmem e')) := by
      intro e'
      have h1 := AdalyFormal.FlatEllGeneral.Qfull_top_gen (PU ell k Lu hell flatCfg a Lam) rfl x e' (hmem e')
      have h2 := tauAdj_apply P B e' (hmem e')
      rw [← hQx] at h2
      rw [show Bf e' = lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp x)
          (AdalyFormal.GenuineU1.bondsE ell k Lu hell e') from rfl]
      rw [← h1]
      have h3 : BU e' = (WithLp.ofLp B) e' := rfl
      rw [h3, ← h2]
      rfl
    have hsumeq : ∑ e' : Bond Lu, ‖Bf e' - BU e'‖ ^ 2
        = ∑ p : BIdx P.G, ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p
            - (bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2 := by
      refine Fintype.sum_equiv (P.eqv hFS) _ _ (fun e' => ?_)
      rw [hpt e']; rfl
    have hlev : ∀ p : BIdx (GF ell k Lu), a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) = a * n := by
      intro p
      have := AdalyFormal.GenuineU1.Gen.level_eq P hFS p
      show a * (ell : ℝ) ^ (p.1 : ℕ) = a * n
      rw [this]
    have hc1x := hC1 x
    simp only [hlev] at hc1x
    rw [← Finset.mul_sum] at hc1x
    rw [hsumeq]
    have han : 0 < a * n := by positivity
    have hsq : dq ^ 2 = δm ^ 2 / (a * n) := by
      rw [hdq, div_pow, Real.sq_sqrt han.le]
    rw [hsq, div_mul_eq_mul_div, le_div_iff₀ han]
    linarith
  have h7 : ∑ b : Bond Lu, ‖Bf b - B1 b‖ ^ 2 ≤ 2 * dC ^ 2 * ‖B‖ ^ 2 + 2 * dq ^ 2 * ‖x‖ ^ 2 := by
    have hs := sum_sub_sq_le Bf B1 BU
    have hsym : ∑ b : Bond Lu, ‖B1 b - BU b‖ ^ 2 = ∑ b : Bond Lu, ‖BU b - B1 b‖ ^ 2 :=
      Finset.sum_congr rfl (fun b _ => by rw [norm_sub_rev])
    rw [hsym] at hs
    have hc := hCU.1
    rw [← hβsq] at hc
    linarith
  -- h9 : β ≤ cB bt
  have hbt0 : 0 ≤ bondEnergy Bt := Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have h9 : ‖B‖ ≤ cB * Real.sqrt (bondEnergy Bt) := by
    have hc := hCU.2
    rw [← hβsq] at hc
    have : ‖B‖ ^ 2 ≤ (cB * Real.sqrt (bondEnergy Bt)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hbt0]; exact hc
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp this
  -- h4, h8 in the combination's variables
  set Kq := ∑ q : PeriodicLatticePlaquette Lu, ‖flatCurlValue Bf q‖ ^ 2 with hKq
  set dd := ∑ b : Bond Lu, ‖Bf b - B1 b‖ ^ 2 with hdd
  have h4 : n * Kq ≤ ‖c1v‖ ^ 2 := by rw [hc1sum]; exact hS
  have h8 : (1 / 54 * (1 / (ell : ℝ) ^ 5)) * Real.sqrt (bondEnergy Bt) ^ 2 ≤ 2 * Kq + 64 * dd := by
    rw [Real.sq_sqrt hbt0]; exact hfl
  -- the k-free budget
  have hEt : (4 * θ + 4 * δc ^ 2 + 128 * n * dq ^ 2) * n ^ 2 * Kh ≤ EbarM0 ell a t ρ := by
    unfold EbarM0
    rw [← hKh]
    refine mul_le_mul_of_nonneg_right ?_ hKhpos.le
    have hq := (class_bounds ell k (by omega) e q0 he0 hq0).2.1
    have hn2 : ((ell : ℝ) ^ 2) ^ k = n ^ 2 := by rw [hn, ← pow_mul, ← pow_mul, mul_comm]
    rw [hn2] at hq
    have e1 : 4 * θ * n ^ 2 ≤ 4 * (272 * (ρ / (3 * Real.pi)) / (4 * Real.sqrt 2)) := by
      rw [hθ]
      have hs : 0 < 4 * Real.sqrt 2 := by positivity
      have : 272 * (q0 / (4 * Real.sqrt 2)) * n ^ 2 = 272 * (n ^ 2 * q0) / (4 * Real.sqrt 2) := by ring
      rw [mul_assoc, this]
      have h272 : 272 * (n ^ 2 * q0) / (4 * Real.sqrt 2) ≤ 272 * (ρ / (3 * Real.pi)) / (4 * Real.sqrt 2) :=
        div_le_div_of_nonneg_right (by linarith) hs.le
      linarith
    have e2 : 4 * δc ^ 2 * n ^ 2 = 128 * ρ ^ 2 := by
      rw [hδc]
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp
      rw [h2]; ring
    have e3 : 128 * n * dq ^ 2 * n ^ 2 = 128 * phiC ell (3600 * (ell : ℝ) * ρ) ^ 2 := by
      have han : 0 < a * n := by positivity
      rw [hdq, div_pow, Real.sq_sqrt han.le, hδm, div_pow, mul_pow, Real.sq_sqrt ha.le]
      field_simp
    nlinarith [e1, e2, e3]
  have hfin := mf_combine_ub n (1 / 54 * (1 / (ell : ℝ) ^ 5)) Kh a θ δc dq dC cB ε' εJ (EbarM0 ell a t ρ)
    X (‖x‖ ^ 2) ‖B‖ (Real.sqrt (bondEnergy Bt)) Kq (2 * Kq + 64 * dd) (32 * dd) dd (‖cUv‖ ^ 2) (‖c1v‖ ^ 2)
    (GenP.genForm P B) hnpos hKhpos hEt ha.le hθ0 (sq_nonneg _) (norm_nonneg _) (Real.sqrt_nonneg _) hcB
    hε'0 hε' hεJ hcx h2 h3 h4 (by linarith) le_rfl h7 h8 h9 hgen
  rw [Real.sq_sqrt hbt0] at hfin
  exact hfin

/-- **`InstIneq` at M0 with explicit k- and volume-free `γ₀`, conditional ONLY on the D-layer (`hD2`, `hJ`).** -/
theorem instIneq_M0_kuniform_f (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0) (H : KUSmall ell (rhoM0 ell k e q0))
    (HU : UnitSmall ell (rhoM0 ell k e q0))
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam)
    (ε' εJ : ℝ) (hε'0 : 0 ≤ ε') (hεJ : 0 ≤ εJ)
    (hε' : ε' < 1)
    (hD2f : ∀ A : ↥(bondSupp (PU ell k Lu hell U a Lam).G),
      |⟪A, (PU ell k Lu hell U a Lam).data.Delta2 (PU ell k Lu hell U a Lam).data_laws A⟫|
        ≤ ε' * ⟪A, (PU ell k Lu hell U a Lam).data.Ginv A⟫)
    (hJ : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
        |⟪(PU ell k Lu hell U a Lam).H1in ((PU ell k Lu hell U a Lam).D2in
            (WithLp.toLp 2 (Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt))), (PU ell k Lu hell U a Lam).Jf⟫|
          ≤ εJ * ‖(WithLp.toLp 2 (Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt) : BondFnL2 Lu)‖ ^ 2) :
    InstIneq ell k hell a Lu
      (gam0M0f ell a t (rhoM0 ell k e q0) ε' εJ (dCM0 ell (rhoM0 ell k e q0)) (cBM0 ell (rhoM0 ell k e q0)))
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
  obtain ⟨hG, hN⟩ := units_PU_f ell k Lu hell U a Lam (n ^ 2 * Kh) ε' hC0 hε' hcoer hD2f hQs
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
  exact instIneq_M0_cond_f ell k Lu hell U a t e q0 R H hstrict hd Lam hLB hG hN ε' εJ (dCM0 ell ρ) (cBM0 ell ρ)
    hε'0 hεJ hcB hε'.le hD2f hJ hC

#print axioms gam0M0f
#print axioms gam0M0_eq_f
#print axioms instIneq_M0_cond_f
#print axioms instIneq_M0_kuniform_f

end AdalyFormal.DLayer
