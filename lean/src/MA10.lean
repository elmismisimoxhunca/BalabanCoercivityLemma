import HB2
import MA9

/-!
# MA10 -- the unit-level `C`-perturbation at the M1 chart (lane m1_assembly_20261014)

`cop_M1`: for `U in M1Regular` (gauge `g`), the genuine `C = Cop Lam Q1` of `gparams .. (U^g) ..` satisfies, with `kappa = kapM1 (12 M alpha0)`,
`dC = ell^3 sqrt(384 (ell kappa)^2 + 480 e2Majorant(rhoOf ell kappa)^2)`:
  `sum |C_Q1 Bt - C_1 Bt|^2 <= dC^2 sum |C_Q1 Bt|^2` and `sum |C_Q1 Bt|^2 <= ((1 + ell^3 sqrt(1/ell^3))/(1-dC))^2 ||Bt||^2`.
Route of HB1 `hb_M1` (rows of `Lambda'` read `Ubar^k` only on balls near `Lambda`; `Vcut`), ending in R7 `cop_bounds` instead of the `H0` bijectivity.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1Assembly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible pdist scaleUp CRowIn TorusOK)
open AdalyFormal.StatementLaneG (LambdaOK2 gparams)
open AdalyFormal.StatementLaneR8 (Ball pdist_triangle pdist_comm pdist_coarseShift_le lamPrime_sub)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.IngredientFamilyR2 (RegBg Q1jet H0 IngrBParams Dset Cop)
open AdalyFormal.IngredientFamily (q1SU2)
open AdalyFormal.NonflatJet (rhoOf r0)
open EstimatesLayer.E1E3 (e2Majorant)
open AdalyFormal.DLayer (H0_drift_l1)
open AdalyFormal.M1DK
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- the `C`-perturbation constant. -/
noncomputable def dCof (ell : ℕ) (κ : ℝ) : ℝ :=
  (ell : ℝ) ^ 3 * Real.sqrt (384 * ((ell : ℝ) * κ) ^ 2 + 480 * (e2Majorant (rhoOf ell κ)) ^ 2)

theorem dCof_lt_one (ell : ℕ) (hell : 0 < ell) (κ : ℝ) (hκ : 0 ≤ κ)
    (kd : 192 * (8 * (ell : ℝ) * κ + 8 * e2Majorant (rhoOf ell κ)) ≤ 1 / (2 * (ell : ℝ) ^ 3)) : dCof ell κ < 1 := by
  have hr : (0 : ℝ) < ell := by exact_mod_cast hell
  have hρ0 : 0 ≤ rhoOf ell κ := by
    unfold rhoOf; have := Real.pi_pos; positivity
  have hE0 : 0 ≤ e2Majorant (rhoOf ell κ) := EstimatesLayer.E1E3.e2Majorant_nonneg hρ0
  set E := e2Majorant (rhoOf ell κ) with hE
  have h3 : 0 < (ell : ℝ) ^ 3 := by positivity
  have hx : (ell : ℝ) * κ ≤ 1 / (3072 * (ell : ℝ) ^ 3) := by
    have : 1536 * ((ell : ℝ) * κ) ≤ 1 / (2 * (ell : ℝ) ^ 3) := by nlinarith [mul_nonneg hE0 (by norm_num : (0:ℝ) ≤ 1536)]
    rw [le_div_iff₀ (by positivity)]
    have h4 : 1536 * ((ell : ℝ) * κ) * (2 * (ell : ℝ) ^ 3) ≤ 1 := by
      have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * (ell : ℝ) ^ 3)).mp this
      linarith
    nlinarith
  have hy : E ≤ 1 / (3072 * (ell : ℝ) ^ 3) := by
    have : 1536 * E ≤ 1 / (2 * (ell : ℝ) ^ 3) := by nlinarith [mul_nonneg hr.le hκ]
    rw [le_div_iff₀ (by positivity)]
    have h4 : 1536 * E * (2 * (ell : ℝ) ^ 3) ≤ 1 := by
      have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * (ell : ℝ) ^ 3)).mp this
      linarith
    nlinarith
  unfold dCof
  rw [← hE]
  have hsq : 384 * ((ell : ℝ) * κ) ^ 2 + 480 * E ^ 2 ≤ 864 * (1 / (3072 * (ell : ℝ) ^ 3)) ^ 2 := by
    have h1 : ((ell : ℝ) * κ) ^ 2 ≤ (1 / (3072 * (ell : ℝ) ^ 3)) ^ 2 := pow_le_pow_left₀ (by positivity) hx 2
    have h2 : E ^ 2 ≤ (1 / (3072 * (ell : ℝ) ^ 3)) ^ 2 := pow_le_pow_left₀ hE0 hy 2
    nlinarith
  have hs : Real.sqrt (384 * ((ell : ℝ) * κ) ^ 2 + 480 * E ^ 2) ≤ Real.sqrt (864 * (1 / (3072 * (ell : ℝ) ^ 3)) ^ 2) :=
    Real.sqrt_le_sqrt hsq
  have hs2 : Real.sqrt (864 * (1 / (3072 * (ell : ℝ) ^ 3)) ^ 2) = Real.sqrt 864 * (1 / (3072 * (ell : ℝ) ^ 3)) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  have h864 : Real.sqrt 864 < 31 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  calc (ell : ℝ) ^ 3 * Real.sqrt (384 * ((ell : ℝ) * κ) ^ 2 + 480 * E ^ 2)
      ≤ (ell : ℝ) ^ 3 * (Real.sqrt 864 * (1 / (3072 * (ell : ℝ) ^ 3))) := by
        rw [← hs2]; exact mul_le_mul_of_nonneg_left hs h3.le
    _ = Real.sqrt 864 / 3072 := by field_simp
    _ < 1 := by rw [div_lt_one (by norm_num)]; linarith


theorem cop_M1 (ell M R k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (α₀ : ℝ)
    (hA : Admissible ell M R k S) (hell2 : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hT : TorusOK ell M Lu)
    (hL : LambdaOK2 ell M R k S Lam)
    (g : PeriodicLatticeSite (scaleUp ell k Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (A : Bond (scaleUp ell k Lu) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ e : Bond (scaleUp ell k Lu), ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp (((((ell : ℝ) ^ k)⁻¹ : ℝ) * Complex.I) • A e))
    (hb : AdalyFormal.M1.M1Bounds S ell M 12 k α₀ ((ell : ℝ) ^ k)⁻¹ A)
    (hα : 0 ≤ α₀) (hsm : KDsmall ell (12 * M * α₀)) (Bt : Bond Lu → SuTwo) :
    ∑ b, ‖Cop Lam (gparams ell k Lu hell S (periodicGaugeTransform g U) a Lam).Q1 Bt b - Cop Lam (q1SU2 ell) Bt b‖ ^ 2
        ≤ (dCof ell (kapM1 (12 * M * α₀))) ^ 2 *
          ∑ b, ‖Cop Lam (gparams ell k Lu hell S (periodicGaugeTransform g U) a Lam).Q1 Bt b‖ ^ 2 ∧
      ∑ b, ‖Cop Lam (gparams ell k Lu hell S (periodicGaugeTransform g U) a Lam).Q1 Bt b‖ ^ 2
        ≤ ((1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) / (1 - dCof ell (kapM1 (12 * M * α₀)))) ^ 2
          * bondEnergy Bt := by
  set β : ℝ := 12 * M * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  obtain ⟨hlk, hpl⟩ := chart_bounds ell M k hell S α₀ U g A _ rfl hg hb hα hsm.h1
  have hd : ∀ μ, ell ∣ Lu μ + 1 := hT.1
  have hT3 : ∀ μ, 3 ≤ Lu μ + 1 := fun μ => by have := hT.2.1 μ; omega
  set P' := gparams ell k Lu hell S (periodicGaugeTransform g U) a Lam with hP'
  have hnear : ∀ c : CoarseBond Lu ell, CRowIn ell Lam c → ∀ z ∈ Ball c.1.1 (4 * (1 * ell)), ∀ μ : Fin 3,
      frobNorm (((P'.unitBgU (z, μ) : SU2) : M2) - 1) ≤ kapM1 β := by
    intro c hc z hz μ
    have hz' : pdist c.1.1 z ≤ 4 * (1 * ell) := hz
    obtain ⟨y, hy, hyz⟩ : ∃ y ∈ Lam, pdist y z + 17 ≤ R * M := by
      rcases hc with h | h
      · exact ⟨c.1.1, lamPrime_sub hell h, by omega⟩
      · refine ⟨coarseShift c.1.1 ell c.2, lamPrime_sub hell h, ?_⟩
        have h1 : pdist (coarseShift c.1.1 ell c.2) c.1.1 ≤ ell := by
          rw [pdist_comm]; exact pdist_coarseShift_le _ _ _
        have h2 := pdist_triangle (coarseShift c.1.1 ell c.2) c.1.1 z
        omega
    exact tower_near ell M R k Lu hell2 hell S hA Lam hL hT3 (periodicGaugeTransform g U) β (qM1 β)
      (qM1_nonneg hβ0) hlk hpl hsm.hcb hy hyz μ
  set κ := kapM1 β with hκ
  have hκ0 : 0 ≤ κ := kapM1_nonneg hβ0
  set V0 := Vcut ell Lam P'.unitBgU with hV0
  have hV : ∀ e', frobNorm (((V0 e' : SU2) : M2) - 1) ≤ κ := Vcut_small ell Lam P'.unitBgU κ hκ0 hnear
  have hns := AdalyFormal.NonflatJet.numeric_small hell κ hκ0 hsm.u1
  have hreg1 : RegBg 1 ell V0 := AdalyFormal.NonflatJet.regBg_of_small Nat.one_pos V0 κ hκ0 hV hsm.u2
  set δ := 192 * (8 * (ell : ℝ) * κ + 8 * e2Majorant (rhoOf ell κ)) with hδ
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hδlt : δ < 1 / (ell : ℝ) ^ 3 := by
    have : 1 / (2 * (ell : ℝ) ^ 3) < 1 / (ell : ℝ) ^ 3 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_pos hellR 3]
    linarith [hsm.kd]
  have hdrift := fun w => H0_drift_l1 hell hd Lam V0 κ hκ0 hV hns.1 hreg1 w
  have hbV : Function.Bijective (H0 Lam (Q1jet ell V0)) := H0_bij_of_drift hell hd Lam (Q1jet ell V0) δ hδlt hdrift
  have hcongr : Cop Lam P'.Q1 = Cop Lam (Q1jet ell V0) :=
    AdalyFormal.StatementLaneR8.Cop_congr_rows Lam (fun B c hc => Q1jet_cut ell Lam P'.unitBgU B hc)
  have hdC1 : dCof ell κ < 1 := dCof_lt_one ell hell κ hκ0 hsm.kd
  have h := AdalyFormal.M0Finish.R7.cop_bounds hell hd Lam V0 κ hκ0 hV hns.1 hreg1 hbV (dCof ell κ) rfl hdC1 Bt
  rw [hcongr]
  exact h

end AdalyFormal.M1Assembly

#print axioms AdalyFormal.M1Assembly.dCof_lt_one
#print axioms AdalyFormal.M1Assembly.cop_M1
