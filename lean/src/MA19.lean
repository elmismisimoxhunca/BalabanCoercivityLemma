import MA18

/-!
# MA19 -- `m1Core_ell_a` and `m1Target` (lane m1_assembly_20261014)

The M1 inequality `InstIneq` on proper towers for `M1Regular` `U`, in the headline quantifier order
`exists m0, forall m >= m0, exists R0, forall R >= R0, M1Core ell (ell^m) R a`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 32000000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.M1Assembly

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp OnLambdaTildeIn TorusOK)
open AdalyFormal.StatementLaneG (gparams LambdaOK2 GenP.WellDef InstIneq)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1IMS AdalyFormal.M1GaugeW4 AdalyFormal.TowerLoc
open AdalyFormal.M1DK (KDsmall kapM1 beta0 beta0_pos KDsmall_of_le)
open AdalyFormal.M1NonFlat (epsNF PkA thetaN)

theorem m1Core_ell_a {ell : ℕ} (hell2 : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      AdalyFormal.M1.M1Core ell (ell ^ m) R (by omega) a := by
  have hell0 : 0 < ell := by omega
  obtain ⟨cW1, hcW1, a01, ha01, D1, hD1, hDle1, hall1⟩ := w4_M1_patched hell2 ha
  obtain ⟨cW2, hcW2, a02, ha02, D2, hD2', hDle2, hall2⟩ := wellDef_M1_patched hell2 ha
  obtain ⟨W₀, hW₀, ε1, hε1, a₁, ha₁, hN⟩ := AdalyFormal.M1W4Num.w4Num_exists ell hell2 a ha
  obtain ⟨a₂, ha₂, hQ⟩ := AdalyFormal.M1W4Num.qsNum_small_exists ell hell0
  have hlp := AdalyFormal.M1W4Num.aLin_pos ell hell0
  have hε1' : ε1 < 1 := by
    obtain ⟨-, -, h0⟩ := hN 1 W₀ one_pos le_rfl 0 le_rfl (by simpa using ha₁.le)
    have h := h0.hη
    have hr : rho1 12 1 0 = 0 := by simp [rho1]
    rw [hr] at h
    unfold etaC nuC at h
    simpa using h
  obtain ⟨δ1, hδ1, c1, hc1, hU1⟩ := AdalyFormal.M1Num.cw_uniform ell hell0 a ε1 1 (min a (cW1 / 2)) ha hε1 hε1' one_pos
    (lt_min ha (by linarith))
  obtain ⟨δ2, hδ2, c2, hc2, hU2⟩ := AdalyFormal.M1Num.cw_uniform ell hell0 a ε1 1 (min a (cW2 / 2)) ha hε1 hε1' one_pos
    (lt_min ha (by linarith))
  set Γ : ℝ := 1 / 54 * (1 / (ell : ℝ) ^ 5) with hΓ
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell0
  have hΓ0 : 0 < Γ := by rw [hΓ]; positivity
  set T1 : ℝ := 4 / (1 - ε1) + 1 with hT1
  have hT1p : 0 < T1 := by
    have : 0 < 4 / (1 - ε1) := div_pos (by norm_num) (by linarith)
    rw [hT1]; linarith
  set cBm : ℝ := 2 * (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) with hcBm
  have hcBm0 : 0 < cBm := by rw [hcBm]; positivity
  obtain ⟨εJ, ε2s, hεJ, hε2s, hε2c1, hε2c2, he1, he2⟩ :=
    eps_choice a cBm c1 c2 (Γ / (8 * T1)) ha hcBm0 hc1 hc2 (by positivity)
  obtain ⟨N₀, hN₀⟩ := AdalyFormal.M1DStrat.dlayerObligationW4_holds hell2 hell0 ha hc1
  set δ : ℝ := min δ1 δ2 with hδ
  have hδp : 0 < δ := lt_min hδ1 hδ2
  obtain ⟨M₁, hM₁⟩ := KG_small ell δ hδp
  set d : ℕ := max D1 D2 with hd
  obtain ⟨s₀, hs₀, hwin⟩ := small_window ell a ε1 c1 Γ cBm hε1' hc1 hΓ0
  refine ⟨max 1 (max (max 5 (d + 64 * ell ^ 2)) M₁), le_max_left _ _, fun m hm => ?_⟩
  have hmM : m < ell ^ m := Nat.lt_pow_self (by omega)
  have hMmin : max (max 5 (d + 64 * ell ^ 2)) M₁ ≤ ell ^ m :=
    le_trans (le_trans (le_max_right _ _) hm) hmM.le
  have hM5 : 5 ≤ ell ^ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMmin
  have hMd : d + 64 * ell ^ 2 ≤ ell ^ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMmin
  have hMK : M₁ ≤ ell ^ m := le_trans (le_max_right _ _) hMmin
  refine ⟨max (max W₀ N₀) (max (18 * ell) (⌈1 / δ⌉₊ + 1)), fun R hR => ?_⟩
  have hRW : W₀ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRN : N₀ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hR18 : 18 * ell ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hRc : ⌈1 / δ⌉₊ + 1 ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have hM0 : 0 < ell ^ m := by omega
  have hR1 : 1 ≤ R := by omega
  have hRM : R ≤ R * ell ^ m := Nat.le_mul_of_pos_right R hM0
  have hroom : 17 * ell ≤ R * ell ^ m := by omega
  have hR8 : 8 * ell ≤ R := by omega
  obtain ⟨a₁D, ha₁D, hDL⟩ := hN₀ (ell ^ m) R (by omega) hR8 (by omega) (le_trans hRN hRM) ε2s hε2s εJ hεJ
  have hKGm : AdalyFormal.M1IMS.KG ell (ell ^ m) 1 5 < δ := hM₁ _ hMK
  have hKG0 := AdalyFormal.M1IMS.KG_nonneg ell (ell ^ m) 1 5
  have hWpos : (0 : ℝ) < ((R * ell ^ m * ell : ℕ) : ℝ) := by
    have : 0 < R * ell ^ m * ell := by positivity
    exact_mod_cast this
  have hxδ : ((R * ell ^ m * ell : ℕ) : ℝ)⁻¹ < δ := by
    have h1 : 1 / δ < (R : ℝ) := by
      have := Nat.lt_of_ceil_lt (by omega : ⌈1 / δ⌉₊ < R)
      exact_mod_cast this
    have h2 : (R : ℝ) ≤ ((R * ell ^ m * ell : ℕ) : ℝ) := by
      have : R ≤ R * ell ^ m * ell := le_trans hRM (Nat.le_mul_of_pos_right _ hell0)
      exact_mod_cast this
    rw [inv_eq_one_div, div_lt_iff₀ hWpos]
    rw [div_lt_iff₀ hδp] at h1
    nlinarith
  refine ⟨min (min (min (min a01 a02) (min a₁ (AdalyFormal.M1W4Num.aLin ell)))
      (min (min a₂ (beta0 ell)) (min a₁D (δ / 2)))) s₀, ?_, Γ / (4 * T1), by positivity, ?_⟩
  · refine lt_min (lt_min (lt_min (lt_min ha01 ha02) (lt_min ha₁ hlp)) (lt_min (lt_min ha₂ (beta0_pos ell hell0))
      (lt_min ha₁D (by positivity)))) hs₀
  intro k hk Lu α₀ hα hsm hT S hS hcov Lam hL U hU
  simp only [le_min_iff] at hsm
  obtain ⟨⟨⟨⟨h_a01, h_a02⟩, h_a1, h_lin⟩, ⟨h_a2, h_b0⟩, h_a1D, h_dh⟩, h_s0⟩ := hsm
  obtain ⟨g, A0, hUg, hB⟩ := hU
  have hLu5 : ∀ μ, 5 ≤ Lu μ + 1 := fun μ => le_trans hM5 (Nat.le_of_dvd (Nat.succ_pos _) (hT.2.2 μ))
  have hregV : AdalyFormal.M1.M1Regular ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ (periodicGaugeTransform g U) := by
    refine ⟨fun _ => 1, A0, fun e => ?_, hB⟩
    rw [AdalyFormal.StatementLane2.gauge_one]
    exact hUg e
  obtain ⟨ha1, hsm4, hsmA, hrr⟩ := AdalyFormal.M1W4Num.lin_small ell (ell ^ m) hell0 α₀ hα.le h_lin
  obtain ⟨hW, -, hNum⟩ := hN (ell ^ m) R hM0 hRW α₀ hα.le h_a1
  have hs0 : 0 ≤ (12 : ℝ) * (ell ^ m : ℕ) * α₀ := by positivity
  have hKD : KDsmall ell (12 * (ell ^ m : ℕ) * α₀) := KDsmall_of_le ell hell0 _ hs0 h_b0
  have h216 := (rhoT_smalls ell 12 (ell ^ m) α₀ hα.le hell0 hsm4).1
  have hcs : 0 < csOf a (rhoT ell 12 (ell ^ m) α₀) := by
    unfold csOf
    apply div_pos (by linarith) (lt_max_of_lt_left (by norm_num))
  have hs12 : ((12 : ℕ) : ℝ) * (ell ^ m : ℕ) * α₀ = (12 : ℝ) * (ell ^ m : ℕ) * α₀ := by norm_num
  have hsδ : |((12 : ℕ) : ℝ) * (ell ^ m : ℕ) * α₀| < δ := by
    rw [hs12, abs_of_nonneg hs0]; linarith
  have hxδ' : |((R * ell ^ m * ell : ℕ) : ℝ)⁻¹| < δ := by
    rw [abs_of_nonneg (inv_nonneg.mpr hWpos.le)]; exact hxδ
  have hKδ : |AdalyFormal.M1IMS.KG ell (ell ^ m) 1 5| < δ := by rw [abs_of_nonneg hKG0]; exact hKGm
  have cw1 := cwW4_lower (ell := ell) (M := ell ^ m) (R := R) (d := d) (a := a) (cW := cW1) (α₀ := α₀) hε1 hα.le
    (hDle1 d (le_max_left _ _)) hcs hNum.hη
    (fun s x K hs hx hK => hU1 s x K hs hx hK) (lt_of_lt_of_le hsδ (min_le_left _ _)) (lt_of_lt_of_le hxδ' (min_le_left _ _))
    (lt_of_lt_of_le hKδ (min_le_left _ _))
  have cw2 := cwW4_lower (ell := ell) (M := ell ^ m) (R := R) (d := d) (a := a) (cW := cW2) (α₀ := α₀) hε1 hα.le
    (hDle2 d (le_max_right _ _)) hcs hNum.hη
    (fun s x K hs hx hK => hU2 s x K hs hx hK) (lt_of_lt_of_le hsδ (min_le_right _ _)) (lt_of_lt_of_le hxδ' (min_le_right _ _))
    (lt_of_lt_of_le hKδ (min_le_right _ _))
  have hdM : d + 64 * ell ^ 2 ≤ 1 * ell ^ m := by omega
  have hcoer : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam).G),
      c1 * AdalyFormal.M1.wnormSq S ell k (A : AdalyFormal.Balaban.CovariantOperators.BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A, (gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam).data.Ginv A⟫ := by
    intro A
    have h := hall1 (κ := 1) (c := 5) hell0 hS one_pos (by omega) hR1 (by omega) (le_refl 5) hroom
      (le_max_left D1 D2) hdM hW le_rfl hLu5 (periodicGaugeTransform g U) hregV hα h_a01 ha1 hsm4 hsmA hrr Lam ε1 1 hε1
      one_pos hNum A
    exact le_trans (mul_le_mul_of_nonneg_right cw1 (AdalyFormal.M1DStrat.wnormSq_nonneg' S _)) h
  have hDS := hDL k hk Lu α₀ hα h_a1D hT S hS hcov Lam hL (periodicGaugeTransform g U) hregV hcoer
  have hb := AdalyFormal.M1HB.hb_M1' ell (ell ^ m) R k Lu hell0 S (periodicGaugeTransform g U) a Lam α₀ hS hell2 hroom hT hL
    hregV hα.le h_b0
  have hWD := hall2 (κ := 1) (c := 5) hell0 hS one_pos (by omega) hR1 (by omega) (le_refl 5) hroom
    (le_max_right D1 D2) hdM hW le_rfl hLu5 (periodicGaugeTransform g U) hregV hα h_a02 ha1 hsm4 hsmA hrr Lam ε1 1 hε1
    one_pos hNum (hQ (ell ^ m) α₀ hα.le h_a2) ε2s (lt_of_lt_of_le hε2c2 cw2) hDS.1 hb
  obtain ⟨hw1, hw2, hw3⟩ := hwin ((12 : ℝ) * (ell ^ m : ℕ) * α₀) hs0 h_s0
  exact config_inst hell2 hS hroom hM0 hR8 hT hLu5 hL U g A0 hα hUg hB ha1 hsm4 hsmA hrr hKD a ha ε1 hε1 hε1' hNum hWD
    c1 ε2s εJ hc1 hε2s.le hεJ.le hε2c1 hcoer hDS.1 hDS.2 Γ rfl cBm rfl hw1 hw2 hw3 he1 he2

/-- **`M1Target`**: the M1 inequality on proper towers for `M1Regular` `U`, headline quantifier order. -/
theorem m1Target : AdalyFormal.M1.M1Target := by
  intro ell hell a ha
  exact m1Core_ell_a hell ha

end AdalyFormal.M1Assembly

#print axioms AdalyFormal.M1Assembly.m1Core_ell_a
#print axioms AdalyFormal.M1Assembly.m1Target
