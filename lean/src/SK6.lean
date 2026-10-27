import SK5
import SK6a
import UD13

/-!
# SK6 -- `class_core`: the headline block `P428Genuine8 ell (ell^m) R hell a` from `RemainingInputs` (lane m2_skeleton_20261015)

Analogue of MA19 `m1Core_ell_a`.  Order of choices (the headline order): `ell, a` first; `m₀`; `m ≥ m₀`; `R₀`; `R ≥ R₀`; then `a₀, γ₀`
(depending on `ell, a, m, R`, the field constants `c_i` and thresholds `s_i`) and only then `k, Lu, α₀, S, Λ, U`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false
namespace AdalyFormal.M2Skel

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp OnLambdaTildeIn TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled OnLambdaT)
open AdalyFormal.StatementLaneG (gparams LambdaOK2 InstIneq P428Genuine8 P428Core8 P428Core8At CoercG8At SidePow6)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1IMS AdalyFormal.M1GaugeW4 AdalyFormal.TowerLoc
open AdalyFormal.M1DK (KDsmall kapM1 beta0 beta0_pos KDsmall_of_le)
open AdalyFormal.M1Assembly (eps_choice cwW4_lower KG_small)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

theorem class_core (RI : RemainingInputs) {ell : ℕ} (hell2 : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8 ell (ell ^ m) R (by omega) a := by
  have hell0 : 0 < ell := by omega
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell0
  -- (ell, a)-constants
  obtain ⟨cW, hcW, a0P, ha0P, D, hD, hDle, hw4⟩ := w4_class hell2 ha
  obtain ⟨W₀, hW₀, ε1, hε1, a₁, ha₁, hN⟩ := AdalyFormal.M1W4Num.w4Num_exists ell hell2 a ha
  have hlp := AdalyFormal.M1W4Num.aLin_pos ell hell0
  have hε1' : ε1 < 1 := by
    obtain ⟨-, -, h0⟩ := hN 1 W₀ one_pos le_rfl 0 le_rfl (by simpa using ha₁.le)
    have h := h0.hη
    have hr : rho1 12 1 0 = 0 := by simp [rho1]
    rw [hr] at h
    unfold etaC nuC at h
    simpa using h
  obtain ⟨δ, hδ, c1, hc1, hU1⟩ := AdalyFormal.M1Num.cw_uniform ell hell0 a ε1 1 (min a (cW / 2)) ha hε1 hε1' one_pos
    (lt_min ha (by linarith))
  set Γ : ℝ := Gam0 ell with hΓ
  have hΓ0 : 0 < Γ := Gam0_pos hell0
  set T1 : ℝ := 4 / (1 - ε1) + 1 with hT1
  have hT1p : 0 < T1 := by
    have : 0 < 4 / (1 - ε1) := div_pos (by norm_num) (by linarith)
    rw [hT1]; linarith
  obtain ⟨εJ, ε2s, hεJ, hε2s, hε2c1, hε2c2, he1, he2⟩ :=
    eps_choice a 1 c1 c1 (Γ / (8 * T1)) ha one_pos hc1 hc1 (by positivity)
  obtain ⟨s₀, hs₀, hwin⟩ := Etc_window ell a ε1 c1 Γ hε1' hc1 hΓ0
  obtain ⟨s₁, hs₁, hcu⟩ := cu_window ell hell0
  obtain ⟨Mc₀, hMc₀, hMcw⟩ := Mc_window ell hell0
  obtain ⟨M₁, hM₁⟩ := KG_small ell δ hδ
  -- the open fields
  obtain ⟨mH, hH⟩ := RI.siteS1 ell hell2 a ha
  obtain ⟨mG, hG⟩ := RI.rowBound ell hell2 a ha
  obtain ⟨mC, hC⟩ := RI.massComm ell hell2 a ha
  obtain ⟨df, mI, hI⟩ := RI.interfaceCharts ell hell2 a ha
  obtain ⟨mO, hO⟩ := RI.opLayer ell hell2 a ha
  obtain ⟨mQ, hQ⟩ := RI.qsInj ell hell2 a ha
  set d : ℕ := max D df with hd
  refine ⟨mH + mG + mC + mI + mO + mQ + 8 + (d + 64 * ell ^ 2 + 2) + M₁ + (Mc₀ + 1), by omega, fun m hm => ?_⟩
  have hmH : mH ≤ m := by omega
  have hmG : mG ≤ m := by omega
  have hmC : mC ≤ m := by omega
  have hmI : mI ≤ m := by omega
  have hmO : mO ≤ m := by omega
  have hmQ : mQ ≤ m := by omega
  have hm8 : 8 ≤ m := by omega
  have hmd : d + 64 * ell ^ 2 + 2 ≤ m := by omega
  have hmM1 : M₁ ≤ m := by omega
  have hmMc : Mc₀ + 1 ≤ m := by omega
  have hmM : m < ell ^ m := Nat.lt_pow_self (by omega)
  have hMge : ell ≤ ell ^ m := by
    calc ell = ell ^ 1 := (pow_one ell).symm
      _ ≤ ell ^ m := Nat.pow_le_pow_right hell0 (by omega)
  obtain ⟨R1H, hR1H⟩ := hH m hmH
  obtain ⟨R1G, hR1G⟩ := hG m hmG
  obtain ⟨R1C, hR1C⟩ := hC m hmC
  obtain ⟨R1I, hR1I⟩ := hI m hmI
  obtain ⟨R1O, hR1O⟩ := hO m hmO
  obtain ⟨R1Q, hR1Q⟩ := hQ m hmQ
  refine ⟨R1H + R1G + R1C + R1I + R1O + R1Q + W₀ + 9 * ell + 24 + (⌈1 / δ⌉₊ + 1), fun R hR => ?_⟩
  have hRH : R1H ≤ R := by omega
  have hRG : R1G ≤ R := by omega
  have hRC : R1C ≤ R := by omega
  have hRI : R1I ≤ R := by omega
  have hRO : R1O ≤ R := by omega
  have hRQ : R1Q ≤ R := by omega
  have hRW : W₀ ≤ R := by omega
  have hR9 : 9 * ell ≤ R := by omega
  have hR24 : 24 ≤ R := by omega
  have hRc : ⌈1 / δ⌉₊ + 1 ≤ R := by omega
  obtain ⟨hpow, hMc0, hMbig, hRMn⟩ := AdalyFormal.M2UnitCharts.headline_numerics (R := R) hell2 hm8 (by omega)
  obtain ⟨cH, -, sH, hsH, hHf⟩ := hR1H R hRH
  obtain ⟨cG, -, sG, hsG, hGf⟩ := hR1G R hRG
  obtain ⟨cC, -, sC, hsC, hCf⟩ := hR1C R hRC
  obtain ⟨cI, -, sI, hsI, hIf⟩ := hR1I R hRI
  obtain ⟨cO, ⟨hθ, hq, hKH, hKH1, hK2, hCW, hKD⟩, sO, hsO, hOf⟩ := hR1O R hRO
  obtain ⟨cQ, -, sQ, hsQ, hQf⟩ := hR1Q R hRQ
  have hM0 : 0 < ell ^ m := by omega
  have hM5 : 5 ≤ ell ^ m := by omega
  have hR1 : 1 ≤ R := by omega
  have hRM4 : 4 ≤ R * ell ^ m := by
    calc 4 ≤ 24 * ell := by omega
      _ ≤ R * ell := Nat.mul_le_mul_right ell hR24
      _ ≤ R * ell ^ m := Nat.mul_le_mul_left R hMge
  have hroom : 17 * ell ≤ R * ell ^ m := by
    calc 17 * ell ≤ R * ell := Nat.mul_le_mul_right ell (by omega)
      _ ≤ R * ell ^ m := Nat.mul_le_mul_left R hMge
  have hRl : 3 * 12 ≤ R * ell := by
    calc 3 * 12 ≤ 24 * 2 := by norm_num
      _ ≤ R * ell := Nat.mul_le_mul hR24 hell2
  have hR4 : (5 + 4) * 1 * ell ≤ R := by omega
  have hR8 : 8 * ell ≤ R := by omega
  have hdM : d + 64 * ell ^ 2 + 2 ≤ ell ^ m := by omega
  obtain ⟨a₁D, ha₁D, hDL⟩ := AdalyFormal.M2DLayer.dlayerObligationClass_holds hell0 hell2 hR1 hM0 hRM4 a hθ hq hKH hKH1 hK2 hCW hKD
    ε2s hε2s εJ hεJ
  set sthr : ℝ := min (min (min a₁ (AdalyFormal.M1W4Num.aLin ell)) (min (beta0 ell) (δ / 2))) (min s₀ s₁) with hsthr
  have hsthr0 : 0 < sthr := lt_min (lt_min (lt_min ha₁ hlp) (lt_min (beta0_pos ell hell0) (by positivity))) (lt_min hs₀ hs₁)
  set a₀ : ℝ := min (min (min (min sH sG) (min sC sI)) (min (min sO sQ) (min a0P (min 1 a₁D))))
    (sthr / (2 * (ell : ℝ) ^ 3)) with ha₀
  have ha₀pos : 0 < a₀ := lt_min (lt_min (lt_min (lt_min hsH hsG) (lt_min hsC hsI)) (lt_min (lt_min hsO hsQ)
    (lt_min ha0P (lt_min one_pos ha₁D)))) (by positivity)
  have hΓT : 0 < Γ / (4 * T1) := by positivity
  refine ⟨⟨hell2, ⟨m, by omega, rfl⟩, ha⟩, a₀, ha₀pos, Γ / (4 * T1), hΓT, ?_⟩
  intro k hk Lu α₀ hα hbound hT S hS Lam hL U0 hU0
  suffices main : ∀ U : LinkCfg (scaleUp ell k Lu), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) 12 k S e → U e = 1) →
      InstIneq ell k hell0 a Lu (Γ / (4 * T1)) S Lam U by
    have hroom0 : 17 * ell ≤ R * ell ^ m := by
      calc 17 * ell ≤ R * ell := Nat.mul_le_mul_right ell (by omega)
        _ ≤ R * ell ^ m := Nat.mul_le_mul_left R hMge
    exact inst_of_loc hell0 hell2 hk hS hroom0 (by omega) hL hU0 a _
      (main (Uloc (ell ^ m) S U0) (classCoupled_loc hU0) (fun e he => Uloc_triv he))
  intro U hU hloc
  have hb : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by simpa using hbound
  have hb1 : ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ 1 := by
    have : a₀ ≤ 1 := by simp only [ha₀, min_le_iff, le_refl, true_or, or_true]
    simpa using hb.trans this
  have hbsH : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sH := hb.trans (by simp only [ha₀, min_le_iff, le_refl, true_or, or_true])
  have hbsG : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sG := hb.trans (by simp only [ha₀, min_le_iff, le_refl, true_or, or_true])
  have hbsC : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sC := hb.trans (by simp only [ha₀, min_le_iff, le_refl, true_or, or_true])
  have hbsI : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sI := hb.trans (by simp only [ha₀, min_le_iff, le_refl, true_or, or_true])
  have hbsO : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sO := hb.trans (by simp only [ha₀, min_le_iff, le_refl, true_or, or_true])
  have hbsQ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sQ := hb.trans (by simp only [ha₀, min_le_iff, le_refl, true_or, or_true])
  have hbP : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a0P := hb.trans (by simp only [ha₀, min_le_iff, le_refl, true_or, or_true])
  have hbD : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₁D := hb.trans (by simp only [ha₀, min_le_iff, le_refl, true_or, or_true])
  have hαa : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sthr / (2 * (ell : ℝ) ^ 3) :=
    hb.trans (by simp only [ha₀, min_le_iff, le_refl, true_or, or_true])
  have hα1p : 0 < alpha1 ell α₀ := by unfold alpha1; positivity
  have hsα : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell α₀ = 2 * (ell : ℝ) ^ 3 * ((12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀) := by
    unfold alpha1; ring
  have hs : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell α₀ ≤ sthr := by
    rw [hsα]
    calc 2 * (ell : ℝ) ^ 3 * ((12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀) ≤ 2 * (ell : ℝ) ^ 3 * (sthr / (2 * (ell : ℝ) ^ 3)) :=
          mul_le_mul_of_nonneg_left hαa (by positivity)
      _ = sthr := by field_simp
  have hs0 : 0 ≤ (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell α₀ := by positivity
  have hsa₁ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell α₀ ≤ a₁ := hs.trans (by simp only [hsthr, min_le_iff, le_refl, true_or, or_true])
  have hsLin : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell α₀ ≤ AdalyFormal.M1W4Num.aLin ell :=
    hs.trans (by simp only [hsthr, min_le_iff, le_refl, true_or, or_true])
  have hsβ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell α₀ ≤ beta0 ell := hs.trans (by simp only [hsthr, min_le_iff, le_refl, true_or, or_true])
  have hsδ' : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell α₀ ≤ δ / 2 := hs.trans (by simp only [hsthr, min_le_iff, le_refl, true_or, or_true])
  have hss₀ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell α₀ ≤ s₀ := hs.trans (by simp only [hsthr, min_le_iff, le_refl, true_or, or_true])
  have hss₁ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell α₀ ≤ s₁ := hs.trans (by simp only [hsthr, min_le_iff, le_refl, true_or, or_true])
  -- the open fields at this configuration
  have hHc := hHf k hk Lu α₀ hα hbsH hT S hS Lam hL U hU hloc
  have hGc := hGf k hk Lu α₀ hα hbsG hT S hS Lam hL U hU hloc
  have hCc := hCf k hk Lu α₀ hα hbsC hT S hS Lam hL U hU hloc
  have hIc := hIf k hk Lu α₀ hα hbsI hT S hS Lam hL U hU hloc d (le_max_right D df) hdM
  have hOc := hOf k hk Lu α₀ hα hbsO hT S hS Lam hL U hU hloc
  have hQc := hQf k hk Lu α₀ hα hbsQ hT S hS Lam hL U hU hloc
  -- numerics at alpha1
  obtain ⟨ha1', hsm4, hsmA, hrr⟩ := AdalyFormal.M1W4Num.lin_small ell (ell ^ m) hell0 (alpha1 ell α₀) hα1p.le hsLin
  have hKD : KDsmall ell (12 * ((ell ^ m : ℕ) : ℝ) * alpha1 ell α₀) := KDsmall_of_le ell hell0 _ hs0 hsβ
  obtain ⟨hW, -, hNum⟩ := hN (ell ^ m) R hM0 hRW (alpha1 ell α₀) hα1p.le hsa₁
  have h216 := (rhoT_smalls ell 12 (ell ^ m) (alpha1 ell α₀) hα1p.le hell0 hsm4).1
  have hcs : 0 < csOf a (rhoT ell 12 (ell ^ m) (alpha1 ell α₀)) := by
    unfold csOf
    exact div_pos (by linarith) (lt_max_of_lt_left (by norm_num))
  have hsδ : |((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell α₀| < δ := by
    rw [show ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell α₀ = (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell α₀ by norm_num,
      abs_of_nonneg hs0]
    linarith
  have hWpos : (0 : ℝ) < ((R * ell ^ m * ell : ℕ) : ℝ) := by
    have : 0 < R * ell ^ m * ell := by positivity
    exact_mod_cast this
  have hxδ : ((R * ell ^ m * ell : ℕ) : ℝ)⁻¹ < δ := by
    have h1 : 1 / δ < (R : ℝ) := by
      have := Nat.lt_of_ceil_lt (by omega : ⌈1 / δ⌉₊ < R)
      exact_mod_cast this
    have h2 : (R : ℝ) ≤ ((R * ell ^ m * ell : ℕ) : ℝ) := by
      have : R ≤ R * ell ^ m * ell := le_trans (Nat.le_mul_of_pos_right R hM0) (Nat.le_mul_of_pos_right _ hell0)
      exact_mod_cast this
    rw [inv_eq_one_div, div_lt_iff₀ hWpos]
    rw [div_lt_iff₀ hδ] at h1
    calc (1 : ℝ) < (R : ℝ) * δ := h1
      _ ≤ ((R * ell ^ m * ell : ℕ) : ℝ) * δ := mul_le_mul_of_nonneg_right h2 hδ.le
      _ = δ * ((R * ell ^ m * ell : ℕ) : ℝ) := mul_comm _ _
  have hxδ' : |((R * ell ^ m * ell : ℕ) : ℝ)⁻¹| < δ := by
    rw [abs_of_nonneg (inv_nonneg.mpr hWpos.le)]; exact hxδ
  have hKδ : |AdalyFormal.M1IMS.KG ell (ell ^ m) 1 5| < δ := by
    rw [abs_of_nonneg (AdalyFormal.M1IMS.KG_nonneg ell (ell ^ m) 1 5)]
    exact hM₁ _ (by omega)
  have cw1 := cwW4_lower (ell := ell) (M := ell ^ m) (R := R) (d := d) (a := a) (cW := cW) (α₀ := alpha1 ell α₀) hε1 hα1p.le
    (hDle d (le_max_left _ _)) hcs hNum.hη (fun s x K hs hx hK => hU1 s x K hs hx hK) hsδ hxδ' hKδ
  have hηk : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hcoer : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G),
      c1 * AdalyFormal.M1.wnormSq S ell k (A : AdalyFormal.Balaban.CovariantOperators.BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ := by
    intro A
    have h := hw4 hell0 hS hM0 hR1 hR24 hRl hR4 hroom (le_max_left D df) hdM hW le_rfl U hα hbP hU hb1 Lam ε1 1 hε1
      one_pos hNum h216 hHc hGc hCc (hIc) A
    exact le_trans (mul_le_mul_of_nonneg_right cw1 (AdalyFormal.M1DStrat.wnormSq_nonneg' S _)) h
  have hDS := hDL k hk Lu α₀ hα hbD hT S hS hU.1 Lam hL U hU hOc
  have hb' := AdalyFormal.M2UnitCharts.hb_class hell2 hT (by omega) hRMn S hS Lam hL U a α₀ hα hU (alpha1 ell α₀) rfl hKD
  obtain ⟨hG', hNm'⟩ := AdalyFormal.M1IMS.units_strat ell k Lu hell0 S U a Lam c1 ε2s hε2c2 hcoer hDS.1 hQc
  have hWD : AdalyFormal.StatementLaneG.GenP.WellDef (gparams ell k Lu hell0 S U a Lam) := ⟨hb', hG', hNm'⟩
  have hreg := holRegime_rho1 (show 1 ≤ ell by omega) hS hηk hα.le hb1 hU
  have hMcge : Mc₀ ≤ ell ^ (m - 1) := by
    have : m - 1 < ell ^ (m - 1) := Nat.lt_pow_self (by omega)
    omega
  have hcU := cU_lower (Mc := ell ^ (m - 1)) hell0 hs0 hcu hss₁ hMc0 (hMcw _ hMcge)
  have hrho : AdalyFormal.NonflatJet.rhoOf ell (kapM1 (12 * ((ell ^ m : ℕ) : ℝ) * alpha1 ell α₀)) < Real.pi / 2 := by
    have := (hcu _ hs0 hss₁).1
    linarith [Real.pi_gt_three]
  obtain ⟨hw1, hw3⟩ := hwin _ hs0 hss₀
  exact config_inst_class hell2 hS hroom hM0 hT hL U hα hU a ha hpow hMc0 hMbig hRMn ha1' hsm4 hsmA hrr hKD hrho hcU hb' ε1 hε1 hε1' hNum
    hWD c1 ε2s εJ hc1 hε2s.le hεJ.le hε2c1 hcoer hDS.1 hDS.2 h216 hHc hreg hw1 hw3 he1 (by simpa using he2)

end AdalyFormal.M2Skel

#print axioms AdalyFormal.M2Skel.class_core
