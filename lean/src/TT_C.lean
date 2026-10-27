import TT_B
import UMC
import AC_SV1
import AC_Thin
import AU_UD13

/-!
# TT_C -- the strong core, cube-factor-FREE, ALL constants (`γ₀, m₀, R₀, a₀`) before `fc`, `m`, `R` (lane total_20261017)

Text copy of the core of `UnifMax.UMC` (`strong_coreUH`, `strong_coreUC`; lane unif_20261016) with the AllC lane's c-free substitutions of `AU_XSV4`
(`headline_numericsU`, `hb_classU`, `config_inst_classU`, extra `BallChartsAt` conjunct `hBall` and constants `C ≤ K` from `FieldsKT`, no `3 fc` in the `R`-threshold,
`w4_classU`) and the cube factor `fc ≥ 10` quantified after `a₀`.  The explicit D-layer witness `a1D`/`dlayer_explicit` is the UMC one (read-only import).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false

namespace AdalyFormal.Total
open AdalyFormal.AllC
open AdalyFormal.UnifMax (a1D a1D_pos dlayer_explicit)

section core
open AdalyFormal.M2RightInv
open AdalyFormal.M2Skel
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

theorem strong_coreT (hF : ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → FieldsKT ell (by omega) a)
    (hOT : OpLayerThickT) (hRI : ClassRightInvT) {ell : ℕ} (hell2 : 2 ≤ ell)
    (hell0 : 0 < ell) {a : ℝ} (ha : 0 < a) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∃ R₀ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ fc : ℕ, 10 ≤ fc → ∀ m : ℕ, m₀ ≤ m → ∀ R : ℕ, R₀ ≤ R →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
        TorusOK ell (ell ^ m) Lu →
        ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupledH ell (ell ^ m) fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
        InstIneq ell k hell0 a Lu γ₀ S Lam U ∧ AdalyFormal.StatementLaneG.GenP.WellDefG (gparams ell k Lu hell0 S U a Lam) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell0
  -- (ell, a)-constants
  obtain ⟨cW, hcW, a0P, ha0P, D, hD, hDle, hw4⟩ := AdalyFormal.M2Skel.w4_classU hell2 ha
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
  obtain ⟨df, mF, R1F, K, hK1, C, hC1, hCK, sF, hsF, hFU⟩ := hF ell hell2 a ha
  obtain ⟨mO, R1O, cO, sO, hsO, hOU⟩ := hOT ell hell2 a ha
  obtain ⟨⟨hθ, -, hKH, hKH1, hK2, hCW, hKD⟩, -⟩ := hOU 10 le_rfl mO le_rfl R1O le_rfl
  obtain ⟨mQ, bNQ, -, R1Q, sQ, hsQ, hQU⟩ := hRI ell hell2 a ha
  obtain ⟨θc, hθc0, hθcS⟩ := AdalyFormal.ClassJets.classSmall_exists ell
  set d : ℕ := max D df with hd
  set a₁D : ℝ := a1D ell cO.1 cO.2.1 cO.2.2.1 cO.2.2.2.1 cO.2.2.2.2.1 cO.2.2.2.2.2 ε2s εJ with ha₁Ddef
  have ha₁D : 0 < a₁D := a1D_pos hKH hKH1 hK2 hCW hKD hε2s hεJ
  set sthr : ℝ := min (min (min a₁ (AdalyFormal.M1W4Num.aLin ell)) (min (beta0 ell) (δ / 2))) (min s₀ s₁) with hsthr
  have hsthr0 : 0 < sthr := lt_min (lt_min (lt_min ha₁ hlp) (lt_min (beta0_pos ell hell0) (by positivity))) (lt_min hs₀ hs₁)
  have hKpos : 0 < K := by linarith
  set a₀old : ℝ := min (min (min sF (min sO sQ)) (min a0P (min 1 a₁D)))
    (sthr / (2 * (ell : ℝ) ^ 3)) with ha₀old
  have ha₀oldpos : 0 < a₀old := lt_min (lt_min (lt_min hsF (lt_min hsO hsQ))
    (lt_min ha0P (lt_min one_pos ha₁D))) (by positivity)
  set a₀c : ℝ := a₀old / K with ha₀c
  have ha₀cpos : 0 < a₀c := div_pos ha₀oldpos hKpos
  set a₀ : ℝ := min a₀c θc with ha₀
  have ha₀pos : 0 < a₀ := lt_min ha₀cpos hθc0
  have hΓT : 0 < Γ / (4 * T1) := by positivity
  refine ⟨Γ / (4 * T1), by positivity, mF + mO + mQ + 8 + (d + 64 * ell ^ 2 + 2) + M₁ + (Mc₀ + 1), by omega, R1F + R1O + R1Q + W₀ + 9 * ell + 24 + (⌈1 / δ⌉₊ + 1), a₀, ha₀pos, fun fc hfc m hm R hR => ?_⟩
  haveI : CubeFactor fc := ⟨hfc⟩
  have hmF : mF ≤ m := by omega
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
  have hRF : R1F ≤ R := by omega
  have hRO : R1O ≤ R := by omega
  have hRQ : R1Q ≤ R := by omega
  have hRW : W₀ ≤ R := by omega
  have hR9 : 9 * ell ≤ R := by omega
  have hR24 : 24 ≤ R := by omega
  have hRc : ⌈1 / δ⌉₊ + 1 ≤ R := by omega
  obtain ⟨hpow, hMc0, hMbig, hRMn⟩ := AdalyFormal.M2UnitCharts.headline_numericsU (R := R) hell2 hm8 (by omega)
  have hFf := hFU fc hfc m hmF R hRF
  obtain ⟨⟨-, hq, -, -, -, -, -⟩, hOf⟩ := hOU fc hfc m hmO R hRO
  have hQf := hQU fc hfc m hmQ R hRQ
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
  have hR4 : (5 + 4) * 1 * ell ≤ R := by omega
  have hR8 : 8 * ell ≤ R := by omega
  have hdM : d + 64 * ell ^ 2 + 2 ≤ ell ^ m := by omega
  have hDL := (dlayer_explicit (fc := fc) hell0 hell2 hR1 hM0 hRM4 a hθ hq hKH hKH1 hK2 hCW hKD hε2s hεJ).2
  have hroom0 : 17 * ell ≤ R * ell ^ m := by
    calc 17 * ell ≤ R * ell := Nat.mul_le_mul_right ell (by omega)
      _ ≤ R * ell ^ m := Nat.mul_le_mul_left R hMge
  intro k hk Lu0 α₀ hα hbound hT0 S0 hS0 Lam0 hL0 U0 hU0
  have hsmall : AdalyFormal.ClassJets.ClassSmall ell (((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀) :=
    hθcS _ (by positivity) (hbound.trans (min_le_right _ _))
  -- the thick pipeline (OG11's tail), exporting `InstIneq` and `WellDefG`
  have key : ∀ (Lu : PeriodicLatticeExtent), TorusOK ell (ell ^ m) Lu → (∀ σ : Fin 3, 13 * ell ^ m ≤ Lu σ + 1) →
      ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
      ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
      ∀ U : LinkCfg (scaleUp ell k Lu), ClassCoupledH ell (ell ^ m) fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) fc k S e → U e = 1) →
      InstIneq ell k hell0 a Lu (Γ / (4 * T1)) S Lam U ∧
        AdalyFormal.StatementLaneG.GenP.WellDefG (gparams ell k Lu hell0 S U a Lam) := by
    intro Lu hT hthick S hS Lam hL U hU hloc
    have hthick12 : ∀ σ : Fin 3, 12 * (ell ^ m * ell ^ k) ≤ scaleUp ell k Lu σ + 1 := by
      intro σ
      rw [AdalyFormal.M2UnitCharts.scaleUp_succ ell k Lu hell0 σ]
      have := Nat.mul_le_mul_right (ell ^ k) (hthick σ)
      have e : 13 * ell ^ m * ell ^ k = 12 * (ell ^ m * ell ^ k) + ell ^ m * ell ^ k := by ring
      omega
    have hb0 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by simpa using hbound
    have hb0c : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀c := hb0.trans (min_le_left _ _)
    have ha₀le : a₀c ≤ a₀old := div_le_self ha₀oldpos.le (by linarith)
    have hb0' : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀old := hb0c.trans ha₀le
    have hbsF : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sF := hb0'.trans (by simp only [ha₀old, min_le_iff, le_refl, true_or, or_true])
    have hbsO : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sO := hb0'.trans (by simp only [ha₀old, min_le_iff, le_refl, true_or, or_true])
    have hbsQ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sQ := hb0'.trans (by simp only [ha₀old, min_le_iff, le_refl, true_or, or_true])
    -- the open fields at this configuration (class parameter α₀; the chart constant is K α₀)
    obtain ⟨⟨hHc, hGc, hCc, hIc', hQc'⟩, hBall⟩ := hFf k hk Lu α₀ hα hbsF hT S hS hthick Lam hL U hU hloc
    have hIc := hIc' d (le_max_right D df) hdM
    have hOc := hOf k hk Lu α₀ hα hbsO hT S hS Lam hL U hU hloc hthick
    have hQc : Function.Injective (gparams ell k Lu hell0 S U a Lam).data.Qs := by
      by_cases hx : AdalyFormal.OneGap.ExitFree ell k Lu S
      · exact hQc' hx
      · exact AdalyFormal.M2OpLayer.qs_inj_of_hext hell0 S U a Lam bNQ
          (hQf k hk Lu α₀ hα hbsQ hT S hS hthick Lam hL U hU hloc)
    -- from here the pipeline runs at β = K α₀
    have hbK : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * (K * α₀) ≤ a₀old := by
      have h1 : α₀ * (12 * ((ell ^ m : ℕ) : ℝ)) ≤ a₀old / K := by
        have := hbound
        calc α₀ * (12 * ((ell ^ m : ℕ) : ℝ)) = (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ := by ring
          _ ≤ a₀c := hb0c
          _ = a₀old / K := rfl
      have h2 := (le_div_iff₀ hKpos).1 h1
      calc (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * (K * α₀) = α₀ * (12 * ((ell ^ m : ℕ) : ℝ)) * K := by ring
        _ ≤ a₀old := h2
    have hKα0 : α₀ ≤ K * α₀ := by nlinarith
    have hUb := hU.mono (by positivity) hKα0
    set β : ℝ := K * α₀ with hβdef
    have hβ : 0 < β := by rw [hβdef]; positivity
    have hb : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * β ≤ a₀old := hbK
    have hb1 : ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * β ≤ 1 := by
      have : a₀old ≤ 1 := by simp only [ha₀old, min_le_iff, le_refl, true_or, or_true]
      simpa using hb.trans this
    have hbP : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * β ≤ a0P := hb.trans (by simp only [ha₀old, min_le_iff, le_refl, true_or, or_true])
    have hbD : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * β ≤ a₁D := hb.trans (by simp only [ha₀old, min_le_iff, le_refl, true_or, or_true])
    have hαa : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * β ≤ sthr / (2 * (ell : ℝ) ^ 3) :=
      hb.trans (by simp only [ha₀old, min_le_iff, le_refl, true_or, or_true])
    have hα1p : 0 < alpha1 ell β := by unfold alpha1; positivity
    have hsα : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell β = 2 * (ell : ℝ) ^ 3 * ((12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * β) := by
      unfold alpha1; ring
    have hs : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell β ≤ sthr := by
      rw [hsα]
      calc 2 * (ell : ℝ) ^ 3 * ((12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * β) ≤ 2 * (ell : ℝ) ^ 3 * (sthr / (2 * (ell : ℝ) ^ 3)) :=
            mul_le_mul_of_nonneg_left hαa (by positivity)
        _ = sthr := by field_simp
    have hs0 : 0 ≤ (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell β := by positivity
    have hsa₁ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell β ≤ a₁ := hs.trans (by simp only [hsthr, min_le_iff, le_refl, true_or, or_true])
    have hsLin : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell β ≤ AdalyFormal.M1W4Num.aLin ell :=
      hs.trans (by simp only [hsthr, min_le_iff, le_refl, true_or, or_true])
    have hsβ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell β ≤ beta0 ell := hs.trans (by simp only [hsthr, min_le_iff, le_refl, true_or, or_true])
    have hsδ' : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell β ≤ δ / 2 := hs.trans (by simp only [hsthr, min_le_iff, le_refl, true_or, or_true])
    have hss₀ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell β ≤ s₀ := hs.trans (by simp only [hsthr, min_le_iff, le_refl, true_or, or_true])
    have hss₁ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell β ≤ s₁ := hs.trans (by simp only [hsthr, min_le_iff, le_refl, true_or, or_true])
    -- numerics at alpha1
    obtain ⟨ha1', hsm4, hsmA, hrr⟩ := AdalyFormal.M1W4Num.lin_small ell (ell ^ m) hell0 (alpha1 ell β) hα1p.le hsLin
    have hKD : KDsmall ell (12 * ((ell ^ m : ℕ) : ℝ) * alpha1 ell β) := KDsmall_of_le ell hell0 _ hs0 hsβ
    obtain ⟨hW, -, hNum⟩ := hN (ell ^ m) R hM0 hRW (alpha1 ell β) hα1p.le hsa₁
    have h216 := (rhoT_smalls ell 12 (ell ^ m) (alpha1 ell β) hα1p.le hell0 hsm4).1
    have hcs : 0 < csOf a (rhoT ell 12 (ell ^ m) (alpha1 ell β)) := by
      unfold csOf
      exact div_pos (by linarith) (lt_max_of_lt_left (by norm_num))
    have hsδ : |((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell β| < δ := by
      rw [show ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell β = (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * alpha1 ell β by norm_num,
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
    have cw1 := cwW4_lower (ell := ell) (M := ell ^ m) (R := R) (d := d) (a := a) (cW := cW) (α₀ := alpha1 ell β) hε1 hα1p.le
      (hDle d (le_max_left _ _)) hcs hNum.hη (fun s x K hs hx hK => hU1 s x K hs hx hK) hsδ hxδ' hKδ
    have hηk : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
    have hcoer : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G),
        c1 * AdalyFormal.M1.wnormSq S ell k (A : AdalyFormal.Balaban.CovariantOperators.BondFnL2 (scaleUp ell k Lu))
          ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ := by
      intro A
      have h := hw4 hell0 hS hM0 hR1 hR24 hR4 hroom (le_max_left D df) hdM hW le_rfl U hβ hbP hUb hb1 Lam ε1 1 hε1
        one_pos hNum h216 hHc hGc hCc (hIc) A
      exact le_trans (mul_le_mul_of_nonneg_right cw1 (AdalyFormal.M1DStrat.wnormSq_nonneg' S _)) h
    have hDS := hDL k hk Lu β hβ hbD hT S hS hUb.1 Lam hL U hUb hOc
    have hCb : C * α₀ ≤ β := by
      have : C * α₀ ≤ K * α₀ := mul_le_mul_of_nonneg_right hCK hα.le
      rw [hβdef]; exact this
    have hα1C : (ell : ℝ) ^ 3 * (2 * (C * α₀)) ≤ alpha1 ell β := by
      unfold alpha1
      have h3 := pow_pos hellR 3
      exact mul_le_mul_of_nonneg_left (by linarith) h3.le
    have hb' := AdalyFormal.M2UnitCharts.hb_classU hell2 hT (by omega) (by omega : 5 * ell + 17 ≤ R * ell ^ m) (by omega : 6 * ell ≤ R) hk hthick12 S hS Lam hL U a α₀ hα hC1 hBall (alpha1 ell β) hα1C hKD
    obtain ⟨hG', hNm'⟩ := AdalyFormal.M1IMS.units_strat ell k Lu hell0 S U a Lam c1 ε2s hε2c2 hcoer hDS.1 hQc
    have hWD : AdalyFormal.StatementLaneG.GenP.WellDef (gparams ell k Lu hell0 S U a Lam) := ⟨hb', hG', hNm'⟩
    have hreg := holRegime_rho1AC (show 1 ≤ ell by omega) hS hηk hβ.le hb1 hUb
    have hMcge : Mc₀ ≤ ell ^ (m - 1) := by
      have : m - 1 < ell ^ (m - 1) := Nat.lt_pow_self (by omega)
      omega
    have hcU := cU_lower (Mc := ell ^ (m - 1)) hell0 hs0 hcu hss₁ hMc0 (hMcw _ hMcge)
    have hrho : AdalyFormal.NonflatJet.rhoOf ell (kapM1 (12 * ((ell ^ m : ℕ) : ℝ) * alpha1 ell β)) < Real.pi / 2 := by
      have := (hcu _ hs0 hss₁).1
      linarith [Real.pi_gt_three]
    obtain ⟨hw1, hw3⟩ := hwin _ hs0 hss₀

    have hIfinal := config_inst_classU hell2 hS hroom hM0 hT hL U hβ hα hC1 hCb hBall a ha hpow hMc0 hMbig hRMn (by omega : 6 * ell ≤ R) hk hthick12 ha1' hsm4 hsmA hrr hKD hrho hcU hb' ε1 hε1 hε1' hNum
      hWD c1 ε2s εJ hc1 hε2s.le hεJ.le hε2c1 hcoer hDS.1 hDS.2 h216 hHc hreg hw1 hw3 he1 (by simpa using he2)
    refine ⟨hIfinal, hWD, ?_⟩
    exact AdalyFormal.Thin.guardsUnit_of_fields hell0 S U a Lam hcs (csOf_le_one ha) hHc hc1 hcoer hQc

  -- the cover
  have hM5' : 2 ≤ 13 * ell ^ m := by omega
  set Lut : PeriodicLatticeExtent := fun μ => 13 * ell ^ m * (Lu0 μ + 1) - 1 with hLut
  have hLut1 : ∀ μ, Lut μ + 1 = 13 * ell ^ m * (Lu0 μ + 1) := by
    intro μ
    have : 0 < 13 * ell ^ m * (Lu0 μ + 1) := by positivity
    simp only [hLut]; omega
  have hcov : AdalyFormal.Thin.Covers Lut Lu0 := fun μ => by rw [hLut1]; exact Dvd.intro_left _ rfl
  have hstrict : ∀ μ, Lu0 μ + 1 < Lut μ + 1 := fun μ => by rw [hLut1]; nlinarith [Nat.succ_pos (Lu0 μ)]
  obtain ⟨hT1', hS1', hL1', hU1'⟩ := AdalyFormal.Thin.geometry_liftH (hell := hell0) (R := R) (k := k)
    (⟨hcov, hstrict⟩ : AdalyFormal.Thin.GeomLift ell k hell0 Lut Lu0) (by have := CubeFactor.ge (fc := fc); omega) hT0 hS0 hL0 hU0
  set S' := AdalyFormal.Thin.towerPull (AdalyFormal.Thin.covers_scaleUp ell k hell0 hcov) (fun _ => 0) S0 with hS'def
  set U' := AdalyFormal.Thin.pullCfg (AdalyFormal.Thin.covers_scaleUp ell k hell0 hcov) (fun _ => 0) U0 with hU'def
  set Lam' := AdalyFormal.Thin.phiS hcov (fun _ => 0) ⁻¹' Lam0 with hLam'def
  have hS' : Admissible ell (ell ^ m) R k S' := by
    have := hS1'; rwa [AdalyFormal.Thin.liftTower_eq] at this
  have hL' : LambdaOK2 ell (ell ^ m) R k S' Lam' := by
    have := hL1'; rwa [AdalyFormal.Thin.liftTower_eq, AdalyFormal.Thin.projS_eq_phiS] at this
  have hU' : ClassCoupledH ell (ell ^ m) fc 12 k S' α₀ ((ell : ℝ) ^ k)⁻¹ U' := by
    have := hU1'; rwa [AdalyFormal.Thin.liftTower_eq, AdalyFormal.Thin.liftU_eq] at this
  have hthick' : ∀ σ : Fin 3, 13 * ell ^ m ≤ Lut σ + 1 := fun σ => by
    rw [hLut1]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  obtain ⟨hI'', hWD''⟩ := key Lut hT1' hthick' S' hS' Lam' hL' (UlocAC fc (ell ^ m) S' U') (classCoupled_locAC hU')
    (fun e he => Uloc_trivAC he)
  have hI' : InstIneq ell k hell0 a Lut (Γ / (4 * T1)) S' Lam' U' :=
    inst_of_locAC hell0 hell2 hk hS' hroom0 (by omega) hL' hU' a _ hI''
  have hWD' : AdalyFormal.StatementLaneG.GenP.WellDefG (gparams ell k Lut hell0 S' U' a Lam') :=
    (AdalyFormal.StatementLaneR8.WellDefG_congr (gparams ell k Lut hell0 S' (UlocAC fc (ell ^ m) S' U') a Lam')
      ⟨hS', hk, hell2, hroom0, hL'⟩ U'
      (fun e he => Uloc_eqAC (AdalyFormal.StatementLaneR8.bothIn_classBond hS' (by omega) hU'.1 he))).mpr hWD''
  have hp : AdalyFormal.Thin.PhiOK (AdalyFormal.Thin.covers_scaleUp ell k hell0 hcov) (fun _ => 0) (ell ^ k) :=
    ⟨fun μ => by
      rw [AdalyFormal.Thin.scaleUp_add_one ell k hell0]
      first | exact dvd_mul_left _ _ | exact dvd_mul_right _ _, fun μ => dvd_zero _⟩
  have hc := AdalyFormal.Thin.coverHyp_of_wd hcov hell0 S0 U0 a Lam0 hp hT0.1
    (AdalyFormal.Thin.jetReg_of_classH hell2 hroom0 hS' hT1' CubeFactor.pos hU' hsmall)
    (AdalyFormal.Thin.unitReg_of_classH hcov hell0 S0 U0 a Lam0 hell2 hk hroom0 hS' hT1' hL' CubeFactor.pos hU' hsmall) hWD'
  exact ⟨AdalyFormal.Thin.instIneq_of_lift hcov hell0 S0 U0 a Lam0 hc hΓT.le hI', wellDefG_of_coverHyp hc⟩

/-- **uniform strong core at the ORIGINAL class of factor `fc`**: smallness `fc M α₀ ≤ a₀`. -/
theorem strong_coreTC (hF : ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → FieldsKT ell (by omega) a)
    (hOT : OpLayerThickT) (hRI : ClassRightInvT) {ell : ℕ} (hell2 : 2 ≤ ell)
    (hell0 : 0 < ell) {a : ℝ} (ha : 0 < a) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∃ R₀ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ fc : ℕ, 10 ≤ fc → ∀ m : ℕ, m₀ ≤ m → ∀ R : ℕ, R₀ ≤ R →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (fc : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
        TorusOK ell (ell ^ m) Lu →
        ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) fc k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
        InstIneq ell k hell0 a Lu γ₀ S Lam U ∧ AdalyFormal.StatementLaneG.GenP.WellDefG (gparams ell k Lu hell0 S U a Lam) := by
  obtain ⟨γ₀, hγ, m₀, hm₀, R₀, a₀, ha₀, hc⟩ := strong_coreT hF hOT hRI hell2 hell0 ha
  refine ⟨γ₀, hγ, m₀, hm₀, R₀, a₀, ha₀, fun fc hfc m hm R hR k hk Lu α₀ hα hb hT S hS Lam hL U hU => ?_⟩
  haveI : CubeFactor fc := ⟨hfc⟩
  have hfcp := CubeFactor.pos (fc := fc)
  have hα' : 0 < (fc : ℝ) * α₀ / 12 := by positivity
  refine hc fc hfc m hm R hR k hk Lu ((fc : ℝ) * α₀ / 12) hα' ?_ hT S hS Lam hL U (ClassCoupled.toH hU)
  have e : ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * ((fc : ℝ) * α₀ / 12) = (fc : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ := by
    push_cast; ring
  rw [e]; exact hb

end core

end AdalyFormal.Total
