import WN10

/-!
# WN11 -- `W3G0Stmt` (W3 for the decoupled form `G0` at non-flat `U`) from `LemIFlat`, and the W2 lane's `W3G0At`

* `G0form_gauge` : `G0form S ell k (U^γ) a (Ad_γ A) = G0form S ell k U a A` (`0 ≤ a`).
* `wnormSq_gauge` : `wnormSq S ell k (Ad_γ A) = wnormSq S ell k A`.
* `W3G0Stmt ell a` : `∃ cW > 0, ∃ ρ₀ > 0`, on every two-stratum patch (any `j`, `Lu`, `Rg` a union of `ell^{j+1}`-blocks),
  every `U` in lane B's `M1Regular ell 1 1 (j+1) (patchTower j Rg) α₀ (ell^(j+1))⁻¹` with `0 < α₀ ≤ ρ₀`, and EVERY `A`:
  `cW · wnormSq ≤ G0form`.  (Lane D's `W3Stmt` shape with `G0form` in place of the Ginv form.)
* **`w3G0_nonflat_of_LemI`** : `2 ≤ ell → 0 < a → 0 ≤ Ci → LemIFlat ell a Ci → W3G0Stmt ell a`, `cW = 1/(ell² KG0 a Ci)`.
* **`w3G0At_of_stmt`** : `W3G0Stmt ell a → ∃ cW > 0, ∃ ρ₀ > 0, ∀ L U α₀, 0 < α₀ ≤ ρ₀ →` (`U` in the M1 regime on every
  two-stratum patch tower `patchTower i Rg` of `L` with `ell^{i+1} ∣ L μ + 1`) `→ AdalyFormal.M1W2.W3G0At ell L U a cW`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.W3NF

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.StatementLane (BlockClosed scaleUp Tower)
open AdalyFormal.M1Patch (patchTower GP LemIFlat Kflat)
open AdalyFormal.CurvBlock (dv pw)
open AdalyFormal.RegBgKU (KUSmall kapHat)
open AdalyFormal.AsmM0 (rhoM0 Mc)
open AdalyFormal.M1IMS (G0form)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)

theorem G0form_gauge {L : PeriodicLatticeExtent} (S : Tower L) (ell k : ℕ) (U : Cfg L) (a : ℝ) (γ : GaugeFn L)
    (A : BondFnL2 L) :
    G0form S ell k (periodicGaugeTransform γ U) a (AdalyFormal.GaugeCov.adBL γ A) = G0form S ell k U a A := by
  unfold G0form
  have h1 : ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn (S.Om 0))
        (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (periodicGaugeTransform γ U) (AdalyFormal.GaugeCov.adBL γ A))‖ ^ 2
      = ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn (S.Om 0))
        (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact AdalyFormal.GaugeCov.plaq_form_gauge γ U (plaqIn (S.Om 0)) A A
  have h2 : ‖Tfull (geomOf ell k S) (periodicGaugeTransform γ U) (AdalyFormal.GaugeCov.adBL γ A)‖
      = ‖Tfull (geomOf ell k S) U A‖ := by
    rw [AdalyFormal.GaugeCov.Tfull_gauge, LinearIsometryEquiv.norm_map]
  have h3 : ‖AdalyFormal.M1IMS.Ymass (geomOf ell k S) (periodicGaugeTransform γ U) a (AdalyFormal.GaugeCov.adBL γ A)‖
      = ‖AdalyFormal.M1IMS.Ymass (geomOf ell k S) U a A‖ := by
    show ‖diagW (geomOf ell k S) _ (QfullOf (geomOf ell k S) (periodicGaugeTransform γ U) (AdalyFormal.GaugeCov.adBL γ A))‖
      = ‖diagW (geomOf ell k S) _ (QfullOf (geomOf ell k S) U A)‖
    rw [AdalyFormal.GaugeCov.QfullOf_gauge, AdalyFormal.GaugeCov.diagW_adFL, LinearIsometryEquiv.norm_map]
  rw [h1, h2, h3]

theorem wnormSq_gauge {L : PeriodicLatticeExtent} (S : Tower L) (ell k : ℕ) (γ : GaugeFn L) (A : BondFnL2 L) :
    AdalyFormal.M1.wnormSq S ell k (AdalyFormal.GaugeCov.adBL γ A) = AdalyFormal.M1.wnormSq S ell k A := by
  unfold AdalyFormal.M1.wnormSq
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  have e : (WithLp.ofLp (AdalyFormal.GaugeCov.adBL γ A)) b = RMap (γ b.1) ((WithLp.ofLp A) b) := rfl
  rw [e, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    AdalyFormal.Balaban.SuTwoInner.inner_RMap]

/-- **W3 for the decoupled form `G0`** (lane D's `W3Stmt` shape, every bond field `A`). -/
def W3G0Stmt (ell : ℕ) (a : ℝ) : Prop :=
  ∃ cW : ℝ, 0 < cW ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ (j : ℕ) (Lu : PeriodicLatticeExtent) (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))),
    BlockClosed (ell ^ (j + 1)) Rg → ∀ (U : Cfg (scaleUp ell (j + 1) Lu)) (α₀ : ℝ), 0 < α₀ → α₀ ≤ ρ₀ →
    AdalyFormal.M1.M1Regular ell 1 1 (j + 1) (patchTower j Rg) α₀ ((ell : ℝ) ^ (j + 1))⁻¹ U →
    ∀ A : BondFnL2 (scaleUp ell (j + 1) Lu),
      cW * AdalyFormal.M1.wnormSq (patchTower j Rg) ell (j + 1) A ≤ G0form (patchTower j Rg) ell (j + 1) U a A

theorem continuous_hs6 (ell : ℕ) :
    Continuous (fun α => 8 * (272 * (kapHat ell (rhoM1 ell α) / (3 * Real.pi)) / (4 * Real.sqrt 2))) := by
  unfold kapHat rhoM1; fun_prop

theorem hs6_zero (ell : ℕ) : 8 * (272 * (kapHat ell (rhoM1 ell 0) / (3 * Real.pi)) / (4 * Real.sqrt 2)) = 0 := by
  rw [rhoM1_zero, kapHat_zero]; simp

/-- **`W3G0Stmt` from `LemIFlat`.** -/
theorem w3G0_nonflat_of_LemI {ell : ℕ} (hell : 2 ≤ ell) {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci)
    (hI : LemIFlat ell a Ci) : W3G0Stmt ell a := by
  have hell0 : 0 < ell := by omega
  have hlpos : (0 : ℝ) < ell := by exact_mod_cast hell0
  obtain ⟨δ1, hδ1, hsm⟩ := smallness ell hell a Ci ha hCi
  obtain ⟨δ2, hδ2, hsm6⟩ := small_of_continuous (continuous_hs6 ell) (hs6_zero ell)
    (show 0 < 1 / Kflat a Ci by have := Kflat_pos ha hCi; positivity)
  have hK := KG0_pos ha hCi
  refine ⟨1 / ((ell : ℝ) ^ 2 * KG0 a Ci), by positivity, min δ1 δ2, lt_min hδ1 hδ2,
    fun j Lu Rg hRg U α hα0 hαδ hM A => ?_⟩
  obtain ⟨hα1, hKU, hs1, hs2, hs3, hs4, hs5⟩ := hsm α hα0.le (hαδ.trans (min_le_left _ _))
  have hs6 := (hsm6 α hα0.le (hαδ.trans (min_le_right _ _))).le
  obtain ⟨g, hlink, hplaq⟩ := regime_of_M1 ell j hell0 Lu Rg U α hα0.le hα1 hM
  have hρ := rho_M1_eq ell j hell0 α
  set e : ℝ := α / (ell : ℝ) ^ j with he
  set q0 : ℝ := 2 * (α / ((ell : ℝ) ^ j) ^ 2) + (4 * Real.pi + 2) * (α / (ell : ℝ) ^ j) ^ 2 with hq0
  have he0 : 0 ≤ e := by positivity
  have hq00 : 0 ≤ q0 := by have := Real.pi_pos; positivity
  rw [← hρ] at hKU hs1 hs2 hs3 hs4 hs5 hs6
  have hmain := g0_patch_nonflat hell ha hCi hI j Lu Rg hRg (periodicGaugeTransform g U) e q0 he0 hq00 hlink hplaq
    hKU hs1 hs2 hs3 hs4 hs5 hs6 (AdalyFormal.GaugeCov.adBL g A)
  rw [G0form_gauge, LinearIsometryEquiv.norm_map] at hmain
  have hw := AdalyFormal.M1Patch.wnorm_le ell j hell0 Rg A
  set Gx := G0form (patchTower j Rg) ell (j + 1) U a A with hGx
  have hc0 : (0 : ℝ) ≤ 1 / ((ell : ℝ) ^ 2 * KG0 a Ci) := by positivity
  have hinv0 : (0 : ℝ) ≤ (((ell : ℝ) ^ j)⁻¹) ^ 2 := by positivity
  have key : 1 / ((ell : ℝ) ^ 2 * KG0 a Ci) * (((ell : ℝ) ^ j)⁻¹) ^ 2 * (((ell : ℝ) ^ (j + 1)) ^ 2 * KG0 a Ci) = 1 := by
    field_simp; ring
  calc 1 / ((ell : ℝ) ^ 2 * KG0 a Ci) * AdalyFormal.M1.wnormSq (patchTower j Rg) ell (j + 1) A
      ≤ 1 / ((ell : ℝ) ^ 2 * KG0 a Ci) * ((((ell : ℝ) ^ j)⁻¹) ^ 2 * ‖A‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hw hc0
    _ ≤ 1 / ((ell : ℝ) ^ 2 * KG0 a Ci) * ((((ell : ℝ) ^ j)⁻¹) ^ 2 * (((ell : ℝ) ^ (j + 1)) ^ 2 * KG0 a Ci * Gx)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmain hinv0) hc0
    _ = (1 / ((ell : ℝ) ^ 2 * KG0 a Ci) * (((ell : ℝ) ^ j)⁻¹) ^ 2 * (((ell : ℝ) ^ (j + 1)) ^ 2 * KG0 a Ci)) * Gx := by
        ring
    _ = Gx := by rw [key, one_mul]

/-- **the W2 lane's `W3G0At` at a non-flat `U`**, for `U` in the M1 regime on every two-stratum patch tower of `L`. -/
theorem w3G0At_of_stmt {ell : ℕ} (hell0 : 0 < ell) {a : ℝ} (h : W3G0Stmt ell a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (L : PeriodicLatticeExtent) (U : Cfg L) (α₀ : ℝ), 0 < α₀ → α₀ ≤ ρ₀ →
      (∀ (i : ℕ) (Rg : Set (PeriodicLatticeSite L)), BlockClosed (ell ^ (i + 1)) Rg →
        (∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1) →
        AdalyFormal.M1.M1Regular ell 1 1 (i + 1) (patchTower i Rg) α₀ ((ell : ℝ) ^ (i + 1))⁻¹ U) →
      AdalyFormal.M1W2.W3G0At ell L U a cW := by
  obtain ⟨cW, hcW, ρ₀, hρ₀, hall⟩ := h
  refine ⟨cW, hcW, ρ₀, hρ₀, fun L U α₀ hα0 hαρ hM i Rg hRg hdiv A => ?_⟩
  have hMi := hM i Rg hRg hdiv
  obtain ⟨Lu', hL⟩ := AdalyFormal.M1W2.exists_scaleUp ell (i + 1) hell0 L hdiv
  subst hL
  exact hall i Lu' Rg hRg U α₀ hα0 hαρ hMi A

theorem w3G0At_nonflat_of_LemI {ell : ℕ} (hell : 2 ≤ ell) {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci)
    (hI : LemIFlat ell a Ci) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (L : PeriodicLatticeExtent) (U : Cfg L) (α₀ : ℝ), 0 < α₀ → α₀ ≤ ρ₀ →
      (∀ (i : ℕ) (Rg : Set (PeriodicLatticeSite L)), BlockClosed (ell ^ (i + 1)) Rg →
        (∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1) →
        AdalyFormal.M1.M1Regular ell 1 1 (i + 1) (patchTower i Rg) α₀ ((ell : ℝ) ^ (i + 1))⁻¹ U) →
      AdalyFormal.M1W2.W3G0At ell L U a cW :=
  w3G0At_of_stmt (by omega) (w3G0_nonflat_of_LemI hell ha hCi hI)

#print axioms G0form_gauge
#print axioms wnormSq_gauge
#print axioms continuous_hs6
#print axioms hs6_zero
#print axioms w3G0_nonflat_of_LemI
#print axioms w3G0At_of_stmt
#print axioms w3G0At_nonflat_of_LemI

end AdalyFormal.W3NF
