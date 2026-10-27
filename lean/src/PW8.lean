import PW7

/-!
# PW8 -- the W3 statements (flat and non-flat) and the reductions proved here

* `W3FlatStmt ell a` : `∃ c > 0`, on every two-stratum patch (any `j`, unit torus `Lu`, `Rg` a union of `ell^{j+1}`-blocks, `Λ`),
  `c · ‖x‖_w² ≤ ⟨x, G⁻¹ x⟩` at `U = 1`, `‖·‖_w` = lane B's `wnormSq` (weights `ell^{-2 bstrat}`).
* `W3Stmt ell a` : the same for every one-gauge `U` in lane B's stratum-scaled regime `M1Regular ell 1 1 (j+1) (patchTower j Rg) α₀ η U`
  (`η = ell^{-(j+1)}`), `0 < α₀ ≤ ρ₀`, with `c, ρ₀` chosen before `j`.
* `wnorm_le` : `wnormSq ≤ ell^{-2j} ‖x‖²` on the patch.
* **`w3flat_of_LemI`** : `LemIFlat ell a Ci → W3FlatStmt ell a` (`c = 1/(ell² Kflat)`).
* **`w3_of_QI`** (a background `U` satisfying the hypotheses below): Ginv coercivity on the patch from `2 ≤ ell`, `a > 0`,
  `Rg` a union of `ell^{j+1}`-blocks, lane C's S1 hypotheses (`hU`, `hT`, `0 ≤ ρ`, `216ρ² < 1`), `RegTower`, and the two
  named inputs at `U` (`hQ`: `cq ‖y‖² ≤ Φ_U(y)`, `cq > 0`; `hI`: `‖D_U* y‖² ≤ Ci Φ_U(y)`, `Ci ≥ 0`; both for `D_U* y ⟂ N(Q'(U))`),
  constant `Kq cq Ci (Pc ell (j+1) a ρ)`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1Patch

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower BlockClosed scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.M1 (wnormSq bstrat M1Regular)

/-- **W3 at flat `U`** (weighted). -/
def W3FlatStmt (ell : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (j : ℕ) (Lu : PeriodicLatticeExtent) (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))),
    BlockClosed (ell ^ (j + 1)) Rg → ∀ (Lam : Set (PeriodicLatticeSite Lu)) (x : ↥(bondSupp (GP ell j Lu Rg))),
      c * wnormSq (patchTower j Rg) ell (j + 1) (x : BondFnL2 _) ≤
        ⟪x, (gparams ell (j + 1) Lu hell (patchTower j Rg) (flatCfg : Cfg _) a Lam).data.Ginv x⟫

/-- **W3** (one gauge, stratum-scaled regime of lane B, constants chosen before `j`). -/
def W3Stmt (ell : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ (j : ℕ) (Lu : PeriodicLatticeExtent) (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))),
    BlockClosed (ell ^ (j + 1)) Rg → ∀ (U : Cfg (scaleUp ell (j + 1) Lu)) (α₀ : ℝ), 0 < α₀ → α₀ ≤ ρ₀ →
    M1Regular ell 1 1 (j + 1) (patchTower j Rg) α₀ ((ell : ℝ) ^ (j + 1))⁻¹ U →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)) (x : ↥(bondSupp (GP ell j Lu Rg))),
      c * wnormSq (patchTower j Rg) ell (j + 1) (x : BondFnL2 _) ≤
        ⟪x, (gparams ell (j + 1) Lu hell (patchTower j Rg) U a Lam).data.Ginv x⟫

theorem W3Stmt.toFlat {ell : ℕ} {hell : 0 < ell} {a : ℝ} (h : W3Stmt ell hell a) : W3FlatStmt ell hell a := by
  obtain ⟨c, hc, ρ₀, hρ₀, hall⟩ := h
  refine ⟨c, hc, fun j Lu Rg hRg Lam x => hall j Lu Rg hRg flatCfg ρ₀ hρ₀ le_rfl ?_ Lam x⟩
  refine ⟨fun _ => 1, fun _ => 0, fun e => ?_, ?_⟩
  · simp [periodicGaugeTransform, flatCfg]
  · refine ⟨fun e => ?_, fun e j' _ => ?_, fun μ ν x j' _ _ => ?_, fun μ x j' _ => ?_⟩
    · simp [AdalyFormal.StatementLane.HT]
    · simp only [AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]; positivity
    · simp only [sub_self, smul_zero, AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]; positivity
    · have : AdalyFormal.StatementLane2.ddA ((ell : ℝ) ^ (j + 1))⁻¹ (fun _ => 0) x μ = 0 := by
        simp [AdalyFormal.StatementLane2.ddA, AdalyFormal.StatementLane2.curlA]
      rw [this, AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]; positivity

/-- on the patch every bond has stratum `≥ j`, so `wnormSq ≤ ell^{-2j} ‖x‖²`. -/
theorem wnorm_le (ell j : ℕ) (hell : 0 < ell) {L : PeriodicLatticeExtent} (Rg : Set (PeriodicLatticeSite L)) (A : BondFnL2 L) :
    wnormSq (patchTower j Rg) ell (j + 1) A ≤ (((ell : ℝ) ^ j)⁻¹) ^ 2 * ‖A‖ ^ 2 := by
  unfold wnormSq
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun b _ => ?_)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hj : j ≤ bstrat (patchTower j Rg) (j + 1) b := by
    unfold bstrat
    refine le_min ?_ ?_
    · exact AdalyFormal.M1.le_strat_of_mem (by omega) (by rw [om_le j Rg le_rfl]; trivial)
    · exact AdalyFormal.M1.le_strat_of_mem (by omega) (by rw [om_le j Rg le_rfl]; trivial)
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have h1 : (ell : ℝ) ^ j ≤ (ell : ℝ) ^ bstrat (patchTower j Rg) (j + 1) b := pow_le_pow_right₀ hellR hj
  have h0 : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
  have h2 : ((ell : ℝ) ^ bstrat (patchTower j Rg) (j + 1) b)⁻¹ ≤ ((ell : ℝ) ^ j)⁻¹ := inv_anti₀ h0 h1
  exact pow_le_pow_left₀ (by positivity) h2 2

/-- **W3 at flat `U` follows from `LemIFlat`.** -/
theorem w3flat_of_LemI {ell : ℕ} (hell : 2 ≤ ell) {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci) (hI : LemIFlat ell a Ci) :
    W3FlatStmt ell (by omega) a := by
  have hell0 : 0 < ell := by omega
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell0
  have hK : 0 < Kflat a Ci := by
    unfold Kflat
    have hM : (0 : ℝ) < max 6 (16 / (3 * a)) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have : (0 : ℝ) < min a 1 / 1000 := by positivity
    positivity
  refine ⟨1 / ((ell : ℝ) ^ 2 * Kflat a Ci), by positivity, fun j Lu Rg hRg Lam x => ?_⟩
  have h1 := w3_flat_plain hell ha hCi hI j Lu Rg hRg Lam x
  have h2 := wnorm_le ell j hell0 Rg (x : BondFnL2 _)
  have hx : ‖(x : BondFnL2 (scaleUp ell (j + 1) Lu))‖ = ‖x‖ := rfl
  rw [hx] at h2
  have hpow : ((ell : ℝ) ^ (j + 1)) ^ 2 = (ell : ℝ) ^ 2 * ((ell : ℝ) ^ j) ^ 2 := by ring
  have hnj : (0 : ℝ) < ((ell : ℝ) ^ j) ^ 2 := by positivity
  rw [hpow] at h1
  have hinv : (((ell : ℝ) ^ j)⁻¹) ^ 2 = 1 / ((ell : ℝ) ^ j) ^ 2 := by rw [inv_pow, one_div]
  rw [hinv] at h2
  set F := ⟪x, (gparams ell (j + 1) Lu (by omega) (patchTower j Rg) (flatCfg : Cfg _) a Lam).data.Ginv x⟫ with hF
  have hw : wnormSq (patchTower j Rg) ell (j + 1) (x : BondFnL2 _) ≤ (ell : ℝ) ^ 2 * Kflat a Ci * F := by
    have h3 : ‖x‖ ^ 2 / ((ell : ℝ) ^ j) ^ 2 ≤ (ell : ℝ) ^ 2 * Kflat a Ci * F := by
      rw [div_le_iff₀ hnj]; nlinarith
    calc _ ≤ 1 / ((ell : ℝ) ^ j) ^ 2 * ‖x‖ ^ 2 := h2
      _ = ‖x‖ ^ 2 / ((ell : ℝ) ^ j) ^ 2 := by ring
      _ ≤ _ := h3
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  linarith

/-- **W3 at any `U`, modulo the two named inputs at `U`** (quotient coercivity `cq` and divergence control `Ci` on the
orthogonal complement of `D_U N(Q'(U))`), with lane C's S1 tower hypotheses `hU`, `hT` and a regular background tower. -/
theorem w3_of_QI {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) (j : ℕ) (Lu : PeriodicLatticeExtent)
    (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))) (hRg : BlockClosed (ell ^ (j + 1)) Rg)
    (U : Cfg (scaleUp ell (j + 1) Lu)) (ρ : ℝ) (hρ : 0 ≤ ρ) (h216 : 216 * ρ ^ 2 < 1)
    (hU : ∀ i, i ≤ j + 1 → ∀ y ∈ (GP ell j Lu Rg).Lam i, ∀ b ∈ AdalyFormal.SiteCoercivity.inBlockBonds y (ell ^ i),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ i)
    (hT : ∀ i, i ≤ j + 1 → ∀ y ∈ (GP ell j Lu Rg).Lam i, ∀ i', i' < i → ∀ z ∈ blockOf y (ell ^ i),
      z ∈ CoarseLattice (scaleUp ell (j + 1) Lu) (ell ^ i') → ∀ μ : Fin 3, coarseShift z (ell ^ i') μ ∈ blockOf y (ell ^ i) →
      frobNorm ((bgTower (GP ell j Lu Rg) U i' (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i' / (ell : ℝ) ^ i)
    (hreg : RegTower ell (bgTower (GP ell j Lu Rg) U) (j + 1))
    (cq Ci : ℝ) (hcq : 0 < cq) (hCi : 0 ≤ Ci)
    (hQ : ∀ y, (∀ ν ∈ NQp (GP ell j Lu Rg) U, ⟪gradAdj U y, ν⟫ = 0) → cq * ‖y‖ ^ 2 ≤ PhiP (GP ell j Lu Rg) U a y)
    (hI : ∀ y, (∀ ν ∈ NQp (GP ell j Lu Rg) U, ⟪gradAdj U y, ν⟫ = 0) →
      ‖gradAdj U y‖ ^ 2 ≤ Ci * PhiP (GP ell j Lu Rg) U a y)
    (Lam : Set (PeriodicLatticeSite Lu)) (x : ↥(bondSupp (GP ell j Lu Rg))) :
    ‖x‖ ^ 2 ≤ Kq cq Ci (Pc ell (j + 1) a ρ) *
      ⟪x, (gparams ell (j + 1) Lu (by omega) (patchTower j Rg) U a Lam).data.Ginv x⟫ := by
  have hell0 : 0 < ell := by omega
  have hdvd := dvd_scaleUp ell j Lu hell0
  have hP : AdalyFormal.SiteCoercivity.ProperTower (GP ell j Lu Rg) ell (j + 1) := patch_proper hell0 hRg
  have hOm : (GP ell j Lu Rg).Om0 = Set.univ := om0_univ j Rg ell
  have hu : IsUnit (DelpA (GP ell j Lu Rg) U a + (1 - siteMask (GP ell j Lu Rg).Om0)) :=
    AdalyFormal.M1Site.isUnit_LP_strat ell (j + 1) hell hdvd hP U a ha ρ hρ h216 hU hT
  have hB0 := patch_B0 hell0 hRg hdvd U hreg
  have hmain := r1q_coercive (gradL2 U) (NQp (GP ell j Lu Rg) U) (Rproj (GP ell j Lu Rg) U) (PhiP (GP ell j Lu Rg) U a)
    (fun A ν hν => PhiP_inv (GP ell j Lu Rg) U a hOm hu hB0 A ν hν)
    (fun ν hν => Rproj_fix (GP ell j Lu Rg) U hOm ν hν) (fun s => Rproj_le (GP ell j Lu Rg) U s)
    (Pc ell (j + 1) a ρ) cq Ci (Real.sqrt_nonneg _) hcq hCi
    (fun ν hν => poincare_patch hell hdvd hP hOm U a ha ρ hρ h216 hU hT ν hν) hQ hI (iE (GP ell j Lu Rg) x)
  have hform := ginv_form (gparams ell (j + 1) Lu (by omega) (patchTower j Rg) U a Lam) x
  have hx : ‖x‖ = ‖iE (GP ell j Lu Rg) x‖ := rfl
  rw [hx, hform]
  exact hmain

#print axioms W3Stmt.toFlat
#print axioms wnorm_le
#print axioms w3flat_of_LemI
#print axioms w3_of_QI

end AdalyFormal.M1Patch
