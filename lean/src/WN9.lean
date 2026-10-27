import WN8

/-!
# WN9 -- lane C's site hypotheses and the regular background tower on the patch, from lane B's `M1Regular`

For `0 ≤ α ≤ 1` with `KUSmall ell (rhoM1 ell α)` and `432 r² ≤ 1` (explicit hypotheses; all implied by WN8
`smallness` for `α ≤ δ`), lane B's
`M1Regular ell 1 1 (j+1) (patchTower j Rg) α (ell^(j+1))⁻¹ U` gives ONE gauge `g` such that `U' = U^g` satisfies, with
`r = kapHat ell (rhoM1 ell α)` (no `j`, `Lu`, `Rg`):
* lane C's `hU` (fine links in every row block `≤ r/ell^i`) and `hT` (background links `≤ r ell^{i'}/ell^i`), `216 r² < 1`;
* `RegTower ell (bgTower (GP ell j Lu Rg) U') (j+1)`.
The statement is about `U^g`, not `U`: `hU`/`hT` are not gauge invariant, the M1 regime fixes `U` only up to the global
gauge `g` (its own definition).  `site_hyps_of_M1`.  No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.W3NF

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.StatementLane (BlockClosed scaleUp)
open AdalyFormal.M1Patch (patchTower GP)
open AdalyFormal.CurvBlock (dv pw)
open AdalyFormal.RegBgKU (KUSmall kapHat kap)
open AdalyFormal.AsmM0 (rhoM0)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)

theorem site_hyps_of_M1 (ell : ℕ) (hell : 2 ≤ ell) (j : ℕ) (Lu : PeriodicLatticeExtent)
    (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))) (U : Cfg (scaleUp ell (j + 1) Lu)) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hKU : KUSmall ell (rhoM1 ell α))
    (hs1 : 432 * kapHat ell (rhoM1 ell α) ^ 2 ≤ 1)
    (hM : AdalyFormal.M1.M1Regular ell 1 1 (j + 1) (patchTower j Rg) α ((ell : ℝ) ^ (j + 1))⁻¹ U) :
    ∃ g : GaugeFn (scaleUp ell (j + 1) Lu),
      216 * kapHat ell (rhoM1 ell α) ^ 2 < 1 ∧
      (∀ i, i ≤ j + 1 → ∀ y ∈ (GP ell j Lu Rg).Lam i, ∀ b ∈ AdalyFormal.SiteCoercivity.inBlockBonds y (ell ^ i),
        frobNorm (((periodicGaugeTransform g U b : AdalyFormal.Balaban.SuTwoLogExp.SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
          ≤ kapHat ell (rhoM1 ell α) / (ell : ℝ) ^ i) ∧
      (∀ i, i ≤ j + 1 → ∀ y ∈ (GP ell j Lu Rg).Lam i, ∀ i', i' < i → ∀ z ∈ blockOf y (ell ^ i),
        z ∈ CoarseLattice (scaleUp ell (j + 1) Lu) (ell ^ i') → ∀ μ : Fin 3,
        coarseShift z (ell ^ i') μ ∈ blockOf y (ell ^ i) →
        frobNorm ((bgTower (GP ell j Lu Rg) (periodicGaugeTransform g U) i' (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
          ≤ kapHat ell (rhoM1 ell α) * (ell : ℝ) ^ i' / (ell : ℝ) ^ i) ∧
      RegTower ell (bgTower (GP ell j Lu Rg) (periodicGaugeTransform g U)) (j + 1) := by
  have hell0 : 0 < ell := by omega
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast (by omega : 1 ≤ ell)
  have hpi := Real.pi_pos
  obtain ⟨g, hlink, hplaq⟩ := regime_of_M1 ell j hell0 Lu Rg U α hα0 hα1 hM
  have hρ := rho_M1_eq ell j hell0 α
  set e : ℝ := α / (ell : ℝ) ^ j with he
  set q0 : ℝ := 2 * (α / ((ell : ℝ) ^ j) ^ 2) + (4 * Real.pi + 2) * (α / (ell : ℝ) ^ j) ^ 2 with hq0
  have he0 : 0 ≤ e := by positivity
  have hq00 : 0 ≤ q0 := by positivity
  rw [← hρ] at hKU hs1 ⊢
  set U' := periodicGaugeTransform g U with hU'
  set n : ℝ := (ell : ℝ) ^ (j + 1) with hn
  have hnpos : 0 < n := by positivity
  set ρ := rhoM0 ell (j + 1) e q0 with hρdef
  set r := kapHat ell ρ with hr
  have hρ_eq : ρ = n * e + 3 * Real.pi * (n ^ 2 * q0) := by
    rw [hρdef]; unfold rhoM0; rw [← hn]; ring
  have hρ0 : 0 ≤ ρ := by rw [hρ_eq]; positivity
  have hKc := AdalyFormal.RegBgKU.Kc_pos ell hell
  have hρr : ρ ≤ r := by
    rw [hr]; unfold kapHat
    have : 0 ≤ AdalyFormal.RegBgKU.Kc ell * (ρ / (3 * Real.pi) + ρ ^ 2) := by positivity
    linarith
  have hr0 : 0 ≤ r := hρ0.trans hρr
  have hen : e ≤ r / n := by
    rw [le_div_iff₀ hnpos]
    have : 0 ≤ 3 * Real.pi * (n ^ 2 * q0) := by positivity
    nlinarith
  have hlinksr : ∀ b, dv (U' b) ≤ r / n := fun b => (hlink b).trans hen
  obtain ⟨S, -⟩ := AdalyFormal.RegBgKU.towerSmall_of_KU ell (j + 1) hell e q0 he0 hq00 hKU
  have hcl := towerClass_patch ell j hell Lu U' e q0 he0 hq00 hlink hplaq S
  have hkapk : kap ell e q0 (j + 1) ≤ r := AdalyFormal.M0Finish.kap_le_kapHat ell (j + 1) hell e q0 he0 hq00
  have hεη : ∀ i, i < j + 1 → kap ell e q0 i ≤ (ell : ℝ) ^ i * (r / n) := by
    intro i hi
    refine (kap_le_class ell hell e q0 he0 hq00 (j + 1) i hi.le).trans ?_
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hkapk hnpos.le) (by positivity)
  refine ⟨g, by nlinarith, hU_patch ell j hell0 (GP ell j Lu Rg) U' r hr0 hlinksr,
    hT_patch ell j hell0 Lu Rg U' (fun i => kap ell e q0 i) r hr0 hcl hεη, ?_⟩
  exact AdalyFormal.RegBgKU.regTower_M0_kuniform ell (j + 1) Lu hell U' e q0 he0 hq00 hlink
    (AdalyFormal.CurvBlock.plaq_of_pw_one U' q0 hplaq) hKU

#print axioms site_hyps_of_M1

end AdalyFormal.W3NF
