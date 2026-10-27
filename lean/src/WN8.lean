import WN7
import CB9
import GCz2

/-!
# WN8 -- W3 at non-flat `U` (lane D's `W3Stmt`) from `LemIFlat` alone

* `bstrat_patch_ge` : every bond of the patch has both-endpoint stratum `≥ j`.
* `regime_of_M1` : lane B's `M1Regular ell 1 1 (j+1) (patchTower j Rg) α (ell^(j+1))⁻¹ U` (one global gauge `g`,
  `U^g = exp(i η A)`) gives, through curvature_blocking CB9 (`CubeChart` with ALL bonds), the link bound
  `dv (U^g b) ≤ α/ell^j` and the plaquette bound `dv (pw 1 U^g) ≤ 2 α/ell^(2j) + (4π+2)(α/ell^j)²`.
* `rho_M1_eq` : for these `(e, q0)`, `rhoM0 ell (j+1) e q0 = rhoM1 ell α = ell α + 3π ell² (2α + (4π+2)α²)` (no `j`).
* `smallness` : one `δ > 0` (depending on `ell, a, Ci` only) such that every `α ∈ [0, δ]` satisfies `α ≤ 1`, `KUSmall`, and
  the numeric conditions `hs1`–`hs5` of WN7 at `r = kapHat ell (rhoM1 ell α)` (continuity at `α = 0`).
* `ginv_gauge_inner` : `⟨Ad x, G⁻¹(U^g) Ad x⟩ = ⟨x, G⁻¹(U) x⟩` (GaugeCov `genFormHyps_gauge`, `BaseEqv.Ginv`).
* **`w3_nonflat_of_LemI`** : `LemIFlat ell a Ci → W3Stmt ell _ a` (`2 ≤ ell`, `0 < a`, `0 ≤ Ci`),
  with `c = 1/(ell² K0 a Ci)` and `ρ₀ = δ`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.W3NF

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.StatementLane (BlockClosed scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.M1Patch (patchTower GP LemIFlat Kflat W3Stmt)
open AdalyFormal.CurvBlock (dv pw CubeChart)
open AdalyFormal.RegBgKU (KUSmall kapHat Kc)
open AdalyFormal.AsmM0 (rhoM0 Mc phiC)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)

theorem bstrat_patch_ge {j : ℕ} {L : PeriodicLatticeExtent} (Rg : Set (PeriodicLatticeSite L)) (b : Bond L) :
    j ≤ AdalyFormal.M1.bstrat (patchTower j Rg) (j + 1) b := by
  unfold AdalyFormal.M1.bstrat
  refine le_min ?_ ?_
  · exact AdalyFormal.M1.le_strat_of_mem (by omega) (by rw [AdalyFormal.M1Patch.om_le j Rg le_rfl]; trivial)
  · exact AdalyFormal.M1.le_strat_of_mem (by omega) (by rw [AdalyFormal.M1Patch.om_le j Rg le_rfl]; trivial)

/-- **the M1 regime on the patch gives a link/plaquette regime in the gauge `g`.** -/
theorem regime_of_M1 (ell j : ℕ) (hell : 0 < ell) (Lu : PeriodicLatticeExtent)
    (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))) (U : Cfg (scaleUp ell (j + 1) Lu)) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hM : AdalyFormal.M1.M1Regular ell 1 1 (j + 1) (patchTower j Rg) α ((ell : ℝ) ^ (j + 1))⁻¹ U) :
    ∃ g : GaugeFn (scaleUp ell (j + 1) Lu),
      (∀ b, dv (periodicGaugeTransform g U b) ≤ α / (ell : ℝ) ^ j) ∧
      (∀ y ν μ, dv (pw 1 (periodicGaugeTransform g U) y ν μ)
        ≤ 2 * (α / ((ell : ℝ) ^ j) ^ 2) + (4 * Real.pi + 2) * (α / (ell : ℝ) ^ j) ^ 2) := by
  obtain ⟨g, A, hUA, hHT, h1, h2, -⟩ := hM
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  set η : ℝ := ((ell : ℝ) ^ (j + 1))⁻¹ with hη
  have hηpos : 0 < η := by positivity
  set c1 : ℝ := α * (((ell : ℝ) ^ j * η)⁻¹ ^ 1) with hc1
  set c2 : ℝ := α * (((ell : ℝ) ^ j * η)⁻¹ ^ 2) with hc2
  have hA1 : ∀ e : Bond (scaleUp ell (j + 1) Lu), frobNorm (A e) < c1 := by
    intro e
    have h := h1 e j (bstrat_patch_ge Rg e)
    rw [hc1]
    simpa using h
  have hA2 : ∀ (μ ν : Fin 3) (x : PeriodicLatticeSite (scaleUp ell (j + 1) Lu)),
      frobNorm (η⁻¹ • (A (periodicLatticeShift x μ, ν) - A (x, ν))) < c2 := by
    intro μ ν x
    have h := h2 μ ν x j (bstrat_patch_ge Rg _) (bstrat_patch_ge Rg _)
    rw [hc2]
    simpa using h
  let K : CubeChart U (fun _ => True) η c1 c2 :=
    ⟨g, A, fun e _ => ⟨hHT e, hUA e, hA1 e⟩, fun μ ν x _ _ => hA2 μ ν x⟩
  have e1 : η * c1 = α / (ell : ℝ) ^ j := by rw [hc1, hη]; field_simp
  have e2 : η ^ 2 * c2 = α / ((ell : ℝ) ^ j) ^ 2 := by rw [hc2, hη]; field_simp
  have hsmall : η * c1 ≤ 1 := by
    rw [e1, div_le_one (by positivity)]
    exact hα1.trans (one_le_pow₀ (by exact_mod_cast hell))
  refine ⟨g, fun b => ?_, fun y ν μ => ?_⟩
  · have h := AdalyFormal.CurvBlock.cube_link hηpos K b trivial
    rw [e1] at h
    exact h
  · have h := AdalyFormal.CurvBlock.cube_plaq hηpos K hsmall (y, ν, μ) ⟨trivial, trivial, trivial, trivial⟩
    rw [e1, e2] at h
    exact h

/-- the `j`-free regime radius of the M1 chart. -/
noncomputable def rhoM1 (ell : ℕ) (α : ℝ) : ℝ :=
  (ell : ℝ) * α + 3 * Real.pi * ((ell : ℝ) ^ 2 * (2 * α + (4 * Real.pi + 2) * α ^ 2))

theorem rho_M1_eq (ell j : ℕ) (hell : 0 < ell) (α : ℝ) :
    rhoM0 ell (j + 1) (α / (ell : ℝ) ^ j) (2 * (α / ((ell : ℝ) ^ j) ^ 2) + (4 * Real.pi + 2) * (α / (ell : ℝ) ^ j) ^ 2)
      = rhoM1 ell α := by
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  unfold rhoM0 rhoM1
  field_simp
  ring

/-! ### smallness, by continuity at `α = 0` -/

theorem small_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0) {b : ℝ} (hb : 0 < b) :
    ∃ δ > 0, ∀ x, 0 ≤ x → x ≤ δ → f x < b := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.mp hf 0 b hb
  refine ⟨δ / 2, by positivity, fun x hx0 hx => ?_⟩
  have hd : dist x 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hx0]; linarith
  have h' := h x hd
  rw [Real.dist_eq, h0, sub_zero] at h'
  exact lt_of_abs_lt h'

theorem kapHat_zero (ell : ℕ) : kapHat ell 0 = 0 := by unfold kapHat; simp

theorem rhoM1_zero (ell : ℕ) : rhoM1 ell 0 = 0 := by unfold rhoM1; simp

theorem ThetaP_zero (ell : ℕ) (a : ℝ) : ThetaP ell a 0 = 0 := by unfold ThetaP phiC; simp

theorem continuous_rM1 (ell : ℕ) : Continuous (fun α => kapHat ell (rhoM1 ell α)) := by
  unfold kapHat rhoM1; fun_prop

theorem continuous_ThetaP (ell : ℕ) (a : ℝ) : Continuous (fun r => ThetaP ell a r) := by
  unfold ThetaP phiC; fun_prop

/-- the normalised smallness functional (each component `< 1` is one condition). -/
noncomputable def smallF (ell : ℕ) (a Ci : ℝ) (α : ℝ) : ℝ :=
  max (max (max (8 * (ell : ℝ) * kapHat ell (rhoM1 ell α) / (1 / (8 * Real.pi)))
      (Kc ell ^ 2 * (rhoM1 ell α / (3 * Real.pi) + rhoM1 ell α ^ 2)))
    (max ((8 * (ell : ℝ) - 6) * kapHat ell (rhoM1 ell α) / AdalyFormal.NonflatJet.r0)
      (432 * kapHat ell (rhoM1 ell α) ^ 2)))
  (max (max (kapHat ell (rhoM1 ell α) / (1 / (1000 * (ell : ℝ) ^ 3)))
      (324 * lamC ell * kapHat ell (rhoM1 ell α)))
    (max (2 * ThetaP ell a (kapHat ell (rhoM1 ell α)) / (1 / Kflat a Ci)) α))

theorem continuous_smallF (ell : ℕ) (a Ci : ℝ) : Continuous (smallF ell a Ci) := by
  have h1 := continuous_rM1 ell
  have h2 : Continuous (fun α => rhoM1 ell α) := by unfold rhoM1; fun_prop
  have h3 : Continuous (fun α => ThetaP ell a (kapHat ell (rhoM1 ell α))) := (continuous_ThetaP ell a).comp h1
  unfold smallF
  fun_prop

theorem smallF_zero (ell : ℕ) (a Ci : ℝ) : smallF ell a Ci 0 = 0 := by
  unfold smallF
  rw [rhoM1_zero, kapHat_zero, ThetaP_zero]
  simp

/-- **one `δ` for every condition of WN7 and of `regime_of_M1`.** -/
theorem smallness (ell : ℕ) (hell : 2 ≤ ell) (a Ci : ℝ) (ha : 0 < a) (hCi : 0 ≤ Ci) :
    ∃ δ > 0, ∀ α, 0 ≤ α → α ≤ δ →
      α ≤ 1 ∧ KUSmall ell (rhoM1 ell α) ∧
      432 * kapHat ell (rhoM1 ell α) ^ 2 ≤ 1 ∧
      kapHat ell (rhoM1 ell α) ≤ 1 / (1000 * (ell : ℝ) ^ 3) ∧
      kapHat ell (rhoM1 ell α) ≤ 1 ∧
      324 * lamC ell * kapHat ell (rhoM1 ell α) ≤ 1 ∧
      2 * ThetaP ell a (kapHat ell (rhoM1 ell α)) ≤ 1 / Kflat a Ci := by
  obtain ⟨δ, hδ, h⟩ := small_of_continuous (continuous_smallF ell a Ci) (smallF_zero ell a Ci) one_pos
  refine ⟨δ, hδ, fun α hα0 hαδ => ?_⟩
  have hF := h α hα0 hαδ
  have hpi := Real.pi_pos
  have hr0 := AdalyFormal.NonflatJet.r0_pos
  have hKf := Kflat_pos ha hCi
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  unfold smallF at hF
  simp only [max_lt_iff] at hF
  obtain ⟨⟨⟨f1, f2⟩, f3, f4⟩, ⟨f5, f6⟩, f7, f8⟩ := hF
  rw [div_lt_one (by positivity)] at f1 f3 f5 f7
  have hr1 : kapHat ell (rhoM1 ell α) ≤ 1 / (1000 * (ell : ℝ) ^ 3) := f5.le
  have h1000 : 1 / (1000 * (ell : ℝ) ^ 3) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hl 3]
  exact ⟨f8.le, ⟨f1.le, f2.le, f3⟩, f4.le, hr1, hr1.trans h1000, f6.le, f7.le⟩

/-! ### gauge covariance of the `Ginv` form -/

theorem ginv_gauge_inner (P : IngrBParams) (γ : GaugeFn P.Lf) (x : ↥(bondSupp P.G)) :
    ⟪AdalyFormal.GaugeCov.adEL γ P.G x,
      ({ P with U := periodicGaugeTransform γ P.U } : IngrBParams).data.Ginv (AdalyFormal.GaugeCov.adEL γ P.G x)⟫
      = ⟪x, P.data.Ginv x⟫ := by
  rw [(AdalyFormal.GaugeCov.genFormHyps_gauge P γ).data.Ginv x, LinearIsometryEquiv.inner_map_map]

/-! ### W3 at non-flat `U` -/

/-- **W3 (lane D's `W3Stmt`) from `LemIFlat`.** -/
theorem w3_nonflat_of_LemI {ell : ℕ} (hell : 2 ≤ ell) {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci)
    (hI : LemIFlat ell a Ci) : W3Stmt ell (by omega) a := by
  have hell0 : 0 < ell := by omega
  have hlpos : (0 : ℝ) < ell := by exact_mod_cast hell0
  obtain ⟨δ, hδ, hsm⟩ := smallness ell hell a Ci ha hCi
  have hK0 := K0_pos ha hCi
  refine ⟨1 / ((ell : ℝ) ^ 2 * K0 a Ci), by positivity, δ, hδ, fun j Lu Rg hRg U α hα0 hαδ hM Lam x => ?_⟩
  obtain ⟨hα1, hKU, hs1, hs2, hs3, hs4, hs5⟩ := hsm α hα0.le hαδ
  obtain ⟨g, hlink, hplaq⟩ := regime_of_M1 ell j hell0 Lu Rg U α hα0.le hα1 hM
  have hρ := rho_M1_eq ell j hell0 α
  set e : ℝ := α / (ell : ℝ) ^ j with he
  set q0 : ℝ := 2 * (α / ((ell : ℝ) ^ j) ^ 2) + (4 * Real.pi + 2) * (α / (ell : ℝ) ^ j) ^ 2 with hq0
  have he0 : 0 ≤ e := by positivity
  have hq00 : 0 ≤ q0 := by have := Real.pi_pos; positivity
  rw [← hρ] at hKU hs1 hs2 hs3 hs4 hs5
  set P : IngrBParams := gparams ell (j + 1) Lu (by omega) (patchTower j Rg) U a Lam with hP
  have hmain := ginv_patch_nonflat hell ha hCi hI j Lu Rg hRg (periodicGaugeTransform g U) e q0 he0 hq00 hlink hplaq
    hKU hs1 hs2 hs3 hs4 hs5 Lam (AdalyFormal.GaugeCov.adEL g P.G x)
  have hinv : ⟪AdalyFormal.GaugeCov.adEL g P.G x,
      (gparams ell (j + 1) Lu (by omega) (patchTower j Rg) (periodicGaugeTransform g U) a Lam).data.Ginv
        (AdalyFormal.GaugeCov.adEL g P.G x)⟫ = ⟪x, P.data.Ginv x⟫ := ginv_gauge_inner P g x
  have hnorm : ‖AdalyFormal.GaugeCov.adEL g P.G x‖ = ‖x‖ := LinearIsometryEquiv.norm_map _ _
  rw [hinv, hnorm] at hmain
  have hw := AdalyFormal.M1Patch.wnorm_le ell j hell0 Rg (x : BondFnL2 _)
  have hx : ‖(x : BondFnL2 (scaleUp ell (j + 1) Lu))‖ = ‖x‖ := rfl
  rw [hx] at hw
  set Gx := ⟪x, P.data.Ginv x⟫ with hGx
  have hc0 : (0 : ℝ) ≤ 1 / ((ell : ℝ) ^ 2 * K0 a Ci) := by positivity
  have hinv0 : (0 : ℝ) ≤ (((ell : ℝ) ^ j)⁻¹) ^ 2 := by positivity
  have key : 1 / ((ell : ℝ) ^ 2 * K0 a Ci) * (((ell : ℝ) ^ j)⁻¹) ^ 2 * (((ell : ℝ) ^ (j + 1)) ^ 2 * K0 a Ci) = 1 := by
    field_simp; ring
  calc 1 / ((ell : ℝ) ^ 2 * K0 a Ci) * AdalyFormal.M1.wnormSq (patchTower j Rg) ell (j + 1) (x : BondFnL2 _)
      ≤ 1 / ((ell : ℝ) ^ 2 * K0 a Ci) * ((((ell : ℝ) ^ j)⁻¹) ^ 2 * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hw hc0
    _ ≤ 1 / ((ell : ℝ) ^ 2 * K0 a Ci) * ((((ell : ℝ) ^ j)⁻¹) ^ 2 * (((ell : ℝ) ^ (j + 1)) ^ 2 * K0 a Ci * Gx)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmain hinv0) hc0
    _ = (1 / ((ell : ℝ) ^ 2 * K0 a Ci) * (((ell : ℝ) ^ j)⁻¹) ^ 2 * (((ell : ℝ) ^ (j + 1)) ^ 2 * K0 a Ci)) * Gx := by
        ring
    _ = Gx := by rw [key, one_mul]

#print axioms bstrat_patch_ge
#print axioms regime_of_M1
#print axioms rho_M1_eq
#print axioms small_of_continuous
#print axioms kapHat_zero
#print axioms rhoM1_zero
#print axioms ThetaP_zero
#print axioms continuous_rM1
#print axioms continuous_ThetaP
#print axioms continuous_smallF
#print axioms smallF_zero
#print axioms smallness
#print axioms ginv_gauge_inner
#print axioms w3_nonflat_of_LemI

end AdalyFormal.W3NF
