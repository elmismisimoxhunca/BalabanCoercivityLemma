import GW8
import NP13

/-!
# GW9 -- W4 / W5 at `U` from `M1Regular ell M 12 k S α₀ (ℓ^k)⁻¹ U` with `PatchCoercive` DISCHARGED (M1 gauge lane, 2026-10-14)

`PatchCoercive` at `U^g` comes from `NP12.patchCoercive_nonflat` (applied to `U^g`, which is `M1Regular` with the trivial gauge),
and the W4 / W5 conclusions are transported to `U` by `GW1`.  Retained: `hD2` (+ `ε₂' < cwW4`), `hb`, `W4Num`, `QsNum`.
Constants `cW, a₀*, D` depend only on `ℓ, a`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1GaugeW4

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar delStar massComm_M1 qs_injective_M1 rho1_nonneg)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams GenP.WellDef)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.M1 (M1Bounds)
open AdalyFormal.M1NonFlat (epsNF PkA thetaN patchCoercive_nonflat)

/-- the retained-free patch constant of NP12. -/
noncomputable def cPnf (ell W d : ℕ) (a cW α₀ ε1 : ℝ) (f M : ℕ) : ℝ :=
  (1 - etaC ell W (csOf a (rhoT ell f M α₀)) (rho1 f M α₀) ε1) * min a (cW - epsNF ell (PkA a) (thetaN ell) d)
    - 2 * nuC ell (rho1 f M α₀)

/-- `PatchCoercive` at `U^g` from NP12, in the M1 regime of `U` at `f = 12`, `η = (ℓ^k)⁻¹`. -/
theorem patch_at_Ug {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ D : ℕ, 12 * ell + 10 ≤ D ∧
    (∀ d, D ≤ d → epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2) ∧
    ∀ {M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
      {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hR1 : 1 ≤ R)
      (hR4 : (c + 4) * κ * ell ≤ R) (hroom : 17 * ell ≤ R * M) {d : ℕ} (hdD : D ≤ d)
      (hdM : d + 64 * ell ^ 2 ≤ κ * M)
      {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell) (hLu5 : ∀ μ, 5 ≤ Lu μ + 1)
      (U : LinkCfg (scaleUp ell k Lu)) (g : PeriodicLatticeSite (scaleUp ell k Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (A0 : Bond (scaleUp ell k Lu) → Matrix (Fin 2) (Fin 2) ℂ) {α₀ : ℝ}
      (hUg : ∀ e : Bond (scaleUp ell k Lu), ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp ((((((ell : ℝ) ^ k)⁻¹ : ℝ) : ℂ) * Complex.I) • A0 e))
      (hB : M1Bounds S ell M 12 k α₀ (((ell : ℝ) ^ k)⁻¹) A0) (hα0 : 0 < α₀) (hαa : (12 : ℝ) * M * α₀ ≤ a₀)
      (ha1 : ((12 : ℕ) : ℝ) * M * α₀ ≤ 1)
      (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M α₀ ≤ 1)
      (Lam : Set (PeriodicLatticeSite Lu)) (ε1 : ℝ) (hε1 : 0 < ε1) (hN : W4Num ell M 12 W a α₀ ε1),
      PatchCoercive ell M k κ c Lu hell0 S (periodicGaugeTransform g U) a Lam
        (cPnf ell W d a cW α₀ ε1 12 M) := by
  obtain ⟨cW, hcW, a₀, ha₀, D, hD, hDle, hall⟩ := patchCoercive_nonflat hell ha
  refine ⟨cW, hcW, a₀, ha₀, D, hD, hDle, ?_⟩
  intro M R k κ c Lu hell0 S hS hκ hM hR1 hR4 hroom d hdD hdM W hW hWR hLu5 U g A0 α₀ hUg hB hα0 hαa ha1 hsm4 Lam ε1 hε1 hN
  have hηk : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  have hα0' : 0 ≤ α₀ := hα0.le
  have hρ := rhoT_nonneg ell 12 M α₀ hα0'
  obtain ⟨h216, h12⟩ := rhoT_smalls ell 12 M α₀ hα0' (by omega) hsm4
  have hU' := site_hU_M1 hell (hS := hS) U g A0 hUg hB hηk hα0'
  have hT' := site_hT_M1 hell hS (by nlinarith) (hbig_of ell k Lu hLu5) U g A0 hUg hB hηk hα0' ha1 hsm4
  have ha0 : 0 ≤ ((12 : ℕ) : ℝ) * M * α₀ := by positivity
  have hreg := holRegime_M1 hell0 U g A0 hUg hB hηk ha0 ha1
  have hM1 : AdalyFormal.M1.M1Regular ell M 12 k S α₀ (((ell : ℝ) ^ k)⁻¹) (periodicGaugeTransform g U) := by
    refine ⟨fun _ => 1, A0, ?_, hB⟩
    intro e
    rw [AdalyFormal.StatementLane2.gauge_one]
    exact hUg e
  exact hall hell0 hS hκ hM hR1 hR4 hroom hdD hdM hW hWR (periodicGaugeTransform g U) (csOf a (rhoT ell 12 M α₀)) Lam
    (hatPack_of hS hell (periodicGaugeTransform g U) a ha (rhoT ell 12 M α₀) hρ h216 hU' hT' hN.hsm hN.hsmD)
    (rho1 12 M α₀) (rho1_nonneg 12 M α₀ hα0') hreg ε1 hε1 hN.hη α₀ hα0 hαa hM1


/-- **W4 at `U` with `PatchCoercive` discharged** (constant `cwW4 … (cPnf …) …`, free of `k`). -/
theorem w4_M1_patched {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ D : ℕ, 12 * ell + 10 ≤ D ∧
    (∀ d, D ≤ d → epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2) ∧
    ∀ {M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
      {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hR1 : 1 ≤ R)
      (hR4 : (c + 4) * κ * ell ≤ R) (hc : 5 ≤ c) (hroom : 17 * ell ≤ R * M) {d : ℕ} (hdD : D ≤ d)
      (hdM : d + 64 * ell ^ 2 ≤ κ * M)
      {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell) (hLu5 : ∀ μ, 5 ≤ Lu μ + 1)
      (U : LinkCfg (scaleUp ell k Lu)) {α₀ : ℝ}
      (hreg : AdalyFormal.M1.M1Regular ell M 12 k S α₀ (((ell : ℝ) ^ k)⁻¹) U) (hα0 : 0 < α₀) (hαa : (12 : ℝ) * M * α₀ ≤ a₀)
      (ha1 : ((12 : ℕ) : ℝ) * M * α₀ ≤ 1)
      (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M α₀ ≤ 1)
      (hsmA : (1 + 3 * Real.pi) * rho1 12 M α₀ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
      (hrr : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M α₀))
          < AdalyFormal.NonflatJet.r0)
      (Lam : Set (PeriodicLatticeSite Lu)) (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2) (hN : W4Num ell M 12 W a α₀ ε1)
      (A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G)),
      cwW4 ell M κ c W a (rhoT ell 12 M α₀) (rho1 12 M α₀) ε1 ε2 (cPnf ell W d a cW α₀ ε1 12 M)
          (epsXnum ell W a (rhoT ell 12 M α₀)) (CMcStar ell M κ c a (SstarM ell 12 M α₀))
        * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ := by
  obtain ⟨cW, hcW, a₀, ha₀, D, hD, hDle, hall⟩ := patch_at_Ug hell ha
  refine ⟨cW, hcW, a₀, ha₀, D, hD, hDle, ?_⟩
  intro M R k κ c Lu hell0 S hS hκ hM hR1 hR4 hc hroom d hdD hdM W hW hWR hLu5 U α₀ hreg hα0 hαa ha1 hsm4 hsmA hrr Lam
    ε1 ε2 hε1 hε2 hN A
  obtain ⟨g, A0, hUg, hB⟩ := hreg
  have hR : (c + 3) * κ * ell ≤ R := by
    have : (c + 3) * κ * ell ≤ (c + 4) * κ * ell := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    omega
  have hP := hall hell0 hS hκ hM hR1 hR4 hroom hdD hdM hW hWR hLu5 U g A0 hUg hB hα0 hαa ha1 hsm4 Lam ε1 hε1 hN
  have hηk : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  exact coercive_of_gauge hell0 S a Lam U g _
    (fun A' => w4_M1_gauged hell0 hS hκ hM hell hR1 hR hc hW hWR hroom hLu5 U g A0 hUg hB hηk hα0.le ha1 hsm4 hsmA hrr a ha
      Lam ε1 ε2 hε1 hε2 hN _ hP A') A

/-- **W5 at `U` with `PatchCoercive` discharged.** -/
theorem wellDef_M1_patched {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ D : ℕ, 12 * ell + 10 ≤ D ∧
    (∀ d, D ≤ d → epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2) ∧
    ∀ {M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
      {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hR1 : 1 ≤ R)
      (hR4 : (c + 4) * κ * ell ≤ R) (hc : 5 ≤ c) (hroom : 17 * ell ≤ R * M) {d : ℕ} (hdD : D ≤ d)
      (hdM : d + 64 * ell ^ 2 ≤ κ * M)
      {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell) (hLu5 : ∀ μ, 5 ≤ Lu μ + 1)
      (U : LinkCfg (scaleUp ell k Lu)) {α₀ : ℝ}
      (hreg : AdalyFormal.M1.M1Regular ell M 12 k S α₀ (((ell : ℝ) ^ k)⁻¹) U) (hα0 : 0 < α₀) (hαa : (12 : ℝ) * M * α₀ ≤ a₀)
      (ha1 : ((12 : ℕ) : ℝ) * M * α₀ ≤ 1)
      (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M α₀ ≤ 1)
      (hsmA : (1 + 3 * Real.pi) * rho1 12 M α₀ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
      (hrr : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M α₀))
          < AdalyFormal.NonflatJet.r0)
      (Lam : Set (PeriodicLatticeSite Lu)) (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2) (hN : W4Num ell M 12 W a α₀ ε1)
      (hQN : QsNum ell 12 M α₀) (ε2' : ℝ)
      (hlt : ε2' < cwW4 ell M κ c W a (rhoT ell 12 M α₀) (rho1 12 M α₀) ε1 ε2 (cPnf ell W d a cW α₀ ε1 12 M)
          (epsXnum ell W a (rhoT ell 12 M α₀)) (CMcStar ell M κ c a (SstarM ell 12 M α₀)))
      (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G),
        |⟪A, (gparams ell k Lu hell0 S U a Lam).data.Delta2 (gparams ell k Lu hell0 S U a Lam).data_laws A⟫|
          ≤ ε2' * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
      (hb : Function.Bijective (H0 (gparams ell k Lu hell0 S U a Lam).Lam (gparams ell k Lu hell0 S U a Lam).Q1)),
      GenP.WellDef (gparams ell k Lu hell0 S U a Lam) := by
  obtain ⟨cW, hcW, a₀, ha₀, D, hD, hDle, hall⟩ := patch_at_Ug hell ha
  refine ⟨cW, hcW, a₀, ha₀, D, hD, hDle, ?_⟩
  intro M R k κ c Lu hell0 S hS hκ hM hR1 hR4 hc hroom d hdD hdM W hW hWR hLu5 U α₀ hreg hα0 hαa ha1 hsm4 hsmA hrr Lam
    ε1 ε2 hε1 hε2 hN hQN ε2' hlt hD2 hb
  obtain ⟨g, A0, hUg, hB⟩ := hreg
  have hR : (c + 3) * κ * ell ≤ R := by
    have : (c + 3) * κ * ell ≤ (c + 4) * κ * ell := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    omega
  have hP := hall hell0 hS hκ hM hR1 hR4 hroom hdD hdM hW hWR hLu5 U g A0 hUg hB hα0 hαa ha1 hsm4 Lam ε1 hε1 hN
  have hηk : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  have hT3 : ∀ μ, 3 ≤ Lu μ + 1 := fun μ => by have := hLu5 μ; omega
  have hR8 : 8 * ell ≤ R := by
    have h1 : 8 * ell ≤ (c + 3) * κ * ell := by
      have : 8 ≤ (c + 3) * κ := by nlinarith
      exact Nat.mul_le_mul_right _ this
    omega
  have hcoer := fun A' => w4_M1_gauged hell0 hS hκ hM hell hR1 hR hc hW hWR hroom hLu5 U g A0 hUg hB hηk hα0.le ha1 hsm4
    hsmA hrr a ha Lam ε1 ε2 hε1 hε2 hN _ hP A'
  have hD2' := dlayer_form_gauge hell0 S a Lam U g ε2' hD2
  have hQs := qs_injective_M1 hell hS hroom hT3 U g A0 hUg hB hηk hα0.le ha1 hsm4 hsmA hrr hM hR8 a Lam
    (qsNum_small ell 12 M α₀ hα0.le hell0 hQN)
  obtain ⟨hG, hNm⟩ := units_strat ell k Lu hell0 S (periodicGaugeTransform g U) a Lam _ ε2' hlt hcoer hD2' hQs
  exact (wellDef_gauge_iff hell0 S a Lam U g).1 ⟨(hb_gauge_iff hell0 S a Lam U g).2 hb, hG, hNm⟩

end AdalyFormal.M1GaugeW4

#print axioms AdalyFormal.M1GaugeW4.patch_at_Ug
#print axioms AdalyFormal.M1GaugeW4.w4_M1_patched
#print axioms AdalyFormal.M1GaugeW4.wellDef_M1_patched
