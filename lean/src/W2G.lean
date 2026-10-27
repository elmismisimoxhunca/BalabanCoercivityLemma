import W2E
import MI34

/-!
# W2G -- W4 and W5 re-closed with W2: the patch-coercivity hypothesis `PatchCoercive cP` of lane E REPLACED by the patch-tower
inputs `W3G0At` / `OptDecayAt` (M1 lane W2, 2026-10-13)

* **`ginv_weighted_coercive_W2`** : lane E's `ginv_weighted_coercive_full` (MI33) with `hP : PatchCoercive cP` discharged by
  `patchCoercive_W2` at `cP = (1 − etaC) · min(a, cW − δ) − 2 · nuC` (lane E's own `etaC`, `nuC` at `cs = csOf a ρ`, holonomy
  constant `ρh`).  Extra hypotheses relative to MI33: `(c+4) κ ell ≤ R` (instead of `(c+3)`), `17 ell ≤ R M`, `d + 32 ell² ≤ κ M`,
  and per patch a comparison configuration `Up j w` (equal to `U` within `(c+1) G_j`) with the two inputs.
* **`wellDef_strat_W2`** : lane E's `wellDef_strat` (W5) with the same replacement.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1W2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp pdist)
open AdalyFormal.StatementLaneG (gparams GenP.WellDef GenP.Nmat)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.NonflatJet (rhoOf r0)
open AdalyFormal.BondComposite (TowerClass)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.M1IMS (cwW4 CMc csOf etaC nuC hatPack_of psiHypP HolRegime ginv_weighted_coercive_full wellDef_strat)
open AdalyFormal.M1 (IsPatch gsp)

section main
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR4 : (c + 4) * κ * ell ≤ R) (hc : 5 ≤ c) (hroom : 17 * ell ≤ R * M) {d : ℕ} (hdM : d + 32 * ell ^ 2 ≤ κ * M)
  {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
include hell0 hS hκ hM hell hR1 hR4 hc hroom hdM hW hWR

theorem hR3_of_hR4 : (c + 3) * κ * ell ≤ R := by
  have : (c + 3) * κ * ell ≤ (c + 4) * κ * ell := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  omega

/-- **W4 with W2**: the stratum-weighted coercivity of the genuine `Ginv`, `PatchCoercive` discharged. -/
theorem ginv_weighted_coercive_W2 (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a)
    (Lam : Set (PeriodicLatticeSite Lu))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (h216 : 216 * ρ ^ 2 < 1) (h12 : 12 * ρ ≤ 1)
    (hU : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
    (hT : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j),
      z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ i) → ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower (geomOf ell k S) U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)
    (hsm : 24 * ((Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2
          + 1 * (Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1)) ^ 2) ≤ csOf a ρ)
    (hsmD : 4 * (Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2 ≤ csOf a ρ)
    (hgs : Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a)
        * (psiHypP hS hW hell hR1 (by omega) hWR U a (csOf a ρ)
            (hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD)).epsX (Real.sqrt (max a 1)) < (1 - 12 * ρ) ^ 2)
    (ρh : ℝ) (hρh : 0 ≤ ρh) (hreg : HolRegime S ell k U ρh)
    (ε : ℕ → ℝ) (hregT : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsmε : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2) (hη : etaC ell W (csOf a ρ) ρh ε1 < 1)
    (Up : ℕ → PeriodicLatticeSite (scaleUp ell k Lu) → Cfg (scaleUp ell k Lu))
    (hUp : ∀ j w, IsPatch ell M k κ S j w → ∀ e : Bond (scaleUp ell k Lu),
      pdist w e.1 ≤ (c + 1) * gsp ell M κ j → U e = Up j w e)
    (cW δ : ℝ)
    (hW3 : ∀ j w, IsPatch ell M k κ S j w → W3G0At ell (scaleUp ell k Lu) (Up j w) a cW)
    (hDec : ∀ j w, IsPatch ell M k κ S j w → OptDecayAt ell (scaleUp ell k Lu) (Up j w) δ d)
    (A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G)) :
    cwW4 ell M κ c W a ρ ρh ε1 ε2 ((1 - etaC ell W (csOf a ρ) ρh ε1) * min a (cW - δ) - 2 * nuC ell ρh)
        ((psiHypP hS hW hell hR1 (by omega) hWR U a (csOf a ρ)
          (hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD)).epsX (Real.sqrt (max a 1)))
        (CMc ell M κ c k a ε)
      * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ := by
  have hR := hR3_of_hR4 hell0 hS hκ hM hell hR1 hR4 hc hroom hdM hW hWR
  have hP := patchCoercive_W2 hell0 hS hκ hM hell hR1 hR4 hroom hdM hW hWR U a (csOf a ρ) Lam
    (hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD) ρh hρh hreg ε1 hε1 hη Up hUp cW δ hW3 hDec
  exact ginv_weighted_coercive_full hell0 hS hκ hM hell hR1 hR hc hW hWR U a ha Lam ρ hρ h216 h12 hU hT hsm hsmD hgs
    ρh hρh hreg ε hregT hcl hε0 hsmε ε1 ε2 hε1 hε2 hη _ hP A

/-- **W5 with W2**: `WellDef` from W4 (W2-closed), the D-layer form bound, `Q*` injective and `hb`. -/
theorem wellDef_strat_W2 (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a)
    (Lam : Set (PeriodicLatticeSite Lu))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (h216 : 216 * ρ ^ 2 < 1) (h12 : 12 * ρ ≤ 1)
    (hU : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
    (hT : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j),
      z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ i) → ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower (geomOf ell k S) U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)
    (hsm : 24 * ((Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2
          + 1 * (Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1)) ^ 2) ≤ csOf a ρ)
    (hsmD : 4 * (Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2 ≤ csOf a ρ)
    (hgs : Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a)
        * (psiHypP hS hW hell hR1 (by omega) hWR U a (csOf a ρ)
            (hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD)).epsX (Real.sqrt (max a 1)) < (1 - 12 * ρ) ^ 2)
    (ρh : ℝ) (hρh : 0 ≤ ρh) (hreg : HolRegime S ell k U ρh)
    (ε : ℕ → ℝ) (hregT : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsmε : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2) (hη : etaC ell W (csOf a ρ) ρh ε1 < 1)
    (Up : ℕ → PeriodicLatticeSite (scaleUp ell k Lu) → Cfg (scaleUp ell k Lu))
    (hUp : ∀ j w, IsPatch ell M k κ S j w → ∀ e : Bond (scaleUp ell k Lu),
      pdist w e.1 ≤ (c + 1) * gsp ell M κ j → U e = Up j w e)
    (cW δ : ℝ)
    (hW3 : ∀ j w, IsPatch ell M k κ S j w → W3G0At ell (scaleUp ell k Lu) (Up j w) a cW)
    (hDec : ∀ j w, IsPatch ell M k κ S j w → OptDecayAt ell (scaleUp ell k Lu) (Up j w) δ d)
    (ε2' : ℝ)
    (hlt : ε2' < cwW4 ell M κ c W a ρ ρh ε1 ε2 ((1 - etaC ell W (csOf a ρ) ρh ε1) * min a (cW - δ) - 2 * nuC ell ρh)
        ((psiHypP hS hW hell hR1 (by omega) hWR U a (csOf a ρ)
          (hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD)).epsX (Real.sqrt (max a 1)))
        (CMc ell M κ c k a ε))
    (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G),
      |⟪A, (gparams ell k Lu hell0 S U a Lam).data.Delta2 (gparams ell k Lu hell0 S U a Lam).data_laws A⟫|
        ≤ ε2' * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
    (hQs : Function.Injective (gparams ell k Lu hell0 S U a Lam).data.Qs)
    (hb : Function.Bijective (H0 (gparams ell k Lu hell0 S U a Lam).Lam (gparams ell k Lu hell0 S U a Lam).Q1)) :
    GenP.WellDef (gparams ell k Lu hell0 S U a Lam) := by
  have hR := hR3_of_hR4 hell0 hS hκ hM hell hR1 hR4 hc hroom hdM hW hWR
  have hP := patchCoercive_W2 hell0 hS hκ hM hell hR1 hR4 hroom hdM hW hWR U a (csOf a ρ) Lam
    (hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD) ρh hρh hreg ε1 hε1 hη Up hUp cW δ hW3 hDec
  exact wellDef_strat hell0 hS hκ hM hell hR1 hR hc hW hWR U a ha Lam ρ hρ h216 h12 hU hT hsm hsmD hgs ρh hρh hreg ε hregT
    hcl hε0 hsmε ε1 ε2 hε1 hε2 hη _ hP ε2' hlt hD2 hQs hb

end main

end AdalyFormal.M1W2

#print axioms AdalyFormal.M1W2.hR3_of_hR4
#print axioms AdalyFormal.M1W2.ginv_weighted_coercive_W2
#print axioms AdalyFormal.M1W2.wellDef_strat_W2
