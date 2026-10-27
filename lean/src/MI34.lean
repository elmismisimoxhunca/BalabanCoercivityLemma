import MI33
import ZR8Data

/-!
# MI34 -- LOCALISATION of the W4/W5 hypotheses to `Ω₀` via the r8 locality theorem (M1 lane E, 2026-10-13)

The r8 statement's locality layer (`ZR8DataB.data_congr`, `ZR8Data.WellDef_congr`) says: under `Admissible`, `ℓ ≥ 2` and the room
`17ℓ ≤ RM`, the whole base data of `gparams … U …` reads `U` only on the bonds with BOTH endpoints in `Ω₀`.  Hence every
hypothesis on `U` used by MI33 may be imposed on ANY `U'` agreeing with `U` on those bonds (e.g. `U` inside `Ω₀`, `1` outside).
* `ginv_congr_U` : `⟪A, Ginv_U A⟫ = ⟪A, Ginv_{U'} A⟫`;  `patch_congr_U` : `PatchCoercive … U … cP ↔ PatchCoercive … U' … cP`;
* **`ginv_weighted_coercive_loc`** : W4 for `U` from the MI33 hypotheses for `U'` (in particular the GLOBAL tower class for the
  bond `Q` and the site/holonomy regimes are only needed for `U'`);
* **`wellDef_strat_loc`** : W5 (`WellDef`) for `U` from the MI33 hypotheses for `U'` (with `hb` from `hb_of_small` at `U'`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
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

section congr
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}

theorem data_congr_U (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    (U U' : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hUU : ∀ e : Bond (scaleUp ell k Lu), BothIn (S.Om 0) e → U e = U' e) :
    (gparams ell k Lu hell0 S U' a Lam).data = (gparams ell k Lu hell0 S U a Lam).data :=
  AdalyFormal.StatementLaneR8.data_congr (gparams ell k Lu hell0 S U a Lam) hS hell hroom U' hUU

theorem ginv_congr_U (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    (U U' : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hUU : ∀ e : Bond (scaleUp ell k Lu), BothIn (S.Om 0) e → U e = U' e)
    (A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G)) :
    ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ = ⟪A, (gparams ell k Lu hell0 S U' a Lam).data.Ginv A⟫ := by
  rw [data_congr_U hell0 hS hell hroom U U' a Lam hUU]

theorem patch_congr_U {κ c : ℕ} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    (U U' : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hUU : ∀ e : Bond (scaleUp ell k Lu), BothIn (S.Om 0) e → U e = U' e) (cP : ℝ) :
    PatchCoercive ell M k κ c Lu hell0 S U a Lam cP ↔ PatchCoercive ell M k κ c Lu hell0 S U' a Lam cP := by
  have hd := data_congr_U hell0 hS hell hroom U U' a Lam hUU
  unfold PatchCoercive ginvForm wN
  rw [hd]

end congr

section main
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c) {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
include hell0 hS hκ hM hell hR1 hR hc hW hWR

/-- **W4 for `U` from the hypotheses at any `U'` agreeing with `U` on the `Ω₀` bonds**. -/
theorem ginv_weighted_coercive_loc (hroom : 17 * ell ≤ R * M) (U U' : LinkCfg (scaleUp ell k Lu))
    (hUU : ∀ e : Bond (scaleUp ell k Lu), BothIn (S.Om 0) e → U e = U' e) (a : ℝ) (ha : 0 < a)
    (Lam : Set (PeriodicLatticeSite Lu))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (h216 : 216 * ρ ^ 2 < 1) (h12 : 12 * ρ ≤ 1)
    (hU : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U' b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
    (hT : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j),
      z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ i) → ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower (geomOf ell k S) U' i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)
    (hsm : 24 * ((Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2
          + 1 * (Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1)) ^ 2) ≤ csOf a ρ)
    (hsmD : 4 * (Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2 ≤ csOf a ρ)
    (hgs : Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a)
        * (psiHypP hS hW hell hR1 (by omega) hWR U' a (csOf a ρ)
            (hatPack_of hS hell U' a ha ρ hρ h216 hU hT hsm hsmD)).epsX (Real.sqrt (max a 1)) < (1 - 12 * ρ) ^ 2)
    (ρh : ℝ) (hρh : 0 ≤ ρh) (hreg : HolRegime S ell k U' ρh)
    (ε : ℕ → ℝ) (hregT : RegTower ell (bgTower (GF ell k Lu) U') k) (hcl : TowerClass ell k Lu U' ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsmε : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2) (hη : etaC ell W (csOf a ρ) ρh ε1 < 1)
    (cP : ℝ) (hP : PatchCoercive ell M k κ c Lu hell0 S U a Lam cP)
    (A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G)) :
    cwW4 ell M κ c W a ρ ρh ε1 ε2 cP
        ((psiHypP hS hW hell hR1 (by omega) hWR U' a (csOf a ρ)
          (hatPack_of hS hell U' a ha ρ hρ h216 hU hT hsm hsmD)).epsX (Real.sqrt (max a 1)))
        (CMc ell M κ c k a ε)
      * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ := by
  have hP' := (patch_congr_U hell0 hS hell hroom U U' a Lam hUU cP).mp hP
  rw [ginv_congr_U hell0 hS hell hroom U U' a Lam hUU A]
  exact ginv_weighted_coercive_full hell0 hS hκ hM hell hR1 hR hc hW hWR U' a ha Lam ρ hρ h216 h12 hU hT hsm hsmD hgs
    ρh hρh hreg ε hregT hcl hε0 hsmε ε1 ε2 hε1 hε2 hη cP hP' A

/-- **W5 for `U` from the hypotheses at any `U'` agreeing with `U` on the `Ω₀` bonds** (r8 `WellDef_congr`). -/
theorem wellDef_strat_loc (Lam0 : Set (PeriodicLatticeSite Lu)) (hloc : AdalyFormal.StatementLaneR8.LocHyp ell M R k S Lam0)
    (U U' : LinkCfg (scaleUp ell k Lu))
    (hUU : ∀ e : Bond (scaleUp ell k Lu), BothIn (S.Om 0) e → U e = U' e) (a : ℝ) (ha : 0 < a)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (h216 : 216 * ρ ^ 2 < 1) (h12 : 12 * ρ ≤ 1)
    (hU : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U' b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
    (hT : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j),
      z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ i) → ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower (geomOf ell k S) U' i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)
    (hsm : 24 * ((Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2
          + 1 * (Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1)) ^ 2) ≤ csOf a ρ)
    (hsmD : 4 * (Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2 ≤ csOf a ρ)
    (hgs : Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a)
        * (psiHypP hS hW hell hR1 (by omega) hWR U' a (csOf a ρ)
            (hatPack_of hS hell U' a ha ρ hρ h216 hU hT hsm hsmD)).epsX (Real.sqrt (max a 1)) < (1 - 12 * ρ) ^ 2)
    (ρh : ℝ) (hρh : 0 ≤ ρh) (hreg : HolRegime S ell k U' ρh)
    (ε : ℕ → ℝ) (hregT : RegTower ell (bgTower (GF ell k Lu) U') k) (hcl : TowerClass ell k Lu U' ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsmε : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2) (hη : etaC ell W (csOf a ρ) ρh ε1 < 1)
    (cP : ℝ) (hP : PatchCoercive ell M k κ c Lu hell0 S U a Lam0 cP)
    (ε2' : ℝ)
    (hlt : ε2' < cwW4 ell M κ c W a ρ ρh ε1 ε2 cP
        ((psiHypP hS hW hell hR1 (by omega) hWR U' a (csOf a ρ)
          (hatPack_of hS hell U' a ha ρ hρ h216 hU hT hsm hsmD)).epsX (Real.sqrt (max a 1)))
        (CMc ell M κ c k a ε))
    (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U' a Lam0).G),
      |⟪A, (gparams ell k Lu hell0 S U' a Lam0).data.Delta2 (gparams ell k Lu hell0 S U' a Lam0).data_laws A⟫|
        ≤ ε2' * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
    (hQs : Function.Injective (gparams ell k Lu hell0 S U' a Lam0).data.Qs)
    (hd : ∀ μ, ell ∣ Lu μ + 1) (e0 : ℝ) (he0 : 0 ≤ e0) (hle : e0 ≤ 1 / (1000 * (ell : ℝ) ^ 4))
    (hr : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * e0) < r0)
    (hV : ∀ e, frobNorm (((gparams ell k Lu hell0 S U' a Lam0).unitBgU e : M2) - 1) ≤ e0) :
    GenP.WellDef (gparams ell k Lu hell0 S U a Lam0) := by
  have hP' := (patch_congr_U hell0 hS hell hloc.room U U' a Lam0 hUU cP).mp hP
  have hW' := wellDef_strat_small hell0 hS hκ hM hell hR1 hR hc hW hWR U' a ha Lam0 ρ hρ h216 h12 hU hT hsm hsmD hgs
    ρh hρh hreg ε hregT hcl hε0 hsmε ε1 ε2 hε1 hε2 hη cP hP' ε2' hlt hD2 hQs hd e0 he0 hle hr hV
  exact (AdalyFormal.StatementLaneR8.WellDef_congr (gparams ell k Lu hell0 S U a Lam0) hloc U' hUU).mp hW'

end main

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.data_congr_U
#print axioms AdalyFormal.M1IMS.ginv_congr_U
#print axioms AdalyFormal.M1IMS.patch_congr_U
#print axioms AdalyFormal.M1IMS.ginv_weighted_coercive_loc
#print axioms AdalyFormal.M1IMS.wellDef_strat_loc
