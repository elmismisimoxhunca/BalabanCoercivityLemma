import MI28
import MI32
import MI21
import MF6d

/-!
# MI33 -- W4 and W5 on a proper tower with the sharp row bound, `Γ⁻¹` and the mass commutator DISCHARGED (M1 lane E)

* `cwW4` : the W4 constant (MI22 form) with `cs = csOf a ρ`, `γ = gamC …`, `CM = CMc …`.
* **`ginv_weighted_coercive_full`** : `cwW4 · wnormSq A ≤ ⟪A, Ginv A⟫` for every `A ∈ bondSupp`, on `G = geomOf ell k S`
  (admissible), from: lane C's site gauge hypotheses `hU`, `hT` (ρ, `216ρ² < 1`, `12ρ ≤ 1`); the holonomy regime
  `HolRegime` (ρh); the M0-chain tower hypotheses for the bond `Q` (`RegTower`, `TowerClass ε`, `ε ≥ 0`, `ρ(ε) < π/2`);
  W3 `PatchCoercive cP` (lane D's object, stated in MI2); the explicit numeric smallness `hsm`, `hsmD`, `hgs`, `hη`.
* **`wellDef_strat`** : `GenP.WellDef (gparams …)` (= `hb ∧ IsUnit G₁⁻¹ ∧ IsUnit (Q G₁ Q*)`) from W4 + the stratified D-layer
  form bound `hD2` (`ε₂' < cwW4`) + `Q*` injective (W6) + `hb`.
* `wellDef_strat_small` : the same with `hb` from the ported `hb_of_small` (per-link smallness of the level-`k` unit background
  at EVERY unit bond, as in M0's `wellDef_M0`).
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

/-- the W4 constant. -/
noncomputable def cwW4 (ell M κ c W : ℕ) (a ρ ρh ε1 ε2 cP eX CM : ℝ) : ℝ :=
  (cP - ((1 + etaC ell W (csOf a ρ) ρh ε1) * (1 + ε2) * (2 * nuC ell ρh) / (1 - etaC ell W (csOf a ρ) ρh ε1)
      + (1 + etaC ell W (csOf a ρ) ρh ε1) * C1c ell M κ c W a (csOf a ρ) (gamC ell a ρ eX) CM ε2
      + 2 * nuC ell ρh))
    / (1 + ((1 + etaC ell W (csOf a ρ) ρh ε1) * (1 + ε2) / (1 - etaC ell W (csOf a ρ) ρh ε1) - 1))

theorem CMc_nonneg (ell M κ c k : ℕ) (a : ℝ) (ha : 0 ≤ a) (ε : ℕ → ℝ) : 0 ≤ CMc ell M κ c k a ε := by
  unfold CMc
  have := KG_nonneg ell M κ c
  positivity

section main
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c) {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
include hell0 hS hκ hM hell hR1 hR hc hW hWR

/-- **W4, proper tower, everything but W3 and the regime hypotheses discharged**. -/
theorem ginv_weighted_coercive_full (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a)
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
    (cP : ℝ) (hP : PatchCoercive ell M k κ c Lu hell0 S U a Lam cP)
    (A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G)) :
    cwW4 ell M κ c W a ρ ρh ε1 ε2 cP
        ((psiHypP hS hW hell hR1 (by omega) hWR U a (csOf a ρ)
          (hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD)).epsX (Real.sqrt (max a 1)))
        (CMc ell M κ c k a ε)
      * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ := by
  have hMass := massComm_proper hS hκ hM hell hR1 hR hc U a ha.le ε hregT hcl hε0 hsmε
  exact ginv_weighted_coercive_M1 hell0 hS hκ hM hell hR1 hR hc hW hWR U a ha Lam ρ hρ h216 h12 hU hT hsm hsmD hgs
    ρh hρh hreg (CMc ell M κ c k a ε) (CMc_nonneg ell M κ c k a ha.le ε) hMass ε1 ε2 hε1 hε2 hη cP hP A

/-- **W5 on a proper tower**: `WellDef` from W4, the D-layer form bound, `Q*` injective and `hb`. -/
theorem wellDef_strat (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a)
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
    (cP : ℝ) (hP : PatchCoercive ell M k κ c Lu hell0 S U a Lam cP)
    (ε2' : ℝ)
    (hlt : ε2' < cwW4 ell M κ c W a ρ ρh ε1 ε2 cP
        ((psiHypP hS hW hell hR1 (by omega) hWR U a (csOf a ρ)
          (hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD)).epsX (Real.sqrt (max a 1)))
        (CMc ell M κ c k a ε))
    (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G),
      |⟪A, (gparams ell k Lu hell0 S U a Lam).data.Delta2 (gparams ell k Lu hell0 S U a Lam).data_laws A⟫|
        ≤ ε2' * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
    (hQs : Function.Injective (gparams ell k Lu hell0 S U a Lam).data.Qs)
    (hb : Function.Bijective (H0 (gparams ell k Lu hell0 S U a Lam).Lam (gparams ell k Lu hell0 S U a Lam).Q1)) :
    GenP.WellDef (gparams ell k Lu hell0 S U a Lam) := by
  have hcoer := fun A => ginv_weighted_coercive_full hell0 hS hκ hM hell hR1 hR hc hW hWR U a ha Lam ρ hρ h216 h12
    hU hT hsm hsmD hgs ρh hρh hreg ε hregT hcl hε0 hsmε ε1 ε2 hε1 hε2 hη cP hP A
  obtain ⟨hG, hN⟩ := units_strat ell k Lu hell0 S U a Lam _ ε2' hlt hcoer hD2 hQs
  exact ⟨hb, hG, hN⟩

/-- **W5 with `hb` from per-link smallness of the unit background** (`hb_of_small`, the M0 pattern). -/
theorem wellDef_strat_small (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a)
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
    (cP : ℝ) (hP : PatchCoercive ell M k κ c Lu hell0 S U a Lam cP)
    (ε2' : ℝ)
    (hlt : ε2' < cwW4 ell M κ c W a ρ ρh ε1 ε2 cP
        ((psiHypP hS hW hell hR1 (by omega) hWR U a (csOf a ρ)
          (hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD)).epsX (Real.sqrt (max a 1)))
        (CMc ell M κ c k a ε))
    (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G),
      |⟪A, (gparams ell k Lu hell0 S U a Lam).data.Delta2 (gparams ell k Lu hell0 S U a Lam).data_laws A⟫|
        ≤ ε2' * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
    (hQs : Function.Injective (gparams ell k Lu hell0 S U a Lam).data.Qs)
    (hd : ∀ μ, ell ∣ Lu μ + 1) (e0 : ℝ) (he0 : 0 ≤ e0) (hle : e0 ≤ 1 / (1000 * (ell : ℝ) ^ 4))
    (hr : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * e0) < r0)
    (hV : ∀ e, frobNorm (((gparams ell k Lu hell0 S U a Lam).unitBgU e : M2) - 1) ≤ e0) :
    GenP.WellDef (gparams ell k Lu hell0 S U a Lam) :=
  wellDef_strat hell0 hS hκ hM hell hR1 hR hc hW hWR U a ha Lam ρ hρ h216 h12 hU hT hsm hsmD hgs ρh hρh hreg ε hregT
    hcl hε0 hsmε ε1 ε2 hε1 hε2 hη cP hP ε2' hlt hD2 hQs
    (AdalyFormal.M0Finish.R7.hb_of_small (gparams ell k Lu hell0 S U a Lam) hd e0 he0 hle hr hV)

end main

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.cwW4
#print axioms AdalyFormal.M1IMS.CMc_nonneg
#print axioms AdalyFormal.M1IMS.ginv_weighted_coercive_full
#print axioms AdalyFormal.M1IMS.wellDef_strat
#print axioms AdalyFormal.M1IMS.wellDef_strat_small
