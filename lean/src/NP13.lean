import NP12

/-!
# NP13 -- W4 / W5 with the patch input discharged at NON-FLAT `U`
(m1_patch_nonflat, 2026-10-14)

**`ginv_weighted_coercive_nonflat`** : lane E's MI33 `ginv_weighted_coercive_full` (every hypothesis of MI33 kept as
stated there) with its `hP : PatchCoercive … cP` supplied by NP12 `patchCoercive_nonflat` for `U` in lane B's regime
`M1Regular ell M 12 k S α₀ (ell^k)⁻¹ U`, `12 M α₀ ≤ a₀`.  Room `(c+4)κ ell ≤ R` (MI33's `(c+3)` follows, W2G
`hR3_of_hR4`) and `d + 64 ell² ≤ κ M`.  The constants `cW, a₀, D` depend on `ell, a` only.
**`wellDef_strat_nonflat`** : MI33 `wellDef_strat` (W5) likewise, its remaining hypotheses (`hlt`, `hD2`, `hQs`, `hb`) kept.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1NonFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp pdist)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.NonflatJet (rhoOf)
open AdalyFormal.BondComposite (TowerClass)
open AdalyFormal.M1IMS (cwW4 CMc csOf etaC nuC hatPack_of psiHypP HolRegime ginv_weighted_coercive_full)

theorem ginv_weighted_coercive_nonflat {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ D : ℕ, 12 * ell + 10 ≤ D ∧
    (∀ d, D ≤ d → epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2) ∧
    ∀ {M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
      {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hR1 : 1 ≤ R)
      (hR4 : (c + 4) * κ * ell ≤ R) (hc : 5 ≤ c) (hroom : 17 * ell ≤ R * M) {d : ℕ} (_hdD : D ≤ d)
      (hdM : d + 64 * ell ^ 2 ≤ κ * M)
      {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
      (U : LinkCfg (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (ρ : ℝ) (hρ : 0 ≤ ρ) (h216 : 216 * ρ ^ 2 < 1) (h12 : 12 * ρ ≤ 1)
      (hU : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
        frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
      (hT : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j),
        z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ i) → ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
        frobNorm ((bgTower (geomOf ell k S) U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
          ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)
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
      (α₀ : ℝ) (hα0 : 0 < α₀) (hαa : (12 : ℝ) * M * α₀ ≤ a₀)
      (hM1 : AdalyFormal.M1.M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
      (A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G)),
      cwW4 ell M κ c W a ρ ρh ε1 ε2
          ((1 - etaC ell W (csOf a ρ) ρh ε1) * min a (cW - epsNF ell (PkA a) (thetaN ell) d) - 2 * nuC ell ρh)
          ((psiHypP hS hW hell hR1 (by omega) hWR U a (csOf a ρ)
            (hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD)).epsX (Real.sqrt (max a 1)))
          (CMc ell M κ c k a ε)
        * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ := by
  obtain ⟨cW, hcW, a₀, ha₀, D, hD, hDle, hall⟩ := patchCoercive_nonflat hell ha
  refine ⟨cW, hcW, a₀, ha₀, D, hD, hDle, ?_⟩
  intro M R k κ c Lu hell0 S hS hκ hM hR1 hR4 hc hroom d hdD hdM W hW hWR U Lam ρ hρ h216 h12 hU hT hsm hsmD hgs
    ρh hρh hreg ε hregT hcl hε0 hsmε ε1 ε2 hε1 hε2 hη α₀ hα0 hαa hM1 A
  have hR : (c + 3) * κ * ell ≤ R := by
    have : (c + 3) * κ * ell ≤ (c + 4) * κ * ell := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    omega
  have hP := hall hell0 hS hκ hM hR1 hR4 hroom hdD hdM hW hWR U (csOf a ρ) Lam
    (hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD) ρh hρh hreg ε1 hε1 hη α₀ hα0 hαa hM1
  exact ginv_weighted_coercive_full hell0 hS hκ hM hell hR1 hR hc hW hWR U a ha Lam ρ hρ h216 h12 hU hT hsm hsmD hgs
    ρh hρh hreg ε hregT hcl hε0 hsmε ε1 ε2 hε1 hε2 hη _ hP A

/-- **W5 at non-flat `U`**: MI33 `wellDef_strat` with `PatchCoercive` from NP12. -/
theorem wellDef_strat_nonflat {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ D : ℕ, 12 * ell + 10 ≤ D ∧
    (∀ d, D ≤ d → epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2) ∧
    ∀ {M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
      {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hR1 : 1 ≤ R)
      (hR4 : (c + 4) * κ * ell ≤ R) (hc : 5 ≤ c) (hroom : 17 * ell ≤ R * M) {d : ℕ} (_hdD : D ≤ d)
      (hdM : d + 64 * ell ^ 2 ≤ κ * M)
      {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
      (U : LinkCfg (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (ρ : ℝ) (hρ : 0 ≤ ρ) (h216 : 216 * ρ ^ 2 < 1) (h12 : 12 * ρ ≤ 1)
      (hU : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
        frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
      (hT : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j),
        z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ i) → ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
        frobNorm ((bgTower (geomOf ell k S) U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
          ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)
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
      (α₀ : ℝ) (hα0 : 0 < α₀) (hαa : (12 : ℝ) * M * α₀ ≤ a₀)
      (hM1 : AdalyFormal.M1.M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
      (ε2' : ℝ)
      (hlt : ε2' < cwW4 ell M κ c W a ρ ρh ε1 ε2
          ((1 - etaC ell W (csOf a ρ) ρh ε1) * min a (cW - epsNF ell (PkA a) (thetaN ell) d) - 2 * nuC ell ρh)
          ((psiHypP hS hW hell hR1 (by omega) hWR U a (csOf a ρ)
            (hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD)).epsX (Real.sqrt (max a 1)))
          (CMc ell M κ c k a ε))
      (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G),
        |⟪A, (gparams ell k Lu hell0 S U a Lam).data.Delta2 (gparams ell k Lu hell0 S U a Lam).data_laws A⟫|
          ≤ ε2' * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
      (hQs : Function.Injective (gparams ell k Lu hell0 S U a Lam).data.Qs)
      (hb : Function.Bijective (H0 (gparams ell k Lu hell0 S U a Lam).Lam (gparams ell k Lu hell0 S U a Lam).Q1)),
      AdalyFormal.StatementLaneG.GenP.WellDef (gparams ell k Lu hell0 S U a Lam) := by
  obtain ⟨cW, hcW, a₀, ha₀, D, hD, hDle, hall⟩ := patchCoercive_nonflat hell ha
  refine ⟨cW, hcW, a₀, ha₀, D, hD, hDle, ?_⟩
  intro M R k κ c Lu hell0 S hS hκ hM hR1 hR4 hc hroom d hdD hdM W hW hWR U Lam ρ hρ h216 h12 hU hT hsm hsmD hgs
    ρh hρh hreg ε hregT hcl hε0 hsmε ε1 ε2 hε1 hε2 hη α₀ hα0 hαa hM1 ε2' hlt hD2 hQs hb
  have hR : (c + 3) * κ * ell ≤ R := by
    have : (c + 3) * κ * ell ≤ (c + 4) * κ * ell := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    omega
  have hP := hall hell0 hS hκ hM hR1 hR4 hroom hdD hdM hW hWR U (csOf a ρ) Lam
    (hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD) ρh hρh hreg ε1 hε1 hη α₀ hα0 hαa hM1
  exact AdalyFormal.M1IMS.wellDef_strat hell0 hS hκ hM hell hR1 hR hc hW hWR U a ha Lam ρ hρ h216 h12 hU hT hsm hsmD
    hgs ρh hρh hreg ε hregT hcl hε0 hsmε ε1 ε2 hε1 hε2 hη _ hP ε2' hlt hD2 hQs hb

end AdalyFormal.M1NonFlat

#print axioms AdalyFormal.M1NonFlat.ginv_weighted_coercive_nonflat
#print axioms AdalyFormal.M1NonFlat.wellDef_strat_nonflat
