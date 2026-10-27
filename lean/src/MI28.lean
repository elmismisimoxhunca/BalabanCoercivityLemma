import MI27
import MI22

/-!
# MI28 -- W4 with the sharp row bound and `Γ⁻¹` DISCHARGED (M1 lane E, 2026-10-13)

* `csOf` : the S1 constant `cs = (1 − 216ρ²)/max(6, 16/(3a))`;
* `hatPack_of` : the `HatPack` from lane C's `site_coercive_weighted` and `isUnit_LP_strat` under lane C's gauge
  hypotheses `hU`, `hT`, plus the two explicit smallness inequalities on `W` (`hsm`, `hsmD`);
* `gamC` : the sharp row constant of MI27 `gamma_sharp`;
* **`ginv_weighted_coercive_M1`** : W4 on a proper tower with `γ` from `gamma_sharp` (MI27) and `Γ⁻¹` from lane C's
  `exists_Gami_strat`; remaining inputs: `hU`, `hT` (gauge), `HolRegime` (holonomy), `MassComm` (discharged in MI32/MI33),
  `PatchCoercive` (W3), numeric smallness.
(W5 `wellDef_strat` is in MI33.)
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
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

/-- the S1 constant. -/
noncomputable def csOf (a ρ : ℝ) : ℝ := (1 - 216 * ρ ^ 2) / max 6 (16 / (3 * a))

section hp
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} {W : ℕ}

theorem hatPack_of (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (U : Cfg Lf) (a : ℝ) (ha : 0 < a)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (h216 : 216 * ρ ^ 2 < 1)
    (hU : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
    (hT : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j),
      z ∈ CoarseLattice Lf (ell ^ i) → ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower (geomOf ell k S) U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)
    (hsm : 24 * ((Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2
          + 1 * (Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1)) ^ 2) ≤ csOf a ρ)
    (hsmD : 4 * (Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2 ≤ csOf a ρ) :
    HatPack (ell := ell) (k := k) (S := S) (W := W) U a (csOf a ρ) := by
  have hell0 : 0 < ell := by omega
  have hP := properTower_geomOf hell0 hS
  have hdvd := hdvd_of_admissible hS
  have hM6 : (6 : ℝ) ≤ max 6 (16 / (3 * a)) := le_max_left _ _
  have hM0 : (0 : ℝ) < max 6 (16 / (3 * a)) := lt_of_lt_of_le (by norm_num) hM6
  have h1 : 0 < 1 - 216 * ρ ^ 2 := by linarith
  refine ⟨ha, isUnit_LP_strat ell k hell hdvd hP U a ha ρ hρ h216 hU hT, div_pos h1 hM0, ?_, ?_, hsm, hsmD⟩
  · unfold csOf
    rw [div_le_one hM0]
    nlinarith [sq_nonneg ρ]
  · intro f
    have h := site_coercive_weighted ell k hell hdvd hP U a ha ρ hρ hU hT f
    unfold csOf
    rw [div_mul_eq_mul_div, div_le_iff₀ hM0]
    linarith [h, mul_comm (max 6 (16 / (3 * a))) ⟪f, DelpA (geomOf ell k S) U a f⟫]

end hp

/-- the sharp row constant of MI27. -/
noncomputable def gamC (ell : ℕ) (a ρ eX : ℝ) : ℝ :=
  (ell : ℝ) * (Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a))
    / ((1 - 12 * ρ) ^ 2 - Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a) * eX)

section main
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c) {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
include hell0 hS hκ hM hell hR1 hR hc hW hWR

/-- **W4 on a proper tower, with the sharp row bound and `Γ⁻¹` discharged**. -/
theorem ginv_weighted_coercive_M1 (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a)
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
    (CM : ℝ) (hCM : 0 ≤ CM) (hMass : MassComm ell M k κ c S U a CM)
    (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2) (hη : etaC ell W (csOf a ρ) ρh ε1 < 1)
    (cP : ℝ) (hP : PatchCoercive ell M k κ c Lu hell0 S U a Lam cP)
    (A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G)) :
    ((cP - ((1 + etaC ell W (csOf a ρ) ρh ε1) * (1 + ε2) * (2 * nuC ell ρh) / (1 - etaC ell W (csOf a ρ) ρh ε1)
        + (1 + etaC ell W (csOf a ρ) ρh ε1) * C1c ell M κ c W a (csOf a ρ)
            (gamC ell a ρ ((psiHypP hS hW hell hR1 (by omega) hWR U a (csOf a ρ)
              (hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD)).epsX (Real.sqrt (max a 1)))) CM ε2
        + 2 * nuC ell ρh))
      / (1 + ((1 + etaC ell W (csOf a ρ) ρh ε1) * (1 + ε2) / (1 - etaC ell W (csOf a ρ) ρh ε1) - 1)))
      * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ := by
  have hp := hatPack_of hS hell U a ha ρ hρ h216 hU hT hsm hsmD
  have hP0 := properTower_geomOf hell0 hS
  obtain ⟨Gi, hG1, hG2⟩ := exists_Gami_strat ell k hell (hdvd_of_admissible hS) hP0 U a ha ρ hρ h216 hU hT
  set eX := (psiHypP hS hW hell hR1 (by omega) hWR U a (csOf a ρ) hp).epsX (Real.sqrt (max a 1)) with heX
  have hγ := gamma_sharp hS hW hell hR1 (by omega) hWR U a (csOf a ρ) hp ρ hρ h12 hU hT hgs
  have hD : 0 < (1 - 12 * ρ) ^ 2 - Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a) * eX := by
    linarith
  have hγ0 : 0 ≤ gamC ell a ρ eX := by
    unfold gamC
    have : 0 ≤ Real.sqrt (max a 1) := Real.sqrt_nonneg _
    positivity
  exact ginv_weighted_coercive hell0 hS hκ hM hell hR1 hR hc hW hWR U a (csOf a ρ) Lam hp Gi hG1 hG2
    (gamC ell a ρ eX) hγ0 hγ ρh hρh hreg CM hCM hMass ε1 ε2 hε1 hε2 hη cP hP A

end main

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.csOf
#print axioms AdalyFormal.M1IMS.hatPack_of
#print axioms AdalyFormal.M1IMS.gamC
#print axioms AdalyFormal.M1IMS.ginv_weighted_coercive_M1
