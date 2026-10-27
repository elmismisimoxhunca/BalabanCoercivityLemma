import MXQ_Base
import CovH

/-!
# MXQ_CovF -- `fnu_in_cube` for ONE cube's regularity body (lane mixed_20261017, round 2).  Text copy of CovH.fnu_in_cube.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MXQ.M2Coverage

open AdalyFormal.M2Coverage
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2 (plaqIn)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.SourceJ (FnuMu DstarDir)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.DLayer (LocRep fN_sub fN_rsmul fN_sum3 sum_ite_ne fN_zero fN_neg frobNorm_cjM)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

/-- the plaquette function inside one class cube of index `i`: `‖F‖ ≤ (2β + 6β² + 1024β³) (ell^{2i})⁻¹`. -/
theorem fnu_in_cubeRB {ell M c : ℕ} {α₀ η : ℝ} {U : LinkCfg L} (hη : 0 < η) (hell : 1 ≤ ell)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hReg : MXQ.AllC.RegBodyH ell M c sites i α₀ η U)
    (hα : 0 ≤ α₀) (hsm : 4 * ((c : ℝ) * M * α₀) ≤ 1)
    (ν μ : Fin 3) (hνμ : ν ≠ μ) (y : PeriodicLatticeSite L)
    (b1 : CubeBond sites (y, ν)) (b2 : CubeBond sites (periodicLatticeShift y ν, μ))
    (b3 : CubeBond sites (periodicLatticeShift y μ, ν)) (b4 : CubeBond sites (y, μ)) :
    ∃ g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ,
      frobNorm (FnuMu (periodicGaugeTransform g U) ν μ y)
        ≤ (2 * ((c : ℝ) * M * α₀) + 6 * ((c : ℝ) * M * α₀) ^ 2 + 1024 * ((c : ℝ) * M * α₀) ^ 3) * ((ell : ℝ) ^ (2 * i))⁻¹ := by
  obtain ⟨g, A, h1, h2, -⟩ := hReg
  set β : ℝ := (c : ℝ) * M * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpi : (1 : ℝ) ≤ (ell : ℝ) ^ i := one_le_pow₀ hellr
  set q : ℝ := ((ell : ℝ) ^ i * η)⁻¹ with hq'
  have hηq : η * q = ((ell : ℝ) ^ i)⁻¹ := by
    rw [hq', mul_inv]; field_simp
  have hs0 : 0 ≤ ((ell : ℝ) ^ i)⁻¹ := by positivity
  have hs1 : ((ell : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpi
  have hl : LocRep (periodicGaugeTransform g U) η A (β * q ^ 1) (β * q ^ 2) (CubeBond sites) := by
    refine ⟨hη, fun e he => (h1 e he).2.1, fun e he => (h1 e he).1, fun e he => (h1 e he).2.2.le,
      fun z d d' h0 h1' => (h2 d' d z h0 h1').le, ?_⟩
    have : 4 * η * (β * q ^ 1) = 4 * β * ((ell : ℝ) ^ i)⁻¹ := by rw [pow_one, ← hηq]; ring
    rw [this]
    have : 4 * β * ((ell : ℝ) ^ i)⁻¹ ≤ 4 * β * 1 := mul_le_mul_of_nonneg_left hs1 (by positivity)
    linarith
  refine ⟨g, ?_⟩
  obtain ⟨R, hF, hR⟩ := hl.F_expand ν μ hνμ y b1 b2 b3 b4
  have hc := hl.curl_le y ν μ b1 b2 b3 b4
  have hk := hl.Kpl_le ν μ y b1 b2 b3 b4
  rw [hF]
  refine (AdalyFormal.DLayer.fN_add _ _).trans ?_
  refine (add_le_add (AdalyFormal.DLayer.fN_add _ _) le_rfl).trans ?_
  rw [fN_rsmul, abs_of_nonneg (by positivity)]
  set s : ℝ := ((ell : ℝ) ^ i)⁻¹ with hs
  have e2 : ((ell : ℝ) ^ (2 * i))⁻¹ = s ^ 2 := by rw [hs, pow_mul', inv_pow]
  have ea : η ^ 2 * (2 * (β * q ^ 2)) = 2 * β * s ^ 2 := by rw [← hηq]; ring
  have eb : 6 * (η * (β * q ^ 1)) ^ 2 = 6 * β ^ 2 * s ^ 2 := by rw [pow_one, ← hηq]; ring
  have ec : 1024 * η ^ 3 * (β * q ^ 1) ^ 3 = 1024 * β ^ 3 * s ^ 3 := by rw [pow_one, ← hηq]; ring
  have hcs := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ η ^ 2)
  rw [ea] at hcs
  rw [eb] at hk
  rw [ec] at hR
  have s3 : s ^ 3 ≤ s ^ 2 := by
    have : s ^ 3 = s ^ 2 * s := by ring
    rw [this]; exact mul_le_of_le_one_right (by positivity) hs1
  have hb3 : 0 ≤ β ^ 3 := by positivity
  rw [e2]
  nlinarith

end MXQ.M2Coverage

#print axioms MXQ.M2Coverage.fnu_in_cubeRB
