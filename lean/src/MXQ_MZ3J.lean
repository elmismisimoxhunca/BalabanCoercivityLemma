import MXQ_Base
import MZ3

/-!
# MXQ_MZ3J -- `Jf_covered` for ONE cube's regularity body (lane mixed_20261017, round 2).  Text copy of MZ3.Jf_covered.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace MXQ.M2DLayer

open AdalyFormal.M2DLayer
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2 (plaqIn)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.SourceJ (Jfield)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.DLayer (LocRep NeedBonds frobNorm_cjM)
open AdalyFormal.M1 (strat bstrat strat_le strat_eq_iff)
open AdalyFormal.M1DStrat (omJ JfieldLoc_eq_of_near jpoly_le)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

/-- **the covered-stencil source bound at class `U`, with the cube's own gauge** -/
theorem Jf_coveredRB {ell M R k c : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)}
    (hS : Admissible ell M R k S) (hRM : 4 ≤ R * M)
    (hα : 0 ≤ α₀) (hsm : 4 * ((c : ℝ) * M * α₀) ≤ 1)
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (b : Bond (scaleUp ell k Lu)) (hb2 : 2 ≤ bstrat S k b)
    {Q : Set (PeriodicLatticeSite (scaleUp ell k Lu))} {i : ℕ} (hq : IsClassCube ell M c k S Q i)
    (hReg : MXQ.AllC.RegBodyH ell M c Q i α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hcr : ∀ ν : Fin 3, ν ≠ b.2 → CurlReads Q (periodicLatticeShiftBack b.1 ν) ν b.2 ∧ CurlReads Q b.1 ν b.2) :
    ‖(gparams ell k Lu hell S U a Lam).Jf b‖ ≤ (400 * (ell : ℝ) ^ 3 * ((c : ℝ) * M * α₀)) * omJ S ell k b := by
  obtain ⟨g, A, h1, h2, h3⟩ := hReg
  have hell1 : 1 ≤ ell := hell
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  set η : ℝ := ((ell : ℝ) ^ k)⁻¹ with hηdef
  have hη : 0 < η := by positivity
  set β : ℝ := (c : ℝ) * M * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  set x := b.1 with hx
  set μ := b.2 with hμ
  set V := periodicGaugeTransform g U with hV
  -- `x` and its stratum
  have hsx : bstrat S k b ≤ strat S k x := min_le_left _ _
  have hs2 : 2 ≤ strat S k x := le_trans hb2 hsx
  have hx0 : x ∈ S.Om 0 := AdalyFormal.M1DStrat.mem_om0_of_strat hS (by omega)
  obtain ⟨ν0, hν0⟩ := exists_ne3 μ
  have hxQ : x ∈ Q := ((hcr ν0 hν0).2.2.2.2).1
  have hj : x ∈ towerBj S (strat S k x) := (strat_eq_iff hS (strat_le S k x) x).2 ⟨hx0, rfl⟩
  have hi : strat S k x ≤ i + 1 := AdalyFormal.M2Coverage.cube_index_ge hS hq hxQ hj
  -- the cube's local representation
  set q : ℝ := ((ell : ℝ) ^ i * η)⁻¹ with hq'
  set t : ℝ := ((ell : ℝ) ^ i)⁻¹ with ht
  have hpi : (1 : ℝ) ≤ (ell : ℝ) ^ i := one_le_pow₀ hellr
  have hηq : η * q = t := by rw [hq', ht, mul_inv]; field_simp
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ hpi
  have hl : LocRep V η A (β * q ^ 1) (β * q ^ 2) (CubeBond Q) := by
    refine ⟨hη, fun e he => (h1 e he).2.1, fun e he => (h1 e he).1, fun e he => (h1 e he).2.2.le,
      fun z d d' h0 h1' => (h2 d' d z h0 h1').le, ?_⟩
    have : 4 * η * (β * q ^ 1) = 4 * β * t := by rw [pow_one, ← hηq]; ring
    rw [this]
    have : 4 * β * t ≤ 4 * β * 1 := mul_le_mul_of_nonneg_left ht1 (by positivity)
    linarith
  -- the source in terms of `V`, without truncation
  have hnorm := AdalyFormal.DLayer.Jf_norm (gparams ell k Lu hell S U a Lam) b
  have hOm : (gparams ell k Lu hell S U a Lam).G.Om0 = S.Om 0 := rfl
  have hUP : (gparams ell k Lu hell S U a Lam).U = U := rfl
  rw [hOm, hUP] at hnorm
  have hg := AdalyFormal.GaugeCov.JfieldLoc_gauge g (plaqIn (S.Om 0)) U b.1 b.2
  have hfV : frobNorm (AdalyFormal.IngredientFamily.JfieldLoc (plaqIn (S.Om 0)) V b.1 b.2)
      = frobNorm (AdalyFormal.IngredientFamily.JfieldLoc (plaqIn (S.Om 0)) U b.1 b.2) := by
    rw [hV, hg, frobNorm_cjM]
  rw [← hfV] at hnorm
  rw [hnorm]
  have hs2' : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]; exact Real.sqrt_le_sqrt (by norm_num)
  refine (div_le_self (frobNorm_nonneg _) hs2').trans ?_
  have hzin : ∀ z, pdist x z ≤ 3 → z ∈ S.Om 0 := fun z hz => near_om0 hS hell1 (by omega) hs2 hz
  rw [JfieldLoc_eq_of_near (S.Om 0) V x μ hzin]
  have hneed : ∀ ν, ν ≠ μ → NeedBonds (CubeBond Q) (periodicLatticeShiftBack x ν) ν μ :=
    fun ν hν => needbonds_of_curl Q x μ ν (hcr ν hν).1 (hcr ν hν).2
  have hdd : frobNorm (AdalyFormal.StatementLane2.ddA η A x μ) ≤ β * q ^ 3 := (h3 μ x hcr).le
  have hJ := hl.J_local_bound x μ (β * q ^ 3) hneed hdd
  have hpoly : η ^ 3 * (β * q ^ 3 + 40 * (β * q ^ 1) * (β * q ^ 2) + 4144 * (β * q ^ 1) ^ 3
      + 8192 * η * (β * q ^ 1) ^ 4) ≤ t ^ 3 * (β + 40 * β ^ 2 + 4144 * β ^ 3 + 8192 * β ^ 4) := by
    have e1 : η ^ 3 * (β * q ^ 3 + 40 * (β * q ^ 1) * (β * q ^ 2) + 4144 * (β * q ^ 1) ^ 3
        + 8192 * η * (β * q ^ 1) ^ 4)
        = (η * q) ^ 3 * (β + 40 * β ^ 2 + 4144 * β ^ 3) + 8192 * β ^ 4 * (η * q) ^ 4 := by ring
    rw [e1, hηq]
    have : t ^ 4 ≤ t ^ 3 := by
      have := pow_le_pow_left₀ ht0.le ht1 3
      nlinarith [pow_pos ht0 3]
    nlinarith [pow_nonneg hβ0 4]
  have hjp := jpoly_le β hβ0 hsm
  -- `t³ ≤ ℓ³ omJ b`
  have hom : t ^ 3 ≤ (ell : ℝ) ^ 3 * omJ S ell k b := by
    unfold omJ
    have hb1 : bstrat S k b ≤ i + 1 := le_trans hsx hi
    have hp1 : (ell : ℝ) ^ bstrat S k b ≤ (ell : ℝ) ^ (i + 1) := pow_le_pow_right₀ hellr hb1
    have hpb : (0 : ℝ) < (ell : ℝ) ^ bstrat S k b := by positivity
    have hpi0 : (0 : ℝ) < (ell : ℝ) ^ i := by positivity
    have hl0 : (0 : ℝ) < ell := by linarith
    have h1' : t ≤ (ell : ℝ) * ((ell : ℝ) ^ bstrat S k b)⁻¹ := by
      have e : t = (ell : ℝ) * ((ell : ℝ) ^ (i + 1))⁻¹ := by rw [ht, pow_succ]; field_simp
      have h3 : ((ell : ℝ) ^ (i + 1))⁻¹ ≤ ((ell : ℝ) ^ bstrat S k b)⁻¹ := inv_anti₀ hpb hp1
      rw [e]; exact mul_le_mul_of_nonneg_left h3 hl0.le
    have h2' := pow_le_pow_left₀ ht0.le h1' 3
    calc t ^ 3 ≤ ((ell : ℝ) * ((ell : ℝ) ^ bstrat S k b)⁻¹) ^ 3 := h2'
      _ = (ell : ℝ) ^ 3 * (((ell : ℝ) ^ bstrat S k b)⁻¹) ^ 3 := by ring
  calc frobNorm (Jfield V x μ) ≤ t ^ 3 * (β + 40 * β ^ 2 + 4144 * β ^ 3 + 8192 * β ^ 4) := hJ.trans hpoly
    _ ≤ t ^ 3 * (400 * β) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ ((ell : ℝ) ^ 3 * omJ S ell k b) * (400 * β) := mul_le_mul_of_nonneg_right hom (by positivity)
    _ = 400 * (ell : ℝ) ^ 3 * β * omJ S ell k b := by ring

end MXQ.M2DLayer

#print axioms MXQ.M2DLayer.Jf_coveredRB
