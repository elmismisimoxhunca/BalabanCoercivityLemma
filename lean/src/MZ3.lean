import MZ2

/-!
# MZ3 -- the source `Jf` at printed-class `U`, bond by bond, with NO global gauge (m2_dlayer, 2026-10-15)

* `needbonds_of_curl` : the two `CurlReads` of clause 3 contain the seven bonds `J_local_bound` reads.
* **`Jf_covered`** : at a bond with `bstrat ≥ 2` whose `ddA` stencil lies in ONE class cube (index `i`), the gauge and the
  field `A` of THAT cube (the `∃ g A` inside `∀ cube` of `PerCubeRegular2`) give
  `‖Jf b‖ ≤ 400 ℓ³ β · ℓ^{-3 bstrat b}` (`β = c M α₀`), the M1 bound `Jf_strat` (m1_dstrat DS3) without a global gauge.
* **`Jf_split`** : at EVERY bond, under `ClassCoupled ℓ M 12`:
  `‖Jf b‖ ≤ 400 ℓ³ β · omJ b + [b uncovered] · 4(2β + 6β² + 1024β³) · ℓ² ℓ^{-2 strat b.1}`,
  `uncovered` = `2 ≤ bstrat b ∧ ¬ StencilCovered b.1`.  (bstrat ≤ 1: CovE crude bound; uncovered: CovH `Jf_class_strat`.)
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2DLayer

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

theorem exists_ne3 (μ : Fin 3) : ∃ ν : Fin 3, ν ≠ μ := ⟨μ + 1, by fin_cases μ <;> decide⟩

theorem needbonds_of_curl (Q : Set (PeriodicLatticeSite L)) (x : PeriodicLatticeSite L) (μ ν : Fin 3)
    (h1 : CurlReads Q (periodicLatticeShiftBack x ν) ν μ) (h2 : CurlReads Q x ν μ) :
    NeedBonds (CubeBond Q) (periodicLatticeShiftBack x ν) ν μ := by
  have e1 : periodicLatticeShift (periodicLatticeShiftBack x ν) ν = x := periodicLatticeShift_shiftBack x ν
  obtain ⟨a1, a2, a3, a4⟩ := h1
  obtain ⟨b1, b2, b3, b4⟩ := h2
  refine ⟨a4, a1, a3, a2, ?_, ?_, ?_⟩
  · rw [e1]; exact b4
  · rw [e1]; exact b1
  · rw [e1]; exact b3

/-- **the covered-stencil source bound at class `U`, with the cube's own gauge** -/
theorem Jf_covered {ell M R k c : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)}
    (hS : Admissible ell M R k S) (hRM : 4 ≤ R * M)
    (hU : PerCubeRegular2 ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hα : 0 ≤ α₀) (hsm : 4 * ((c : ℝ) * M * α₀) ≤ 1)
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (b : Bond (scaleUp ell k Lu)) (hb2 : 2 ≤ bstrat S k b)
    {Q : Set (PeriodicLatticeSite (scaleUp ell k Lu))} {i : ℕ} (hq : IsClassCube ell M c k S Q i)
    (hcr : ∀ ν : Fin 3, ν ≠ b.2 → CurlReads Q (periodicLatticeShiftBack b.1 ν) ν b.2 ∧ CurlReads Q b.1 ν b.2) :
    ‖(gparams ell k Lu hell S U a Lam).Jf b‖ ≤ (400 * (ell : ℝ) ^ 3 * ((c : ℝ) * M * α₀)) * omJ S ell k b := by
  obtain ⟨g, A, h1, h2, h3⟩ := hU Q i hq
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

/-- the uncovered set of bonds -/
def Unc {L : PeriodicLatticeExtent} (ell M k : ℕ) (S : Tower L) (b : Bond L) : Prop :=
  2 ≤ bstrat S k b ∧ ¬ StencilCovered ell M k S b.1

/-- the class source weight at an uncovered bond -/
noncomputable def omU {L : PeriodicLatticeExtent} (S : Tower L) (ell k : ℕ) (b : Bond L) : ℝ :=
  (ell : ℝ) ^ 2 * ((ell : ℝ) ^ (2 * strat S k b.1))⁻¹

open Classical in
/-- **the split source bound at every bond of a printed-class configuration** -/
theorem Jf_split {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)}
    (hS : Admissible ell M R k S) (hRM : 4 ≤ R * M)
    (hU : ClassCoupled ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hα : 0 ≤ α₀) (hsm : 4 * ((12 : ℝ) * M * α₀) ≤ 1)
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (b : Bond (scaleUp ell k Lu)) :
    ‖(gparams ell k Lu hell S U a Lam).Jf b‖
      ≤ (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀)) * omJ S ell k b
        + (if Unc ell M k S b then
            4 * (2 * ((12 : ℝ) * M * α₀) + 6 * ((12 : ℝ) * M * α₀) ^ 2 + 1024 * ((12 : ℝ) * M * α₀) ^ 3)
              * omU S ell k b else 0) := by
  have hf : ((12 : ℕ) : ℝ) = 12 := by norm_num
  set β : ℝ := (12 : ℝ) * M * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hell1 : 1 ≤ ell := hell
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have homJ : 0 ≤ omJ S ell k b := by unfold omJ; positivity
  have hsmc : 4 * (((12 : ℕ) : ℝ) * M * α₀) ≤ 1 := by rw [hf]; exact hsm
  have hfirst : 0 ≤ (400 * (ell : ℝ) ^ 3 * β) * omJ S ell k b := by positivity
  have hsec : 0 ≤ (if Unc ell M k S b then
      4 * (2 * β + 6 * β ^ 2 + 1024 * β ^ 3) * omU S ell k b else 0) := by
    split_ifs
    · unfold omU; positivity
    · exact le_rfl
  by_cases hb1 : bstrat S k b ≤ 1
  · -- crude
    have h := AdalyFormal.M2Coverage.Jf_class_bound hell hU hα hsmc a Lam b
    rw [hf] at h
    have hb4 : β ≤ 1 / 4 := by linarith
    have a2 : β ^ 2 ≤ β * (1 / 4) := by nlinarith
    have a3 : β ^ 3 ≤ β * (1 / 16) := by nlinarith [pow_le_pow_left₀ hβ0 hb4 2]
    have hcr : 4 * (4 * β + 6 * β ^ 2 + 1024 * β ^ 3) ≤ 400 * β := by nlinarith
    have hom : 1 ≤ (ell : ℝ) ^ 3 * omJ S ell k b := by
      unfold omJ
      have hp : (ell : ℝ) ^ bstrat S k b ≤ (ell : ℝ) ^ 1 := pow_le_pow_right₀ hellr hb1
      have hpos : (0 : ℝ) < (ell : ℝ) ^ bstrat S k b := by positivity
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hpos.le (hp.trans_eq (pow_one _)) 3
    have : 400 * β ≤ (400 * (ell : ℝ) ^ 3 * β) * omJ S ell k b := by nlinarith
    linarith
  push Not at hb1
  by_cases hc : StencilCovered ell M k S b.1
  · obtain ⟨Q, i, hq, hcr⟩ := hc
    have h := Jf_covered hell hS hRM hU.2 hα hsmc a Lam b hb1 hq (fun ν hν => hcr b.2 ν hν)
    rw [hf] at h
    linarith
  · have hun : Unc ell M k S b := ⟨hb1, hc⟩
    rw [if_pos hun]
    have hs2 : 2 ≤ strat S k b.1 := le_trans hb1 (min_le_left _ _)
    have hx0 : b.1 ∈ S.Om 0 := AdalyFormal.M1DStrat.mem_om0_of_strat hS (by omega)
    have hj : b.1 ∈ towerBj S (strat S k b.1) := (strat_eq_iff hS (strat_le S k b.1) b.1).2 ⟨hx0, rfl⟩
    have h := AdalyFormal.M2Coverage.Jf_class_strat hell hS hU hα hsmc a Lam b hj
    rw [hf] at h
    have e : 4 * (2 * β + 6 * β ^ 2 + 1024 * β ^ 3) * omU S ell k b
        = 4 * ((2 * β + 6 * β ^ 2 + 1024 * β ^ 3) * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ (2 * strat S k b.1))⁻¹) := by
      unfold omU; ring
    rw [e]
    linarith

#print axioms exists_ne3
#print axioms needbonds_of_curl
#print axioms Jf_covered
#print axioms Unc
#print axioms omU
#print axioms Jf_split

end AdalyFormal.M2DLayer
