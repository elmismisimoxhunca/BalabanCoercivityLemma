import MZ3
import AC_MZ1
import AC_Base

/-! AC copy of MZ3: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2DLayer

open AdalyFormal.AllC
variable {fc : ℕ} [CubeFactor fc]

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

/-- the uncovered set of bonds -/
def UncAC {L : PeriodicLatticeExtent} (fc ell M k : ℕ) (S : Tower L) (b : Bond L) : Prop :=
  2 ≤ bstrat S k b ∧ ¬ StencilCoveredAC fc ell M k S b.1

open Classical in
/-- **the split source bound at every bond of a printed-class configuration** -/
theorem Jf_splitAC {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)}
    (hS : Admissible ell M R k S) (hRM : 4 ≤ R * M)
    (hU : ClassCoupledH ell M fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hα : 0 ≤ α₀) (hsm : 4 * ((12 : ℝ) * M * α₀) ≤ 1)
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (b : Bond (scaleUp ell k Lu)) :
    ‖(gparams ell k Lu hell S U a Lam).Jf b‖
      ≤ (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀)) * omJ S ell k b
        + (if UncAC fc ell M k S b then
            4 * (2 * ((12 : ℝ) * M * α₀) + 6 * ((12 : ℝ) * M * α₀) ^ 2 + 1024 * ((12 : ℝ) * M * α₀) ^ 3)
              * omU S ell k b else 0) := by
  have hf : ((12 : ℕ) : ℝ) = 12 := by norm_num
  set β : ℝ := (12 : ℝ) * M * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hell1 : 1 ≤ ell := hell
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have homJ : 0 ≤ omJ S ell k b := by unfold omJ; positivity
  have hfc := CubeFactor.pos (fc := fc)
  have hU' := ClassCoupledH.toOrig hfc hU
  have e := bound_eq (M := M) (b := 12) hfc α₀
  have hα'' : 0 ≤ ((12 : ℕ) : ℝ) * α₀ / fc := by positivity
  have hsmc : 4 * ((fc : ℝ) * M * (((12 : ℕ) : ℝ) * α₀ / fc)) ≤ 1 := by rw [e, hf]; exact hsm
  have hfirst : 0 ≤ (400 * (ell : ℝ) ^ 3 * β) * omJ S ell k b := by positivity
  have hsec : 0 ≤ (if UncAC fc ell M k S b then
      4 * (2 * β + 6 * β ^ 2 + 1024 * β ^ 3) * omU S ell k b else 0) := by
    split_ifs
    · unfold omU; positivity
    · exact le_rfl
  by_cases hb1 : bstrat S k b ≤ 1
  · -- crude
    have h := AdalyFormal.M2Coverage.Jf_class_bound hell hU' hα'' hsmc a Lam b
    rw [e, hf] at h
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
  by_cases hc : StencilCoveredAC fc ell M k S b.1
  · obtain ⟨Q, i, hq, hcr⟩ := hc
    have h := Jf_covered hell hS hRM hU'.2 hα'' hsmc a Lam b hb1 hq (fun ν hν => hcr b.2 ν hν)
    rw [e, hf] at h
    linarith
  · have hun : UncAC fc ell M k S b := ⟨hb1, hc⟩
    rw [if_pos hun]
    have hs2 : 2 ≤ strat S k b.1 := le_trans hb1 (min_le_left _ _)
    have hx0 : b.1 ∈ S.Om 0 := AdalyFormal.M1DStrat.mem_om0_of_strat hS (by omega)
    have hj : b.1 ∈ towerBj S (strat S k b.1) := (strat_eq_iff hS (strat_le S k b.1) b.1).2 ⟨hx0, rfl⟩
    have h := AdalyFormal.M2Coverage.Jf_class_strat hell hS hU' hα'' hsmc a Lam b hj
    rw [e, hf] at h
    have e : 4 * (2 * β + 6 * β ^ 2 + 1024 * β ^ 3) * omU S ell k b
        = 4 * ((2 * β + 6 * β ^ 2 + 1024 * β ^ 3) * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ (2 * strat S k b.1))⁻¹) := by
      unfold omU; ring
    rw [e]
    linarith

end AdalyFormal.M2DLayer

