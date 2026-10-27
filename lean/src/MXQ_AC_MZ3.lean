import MZ3
import MXQ_Base
import MXQ_MZ3J
import MXQ_Cov
import MXQ_AC_MZ1
import AC_MZ3

/-! AC copy of MZ3: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace MXQ.M2DLayer
open MXQ.AllC (CF CubeFamOK)
open AdalyFormal.M2DLayer

open AdalyFormal.AllC MXQ.AllC
variable {Fm : CF} [CubeFamOK Fm]

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
def UncACΦ {L : PeriodicLatticeExtent} (Fm : CF) (ell M k : ℕ) (S : Tower L) (b : Bond L) : Prop :=
  2 ≤ bstrat S k b ∧ ¬ StencilCoveredACΦ Fm ell M k S b.1

open Classical in
/-- **the split source bound at every bond of a printed-class configuration** -/
theorem Jf_splitACΦ {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)}
    (hS : Admissible ell M R k S) (hRM : 4 ≤ R * M)
    (hU : ClassCoupledHQ ell M Fm 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hα : 0 ≤ α₀) (hsm : 4 * ((12 : ℝ) * M * α₀) ≤ 1)
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (b : Bond (scaleUp ell k Lu)) :
    ‖(gparams ell k Lu hell S U a Lam).Jf b‖
      ≤ (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀)) * omJ S ell k b
        + (if UncACΦ Fm ell M k S b then
            4 * (2 * ((12 : ℝ) * M * α₀) + 6 * ((12 : ℝ) * M * α₀) ^ 2 + 1024 * ((12 : ℝ) * M * α₀) ^ 3)
              * omU S ell k b else 0) := by
  have hf : ((12 : ℕ) : ℝ) = 12 := by norm_num
  set β : ℝ := (12 : ℝ) * M * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hell1 : 1 ≤ ell := hell
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have homJ : 0 ≤ omJ S ell k b := by unfold omJ; positivity
  have hsm' : 4 * (((12 : ℕ) : ℝ) * M * α₀) ≤ 1 := by rw [hf]; exact hsm
  have hfirst : 0 ≤ (400 * (ell : ℝ) ^ 3 * β) * omJ S ell k b := by positivity
  have hsec : 0 ≤ (if UncACΦ Fm ell M k S b then
      4 * (2 * β + 6 * β ^ 2 + 1024 * β ^ 3) * omU S ell k b else 0) := by
    split_ifs
    · unfold omU; positivity
    · exact le_rfl
  by_cases hb1 : bstrat S k b ≤ 1
  · -- crude
    have h := MXQ.M2Coverage.Jf_class_boundΦ hell hU hα hsm' a Lam b
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
  by_cases hc : StencilCoveredACΦ Fm ell M k S b.1
  · obtain ⟨Q, i, hqΦ, hcr⟩ := hc
    obtain ⟨fΦ, hfΦ, hq⟩ := hqΦ
    have hfpos := CubeFamOK.pos hfΦ
    have hRegF := RegBodyH.toFactor hfpos (hU.2 fΦ Q i hfΦ hq)
    have e := bound_eq (M := M) (b := 12) hfpos α₀
    have hα'' : 0 ≤ ((12 : ℕ) : ℝ) * α₀ / fΦ := by positivity
    have hsmc : 4 * ((fΦ : ℝ) * M * (((12 : ℕ) : ℝ) * α₀ / fΦ)) ≤ 1 := by rw [e, hf]; exact hsm
    have h := MXQ.M2DLayer.Jf_coveredRB hell hS hRM hα'' hsmc a Lam b hb1 hq hRegF (fun ν hν => hcr b.2 ν hν)
    rw [e, hf] at h
    linarith
  · have hun : UncACΦ Fm ell M k S b := ⟨hb1, hc⟩
    rw [if_pos hun]
    have hs2 : 2 ≤ strat S k b.1 := le_trans hb1 (min_le_left _ _)
    have hx0 : b.1 ∈ S.Om 0 := AdalyFormal.M1DStrat.mem_om0_of_strat hS (by omega)
    have hj : b.1 ∈ towerBj S (strat S k b.1) := (strat_eq_iff hS (strat_le S k b.1) b.1).2 ⟨hx0, rfl⟩
    have h := MXQ.M2Coverage.Jf_class_stratΦ hell hS hU hα hsm' a Lam b hj
    rw [hf] at h
    have e : 4 * (2 * β + 6 * β ^ 2 + 1024 * β ^ 3) * omU S ell k b
        = 4 * ((2 * β + 6 * β ^ 2 + 1024 * β ^ 3) * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ (2 * strat S k b.1))⁻¹) := by
      unfold omU; ring
    rw [e]
    linarith

end MXQ.M2DLayer

