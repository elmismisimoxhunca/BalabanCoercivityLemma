import MXQ_Base

/-!
# MXQ_GG5 -- `gchart_of_cube` at the level of ONE cube's regularity body (`RegBodyH`), no hypothesis on the other cubes (lane mixed_20261017, round 2).  Text copy of GG5.gchart_of_cube.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace MXQ.M2Glue2

open AdalyFormal.M2Glue2
open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq frobSq_nonneg)
open AdalyFormal.Balaban.Bch2 (IsSu2 frobNorm_add_le frobNorm_nonneg frobNorm_smul)
open scoped Matrix

variable {L : PeriodicLatticeExtent}

/-- **class cube ⇒ group-level chart.** -/
theorem gchart_of_cubeRB {ell M b : ℕ} {α₀ η : ℝ} (hη : 0 < η)
    {U : LinkCfg L} {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hReg : MXQ.AllC.RegBodyH ell M b sites j α₀ η U)
    (hsm : (b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹ + (b : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹) ^ 2 ≤ 1)
    (hell : 0 < ell) :
    ∃ g : PeriodicLatticeSite L → SU2, GChart U g sites ((b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹)
      ((1 + 4 * ((b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹)) * ((b : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹) ^ 2)) := by
  obtain ⟨g, A, hA, hD, -⟩ := hReg
  refine ⟨g, ?_, ?_⟩
  · intro x ν hx hxν
    obtain ⟨hHT, hU, hb⟩ := hA (x, ν) ⟨hx, hxν⟩
    rw [gauge_eq_su2Exp hHT hU]
    refine (exp_sub_one_le (isSu2_chZ η hHT)).trans ?_
    rw [frobNorm_chZ hη.le]
    have hl : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
    have := mul_lt_mul_of_pos_left hb hη
    rw [pow_one, mul_inv, show η * ((b : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹ * η⁻¹))
      = (b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹ * (η * η⁻¹) by ring, mul_inv_cancel₀ hη.ne', mul_one] at this
    exact this.le
  · intro x μ ν hx hxν hxμ hxμν
    obtain ⟨hHT0, hU0, hb0⟩ := hA (x, ν) ⟨hx, hxν⟩
    obtain ⟨hHT1, hU1, hb1⟩ := hA (periodicLatticeShift x μ, ν) ⟨hxμ, hxμν⟩
    have hd := hD μ ν x ⟨hx, hxν⟩ ⟨hxμ, hxμν⟩
    rw [gauge_eq_su2Exp hHT0 hU0, gauge_eq_su2Exp hHT1 hU1]
    set c1 : ℝ := (b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹ with hc1
    set c2 : ℝ := (b : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹) ^ 2 with hc2
    have hl : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
    have hZ0 : frobNorm (chZ η (A (x, ν))) ≤ c1 := by
      rw [frobNorm_chZ hη.le]
      have := mul_lt_mul_of_pos_left hb0 hη
      rw [pow_one, mul_inv, show η * ((b : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹ * η⁻¹))
        = (b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹ * (η * η⁻¹) by ring, mul_inv_cancel₀ hη.ne', mul_one] at this
      exact this.le
    have hZd : frobNorm (chZ η (A (periodicLatticeShift x μ, ν)) - chZ η (A (x, ν))) ≤ c2 := by
      rw [chZ_sub, frobNorm_chZ hη.le]
      rw [frobNorm_smul, abs_of_pos (inv_pos.mpr hη)] at hd
      have := mul_lt_mul_of_pos_left hd (mul_pos hη hη)
      have e : η * η * (η⁻¹ * frobNorm (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          = η * frobNorm (A (periodicLatticeShift x μ, ν) - A (x, ν)) := by field_simp
      rw [e, mul_inv, show η * η * ((b : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹ * η⁻¹) ^ 2)
        = (b : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹) ^ 2 * ((η * η⁻¹) ^ 2) by ring, mul_inv_cancel₀ hη.ne',
        one_pow, mul_one] at this
      exact this.le
    have hsm' : frobNorm (chZ η (A (x, ν))) + frobNorm (chZ η (A (periodicLatticeShift x μ, ν)) - chZ η (A (x, ν)))
        ≤ 1 := by linarith
    refine (exp_lip (isSu2_chZ η hHT0) (isSu2_chZ η hHT1) hsm').trans ?_
    have := frobNorm_nonneg (chZ η (A (periodicLatticeShift x μ, ν)) - chZ η (A (x, ν)))
    have : 0 ≤ 1 + 4 * frobNorm (chZ η (A (x, ν))) := by have := frobNorm_nonneg (chZ η (A (x, ν))); linarith
    calc (1 + 4 * frobNorm (chZ η (A (x, ν)))) * frobNorm (chZ η (A (periodicLatticeShift x μ, ν)) - chZ η (A (x, ν)))
        ≤ (1 + 4 * c1) * c2 :=
          mul_le_mul (by linarith) hZd (frobNorm_nonneg _)
            (by have := frobNorm_nonneg (chZ η (A (x, ν))); linarith)
      _ = _ := rfl

end MXQ.M2Glue2

namespace MXQ.AllC
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLane

/-- `gchart_of_cube` for a cube of the family (hybrid bound factor `b`). -/
theorem gchart_of_cubeHΦ {L : PeriodicLatticeExtent} {ell M b k : ℕ} {Fm : CF} {S : Tower L} {α₀ η : ℝ} (hη : 0 < η)
    {U : LinkCfg L} (hP : PerCubeRegular2HQ ell M Fm b k S α₀ η U)
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hq : IsClassCubeQ ell M Fm k S sites j)
    (hsm : (b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹ + (b : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹) ^ 2 ≤ 1)
    (hell : 0 < ell) :
    ∃ g : PeriodicLatticeSite L → AdalyFormal.Balaban.SuTwoLogExp.SU2,
      AdalyFormal.M2Glue2.GChart U g sites ((b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹)
        ((1 + 4 * ((b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹)) * ((b : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹) ^ 2)) := by
  obtain ⟨f, hm, hq⟩ := hq
  exact MXQ.M2Glue2.gchart_of_cubeRB hη (hP f sites j hm hq) hsm hell

end MXQ.AllC

#print axioms MXQ.M2Glue2.gchart_of_cubeRB
#print axioms MXQ.AllC.gchart_of_cubeHΦ
