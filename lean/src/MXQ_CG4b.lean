import MXQ_GG5
import CG4b

/-!
# MXQ_CG4b -- `cube_C12` for ONE cube's regularity body (lane mixed_20261017, round 2).  Text copy of CG4b.cube_C12.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace MXQ.CoverGeom

open AdalyFormal.CoverGeom
open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle)
open AdalyFormal.M2Glue3 (Z3 ev iota iota_shift iota_shift2)
open AdalyFormal.M2Glue2 (GChart)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.UnifLane.Z (Wof gt_iota C1 C2 gt)
open AdalyFormal.M2Bridge (pdist_lt_three_s')
open AdalyFormal.M2BallCharts (iota_mem_ball Bz plq plq_conj)

variable {L : PeriodicLatticeExtent}

/-- **class cube ⇒ ℤ³ charts (clauses 1 and 2) on any set of ball coordinates whose torus images lie in the cube.** -/
theorem cube_C12RB {ell M b : ℕ} {α₀ η : ℝ} (hη : 0 < η)
    {U : LinkCfg L} {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hReg : MXQ.AllC.RegBodyH ell M b sites i α₀ η U)
    (hsm : (b : ℝ) * M * α₀ * ((ell : ℝ) ^ i)⁻¹ + (b : ℝ) * M * α₀ * (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ 1)
    (hell : 0 < ell) (w : PeriodicLatticeSite L) (D : Set Z3) (hD : ∀ p ∈ D, iota w p ∈ sites) :
    ∃ G : Z3 → SU2, C1 (Wof U w) G D ((b : ℝ) * M * α₀ * ((ell : ℝ) ^ i)⁻¹) ∧
      C2 (Wof U w) G D ((1 + 4 * ((b : ℝ) * M * α₀ * ((ell : ℝ) ^ i)⁻¹)) * ((b : ℝ) * M * α₀ * (((ell : ℝ) ^ i)⁻¹) ^ 2)) := by
  obtain ⟨g, hg1, hg2⟩ := MXQ.M2Glue2.gchart_of_cubeRB hη hReg hsm hell
  refine ⟨fun p => g (iota w p), ?_, ?_⟩
  · intro p ν hp hpν
    rw [gt_iota]
    exact hg1 (iota w p) ν (hD p hp) (by rw [iota_shift]; exact hD _ hpν)
  · intro p μ ν hp hpν hpμ hpμν
    have e1 : ∀ q, gt (Wof U w) (fun q => g (iota w q)) q ν = periodicGaugeTransform g U (iota w q, ν) := fun q => gt_iota U w g q ν
    rw [e1, e1]
    refine hg2 (iota w p) μ ν (hD p hp) (by rw [iota_shift]; exact hD _ hpν) (by rw [iota_shift]; exact hD _ hpμ)
      (by rw [iota_shift2]; exact hD _ hpμν) |> fun h => ?_
    rw [iota_shift] at h
    exact h

end MXQ.CoverGeom

#print axioms MXQ.CoverGeom.cube_C12RB
