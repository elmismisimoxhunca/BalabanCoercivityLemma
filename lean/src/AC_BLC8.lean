import BLC8
import AC_BLC7
import AC_Base

/-! AC copy of BLC8: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2BallCharts

open AdalyFormal.AllC
variable {fc : ℕ} [CubeFactor fc]

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2 AdalyFormal.M2GlueGeo
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

/-- **the ball chart at `j = 0`**. -/
theorem ball_chart_zeroAC {ell M R k : ℕ} {S : Tower L} (hcov : CoversOm0p ell M fc k S) (hell : 0 < ell)
    {w : PeriodicLatticeSite L} {r : ℕ} (hr7 : r ≤ 7 * M) (hnw : ∀ σ : Fin 3, 2 * r + 2 ≤ L σ + 1)
    (hin : ∀ x ∈ Ball w r, x ∈ S.Om 0)
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2H ell M fc 12 k S α₀ η U)
    (hX : (12 : ℝ) * M * α₀ ≤ 1 / 2) :
    ∃ g : PeriodicLatticeSite L → SU2, GChart U g (Ball w r)
      (56 * M * ((12 : ℝ) * M * α₀)) (56 * M * ((12 : ℝ) * M * α₀)) := by
  have hL : ∀ μ, 2 * r + 1 < L μ + 1 := fun μ => by have := hnw μ; omega
  set X : ℝ := (12 : ℝ) * M * α₀ with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hPB : ∀ b : Z3, ∀ μ ν : Fin 3, μ < ν → b ∈ Bz r → b + ev μ ∈ Bz r → b + ev ν ∈ Bz r → b + ev μ + ev ν ∈ Bz r →
      frobNorm (((plq U (axg U w r) (iota w b) μ ν : SU2) : M2) - 1) ≤ 4 * X := by
    intro b μ ν hμν h0 h1 h2 h3
    have hc : periodicLatticeShift (periodicLatticeShift (iota w b) μ) ν
        = periodicLatticeShift (periodicLatticeShift (iota w b) ν) μ := by
      rw [iota_shift2, iota_shift2, add_right_comm]
    exact plq_classAC (R := R) hcov hell hη hα hP hX hμν (hin _ (iota_mem_ball h0))
      (by rw [iota_shift]; exact hin _ (iota_mem_ball h1)) (by rw [iota_shift]; exact hin _ (iota_mem_ball h2))
      (by rw [iota_shift2]; exact hin _ (iota_mem_ball h3)) hc _
  have hb := axial_bound (U := U) (w := w) hL (by positivity) hPB
  have hz : ZCh U (axg U w r) w (Bz r) (fun _ => r * (4 * X)) (fun _ => 2 * (r * (4 * X))) := by
    refine ⟨fun p ν hp hpν => hb p ν hp hpν, fun p μ ν h0 h1 h2 h3 => ?_⟩
    have a := hb (p + ev μ) ν h2 h3
    have b := hb p ν h0 h1
    have t := frobNorm_sub_le' ((periodicGaugeTransform (axg U w r) U (iota w (p + ev μ), ν) : SU2) : M2) 1
      ((periodicGaugeTransform (axg U w r) U (iota w p, ν) : SU2) : M2)
    rw [frobNorm_sub_comm 1] at t
    show _ ≤ 2 * (r * (4 * X)); linarith
  have hGs := gchart_sub_of_zch (v := w) hL (S := Bz r) Bz_sub_box (P := fun _ => True) (T := Bz r)
    (fun p hp _ => hp) hz
  refine ⟨axg U w r, hGs.mono (fun x hx => ⟨ball_sub_liftL1 w r hx, trivial⟩) ?_ ?_⟩
  · have : (r : ℝ) ≤ 7 * M := by exact_mod_cast hr7
    nlinarith
  · have : (r : ℝ) ≤ 7 * M := by exact_mod_cast hr7
    nlinarith

end AdalyFormal.M2BallCharts

