import CG5

/-!
# CG6a -- a `GChart` bounds plaquette holonomies at second order
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

namespace AdalyFormal.CoverGeom

open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.M2Glue2 (GChart shift_comm' frobNorm_sub_comm)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M2BallCharts (plq plq_conj)

variable {L : PeriodicLatticeExtent}

theorem plq_near_of_gchart {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {D : Set (PeriodicLatticeSite L)} {t1 t2 : ℝ}
    (h : GChart U g D t1 t2) (x : PeriodicLatticeSite L) (μ ν : Fin 3)
    (h0 : x ∈ D) (h1 : periodicLatticeShift x μ ∈ D) (h2 : periodicLatticeShift x ν ∈ D)
    (h3 : periodicLatticeShift (periodicLatticeShift x μ) ν ∈ D) :
    frobNorm (((plq U g x μ ν : SU2) : M2) - 1) ≤ 2 * t2 + 2 * t1 ^ 2 := by
  have h3' : periodicLatticeShift (periodicLatticeShift x ν) μ ∈ D := by
    rw [← AdalyFormal.M2Glue2.shift_comm']; exact h3
  have hb := h.2 x μ ν h0 h2 h1 h3
  have ha0 := h.2 x ν μ h0 h1 h2 h3'
  have hc : frobNorm (((periodicGaugeTransform g U (periodicLatticeShift x ν, μ) : SU2) : M2) - 1) ≤ t1 := h.1 _ μ h2 h3'
  have hd : frobNorm (((periodicGaugeTransform g U (x, ν) : SU2) : M2) - 1) ≤ t1 := h.1 x ν h0 h2
  have ha : frobNorm (((periodicGaugeTransform g U (x, μ) : SU2) : M2) - ((periodicGaugeTransform g U (periodicLatticeShift x ν, μ) : SU2) : M2)) ≤ t2 := by
    rw [frobNorm_sub_comm]; exact ha0
  exact hol_near_one _ _ _ _ hb ha hc hd

end AdalyFormal.CoverGeom
