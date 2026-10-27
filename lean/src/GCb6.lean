import GCb5

/-!
# GCb6 -- the source `J` of (3.11) (localised, `JSU2Loc`) and the bond-level `Δ`, `Δ_π` equivariant under `Ad_γ`
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply RMap_one conjByAmbient)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply gaugeInv)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SourceJ
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.IngredientFamily
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

theorem piProj_cjM (g : SU2g) (X : Mat2) : piProj (cjM g X) = cjM g (piProj X) := by
  unfold piProj
  rw [trace_cjM, cjM_sub, cjM_smul, cjM_one]

theorem cjM_zero (g : SU2g) : cjM g 0 = 0 := by
  unfold cjM; simp

theorem cjM_mulgrp (g h : SU2g) (X : Mat2) : cjM (g * h) X = cjM g (cjM h X) := by
  unfold cjM
  rw [Submonoid.coe_mul, Matrix.conjTranspose_mul]
  noncomm_ring

theorem cjM_one_id (X : Mat2) : cjM (1 : SU2g) X = X := by
  unfold cjM
  simp

theorem cjM_inv_cancel (g : SU2g) (X : Mat2) : cjM g⁻¹ (cjM g X) = X := by
  rw [← cjM_mulgrp, inv_mul_cancel, cjM_one_id]

theorem FnuMuLoc_gauge (γ : GaugeFn L) (P : Set (PeriodicLatticePlaquette L)) (U : Cfg L)
    (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    FnuMuLoc P (periodicGaugeTransform γ U) ν μ y = cjM (γ y) (FnuMuLoc P U ν μ y) := by
  unfold FnuMuLoc
  split_ifs <;>
    first
    | (rw [imHol_gauge, piProj_cjM, cjM_neg])
    | (rw [imHol_gauge, piProj_cjM])
    | exact (cjM_zero _).symm

/-- `D*_ν` of a plaquette-matrix field is covariant: output frame `γ x`. -/
theorem DstarDir_gauge (γ : GaugeFn L) (U : Cfg L) (ν : Fin 3)
    (F : PeriodicLatticeSite L → Mat2) (x : PeriodicLatticeSite L) :
    DstarDir (periodicGaugeTransform γ U) ν (fun y => cjM (γ y) (F y)) x = cjM (γ x) (DstarDir U ν F x) := by
  unfold DstarDir
  have h1 : (periodicGaugeTransform γ U (periodicLatticeShiftBack x ν, ν))⁻¹
      = γ x * (U (periodicLatticeShiftBack x ν, ν))⁻¹ * (γ (periodicLatticeShiftBack x ν))⁻¹ := by
    show (γ (periodicLatticeShiftBack x ν) * U (periodicLatticeShiftBack x ν, ν)
        * (γ (periodicLatticeShift (periodicLatticeShiftBack x ν) ν))⁻¹)⁻¹ = _
    rw [periodicLatticeShift_shiftBack]
    group
  rw [h1]
  show cjM (γ x * (U (periodicLatticeShiftBack x ν, ν))⁻¹ * (γ (periodicLatticeShiftBack x ν))⁻¹)
      (cjM (γ (periodicLatticeShiftBack x ν)) (F (periodicLatticeShiftBack x ν))) - cjM (γ x) (F x)
    = cjM (γ x) (cjM (U (periodicLatticeShiftBack x ν, ν))⁻¹ (F (periodicLatticeShiftBack x ν)) - F x)
  rw [cjM_sub, cjM_mulgrp, cjM_mulgrp, cjM_inv_cancel]

end AdalyFormal.GaugeCov
