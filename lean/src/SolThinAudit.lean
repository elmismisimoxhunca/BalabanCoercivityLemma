import THL3
import THL6
import THL7
import THL8
import Lean
#print axioms AdalyFormal.ThinLayer.admSplit_of_admissible
#print axioms AdalyFormal.ThinLayer.admissible_of_admSplit
#print axioms AdalyFormal.ThinLayer.admSplit_iff_admissible
#print axioms AdalyFormal.ThinLayer.lambdaOK_mono
#print axioms AdalyFormal.ThinLayer.lambdaOK2_mono
#print axioms AdalyFormal.ThinLayer.famTorusThin_of
#print axioms AdalyFormal.ThinLayer.famTorus_of_thin
#print axioms AdalyFormal.ThinLayer.famTorusThin_iff
#print axioms AdalyFormal.ThinLayer.famTorusThinU
#print axioms AdalyFormal.ThinLayer.famTorusThinBox
#print axioms AdalyFormal.ThinLayer.famTorusCapThin_of
#print axioms AdalyFormal.ThinLayer.famTorusCapThin_unconditional
#print axioms AdalyFormal.ThinLayer.totalThin_of
#print axioms AdalyFormal.ThinLayer.totalThin_unconditional
#print axioms AdalyFormal.ThinLayer.mixedThin_of
#print axioms AdalyFormal.ThinLayer.mixedThin_unconditional
#print axioms AdalyFormal.ThinLayer.asym_om0
#print axioms AdalyFormal.ThinLayer.asym_om1
#print axioms AdalyFormal.ThinLayer.asym_om2
#print axioms AdalyFormal.ThinLayer.pdist_ge0
#print axioms AdalyFormal.ThinLayer.xlt
#print axioms AdalyFormal.ThinLayer.asym_adm5
#print axioms AdalyFormal.ThinLayer.asym_not_baseLaw
#print axioms AdalyFormal.ThinLayer.asym_not_admissible
#print axioms AdalyFormal.ThinLayer.asym_not_admSplit
#print axioms AdalyFormal.ThinLayer.asym_thin_not_radial
#print axioms AdalyFormal.NonVacC.lambdaOK2_congr
#print axioms AdalyFormal.NonVacC.thin_nonvac_core
#print axioms AdalyFormal.NonVacC.thin_headline_regime_nonvacuous
#print axioms AdalyFormal.NonVacC.thin_instance_inequality
#print axioms AdalyFormal.ThinLayer.admT_iff
#print axioms AdalyFormal.ThinLayer.admNoBase_of_splitNB
#print axioms AdalyFormal.ThinLayer.admT_of_splitNB
#print axioms AdalyFormal.ThinLayer.admSplitNB_of_admSplit
#print axioms AdalyFormal.ThinLayer.famTorusLayer_union
#print axioms AdalyFormal.ThinLayer.famTorusLayer_box
#print axioms AdalyFormal.ThinLayer.famTorusLayerCap
#print axioms AdalyFormal.ThinLayer.totalLayer
#print axioms AdalyFormal.ThinLayer.mixedLayer
#print axioms AdalyFormal.ThinLayer.target8Layer
#print axioms AdalyFormal.ThinLayer.famTorusThin_of_layer
#print axioms AdalyFormal.ThinLayer.famTorusThinU'
#print axioms AdalyFormal.ThinLayer.totalThin_of_layer
#print axioms AdalyFormal.ThinLayer.asym_layer_class
#print axioms AdalyFormal.ThinLayer.shift_val'
#print axioms AdalyFormal.ThinLayer.pcd_step_le1
#print axioms AdalyFormal.ThinLayer.pcd_step_le1'
#print axioms AdalyFormal.ThinLayer.pdist_shift_le1
#print axioms AdalyFormal.ThinLayer.pdist_shift_le1'
#print axioms AdalyFormal.ThinLayer.bond_endpoints_in_Om_k
#print axioms AdalyFormal.ThinLayer.competitor_support_in_Om0
#print axioms AdalyFormal.NonVacC.slab3_nest_W
#print axioms AdalyFormal.NonVacC.cube_nbhdW
#print axioms AdalyFormal.NonVacC.slab3_coverspW
#print axioms AdalyFormal.NonVacC.pdist_siteAt0
#print axioms AdalyFormal.NonVacC.pdist_ge0'
#print axioms AdalyFormal.NonVacC.pdist_ge0N
#print axioms AdalyFormal.NonVacC.asym_admSplitNB_slab
#print axioms AdalyFormal.NonVacC.asym_not_admSplit_slab
#print axioms AdalyFormal.NonVacC.asym_nonvac_core
#print axioms AdalyFormal.NonVacC.asym_headline_regime_nonvacuous
#print axioms AdalyFormal.NonVacC.asym_instance_inequality
#print axioms AdalyFormal.Thin.admissible_lift_T
#print axioms AdalyFormal.L0C.path_exists_T

open AdalyFormal.ThinLayer AdalyFormal.StatementLane AdalyFormal.StatementLaneG in
/-- Retain every frozen hypothesis/conclusion except that the new theorem drops T6. -/
theorem Sol_frozen_target_of_layer (h : Target8Layer) : P428Target8 := by
  intro ell hell a ha
  obtain ⟨m0, hm0, H⟩ := h ell hell a ha
  refine ⟨m0, hm0, fun m hm => ?_⟩
  obtain ⟨r0, H⟩ := H m hm
  refine ⟨r0, fun r hr => ?_⟩
  obtain ⟨hp, a0, ha0, g0, hg0, H⟩ := H r hr
  refine ⟨hp, a0, ha0, g0, hg0, fun k hk Lu al hal hsmall htor S hadm Lam hlam U hclass => ?_⟩
  obtain ⟨h1,h2,h3,h4,h5,_⟩ := hadm
  exact H k hk Lu al hal hsmall htor S ⟨h1,h2,h3,h4,h5⟩ Lam hlam U hclass
#print axioms Sol_frozen_target_of_layer

open Lean Elab Command
run_cmd do
  let e ← liftTermElabM <| Term.elabTerm (← `(∀ x : AdalyFormal.Target.ClayStatement.PeriodicLatticeSite (fun _ => 1),
    AdalyFormal.StatementLane.pdist x x = 0 ↔ AdalyFormal.StatementLane.pdist x x = 1)) none
  if !(ThinReplay.t6repl e).isSome then throwError "matcher surface control did not fire"
  logInfo "MATCHER CONTROL: unrelated pdist iff also matches; public statement boundary must be checked"
