import SmallParameter
import SourceCompression

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
noncomputable section
namespace HConstruction.TransversePos.Schur
open HConstruction.Covariance HConstruction.SmallNF HConstruction.G0Close
open HConstruction.TransversePos

def workingPrecision : H →L[ℝ] H := precisionU workingU 1

/-- Self-adjointness of the actual source precision, including correctionBil, at the proved small parameter. -/
theorem workingPrecision_selfAdjoint (x y : H) :
    (inner ℝ (workingPrecision x) y : ℝ) = inner ℝ x (workingPrecision y) := by
  rw [workingPrecision, precisionU, ← gaugeU_identity]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right,
    deltaU_selfAdjoint, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

/-- The actual update, not a numerical or rational surrogate. -/
def sourceUpdate : H →L[ℝ] H := workingPrecision - flatBaseline

theorem sourceUpdate_selfAdjoint (x y : H) :
    (inner ℝ (sourceUpdate x) y : ℝ) = inner ℝ x (sourceUpdate y) := by
  simp only [sourceUpdate, sub_apply, inner_sub_left, inner_sub_right,
    workingPrecision_selfAdjoint, flatBaseline_selfAdjoint]

/-- Intrinsic compression space. This definition supplies no claimed rank-33 bound:
sparse source identities are still required for a small explicit certificate. -/
def updateSpace : Submodule ℝ H := LinearMap.range sourceUpdate.toLinearMap

def chosenV : updateSpace →L[ℝ] H := updateSpace.subtypeL

theorem chosenV_injective : Function.Injective chosenV := Subtype.val_injective

def chosenJ : updateSpace →L[ℝ] updateSpace :=
  chosenV.adjoint.comp (sourceUpdate.comp chosenV)

theorem updateSpace_projection_update (x : H) :
    updateSpace.starProjection (sourceUpdate x) = sourceUpdate x :=
  Submodule.starProjection_eq_self_iff.mpr ⟨x, rfl⟩

theorem sourceUpdate_projection (x : H) :
    sourceUpdate (updateSpace.starProjection x) = sourceUpdate x := by
  apply ext_inner_right ℝ
  intro y
  rw [sourceUpdate_selfAdjoint, sourceUpdate_selfAdjoint,
    Submodule.inner_starProjection_left_eq_right, updateSpace_projection_update]

-- Keep the source formula opaque during typeclass and definitional-equality search.
-- Rewriting named identities below never needs to unfold the 576-dimensional source.
attribute [local irreducible] sourceUpdate updateSpace

/-- Unconditional source decomposition: the range projection is proved to fix the
update on both sides, using its self-adjointness, not guessed from locality. -/
theorem sourceUpdate_compressed : sourceUpdate = chosenV.comp (chosenJ.comp chosenV.adjoint) := by
  ext x
  simp only [chosenJ, chosenV, Submodule.adjoint_subtypeL,
    ContinuousLinearMap.comp_apply]
  change sourceUpdate x = updateSpace.starProjection
    (sourceUpdate (updateSpace.starProjection x))
  rw [sourceUpdate_projection, updateSpace_projection_update]

theorem chosen_source_decomposition :
    workingPrecision = flatBaseline + chosenV.comp (chosenJ.comp chosenV.adjoint) := by
  rw [← sourceUpdate_compressed, sourceUpdate]
  exact ((add_comm flatBaseline (workingPrecision - flatBaseline)).trans
    (sub_add_cancel workingPrecision flatBaseline)).symm

def chosenC : updateSpace →L[ℝ] updateSpace := flatSchurC chosenV chosenV_injective

def chosenLift : updateSpace →L[ℝ] H := flatLift chosenV chosenV_injective

theorem chosen_VK (z : updateSpace) : chosenV.adjoint (chosenLift z) = z :=
  flatLift_VK chosenV chosenV_injective z

theorem chosen_AK (z : updateSpace) : flatBaseline (chosenLift z) = chosenV (chosenC z) :=
  flatLift_AK chosenV chosenV_injective z

/-- Source gate, specialized to workingU. The following theorem discharges its premise. -/
theorem chosen_G0_of_source_schur
    (hschur : ∀ z : updateSpace, z ≠ 0 → (0 : ℝ) < inner ℝ z ((chosenC + chosenJ) z)) :
    HasPhysicalG0 workingU 1 := by
  have hp := HConstruction.G0Final.strict_of_compressed_schur flatBaseline chosenV chosenLift chosenC chosenJ
    flatBaseline_selfAdjoint chosen_VK chosen_AK flatBaseline_positive hschur
  rw [← chosen_source_decomposition] at hp
  obtain ⟨G,hr,hl,_⟩ := HConstruction.DRepair.positive_inverse workingPrecision hp
  exact ⟨G,hr,hl⟩

/-- The source Schur equivalence at workingU; discharged below. -/
theorem source_schur_iff :
    (∀ z : updateSpace, z ≠ 0 → (0 : ℝ) < inner ℝ z ((chosenC + chosenJ) z)) ↔
    (∀ x : H, x ≠ 0 → (0 : ℝ) < inner ℝ x (workingPrecision x)) := by
  constructor
  · intro hs
    have hp := HConstruction.G0Final.strict_of_compressed_schur
      flatBaseline chosenV chosenLift chosenC chosenJ flatBaseline_selfAdjoint
      chosen_VK chosen_AK flatBaseline_positive hs
    rwa [← chosen_source_decomposition] at hp
  · intro hp z hz
    have hk : chosenLift z ≠ 0 := by
      intro hk
      have hv := chosen_VK z
      rw [hk, map_zero] at hv
      exact hz hv.symm
    have h := hp (chosenLift z) hk
    rw [chosen_source_decomposition,
      HConstruction.G0Final.compressed_schur_energy flatBaseline chosenV chosenLift chosenC chosenJ
        flatBaseline_selfAdjoint chosen_VK chosen_AK, chosen_VK] at h
    simpa only [sub_self, map_zero, inner_zero_left, zero_add] using h

/-- Both sides of the Schur gate are discharged, for the explicitly changed background. -/
theorem working_source_schur_positive : ∀ z : updateSpace, z ≠ 0 →
    (0 : ℝ) < inner ℝ z ((chosenC + chosenJ) z) := by
  apply source_schur_iff.mpr
  unfold workingPrecision workingU
  exact precision_small_positive workingThreshold (by rw [abs_of_pos workingThreshold_pos])

theorem workingG0_via_source_schur : HasPhysicalG0 workingU 1 :=
  chosen_G0_of_source_schur working_source_schur_positive

#print axioms working_source_schur_positive
#print axioms workingG0_via_source_schur
#print axioms workingPrecision_selfAdjoint
#print axioms sourceUpdate_selfAdjoint
#print axioms chosen_source_decomposition
#print axioms chosen_VK
#print axioms chosen_AK
#print axioms chosen_G0_of_source_schur
#print axioms source_schur_iff
end HConstruction.TransversePos.Schur
