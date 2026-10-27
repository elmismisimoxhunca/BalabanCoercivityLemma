import Admission
import CovariantDiagnostic
set_option autoImplicit false
noncomputable section
namespace HConstruction.SmallNF
open HConstruction.NfRepair HConstruction.NfRepair.Reproduced
open HConstruction.Carrier HConstruction.Covariance HConstruction.Nonflat
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL witnessY)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.RegularityHolonomy
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)

/-- The two proposed choices are literally the same background at this parameter. -/
def chosenU : PeriodicLinkConfiguration SU2 witnessL := nonflatU (1/16)
theorem chosen_eq_smallCurved : chosenU = smallCurvedU := rfl
theorem chosen_curved : holonomyElem chosenU witnessPlaquette ≠ (1 : SU2) :=
  smallCurvedU_curved
theorem chosen_regular : IsRegularHolonomy chosenU (8/257 : ℝ) := smallCurvedU_regular
theorem chosen_small : PlaquetteBound chosenU (1/5 : ℝ) ∧
    (0 : ℝ) < 1/5 ∧ (1/5 : ℝ) ≤ 2 ∧
    HConstruction.Nonflat.Reproduced.loopRhoPlaqCap (1/5 : ℝ) 2 < Real.pi / 2 ∧
    HConstruction.Nonflat.Reproduced.loopRhoPlaq (1/5 : ℝ) 2 < Real.pi / 2 :=
  smallCurvedU_radius_admission

theorem chosen_exact_defect : holonomyDefectSq chosenU witnessPlaquette = (8/257 : ℝ) := by
  rw [holonomyDefectSq_eq_defectOfElem, chosenU, holonomyElem_nonflatU_witnessPlaquette,
    defectOfElem_rotElem]
  norm_num

theorem chosen_rotation_entry :
    ((RMap (rotElem (1/16)) suTwoWitness : M2) 0 1).im = -(16320/66049 : ℝ) := by
  rw [RMap_coe_apply, rotElem_coe, rotM_conjTranspose]
  norm_num [rotM, rotA, rotB, suTwoWitness, suTwoWitnessVal,
    Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem chosen_rotation_moves : RMap (rotElem (1/16)) suTwoWitness ≠ suTwoWitness := by
  intro h
  have hh := congrArg (fun X : SuTwo => ((X : M2) 0 1).im) h
  rw [chosen_rotation_entry] at hh
  norm_num [suTwoWitness, suTwoWitnessVal] at hh

theorem chosen_covCurl_constant_nonzero : covCurl chosenU constantField ≠ 0 := by
  intro h
  have hp := congrArg (fun A : F => fiberEquiv _ A witnessPlaquette) h
  have hz : curlValueCovariant chosenU (fun _ => suTwoWitness) witnessPlaquette = 0 := by
    simp only [covCurl, smul_apply, map_smul, Pi.smul_apply, map_zero, Pi.zero_apply] at hp
    change (2 : ℝ) • curlValueCovariant chosenU (fun _ => suTwoWitness) witnessPlaquette = 0 at hp
    exact (smul_eq_zero.mp hp).resolve_left (by norm_num)
  change suTwoWitness + RMap (chosenU (witnessY,0)) suTwoWitness -
    RMap (chosenU (witnessY,1)) suTwoWitness - suTwoWitness = 0 at hz
  have hn : (witnessY,(1 : Fin 3)) ≠ (witnessY,0) := by decide
  rw [chosenU,nonflatU_at_x_mu,nonflatU_elsewhere _ hn,RMap_one] at hz
  simp only [LinearMap.id_coe,id_eq] at hz
  apply chosen_rotation_moves
  have he : suTwoWitness + RMap (rotElem (1/16)) suTwoWitness - suTwoWitness -
      suTwoWitness = RMap (rotElem (1/16)) suTwoWitness - suTwoWitness := by abel
  rw [he] at hz
  exact sub_eq_zero.mp hz

theorem chosen_covCurl_not_flat : covCurl chosenU ≠ flatCurl := by
  intro h
  exact chosen_covCurl_constant_nonzero (by rw [h,flatCurl_constant])

theorem chosen_curlSquare_not_flat : curlSquare chosenU ≠ flatDelta := by
  intro h
  have hp : (0 : ℝ) < inner ℝ constantField (curlSquare chosenU constantField) := by
    rw [curlSquare_energy]
    exact pow_pos (norm_pos_iff.mpr chosen_covCurl_constant_nonzero) 2
  rw [h,flatDelta_constant,inner_zero_right] at hp
  exact (lt_irrefl 0) hp
end HConstruction.SmallNF
