import GaugeNorm
import SourceCoordinates
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance 20000] AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo
  AdalyFormal.Balaban.SuTwoInner.instInnerProductSpaceSuTwo
namespace HConstruction.TransversePos
open HConstruction.Circle HConstruction.Covariance HConstruction.SmallNF HConstruction.Nonflat
open HConstruction.NfRepair.Reproduced HConstruction.G0Final.Locality HConstruction.G0HSchur
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL witnessY Bond)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_inv)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)

local instance : SeminormedAddCommGroup SuTwo := instNormedAddCommGroupSuTwo.toSeminormedAddCommGroup
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

local instance {ι : Type} [Fintype ι] : NormedAddCommGroup (ι → SuTwo) :=
  @Pi.normedAddCommGroup _ (fun _ : ι => SuTwo) inferInstance
    (fun _ => AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo)
local instance {ι : Type} [Fintype ι] : SeminormedAddCommGroup (ι → SuTwo) :=
  (inferInstance : NormedAddCommGroup (ι → SuTwo)).toSeminormedAddCommGroup
local instance {ι : Type} [Fintype ι] : NormedSpace ℝ (ι → SuTwo) :=
  @Pi.normedSpace ℝ _ _ (fun _ : ι => SuTwo) inferInstance
    (fun _ => AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo.toSeminormedAddCommGroup)
    (fun _ => AdalyFormal.Balaban.SuTwoInner.instInnerProductSpaceSuTwo.toNormedSpace)

section Generic
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem smooth_of_inner (b : OrthonormalBasis ι ℝ E) (f : ℝ → E)
    (h : ∀ i, ContDiff ℝ ⊤ (fun t => inner ℝ (b i) (f t))) : ContDiff ℝ ⊤ f := by
  have he : f = fun t => ∑ i, (inner ℝ (b i) (f t) : ℝ) • b i := by
    funext t
    exact (b.sum_repr' (f t)).symm
  rw [he]
  exact ContDiff.sum (fun i _ => (h i).smul contDiff_const)

theorem smooth_clm (b : OrthonormalBasis ι ℝ E) (T : ℝ → E →L[ℝ] F)
    (h : ∀ i, ContDiff ℝ ⊤ (fun t => T t (b i))) : ContDiff ℝ ⊤ T := by
  have he : T = fun t => ∑ i, InnerProductSpace.rankOne ℝ (T t (b i)) (b i) := by
    funext t
    ext X
    simp only [_root_.sum_apply, InnerProductSpace.rankOne_apply]
    simpa only [map_sum, map_smul] using congrArg (T t) (b.sum_repr' X).symm
  rw [he]
  apply ContDiff.sum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ E F (innerSL ℝ (b i))).contDiff.comp (h i)
end Generic

def matrixEntry (i j : Fin 2) : M2 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun M => M i j
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- Smoothness of the intrinsic SuTwo topology is recovered from its certified coordinates. -/
theorem smooth_suTwo_of_coe (f : ℝ → SuTwo)
    (h : ContDiff ℝ ⊤ (fun t => (f t : M2))) : ContDiff ℝ ⊤ f := by
  have h01 := (matrixEntry 0 0).contDiff.comp h
  have h02 := (matrixEntry 0 1).contDiff.comp h
  have he : f = fun t =>
      ((f t : M2) 0 1).im • pauliE1 + ((f t : M2) 0 1).re • pauliE2 +
        ((f t : M2) 0 0).im • pauliE3 := by
    funext t
    exact (assemble_coordinates (f t)).symm
  rw [he]
  exact (((Complex.imCLM.contDiff.comp h02).smul contDiff_const).add
    ((Complex.reCLM.contDiff.comp h02).smul contDiff_const)).add
      ((Complex.imCLM.contDiff.comp h01).smul contDiff_const)

theorem smooth_rotA : ContDiff ℝ ⊤ rotA := by
  apply ContDiff.div (contDiff_const.sub (contDiff_id.pow 2))
    (contDiff_const.add (contDiff_id.pow 2))
  exact one_add_sq_ne_zero

theorem smooth_rotB : ContDiff ℝ ⊤ rotB := by
  apply ContDiff.div (contDiff_const.mul contDiff_id)
    (contDiff_const.add (contDiff_id.pow 2))
  exact one_add_sq_ne_zero

theorem smooth_rot_R (X : SuTwo) : ContDiff ℝ ⊤ (fun t => RMap (rotElem t) X) := by
  conv => arg 3; ext t; rw [← assemble_coordinates X, RMap_rot_assemble]
  unfold assemble
  have hp : ContDiff ℝ ⊤ (fun t => rotA t ^ 2 - rotB t ^ 2) :=
    (smooth_rotA.pow 2).sub (smooth_rotB.pow 2)
  have hs : ContDiff ℝ ⊤ (fun t => 2*rotA t*rotB t) :=
    (contDiff_const.mul smooth_rotA).mul smooth_rotB
  exact (((hp.mul contDiff_const).sub (hs.mul contDiff_const)).smul contDiff_const |>.add
    contDiff_const).add
    (((hs.mul contDiff_const).add (hp.mul contDiff_const)).smul contDiff_const)

theorem rotElem_neg (t : ℝ) : rotElem (-t) = (rotElem t)⁻¹ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotElem_coe, coe_inv, rotM, rotA, rotB, Matrix.conjTranspose_apply] <;> ring

theorem smooth_link_R (b : Bond witnessL) (X : SuTwo) :
    ContDiff ℝ ⊤ (fun t => RMap (nonflatU t b) X) := by
  by_cases hb : b = (witnessY,0)
  · simp only [hb, nonflatU_at_x_mu]
    exact smooth_rot_R X
  · simp only [nonflatU_elsewhere _ hb]
    exact contDiff_const

theorem smooth_fiber {ι : Type} [Fintype ι] (f : ℝ → FiberL2 ι)
    (h : ∀ i, ContDiff ℝ ⊤ (fun t => fiberEquiv ι (f t) i)) : ContDiff ℝ ⊤ f := by
  apply smooth_of_inner (Pi.orthonormalBasis (fun _ : ι => fibreBasis))
  intro j
  simp only [← OrthonormalBasis.repr_apply_apply]
  change ContDiff ℝ ⊤ (fun t => fibreBasis.repr (fiberEquiv ι (f t) j.1) j.2)
  exact (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j.2).contDiff.comp
    (fibreBasis.repr.contDiff.comp (h j.1))

theorem smooth_siteFrame : ContDiff ℝ ⊤ siteFrame := by
  apply smooth_clm siteBasis
  intro i
  apply smooth_fiber
  intro x
  simp only [siteFrame_value]
  by_cases hx : x = specialEndpoint
  · simp only [if_pos hx, ← rotElem_neg]
    exact (smooth_rot_R _).comp contDiff_neg
  · simp only [if_neg hx]
    exact contDiff_const

theorem smooth_covGrad : ContDiff ℝ ⊤ (fun t => covGrad (nonflatU t)) := by
  apply smooth_clm siteBasis
  intro i
  apply smooth_fiber
  intro b
  change ContDiff ℝ ⊤ (fun t => (2:ℝ) •
    (RMap (nonflatU t b) (fiberEquiv Site (siteBasis i) (periodicLatticeShift b.1 b.2)) -
      fiberEquiv Site (siteBasis i) b.1))
  exact (smooth_link_R _ _ |>.sub contDiff_const).const_smul 2

theorem smooth_covCurl : ContDiff ℝ ⊤ (fun t => covCurl (nonflatU t)) := by
  apply smooth_clm fineBasis
  intro i
  apply smooth_fiber
  intro p
  change ContDiff ℝ ⊤ (fun t => (2:ℝ) •
    (bfl2Equiv (fineBasis i) (p.1,p.2.1.1) +
      RMap (nonflatU t (p.1,p.2.1.1)) (bfl2Equiv (fineBasis i) (periodicLatticeShift p.1 p.2.1.1,p.2.1.2)) -
      RMap (nonflatU t (p.1,p.2.1.2)) (bfl2Equiv (fineBasis i) (periodicLatticeShift p.1 p.2.1.2,p.2.1.1)) -
      bfl2Equiv (fineBasis i) (p.1,p.2.1.2)))
  exact ((contDiff_const.add (smooth_link_R _ _) |>.sub (smooth_link_R _ _)).sub contDiff_const).const_smul 2

theorem smooth_gaugeSpan : ContDiff ℝ ⊤ gaugeSpan := by
  unfold gaugeSpan siteDeltaU
  have hD : ContDiff ℝ ⊤ (fun t => (covGrad (nonflatU t)).adjoint.comp (covGrad (nonflatU t))) :=
    ((ContinuousLinearMap.adjoint : (S →L[ℝ] H) ≃ₗᵢ[ℝ] (H →L[ℝ] S)).contDiff.comp smooth_covGrad).clm_comp smooth_covGrad
  have hW : ContDiff ℝ ⊤ (fun t => (siteFrame t).comp kernelProjection) :=
    smooth_siteFrame.clm_comp contDiff_const
  exact hD.clm_comp hW

theorem smooth_dualGauge : ContDiff ℝ ⊤ dualGauge := by
  unfold dualGauge
  exact ((ContinuousLinearMap.adjoint : (S →L[ℝ] S) ≃ₗᵢ[ℝ] (S →L[ℝ] S)).contDiff.comp smooth_gaugeSpan).clm_comp
    ((ContinuousLinearMap.adjoint : (S →L[ℝ] H) ≃ₗᵢ[ℝ] (H →L[ℝ] S)).contDiff.comp smooth_covGrad)

#print axioms smooth_rot_R
#print axioms smooth_siteFrame
#print axioms smooth_covGrad
#print axioms smooth_covCurl
#print axioms smooth_gaugeSpan
#print axioms smooth_dualGauge
end HConstruction.TransversePos
