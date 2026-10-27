import SmoothFinite
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance 20000] AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo
  AdalyFormal.Balaban.SuTwoInner.instInnerProductSpaceSuTwo
namespace HConstruction.TransversePos
open HConstruction.Circle HConstruction.Covariance HConstruction.SmallNF HConstruction.Nonflat
open HConstruction.NfRepair.Reproduced HConstruction.G0HSchur
open HConstruction.SmallNF.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL witnessY Bond)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_inv coe_mul)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
local instance : SeminormedAddCommGroup SuTwo := instNormedAddCommGroupSuTwo.toSeminormedAddCommGroup
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

def suCoe : SuTwo →L[ℝ] M2 := LinearMap.toContinuousLinearMap suTwo.subtype

theorem smooth_link_matrix (b : Bond witnessL) : ContDiff ℝ ⊤ (fun t => (nonflatU t b : M2)) := by
  by_cases hb : b = (witnessY,0)
  · have he : (fun t => (nonflatU t b : M2)) =
        fun t => rotA t • (1 : M2) + rotB t • (pauliE2 : M2) := by
      funext t
      rw [hb, nonflatU_at_x_mu, rotElem_coe]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [rotM, pauliE2, witnessM, Complex.real_smul, Matrix.one_apply]
    rw [he]
    exact (smooth_rotA.smul contDiff_const).add (smooth_rotB.smul contDiff_const)
  · simp only [nonflatU_elsewhere _ hb]
    exact contDiff_const

theorem smooth_group_mul {f g : ℝ → SU2}
    (hf : ContDiff ℝ ⊤ (fun t => (f t : M2)))
    (hg : ContDiff ℝ ⊤ (fun t => (g t : M2))) :
    ContDiff ℝ ⊤ (fun t => ((f t * g t : SU2) : M2)) := by
  simpa only [coe_mul] using hf.mul hg

theorem smooth_group_inv {f : ℝ → SU2} (hf : ContDiff ℝ ⊤ (fun t => (f t : M2))) :
    ContDiff ℝ ⊤ (fun t => (((f t)⁻¹ : SU2) : M2)) := by
  have h := AdalySI1.L7.conjTransposeCLM.contDiff.comp hf
  change ContDiff ℝ ⊤ (fun t => (f t : M2).conjTranspose) at h
  simpa only [coe_inv] using h

theorem smooth_holonomy_matrix (p : PeriodicLatticePlaquette witnessL) :
    ContDiff ℝ ⊤ (fun t => (holonomyElem (nonflatU t) p : M2)) := by
  unfold holonomyElem periodicPlaquetteHolonomy
  exact smooth_group_mul
    (smooth_group_mul (smooth_group_mul (smooth_link_matrix _) (smooth_link_matrix _))
      (smooth_group_inv (smooth_link_matrix _)))
    (smooth_group_inv (smooth_link_matrix _))

theorem smooth_reHolonomy (p : PeriodicLatticePlaquette witnessL) :
    ContDiff ℝ ⊤ (fun t => reHolonomy (nonflatU t) p) := by
  unfold reHolonomy holonomyElemInv
  exact ((smooth_holonomy_matrix p).add (smooth_group_inv (smooth_holonomy_matrix p))).const_smul (1/2 : ℂ)

theorem smooth_imHolonomy (p : PeriodicLatticePlaquette witnessL) :
    ContDiff ℝ ⊤ (fun t => imHolonomy (nonflatU t) p) := by
  unfold imHolonomy holonomyElemInv
  exact ((smooth_holonomy_matrix p).sub (smooth_group_inv (smooth_holonomy_matrix p))).const_smul (1/(2*Complex.I) : ℂ)

def traceCLM : M2 →L[ℝ] ℂ := LinearMap.toContinuousLinearMap {
  toFun := Matrix.trace
  map_add' := fun _ _ => Matrix.trace_add _ _
  map_smul' := by intro r M; simp }

theorem smooth_trace_re {f : ℝ → M2} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fun t => (Matrix.trace (f t)).re) :=
  Complex.reCLM.contDiff.comp (traceCLM.contDiff.comp hf)

theorem smooth_curlMat (p : PeriodicLatticePlaquette witnessL) (A : Bond witnessL → SuTwo) :
    ContDiff ℝ ⊤ (fun t => curlMatLM (nonflatU t) p A) := by
  simp only [curlMatLM_apply]
  have h : ContDiff ℝ ⊤ (fun t => curlValueCovariant (nonflatU t) A p) := by
    unfold curlValueCovariant
    exact ((contDiff_const.add (smooth_link_R _ _) |>.sub (smooth_link_R _ _)).sub contDiff_const)
  exact suCoe.contDiff.comp h

theorem smooth_b1 (p : PeriodicLatticePlaquette witnessL) (A : Bond witnessL → SuTwo) :
    ContDiff ℝ ⊤ (fun t => b1LM (nonflatU t) p A) := by
  simp only [b1LM, LinearMap.comp_apply, smulILM_apply, a1LM_apply]
  exact (suCoe.contDiff.comp (smooth_link_R _ _)).neg.const_smul _

theorem smooth_b4 (p : PeriodicLatticePlaquette witnessL) (A : Bond witnessL → SuTwo) :
    ContDiff ℝ ⊤ (fun t => b4LM (nonflatU t) p A) := by
  simp only [b4LM, LinearMap.comp_apply, smulILM_apply, a4LM_apply]
  exact (suCoe.contDiff.comp (smooth_link_R _ _)).const_smul _

theorem smooth_pair_atom (p : PeriodicLatticePlaquette witnessL) (f g : ℝ → M2)
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) :
    ContDiff ℝ ⊤ (fun t =>
      (Matrix.trace ((Complex.I • f t) * g t * imHolonomy (nonflatU t) p)).re -
      (Matrix.trace ((Complex.I • g t) * f t * imHolonomy (nonflatU t) p)).re) :=
  (smooth_trace_re ((hf.const_smul Complex.I).mul hg |>.mul (smooth_imHolonomy p))).sub
    (smooth_trace_re ((hg.const_smul Complex.I).mul hf |>.mul (smooth_imHolonomy p)))

theorem smooth_bilPlaq (p : PeriodicLatticePlaquette witnessL) (A B : Bond witnessL → SuTwo) :
    ContDiff ℝ ⊤ (fun t => bilPlaq (nonflatU t) p A B) := by
  simp only [bilPlaq_apply, firstBilPlaq_apply, secondBilPlaq_apply, pairBil_apply, smulILM_apply]
  have hf := smooth_trace_re (((smooth_curlMat p A).const_smul Complex.I).mul
    ((smooth_curlMat p B).const_smul Complex.I) |>.mul ((smooth_reHolonomy p).sub (contDiff_const (c := (1:M2)))))
  have h12 := smooth_pair_atom p _ (fun _ => b2LM p B) (smooth_b1 p A) contDiff_const
  have h13 := smooth_pair_atom p _ (fun _ => b3LM p B) (smooth_b1 p A) contDiff_const
  have h14 := smooth_pair_atom p _ _ (smooth_b1 p A) (smooth_b4 p B)
  have h23 := smooth_pair_atom p (fun _ => b2LM p A) (fun _ => b3LM p B) contDiff_const contDiff_const
  have h24 := smooth_pair_atom p (fun _ => b2LM p A) _ contDiff_const (smooth_b4 p B)
  have h34 := smooth_pair_atom p (fun _ => b3LM p A) _ contDiff_const (smooth_b4 p B)
  exact hf.add (((((h12.add h13).add h14).add h23).add h24).add h34)

theorem smooth_correction : ContDiff ℝ ⊤ (fun t => fromBil (correctionBil (nonflatU t))) := by
  apply smooth_clm fineBasis
  intro j
  apply smooth_of_inner fineBasis
  intro i
  simp only [inner_fromBil, correctionBil_apply, deltaPrimeBil_apply, deltaPrimeBilRaw_apply]
  exact contDiff_const.mul (contDiff_const.mul
    ((ContDiff.sum (fun p _ => smooth_bilPlaq p _ _)).add
      (ContDiff.sum (fun p _ => smooth_bilPlaq p _ _))))

theorem smooth_deltaU : ContDiff ℝ ⊤ (fun t => deltaU (nonflatU t)) := by
  unfold deltaU curlSquare
  exact (((ContinuousLinearMap.adjoint : (H →L[ℝ] F) ≃ₗᵢ[ℝ] (F →L[ℝ] H)).contDiff.comp
    smooth_covCurl).clm_comp smooth_covCurl).add smooth_correction

#print axioms smooth_link_matrix
#print axioms smooth_bilPlaq
#print axioms smooth_correction
#print axioms smooth_deltaU
end HConstruction.TransversePos
