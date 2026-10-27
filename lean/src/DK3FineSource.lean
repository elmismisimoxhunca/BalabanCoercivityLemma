import DK3IncomingQ

/-! Direct finest-mesh source at eta=1/8. No use of the K-valued DK3.J.
The value-coordinate source is 512 times the eta-one formula; its unweighted
functional representative is the unscaled genuineSource, since eta^3=1/512. -/
set_option autoImplicit false
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance 20000] AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo
  AdalyFormal.Balaban.SuTwoInner.instInnerProductSpaceSuTwo
namespace HConstruction.DK3.FineScale
open CovarianceScale (F fineInner)
open HConstruction.Predicate
open HConstruction.Reproduced.Source
open HConstruction.TransversePos (traceCLM smooth_group_mul smooth_group_inv smooth_fiber smooth_suTwo_of_coe)
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2 coe_inv)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem holonomyElemInv imHolonomy)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.SuTwoInner
local instance : SeminormedAddCommGroup SuTwo := instNormedAddCommGroupSuTwo.toSeminormedAddCommGroup
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

def sourceFunctional (t : ℝ) : F := genuineSource (U t)
def JF (t : ℝ) : F := (512 : ℝ) • sourceFunctional t

/-- The scale-explicit D* eta^-2 formula: D* contributes 8, curvature 64. -/
def sourceMatrix (t : ℝ) (b : Bond fineL) : M2 :=
  ∑ ν : Fin 3, if ν = b.2 then 0 else
    (8 : ℝ) • DstarDir (U t) ν (fun y => (64 : ℝ) • FnuMu (U t) ν b.2 y) b.1

theorem sourceMatrix_scale (t : ℝ) (b : Bond fineL) :
    sourceMatrix t b = (512 : ℝ) • Jsource (U t) b := by
  unfold sourceMatrix Jsource Jfield
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  split_ifs
  · simp
  · simp only [DstarDir, map_smul, ← smul_sub, smul_smul]
    norm_num

theorem JF_exact (t : ℝ) : sourceCoordinates (JF t) = sourceMatrix t := by
  funext b
  rw [sourceMatrix_scale]
  have h := congrFun (genuineSource_exact (U t)) b
  change (-Complex.I) • ((bfl2Equiv ((512 : ℝ) • genuineSource (U t)) b : SuTwo) : M2) = _
  simp only [map_smul, Pi.smul_apply, Submodule.coe_smul]
  rw [smul_comm]
  exact congrArg (fun X : M2 => (512 : ℝ) • X) h

theorem JF_functional (t : ℝ) (A : F) :
    fineInner A (JF t) = inner ℝ A (sourceFunctional t) := by
  simp only [fineInner, JF, inner_smul_right]
  ring

theorem sourceFunctional_zero : sourceFunctional 0 = 0 := by
  unfold sourceFunctional
  rw [U_zero]
  exact genuineSource_trivial

theorem JF_zero : JF 0 = 0 := by rw [JF, sourceFunctional_zero, smul_zero]

theorem smooth_holonomy (p : PeriodicLatticePlaquette fineL) :
    ContDiff ℝ ⊤ (fun t => (holonomyElem (U t) p : M2)) := by
  unfold holonomyElem periodicPlaquetteHolonomy
  exact smooth_group_mul (smooth_group_mul (smooth_group_mul (smooth_U _) (smooth_U _))
    (smooth_group_inv (smooth_U _))) (smooth_group_inv (smooth_U _))

theorem smooth_im (p : PeriodicLatticePlaquette fineL) :
    ContDiff ℝ ⊤ (fun t => imHolonomy (U t) p) := by
  unfold imHolonomy holonomyElemInv
  exact ((smooth_holonomy p).sub (smooth_group_inv (smooth_holonomy p))).const_smul _

private theorem smooth_piProj {f : ℝ → M2} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fun t => piProj (f t)) :=
  hf.sub (((traceCLM.contDiff.comp hf).div_const (2 : ℂ)).smul contDiff_const)

private theorem smooth_FnuMu (ν μ : Fin 3) (y : FS) :
    ContDiff ℝ ⊤ (fun t => FnuMu (U t) ν μ y) := by
  unfold FnuMu
  split_ifs
  · exact smooth_piProj (smooth_im _)
  · exact (smooth_piProj (smooth_im _)).neg
  · exact contDiff_const

private theorem smooth_DstarDir (ν μ : Fin 3) (x : FS) :
    ContDiff ℝ ⊤ (fun t => DstarDir (U t) ν (fun y => FnuMu (U t) ν μ y) x) := by
  unfold DstarDir conjByAmbient
  simp only [coe_inv, Matrix.conjTranspose_conjTranspose, LinearMap.coe_mk, AddHom.coe_mk]
  exact (((smooth_group_inv (smooth_U _)).mul (smooth_FnuMu ν μ _)).mul
    (smooth_U _)).sub (smooth_FnuMu ν μ x)

theorem smooth_source_matrix (b : Bond fineL) :
    ContDiff ℝ ⊤ (fun t => Jsource (U t) b) := by
  unfold Jsource Jfield
  apply ContDiff.sum
  intro ν _
  split_ifs
  · exact contDiff_const
  · exact smooth_DstarDir ν b.2 b.1

theorem smooth_sourceFunctional : ContDiff ℝ ⊤ sourceFunctional := by
  apply smooth_fiber
  intro b
  apply smooth_suTwo_of_coe
  have he (t : ℝ) : ((bfl2Equiv (sourceFunctional t) b : SuTwo) : M2) =
      Complex.I • Jsource (U t) b := by
    have h := congrFun (genuineSource_exact (U t)) b
    have hh := congrArg (fun X : M2 => Complex.I • X) h
    simpa only [sourceFunctional, sourceCoordinates, smul_smul, mul_neg,
      Complex.I_mul_I, neg_neg, one_smul] using hh
  change ContDiff ℝ ⊤ (fun t => ((bfl2Equiv (sourceFunctional t) b : SuTwo) : M2))
  simp only [he]
  exact (smooth_source_matrix b).const_smul Complex.I

theorem smooth_JF : ContDiff ℝ ⊤ JF := smooth_sourceFunctional.const_smul 512

#print axioms JF_exact
#print axioms JF_functional
#print axioms smooth_JF
end HConstruction.DK3.FineScale
