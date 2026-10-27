import DK3FineJet
set_option autoImplicit false
set_option maxRecDepth 512
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.DK3.FineScale.Physical
open HConstruction.Carrier HConstruction.Covariance HConstruction.Nonflat
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice blockOf)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.NormalizationAudit
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)

attribute [local irreducible] blockOf CoarseLattice
  HConstruction.SmallNF.Reproduced.deltaPrimeBil

variable {L : PeriodicLatticeExtent}
abbrev H (L : PeriodicLatticeExtent) := AdalyFormal.Balaban.DeltaKUnified.BFL2 L
abbrev S (L : PeriodicLatticeExtent) := FiberL2 (PeriodicLatticeSite L)
abbrev F (L : PeriodicLatticeExtent) := FiberL2 (PeriodicLatticePlaquette L)
abbrev K (L : PeriodicLatticeExtent) := CFL2 L 2
abbrev CS (L : PeriodicLatticeExtent) := {y : PeriodicLatticeSite L // y ∈ CoarseLattice L 2}

/-- Fine gradient at eta=1/8. -/
noncomputable def covGrad (U : PeriodicLinkConfiguration SU2 L) : (S L) →L[ℝ] (H L) :=
  (8 : ℝ) • LinearMap.toContinuousLinearMap (bfl2Equiv.symm.toLinearMap.comp
    ((gradCovariantLM U).comp (fiberEquiv _).toLinearMap))

noncomputable def covCurl (U : PeriodicLinkConfiguration SU2 L) : (H L) →L[ℝ] (F L) :=
  (8 : ℝ) • LinearMap.toContinuousLinearMap
    ((fiberEquiv (PeriodicLatticePlaquette L)).symm.toLinearMap.comp
      ((curlCovariantLM U).comp bfl2Equiv.toLinearMap))

/-- This is ONLY the curl-square part, NOT the full source Hessian at U. -/
noncomputable def curlSquare (U : PeriodicLinkConfiguration SU2 L) : (H L) →L[ℝ] (H L) :=
  (covCurl U).adjoint.comp (covCurl U)

theorem curlSquare_energy (U : PeriodicLinkConfiguration SU2 L) (A : (H L)) :
    (inner ℝ A (curlSquare U A) : ℝ) = ‖covCurl U A‖ ^ 2 := by
  simp only [curlSquare, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

/-- Exact normalized transported (3.10) correction on the SAME (H L); eta^-2=64. -/
def correctionBil (U : PeriodicLinkConfiguration SU2 L) : (H L) →ₗ[ℝ] (H L) →ₗ[ℝ] ℝ :=
  (32 : ℝ) • (HConstruction.SmallNF.Reproduced.deltaPrimeBil U).compl₁₂ bfl2Equiv.toLinearMap bfl2Equiv.toLinearMap
lemma correctionBil_apply (U : PeriodicLinkConfiguration SU2 L) (A B : (H L)) :
    correctionBil U A B = 32 * HConstruction.SmallNF.Reproduced.deltaPrimeBil U (bfl2Equiv A) (bfl2Equiv B) := by
  simp only [correctionBil, LinearMap.smul_apply, LinearMap.compl₁₂_apply, smul_eq_mul, LinearEquiv.coe_coe]

/-- Finite-dimensional Riesz representation, without adding an inverse assumption. -/
def riesz (f : (H L) →ₗ[ℝ] ℝ) : (H L) := f.adjoint 1
lemma inner_riesz (f : (H L) →ₗ[ℝ] ℝ) (A : (H L)) : (inner ℝ A (riesz f) : ℝ) = f A := by
  rw [riesz,LinearMap.adjoint_inner_right,Real.inner_apply]
  ring

def fromBil (b : (H L) →ₗ[ℝ] (H L) →ₗ[ℝ] ℝ) : (H L) →L[ℝ] (H L) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun B => riesz (b.flip B)
    map_add' := by
      intro B C; apply ext_inner_left ℝ; intro A
      simp only [inner_add_right,inner_riesz]
      simp
    map_smul' := by
      intro r B; apply ext_inner_left ℝ; intro A
      simp only [real_inner_smul_right,inner_riesz]
      simp }
lemma inner_fromBil (b : (H L) →ₗ[ℝ] (H L) →ₗ[ℝ] ℝ) (A B : (H L)) :
    (inner ℝ A (fromBil b B) : ℝ) = b A B := inner_riesz _ _

def deltaU (U : PeriodicLinkConfiguration SU2 L) : (H L) →L[ℝ] (H L) :=
  curlSquare U + fromBil (correctionBil U)

theorem deltaU_energy (U : PeriodicLinkConfiguration SU2 L) (A : (H L)) :
    (inner ℝ A (deltaU U A) : ℝ) = ‖covCurl U A‖^2 +
      64 * deltaPrimeQuadFormNormalizedTransported U (bfl2Equiv A) := by
  simp only [deltaU,add_apply,inner_add_right,curlSquare_energy,inner_fromBil]
  change _ + 32 * HConstruction.SmallNF.Reproduced.deltaPrimeBil U (bfl2Equiv A) (bfl2Equiv A) = _
  rw [HConstruction.SmallNF.Reproduced.deltaPrimeBil_diag,
    deltaPrimeQuadFormNormalizedTransported_eq_half_transported]
  ring

theorem deltaU_selfAdjoint (U : PeriodicLinkConfiguration SU2 L) (A B : (H L)) :
    (inner ℝ (deltaU U A) B : ℝ) = inner ℝ A (deltaU U B) := by
  rw [real_inner_comm]
  simp only [deltaU,add_apply,inner_add_right,inner_fromBil,curlSquare,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]
  simp only [correctionBil_apply]
  rw [HConstruction.SmallNF.Reproduced.deltaPrimeBil_symm U (bfl2Equiv B) (bfl2Equiv A)]
  rw [real_inner_comm (covCurl U B) (covCurl U A)]

def siteDeltaU (U : PeriodicLinkConfiguration SU2 L) : S L →L[ℝ] S L :=
  (covGrad U).adjoint.comp (covGrad U)
end HConstruction.DK3.FineScale.Physical
namespace HConstruction.DK3.FineScale
open HConstruction.Carrier HConstruction.Covariance
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.NormalizationAudit
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open Physical (covGrad covCurl deltaU deltaU_energy siteDeltaU)
abbrev SF := Physical.S fineL
abbrev PF := Physical.F fineL
abbrev F := CovarianceScale.F
abbrev CS := {y : FS // y ∈ CoarseLattice fineL 8}

/-- CMP99b (3.19) depth-three SITE average, evaluated only at genuine stride-8 sites.
No one-step Q prime is silently reused. -/
def siteQU (t : ℝ) : SF →ₗ[ℝ] (CS → SuTwo) :=
  (LinearMap.pi (fun y : CS => LinearMap.proj y.1)).comp
    ((AdalyFormal.Balaban.QjComposite.QcompositeLM (tower t) 2 3).comp
      (fiberEquiv FS).toLinearMap)

def gaugeImageU (t : ℝ) : Submodule ℝ SF :=
  (LinearMap.ker (siteQU t)).map (siteDeltaU (U t)).toLinearMap
def siteRU (t : ℝ) : SF →L[ℝ] SF :=
  (gaugeImageU t).starProjection
lemma siteRU_idempotent (t : ℝ) :
    siteRU t * siteRU t = siteRU t := Submodule.isIdempotentElem_starProjection _
lemma siteRU_adjoint (t : ℝ) :
    (siteRU t).adjoint = siteRU t := by
  ext A; apply ext_inner_right ℝ; intro B
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (Submodule.inner_starProjection_left_eq_right (gaugeImageU t) A B).symm

def gaugeConstraintU (t : ℝ) : F →L[ℝ] SF :=
  (siteRU t).comp (covGrad (U t)).adjoint
lemma gaugeU_identity (t : ℝ) :
    (gaugeConstraintU t).adjoint.comp (gaugeConstraintU t) =
      (covGrad (U t)).comp ((siteRU t).comp (covGrad (U t)).adjoint) := by
  ext A
  simp only [gaugeConstraintU,ContinuousLinearMap.adjoint_comp,siteRU_adjoint,
    ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.comp_apply]
  exact congrArg (covGrad (U t))
    (congrArg (fun T : SF →L[ℝ] SF => T ((covGrad (U t)).adjoint A)) (siteRU_idempotent t))

/-- Full fine VALUE-coordinate precision at eta=1/8. This is not yet an inverse. -/
def precision (t a : ℝ) : F →L[ℝ] F :=
  deltaU (U t) + (covGrad (U t)).comp ((siteRU t).comp (covGrad (U t)).adjoint) +
    (CovarianceScale.incomingPhysicalAdjoint t).comp (a • CovarianceScale.incomingQ t)

theorem precision_energy (t a : ℝ) (A : F) :
    (inner ℝ A (precision t a A) : ℝ) = ‖covCurl (U t) A‖^2 +
      64 * deltaPrimeQuadFormNormalizedTransported (U t) (bfl2Equiv A) +
      ‖gaugeConstraintU t A‖^2 + 512*a*‖CovarianceScale.incomingQ t A‖^2 := by
  rw [precision, ← gaugeU_identity]
  simp only [_root_.add_apply, _root_.smul_apply, inner_add_right, inner_smul_right,
    deltaU_energy, ContinuousLinearMap.comp_apply, CovarianceScale.incomingPhysicalAdjoint,
    map_smul, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  ring

/-- Existence is deliberately a conclusion to be proved, not hidden by Ring.inverse. -/
def HasPhysicalG0 (t a : ℝ) : Prop :=
  ∃ G : F →L[ℝ] F, precision t a * G = 1 ∧ G * precision t a = 1

#print axioms precision_energy
end HConstruction.DK3.FineScale
