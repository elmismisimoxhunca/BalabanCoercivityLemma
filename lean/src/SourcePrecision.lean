import HessianReproduced
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.SmallNF
open HConstruction.Carrier HConstruction.Covariance HConstruction.Nonflat
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL Bond CoarseLattice blockOf)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.NormalizationAudit
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)

abbrev K := CFL2 witnessL 2
abbrev CS := {y : PeriodicLatticeSite witnessL // y ∈ CoarseLattice witnessL 2}

/-- Exact normalized transported (3.10) correction on the SAME H; eta^-2=4. -/
def correctionBil (U : PeriodicLinkConfiguration SU2 witnessL) : H →ₗ[ℝ] H →ₗ[ℝ] ℝ :=
  (2 : ℝ) • (Reproduced.deltaPrimeBil U).compl₁₂ bfl2Equiv.toLinearMap bfl2Equiv.toLinearMap
lemma correctionBil_apply (U : PeriodicLinkConfiguration SU2 witnessL) (A B : H) :
    correctionBil U A B = 2 * Reproduced.deltaPrimeBil U (bfl2Equiv A) (bfl2Equiv B) := rfl

/-- Finite-dimensional Riesz representation, without adding an inverse assumption. -/
def riesz (f : H →ₗ[ℝ] ℝ) : H := f.adjoint 1
lemma inner_riesz (f : H →ₗ[ℝ] ℝ) (A : H) : (inner ℝ A (riesz f) : ℝ) = f A := by
  rw [riesz,LinearMap.adjoint_inner_right,Real.inner_apply]
  ring

def fromBil (b : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) : H →L[ℝ] H :=
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
lemma inner_fromBil (b : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (A B : H) :
    (inner ℝ A (fromBil b B) : ℝ) = b A B := inner_riesz _ _

def deltaU (U : PeriodicLinkConfiguration SU2 witnessL) : H →L[ℝ] H :=
  curlSquare U + fromBil (correctionBil U)

theorem deltaU_energy (U : PeriodicLinkConfiguration SU2 witnessL) (A : H) :
    (inner ℝ A (deltaU U A) : ℝ) = ‖covCurl U A‖^2 +
      4 * deltaPrimeQuadFormNormalizedTransported U (bfl2Equiv A) := by
  simp only [deltaU,add_apply,inner_add_right,curlSquare_energy,inner_fromBil]
  change _ + 2 * Reproduced.deltaPrimeBil U (bfl2Equiv A) (bfl2Equiv A) = _
  rw [Reproduced.deltaPrimeBil_diag,
    deltaPrimeQuadFormNormalizedTransported_eq_half_transported]
  ring

theorem deltaU_selfAdjoint (U : PeriodicLinkConfiguration SU2 witnessL) (A B : H) :
    (inner ℝ (deltaU U A) B : ℝ) = inner ℝ A (deltaU U B) := by
  rw [real_inner_comm]
  simp only [deltaU,add_apply,inner_add_right,inner_fromBil,curlSquare,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]
  simp only [correctionBil_apply]
  rw [Reproduced.deltaPrimeBil_symm U (bfl2Equiv B) (bfl2Equiv A)]
  rw [real_inner_comm (covCurl U B) (covCurl U A)]

/-- Q'_U is the SITE average with parallel transport, not the bond Q and not flatSiteQ. -/
def siteQU (U : PeriodicLinkConfiguration SU2 witnessL) : S →ₗ[ℝ] (CS → SuTwo) :=
  LinearMap.pi fun y => (1/8 : ℝ) •
    ∑ x ∈ blockOf y.1 2,
      (RMap (coarsePathHolonomy 1 U y.1 (coarseGammaPath 1 y.1 x))).comp
        ((LinearMap.proj x).comp (fiberEquiv _).toLinearMap)

def siteDeltaU (U : PeriodicLinkConfiguration SU2 witnessL) : S →L[ℝ] S :=
  (covGrad U).adjoint.comp (covGrad U)
def gaugeImageU (U : PeriodicLinkConfiguration SU2 witnessL) : Submodule ℝ S :=
  (LinearMap.ker (siteQU U)).map (siteDeltaU U).toLinearMap
def siteRU (U : PeriodicLinkConfiguration SU2 witnessL) : S →L[ℝ] S :=
  (gaugeImageU U).starProjection
lemma siteRU_idempotent (U : PeriodicLinkConfiguration SU2 witnessL) :
    siteRU U * siteRU U = siteRU U := Submodule.isIdempotentElem_starProjection _
lemma siteRU_adjoint (U : PeriodicLinkConfiguration SU2 witnessL) :
    (siteRU U).adjoint = siteRU U := by
  ext A; apply ext_inner_right ℝ; intro B
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (Submodule.inner_starProjection_left_eq_right (gaugeImageU U) A B).symm

def gaugeConstraintU (U : PeriodicLinkConfiguration SU2 witnessL) : H →L[ℝ] S :=
  (siteRU U).comp (covGrad U).adjoint
lemma gaugeU_identity (U : PeriodicLinkConfiguration SU2 witnessL) :
    (gaugeConstraintU U).adjoint.comp (gaugeConstraintU U) =
      (covGrad U).comp ((siteRU U).comp (covGrad U).adjoint) := by
  ext A
  simp only [gaugeConstraintU,ContinuousLinearMap.adjoint_comp,siteRU_adjoint,
    ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.comp_apply]
  exact congrArg (covGrad U)
    (congrArg (fun T : S →L[ℝ] S => T ((covGrad U).adjoint A)) (siteRU_idempotent U))

/-- CMP99b p.421 precision in VALUE coordinates; Q*_physical = 8 Q*_Hilbert.
This defines the precision, not a proof that its inverse exists. -/
def precisionU (U : PeriodicLinkConfiguration SU2 witnessL) (a : ℝ) : H →L[ℝ] H :=
  deltaU U + (covGrad U).comp ((siteRU U).comp (covGrad U).adjoint) +
    (8*a) • (nativeLinearQ U 2).adjoint.comp (nativeLinearQ U 2)

theorem precisionU_energy (U : PeriodicLinkConfiguration SU2 witnessL) (a : ℝ) (A : H) :
    (inner ℝ A (precisionU U a A) : ℝ) = ‖covCurl U A‖^2 +
      4 * deltaPrimeQuadFormNormalizedTransported U (bfl2Equiv A) +
      ‖gaugeConstraintU U A‖^2 + 8*a*‖nativeLinearQ U 2 A‖^2 := by
  rw [precisionU,← gaugeU_identity]
  simp only [add_apply,smul_apply,inner_add_right,inner_smul_right,deltaU_energy,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,real_inner_self_eq_norm_sq]

/-- Precise gate left to prove; no totalized Ring.inverse is labelled a covariance. -/
def HasPhysicalG0 (U : PeriodicLinkConfiguration SU2 witnessL) (a : ℝ) : Prop :=
  ∃ G : H →L[ℝ] H, (∀ A, precisionU U a (G A) = A) ∧
    (∀ A, G (precisionU U a A) = A)

/-- A real U-dependent precision at the admitted background, not flatDelta. -/
def chosenPrecision : H →L[ℝ] H := precisionU chosenU 1
end HConstruction.SmallNF
