import DK3GeometryChecks

/-!
Incoming depth-three Q, as distinct from the outgoing unitQ1.
This constructs a Hilbert-space transport of the ALREADY certified fineQ3,
not a new covariance. The variational fine carrier is F (side256), not K
(side32). The source recipe at V on K has instead the outgoing target W.

No G0/G1 existence, no route-5B precision, and no identification with literal
CMP99b (3.156) at k=3 is claimed here. schurPort and solutionPort are explicitly
parameterized typing/wiring diagnostics, NOT physical G1/H1 definitions.
-/
set_option autoImplicit false
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.DK3.CovarianceScale
open HConstruction.Carrier
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.DeltaKUnified (BFL2 bfl2Equiv)

/-- The input of fineQ3: bond fields on the ORIGINAL side256 torus. -/
abbrev F := BFL2 fineL

/-- A bijection of the genuine output bond sets, not of fine and unit bonds. -/
def outputBondEquiv : Bond unitL ≃ CoarseBond fineL 8 :=
  siteEquiv.prodCongr (Equiv.refl (Fin 3))

/-- Reindex just the output of fineQ3 onto the already-built side32 K. -/
def outputCoordinates : K ≃ₗ[ℝ] (CoarseBond fineL 8 → SuTwo) :=
  unitCoordinates.trans (LinearEquiv.funCongrLeft ℝ SuTwo outputBondEquiv.symm)

theorem outputCoordinates_apply (B : K) (b : Bond unitL) :
    outputCoordinates B (outputBondEquiv b) = unitCoordinates B b := by
  change unitCoordinates B (outputBondEquiv.symm (outputBondEquiv b)) = _
  rw [Equiv.symm_apply_apply]

/-- The certified incoming depth-three averaging operator F -> K.
Its domain is NOT changed when its output is reindexed. -/
def incomingQ (t : ℝ) : F →L[ℝ] K :=
  LinearMap.toContinuousLinearMap
    (outputCoordinates.symm.toLinearMap.comp
      ((fineQ3 t).comp fineCoordinates.toLinearMap))

theorem incomingQ_exact (t : ℝ) (A : F) :
    outputCoordinates (incomingQ t A) = fineQ3 t (fineCoordinates A) := by
  exact outputCoordinates.apply_symm_apply _

/-- All-input equality with the certified source-chart three-step map. -/
theorem incomingQ_source (t : ℝ) (A : F) :
    outputCoordinates (incomingQ t A) =
      AdalyQIdentification.QJ.QjInChart (tower t) 2 3 (fineCoordinates A) := by
  rw [fineQ3_source]
  exact incomingQ_exact t A

theorem incomingQ_order (t : ℝ) (A : F) :
    outputCoordinates (incomingQ t A) =
      AdalyFormal.DeltaKR85.q124Principal 4 2 (tower t 2)
        (AdalyFormal.DeltaKR85.q124Principal 2 2
          (AdalyFormal.Balaban.BlockedBackground.ubarSU2 1 2 (U t))
          (AdalyFormal.DeltaKR85.q124Principal 1 2 (U t) (fineCoordinates A))) := by
  rw [incomingQ_exact, fineQ3_order]

/-- The already-built C and unitD2 share the incoming Q's CODOMAIN. -/
def incomingJet (t : ℝ) : K → K := Unit.unitD2 t

/-- Distinct outgoing constraint: Q1 : K -> W. -/
def outgoingQ (t : ℝ) : K →L[ℝ] W := (1/2 : ℝ) • nativeRawQ t

theorem outgoingQ_exact (t : ℝ) (B : K) :
    cfl2Equiv 2 (outgoingQ t B) = unitQ1 t (unitInput B) := by
  change (1/2 : ℝ) • unitQ1 t ((2:ℝ) • unitInput B) = _
  rw [map_smul,smul_smul]
  norm_num

theorem outgoingQ_C (t : ℝ) (ht : |t| ≤ interval) (B : Reduced) :
    outgoingQ t (C t B) = 0 := by
  change (1/2 : ℝ) • nativeRawQ t (C t B) = 0
  rw [(C_mem_domain t ht B).2.2,smul_zero]

/-- At eta=1/8 the physical fine density is 1/512. This is not the k=1 factor 8. -/
def fineInner (A B : F) : ℝ := (1/512 : ℝ) * inner ℝ A B

def incomingPhysicalAdjoint (t : ℝ) : K →L[ℝ] F :=
  (512 : ℝ) • (incomingQ t).adjoint

theorem incomingPhysicalAdjoint_identity (t : ℝ) (A : F) (B : K) :
    fineInner A (incomingPhysicalAdjoint t B) = inner ℝ (incomingQ t A) B := by
  unfold fineInner incomingPhysicalAdjoint
  simp only [_root_.smul_apply, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right]
  ring

/-- Carrier diagnostic: covariance argument has to act on F, not K. -/
def schurPort (t : ℝ) (G : F →L[ℝ] F) : K →L[ℝ] K :=
  (incomingQ t).comp (G.comp (incomingPhysicalAdjoint t))

/-- Carrier diagnostic only. No inverse equation is claimed without IsUnit. -/
def solutionPort (t : ℝ) (G : F →L[ℝ] F) : K →L[ℝ] F :=
  G.comp ((incomingPhysicalAdjoint t).comp (Ring.inverse (schurPort t G)))

theorem solutionPort_interpolates (t : ℝ) (G : F →L[ℝ] F)
    (h : IsUnit (schurPort t G)) :
    (incomingQ t).comp (solutionPort t G) = ContinuousLinearMap.id ℝ K :=
  Ring.mul_inverse_cancel _ h

/-- The genuine unit second jet FITS the input of an incoming H1;
the output is F, so the pairing requires a source in F, not DK3.J : K. -/
def sourcePairingPort (t : ℝ) (H : K →L[ℝ] F) (JF : F) (B : K) : ℝ :=
  fineInner (H (Unit.unitD2 t B)) JF

/-- Lifting the current source by Q* is an additional prescription, not a
source-identification theorem. If chosen, interpolation forces this formula. -/
theorem adjointLiftedSource_pairing (t : ℝ) (H : K →L[ℝ] F)
    (hH : (incomingQ t).comp H = ContinuousLinearMap.id ℝ K) (B : K) :
    sourcePairingPort t H (incomingPhysicalAdjoint t (J t)) B =
      inner ℝ (Unit.unitD2 t B) (J t) := by
  unfold sourcePairingPort
  rw [incomingPhysicalAdjoint_identity]
  have h := congrArg (fun L : K →L[ℝ] K => L (Unit.unitD2 t B)) hH
  change incomingQ t (H (Unit.unitD2 t B)) = Unit.unitD2 t B at h
  rw [h]

end HConstruction.DK3.CovarianceScale
