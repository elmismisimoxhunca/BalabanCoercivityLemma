import CarrierBridge
set_option autoImplicit false
namespace HConstruction.Covariance
open HConstruction.Carrier HConstruction.Predicate
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.DeltaKUnified (BFL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator interpolates)

noncomputable local instance : NormedAddCommGroup M2 := Matrix.linftyOpNormedAddCommGroup
noncomputable local instance : NormedSpace ℝ M2 := Matrix.linftyOpNormedSpace
noncomputable local instance : NormedSpace ℂ M2 := Matrix.linftyOpNormedSpace

/-- Bond-sector q124, NOT CovarianceG1.QLinearMap (which is the site-sector Q'). -/
noncomputable def nativeLinearQ {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ) : BFL2 L →L[ℝ] CFL2 L ell :=
  LinearMap.toContinuousLinearMap ((cfl2Equiv ell).symm.toLinearMap.comp
    ((AdalyFormal.DeltaKR85.q124Principal 1 ell U).comp fineCoordinates.toLinearMap))

theorem nativeLinearQ_exact {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ) (A : BFL2 L)
    (c : CoarseBond L (1 * ell)) :
    ((cfl2Equiv ell (nativeLinearQ U ell A) c : SuTwo) : M2) =
      linearQ U ell (fineCoordinates A) c := rfl

theorem nativeLinearQ_nonzero : nativeLinearQ (trivialU witnessL) 2 ≠ 0 := by
  intro hz
  have hv := congrArg (fun Q : BFL2 witnessL →L[ℝ] CFL2 witnessL 2 =>
    ((cfl2Equiv 2 (Q (fineCoordinates.symm HConstruction.NonzeroJet.A0))
      HConstruction.NonzeroJet.c0 : SuTwo) : M2)) hz
  have hn := HConstruction.NonzeroJet.linearQ_A0_ne_zero
  apply hn
  simpa only [nativeLinearQ_exact, LinearEquiv.apply_symm_apply,
    ContinuousLinearMap.zero_apply, map_zero, Pi.zero_apply, Submodule.coe_zero] using hv

/-- A downstream wiring lemma, NOT the existence of the source covariance datum. -/
theorem variationalQext_identified_firstJet
    (D : BalabanCovarianceData (BFL2 witnessL) (CFL2 witnessL 2))
    (hQ : D.Q = nativeLinearQ (trivialU witnessL) 2)
    (B : CFL2 witnessL 2) (c : CoarseBond witnessL (1 * 2)) :
    HasDerivAt (fun t : ℝ => ((cfl2Equiv 2
      (variationalQext (trivialU witnessL) 2 D (t • B)) c : SuTwo) : M2))
      ((cfl2Equiv 2 B c : SuTwo) : M2) 0 := by
  have h := variationalQext_witness_firstJet D B c
  have hi := interpolates D B
  rw [hQ] at hi
  rw [← nativeLinearQ_exact, hi] at h
  exact h

end HConstruction.Covariance
