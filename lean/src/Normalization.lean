import NativeLinearQ
set_option autoImplicit false
namespace HConstruction.Covariance
open HConstruction.Carrier
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKUnified (BFL2)

/-- CMP99b (3.11), d=3, eta=1/2, expressed in the existing value coordinates.
SuTwoInner already contains the normalized trace. This is the missing spatial
volume, not a second trace normalization. -/
noncomputable def physicalFinePairing (A B : BFL2 witnessL) : ℝ := (1 / 8 : ℝ) * inner ℝ A B

/-- Source adjoint when Q is left unchanged in value coordinates. -/
noncomputable def physicalQstar : CFL2 witnessL 2 →L[ℝ] BFL2 witnessL :=
  (8 : ℝ) • (nativeLinearQ (trivialU witnessL) 2).adjoint

theorem physicalQstar_adjoint (A : BFL2 witnessL) (B : CFL2 witnessL 2) :
    (inner ℝ (nativeLinearQ (trivialU witnessL) 2 A) B : ℝ) =
      physicalFinePairing A (physicalQstar B) := by
  simp only [physicalFinePairing, physicalQstar, smul_apply, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right]
  ring

/-- A covariance structure on the UNWEIGHTED Hilbert carriers cannot use the
source-weighted adjoint unchanged. This is an actual nonzero native-Q test. -/
theorem physicalQstar_not_unweighted_adjoint :
    ¬ (∀ (A : BFL2 witnessL) (B : CFL2 witnessL 2),
      (inner ℝ (nativeLinearQ (trivialU witnessL) 2 A) B : ℝ) =
        inner ℝ A (physicalQstar B)) := by
  intro h
  apply nativeLinearQ_nonzero
  ext A
  have hp := h A (nativeLinearQ (trivialU witnessL) 2 A)
  simp only [physicalQstar, smul_apply, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq] at hp
  have hn : ‖nativeLinearQ (trivialU witnessL) 2 A‖ = 0 := by
    nlinarith [norm_nonneg (nativeLinearQ (trivialU witnessL) 2 A)]
  exact norm_eq_zero.mp hn

theorem no_unrescaled_native_datum :
    ¬ ∃ D : AdalyFormal.Balaban.VariationalProjectorH1.BalabanCovarianceData
      (BFL2 witnessL) (CFL2 witnessL 2),
      D.Q = nativeLinearQ (trivialU witnessL) 2 ∧ D.Qstar = physicalQstar := by
  rintro ⟨D, hQ, hQstar⟩
  apply physicalQstar_not_unweighted_adjoint
  intro A B
  rw [← hQ, ← hQstar]
  exact D.Q_Qstar_adjoint A B

end HConstruction.Covariance
