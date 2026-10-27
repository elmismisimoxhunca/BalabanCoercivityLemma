import WitnessGate
import FlatOperators
set_option autoImplicit false
namespace HConstruction.Nonflat
open HConstruction.Carrier HConstruction.Covariance
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)

/-- Same physical eta=1/2 and SAME carriers as the closed flat construction. -/
noncomputable def covGrad (U : PeriodicLinkConfiguration SU2 witnessL) : S →L[ℝ] H :=
  (2 : ℝ) • LinearMap.toContinuousLinearMap (bfl2Equiv.symm.toLinearMap.comp
    ((gradCovariantLM U).comp (fiberEquiv _).toLinearMap))

noncomputable def covCurl (U : PeriodicLinkConfiguration SU2 witnessL) : H →L[ℝ] F :=
  (2 : ℝ) • LinearMap.toContinuousLinearMap
    ((fiberEquiv (PeriodicLatticePlaquette witnessL)).symm.toLinearMap.comp
      ((curlCovariantLM U).comp bfl2Equiv.toLinearMap))

theorem covGrad_flat : covGrad (trivialU witnessL) = flatGrad := rfl
theorem covCurl_flat : covCurl (trivialU witnessL) = flatCurl := rfl

/-- The flat harmonic constant test field has NONZERO covariant curl. -/
theorem covCurl_constant_nonzero : covCurl witnessU constantField ≠ 0 := by
  intro h
  have hp := congrArg (fun A : F => fiberEquiv _ A witnessPlaquette) h
  have hz : curlValueCovariant witnessU (fun _ => suTwoWitness) witnessPlaquette = 0 := by
    simp only [covCurl, smul_apply, map_smul, Pi.smul_apply, map_zero, Pi.zero_apply] at hp
    change (2 : ℝ) •
      curlValueCovariant witnessU (fun _ => suTwoWitness) witnessPlaquette = 0 at hp
    exact (smul_eq_zero.mp hp).resolve_left (by norm_num)
  change suTwoWitness + RMap (witnessU (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, 0))
      suTwoWitness - RMap (witnessU (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, 1))
      suTwoWitness - suTwoWitness = 0 at hz
  rw [witnessU_at_x_mu, witnessU_at_x_nu, RMap_witnessMElem, RMap_one] at hz
  simp only [LinearMap.id_coe, id_eq] at hz
  simp only [add_neg_cancel, zero_sub] at hz
  exact suTwoWitness_ne_neg_self (sub_eq_zero.mp hz).symm

theorem covCurl_not_flat : covCurl witnessU ≠ flatCurl := by
  intro h
  exact covCurl_constant_nonzero (by rw [h, flatCurl_constant])

/-- This is ONLY the curl-square part, NOT the full source Hessian at U. -/
noncomputable def curlSquare (U : PeriodicLinkConfiguration SU2 witnessL) : H →L[ℝ] H :=
  (covCurl U).adjoint.comp (covCurl U)

theorem curlSquare_energy (U : PeriodicLinkConfiguration SU2 witnessL) (A : H) :
    (inner ℝ A (curlSquare U A) : ℝ) = ‖covCurl U A‖ ^ 2 := by
  simp only [curlSquare, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

theorem curlSquare_not_flatDelta : curlSquare witnessU ≠ flatDelta := by
  intro h
  have hp : (0 : ℝ) < inner ℝ constantField (curlSquare witnessU constantField) := by
    rw [curlSquare_energy]
    exact pow_pos (norm_pos_iff.mpr covCurl_constant_nonzero) 2
  rw [h, flatDelta_constant, inner_zero_right] at hp
  exact (lt_irrefl 0) hp

/-- The source coupling is quadratic in B when the source-prescribed jet is.
This algebraic fact supplies no bound and does not postulate a physical jet. -/
theorem quadratic_coupling_smul {K : Type*} [AddCommGroup K] [Module ℝ K]
    (H1 : K →ₗ[ℝ] H) (jet : K → K)
    (hjet : ∀ (t : ℝ) B, jet (t • B) = t ^ 2 • jet B)
    (J : H) (t : ℝ) (B : K) :
    (2 : ℝ) * inner ℝ (H1 (jet (t • B))) J =
      t ^ 2 * (2 * inner ℝ (H1 (jet B)) J) := by
  rw [hjet, map_smul, real_inner_smul_left]
  ring
end HConstruction.Nonflat
