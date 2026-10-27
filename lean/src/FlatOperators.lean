import NativeLinearQ
import Neumann

set_option autoImplicit false
namespace HConstruction.Covariance
open HConstruction.Carrier HConstruction.Predicate
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL witnessY)
open AdalyFormal.Balaban.DeltaKUnified (BFL2 bfl2Equiv)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

/-- Internally consistent finite L2 carrier, as in BFL2/CFL2; not a sup norm. -/
def FiberL2 (ι : Type) : Type := WithLp 2 (ι → SuTwo)
noncomputable instance {ι : Type} [Fintype ι] : NormedAddCommGroup (FiberL2 ι) :=
  PiLp.normedAddCommGroup (p := 2) (α := fun _ : ι => SuTwo)
noncomputable instance {ι : Type} [Fintype ι] : InnerProductSpace ℝ (FiberL2 ι) :=
  PiLp.innerProductSpace (𝕜 := ℝ) (f := fun _ : ι => SuTwo)
noncomputable instance {ι : Type} [Fintype ι] : FiniteDimensional ℝ (FiberL2 ι) :=
  (inferInstance : FiniteDimensional ℝ (PiLp 2 (fun _ : ι => SuTwo)))
noncomputable instance {ι : Type} [Fintype ι] : CompleteSpace (FiberL2 ι) :=
  FiniteDimensional.complete ℝ (FiberL2 ι)
noncomputable def fiberEquiv (ι : Type) [Fintype ι] : FiberL2 ι ≃ₗ[ℝ] (ι → SuTwo) :=
  WithLp.linearEquiv 2 ℝ _

abbrev H := BFL2 witnessL
abbrev S := FiberL2 (PeriodicLatticeSite witnessL)
abbrev F := FiberL2 (PeriodicLatticePlaquette witnessL)

/-- Fine spacing eta=1/2: CMP99b (3.3). Factor 2 is NOT omitted. -/
noncomputable def flatGrad : S →L[ℝ] H :=
  (2 : ℝ) • LinearMap.toContinuousLinearMap (bfl2Equiv.symm.toLinearMap.comp
    ((gradCovariantLM (trivialU witnessL)).comp (fiberEquiv _).toLinearMap))

/-- CMP99b (3.4), same eta=1/2 and genuine su(2) fibres. -/
noncomputable def flatCurl : H →L[ℝ] F :=
  (2 : ℝ) • LinearMap.toContinuousLinearMap ((fiberEquiv (PeriodicLatticePlaquette witnessL)).symm.toLinearMap.comp
    ((curlCovariantLM (trivialU witnessL)).comp bfl2Equiv.toLinearMap))

/-- CMP99b (3.10) at U=1. The curvature-dependent Delta-prime terms vanish.
This is the BARE Hessian, not the gauge-fixed inverse covariance. -/
noncomputable def flatDelta : H →L[ℝ] H := flatCurl.adjoint.comp flatCurl

theorem flatDelta_energy (A : H) :
    (inner ℝ A (flatDelta A) : ℝ) = ‖flatCurl A‖ ^ 2 := by
  simp only [flatDelta, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

theorem flatDelta_selfAdjoint (A B : H) :
    (inner ℝ (flatDelta A) B : ℝ) = inner ℝ A (flatDelta B) := by
  simp only [flatDelta, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

theorem flatDelta_nonneg (A : H) : (0 : ℝ) ≤ inner ℝ A (flatDelta A) := by
  rw [flatDelta_energy]
  positivity

/-- Same constant nonzero field used in the native block-two first-jet witness. -/
noncomputable def constantField : H := bfl2Equiv.symm (fun _ => suTwoWitness)

theorem constantField_nonzero : constantField ≠ 0 := by
  intro h
  have hv := congrArg (fun A : H => bfl2Equiv A (witnessY, 0)) h
  exact suTwoWitness_ne_zero hv

theorem flatCurl_constant : flatCurl constantField = 0 := by
  apply (fiberEquiv _).injective
  funext p
  simp [flatCurl, constantField, curlCovariantLM, curlValueCovariant,
    trivialU, RMap_one]

theorem flatDelta_constant : flatDelta constantField = 0 := by
  simp [flatDelta, flatCurl_constant]

/-- A nonzero field of zero bare energy: strict positivity of Delta is FALSE. -/
theorem flatDelta_not_strictly_positive :
    ¬ (∀ A : H, A ≠ 0 → (0 : ℝ) < inner ℝ A (flatDelta A)) := by
  intro hp
  have h := hp constantField constantField_nonzero
  simp [flatDelta_constant] at h

/-- No left inverse, hence no two-sided covariance Delta^{-1} on the full H. -/
theorem flatDelta_no_left_inverse : ¬ ∃ G : H →L[ℝ] H, ∀ A, G (flatDelta A) = A := by
  rintro ⟨G, hG⟩
  have h := hG constantField
  rw [flatDelta_constant, map_zero] at h
  exact constantField_nonzero h.symm

/-- Site-sector Q' at the SAME block size 2, tested only at genuine coarse sites. -/
noncomputable def flatSiteQ : S →ₗ[ℝ] ({y : PeriodicLatticeSite witnessL // y ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice witnessL 2} → SuTwo) :=
  { toFun := fun lam y => AdalyFormal.Balaban.CovariantHjMinimizer.coarseRestrictSiteCovariant
        2 (fiberEquiv _ lam) y.1
    map_add' := by
      intro a b
      funext y
      simp only [map_add, AdalyFormal.Balaban.CovariantHjMinimizer.coarseRestrictSiteCovariant_add]
      rfl
    map_smul' := by
      intro c a
      funext y
      simp only [map_smul, AdalyFormal.Balaban.CovariantHjMinimizer.coarseRestrictSiteCovariant_smul]
      rfl }

/-- The SITE Laplacian (3.23); distinct from the BOND Hessian (3.10). -/
noncomputable def flatSiteDelta : S →L[ℝ] S := flatGrad.adjoint.comp flatGrad

/-- Exact source target of R: Delta_site(ker Q'), CMP99b (3.21). -/
noncomputable def gaugeImage : Submodule ℝ S :=
  (LinearMap.ker flatSiteQ).map flatSiteDelta.toLinearMap

/-- R is the actual orthogonal projection from (3.21), on SITE fields. -/
noncomputable def siteR : S →L[ℝ] S := gaugeImage.starProjection

theorem siteR_idempotent : siteR * siteR = siteR :=
  Submodule.isIdempotentElem_starProjection gaugeImage

theorem siteR_selfAdjoint (x y : S) :
    (inner ℝ (siteR x) y : ℝ) = inner ℝ x (siteR y) :=
  Submodule.inner_starProjection_left_eq_right gaugeImage x y

/-- The second constraint is a map H -> S, NOT the Neumann perturbation H -> H. -/
noncomputable def gaugeConstraint : H →L[ℝ] S := siteR.comp flatGrad.adjoint

/-- Correct candidate precision FORM on the unweighted BFL2 carrier.
Fine volume eta^3=1/8, coarse volume=1: the physical form is
(1/8)*(curl-energy + gauge-energy) + a*(native bond-average energy).
No invertibility/physical covariance is asserted by this definition. -/
noncomputable def basePrecision (a : ℝ) : H →L[ℝ] H :=
  (1 / 8 : ℝ) • (flatDelta + gaugeConstraint.adjoint.comp gaugeConstraint) +
    a • (nativeLinearQ (trivialU witnessL) 2).adjoint.comp
      (nativeLinearQ (trivialU witnessL) 2)

theorem basePrecision_energy (a : ℝ) (A : H) :
    (inner ℝ A (basePrecision a A) : ℝ) =
      (1 / 8 : ℝ) * (‖flatCurl A‖ ^ 2 + ‖gaugeConstraint A‖ ^ 2) +
        a * ‖nativeLinearQ (trivialU witnessL) 2 A‖ ^ 2 := by
  simp only [basePrecision, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, inner_add_right, inner_smul_right,
    flatDelta_energy, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

theorem basePrecision_nonneg (a : ℝ) (ha : 0 ≤ a) (A : H) :
    (0 : ℝ) ≤ inner ℝ A (basePrecision a A) := by
  rw [basePrecision_energy]
  positivity

theorem basePrecision_selfAdjoint (a : ℝ) (A B : H) :
    (inner ℝ (basePrecision a A) B : ℝ) = inner ℝ A (basePrecision a B) := by
  simp only [basePrecision, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right,
    flatDelta_selfAdjoint, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

/-- A localized field has nonzero curvature, unlike the constant null mode. -/
noncomputable def pulseField : H := bfl2Equiv.symm
  (fun b => if b = (witnessY, (0 : Fin 3)) then suTwoWitness else 0)

lemma flatCurl_pulse_nonzero : flatCurl pulseField ≠ 0 := by
  intro hz
  let p : PeriodicLatticePlaquette witnessL := (witnessY, ⟨(0, 1), by decide⟩)
  have h := congrArg (fun F => fiberEquiv _ F p) hz
  have h10 : (periodicLatticeShift witnessY 0, (1 : Fin 3)) ≠ (witnessY, 0) := by decide
  have h01 : (periodicLatticeShift witnessY 1, (0 : Fin 3)) ≠ (witnessY, 0) := by decide
  have hd : (witnessY, (1 : Fin 3)) ≠ (witnessY, 0) := by decide
  have hx : (2 : ℝ) • suTwoWitness = 0 := by
    simpa [flatCurl, pulseField, curlCovariantLM, curlValueCovariant, trivialU,
      RMap_one, p, h10, h01, hd] using h
  exact suTwoWitness_ne_zero ((smul_eq_zero.mp hx).resolve_left (by norm_num))

theorem flatDelta_nonzero : flatDelta ≠ 0 := by
  intro hz
  have h := flatDelta_energy pulseField
  rw [hz, zero_apply, inner_zero_right] at h
  have hn : 0 < ‖flatCurl pulseField‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr flatCurl_pulse_nonzero)
  linarith

end HConstruction.Covariance
