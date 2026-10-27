import WorkingCovariance
import GaugeSection

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
noncomputable section
namespace HConstruction.G0CoerceFinal
open HConstruction.Covariance HConstruction.SmallNF HConstruction.TransversePos
open HConstruction.DRepair HConstruction.Nonflat
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

section Lift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A linear lift of the actual orthogonal projection onto L(N). No injectivity
or invertibility is postulated. Nonuniqueness in ker L will disappear after D. -/
theorem projection_lift_exists (L : E →L[ℝ] E) (N : Submodule ℝ E) :
    ∃ V : E →L[ℝ] E, (∀ x, V x ∈ N) ∧
      (∀ x, L (V x) = (N.map L.toLinearMap).starProjection x) := by
  let M := N.map L.toLinearMap
  let F : N →ₗ[ℝ] M := {
    toFun := fun x => ⟨L x, ⟨x, x.property, rfl⟩⟩
    map_add' := fun x y => Subtype.ext (map_add L (x : E) (y : E))
    map_smul' := fun r x => Subtype.ext (map_smul L r (x : E)) }
  have hF : LinearMap.range F = ⊤ := LinearMap.range_eq_top.mpr (by
    intro y
    obtain ⟨x,hx,hxy⟩ := y.property
    exact ⟨⟨x,hx⟩, Subtype.ext hxy⟩)
  obtain ⟨G,hG⟩ := F.exists_rightInverse_of_surjective hF
  let R : E →ₗ[ℝ] M := {
    toFun := fun x => ⟨M.starProjection x, Submodule.starProjection_apply_mem M x⟩
    map_add' := fun x y => Subtype.ext (map_add M.starProjection x y)
    map_smul' := fun r x => Subtype.ext (map_smul M.starProjection r x) }
  refine ⟨(N.subtype.comp (G.comp R)).toContinuousLinearMap, ?_, ?_⟩
  · intro x
    exact (G (R x)).property
  · intro x
    exact congrArg Subtype.val (LinearMap.congr_fun hG (R x))
end Lift

abbrev Background := PeriodicLinkConfiguration SU2 witnessL

/-- The site potential solving L lambda = R x with Q' lambda = 0.
Only D lambda, and not an arbitrary choice of lambda, is used below. -/
def gaugePotential (U : Background) : S →L[ℝ] S :=
  Classical.choose (projection_lift_exists (siteDeltaU U) (LinearMap.ker (siteQU U)))

theorem gaugePotential_kernel (U : Background) (X : S) :
    siteQU U (gaugePotential U X) = 0 :=
  (Classical.choose_spec (projection_lift_exists (siteDeltaU U)
    (LinearMap.ker (siteQU U)))).1 X

theorem gaugePotential_solve (U : Background) (X : S) :
    siteDeltaU U (gaugePotential U X) = siteRU U X :=
  (Classical.choose_spec (projection_lift_exists (siteDeltaU U)
    (LinearMap.ker (siteQU U)))).2 X

attribute [local irreducible] gaugePotential

/-- The bond operator in (3.119), NOT the orthogonal bond gauge projector and
NOT the Neumann perturbation. It uses the actual site R and actual covariant D. -/
def gaugePi (U : Background) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H -
    (covGrad U).comp ((gaugePotential U).comp (covGrad U).adjoint)

theorem gaugePi_apply (U : Background) (A : H) :
    gaugePi U A = A - covGrad U (gaugePotential U ((covGrad U).adjoint A)) := rfl

theorem covGrad_eq_of_siteDelta_eq (U : Background) (X Y : S)
    (h : siteDeltaU U X = siteDeltaU U Y) : covGrad U X = covGrad U Y := by
  have hz : siteDeltaU U (X-Y) = 0 := by rw [map_sub, h, sub_self]
  have he : (inner ℝ (X-Y) (siteDeltaU U (X-Y)) : ℝ) = 0 := by rw [hz, inner_zero_right]
  change inner ℝ (X-Y) ((covGrad U).adjoint (covGrad U (X-Y))) = 0 at he
  rw [ContinuousLinearMap.adjoint_inner_right] at he
  exact sub_eq_zero.mp (by simpa only [map_sub] using (inner_self_eq_zero.mp he))

/-- Canonical source identification: any Q'-null solution of the site equation
gives exactly this Pi. Thus the choice of linear lift cannot change Pi. -/
theorem gaugePi_eq_of_solution (U : Background) (A : H) (X : S)
    (hX : siteDeltaU U X = gaugeConstraintU U A) :
    gaugePi U A = A - covGrad U X := by
  rw [gaugePi_apply]
  congr 1
  apply covGrad_eq_of_siteDelta_eq
  rw [gaugePotential_solve]
  exact hX.symm

theorem gaugePi_constraint (U : Background) (A : H) :
    gaugeConstraintU U (gaugePi U A) = 0 := by
  have hR : siteRU U (siteRU U ((covGrad U).adjoint A)) =
      siteRU U ((covGrad U).adjoint A) :=
    congrArg (fun T : S →L[ℝ] S => T ((covGrad U).adjoint A)) (siteRU_idempotent U)
  rw [gaugePi_apply]
  change siteRU U ((covGrad U).adjoint (A - covGrad U (gaugePotential U ((covGrad U).adjoint A)))) = 0
  rw [map_sub, map_sub]
  change siteRU U ((covGrad U).adjoint A) -
    siteRU U (siteDeltaU U (gaugePotential U ((covGrad U).adjoint A))) = 0
  rw [gaugePotential_solve, hR, sub_self]

theorem gaugePi_slice (U : Background) (A : H) (hA : gaugeConstraintU U A = 0) :
    gaugePi U A = A := by
  have h := gaugePi_eq_of_solution U A 0 (by simpa only [map_zero] using hA.symm)
  simpa only [map_zero, sub_zero] using h

theorem gaugePi_idempotent (U : Background) : (gaugePi U).comp (gaugePi U) = gaugePi U := by
  ext A
  exact gaugePi_slice U _ (gaugePi_constraint U A)

theorem gaugePi_gauge_zero (U : Background) (X : S) (hX : siteQU U X = 0) :
    gaugePi U (covGrad U X) = 0 := by
  have hm : siteDeltaU U X ∈ gaugeImageU U := ⟨X,hX,rfl⟩
  have he : siteRU U (siteDeltaU U X) = siteDeltaU U X :=
    Submodule.starProjection_eq_self_iff.mpr hm
  rw [gaugePi_eq_of_solution U (covGrad U X) X he.symm, sub_self]

/-- Exact gauge-extended Hessian (3.119). -/
def deltaPi (U : Background) : H →L[ℝ] H :=
  (gaugePi U).adjoint.comp ((deltaU U).comp (gaugePi U))

/-- The FIRST source Neumann correction (3.120); it is not correctionBil. -/
def deltaPrimePi (U : Background) : H →L[ℝ] H := deltaU U - deltaPi U

theorem deltaPi_bilinear (U : Background) (A B : H) :
    (inner ℝ A (deltaPi U B) : ℝ) = inner ℝ (gaugePi U A) (deltaU U (gaugePi U B)) := by
  change (inner ℝ A ((gaugePi U).adjoint (deltaU U (gaugePi U B))) : ℝ) = _
  rw [ContinuousLinearMap.adjoint_inner_right]

theorem deltaPi_selfAdjoint (U : Background) (A B : H) :
    (inner ℝ (deltaPi U A) B : ℝ) = inner ℝ A (deltaPi U B) := by
  rw [real_inner_comm, deltaPi_bilinear, ← deltaU_selfAdjoint, real_inner_comm,
    ← deltaPi_bilinear]

theorem deltaPrimePi_selfAdjoint (U : Background) (A B : H) :
    (inner ℝ (deltaPrimePi U A) B : ℝ) = inner ℝ A (deltaPrimePi U B) := by
  simp only [deltaPrimePi, _root_.sub_apply, inner_sub_left, inner_sub_right,
    deltaU_selfAdjoint, deltaPi_selfAdjoint]

theorem deltaPi_slice_energy (U : Background) (A : H)
    (hA : gaugeConstraintU U A = 0) :
    (inner ℝ A (deltaPi U A) : ℝ) = inner ℝ A (deltaU U A) := by
  rw [deltaPi_bilinear, gaugePi_slice U A hA]

theorem deltaU_flat_bilinear (A B : H) :
    (inner ℝ A (deltaU (trivialU witnessL) B) : ℝ) = inner ℝ (flatCurl A) (flatCurl B) := by
  simp only [deltaU, _root_.add_apply, inner_add_right, inner_fromBil,
    correction_flat_zero, add_zero, curlSquare, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem flatCurl_gaugePi (A : H) :
    flatCurl (gaugePi (trivialU witnessL) A) = flatCurl A := by
  rw [gaugePi_apply, map_sub]
  change flatCurl A - flatCurl (flatGrad _) = flatCurl A
  rw [flatCurl_grad, sub_zero]

/-- The source gauge-extension correction really vanishes at flat background. -/
theorem deltaPrimePi_flat : deltaPrimePi (trivialU witnessL) = 0 := by
  ext A
  apply ext_inner_left ℝ
  intro B
  simp only [deltaPrimePi, _root_.sub_apply, inner_sub_right, deltaPi_bilinear,
    deltaU_flat_bilinear, flatCurl_gaugePi, sub_self, _root_.zero_apply,
    inner_zero_right]

#print axioms projection_lift_exists
#print axioms gaugePi_constraint
#print axioms gaugePi_eq_of_solution
#print axioms gaugePi_gauge_zero
#print axioms deltaPrimePi_flat
end HConstruction.G0CoerceFinal
