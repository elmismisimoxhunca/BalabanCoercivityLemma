import DK3FinePrecision
set_option autoImplicit false
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.DK3.FineScale.Physical
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open HConstruction.SmallNF.Reproduced
variable {L : PeriodicLatticeExtent}
theorem flat_reHolonomy (p : PeriodicLatticePlaquette L) :
    reHolonomy (trivialU L) p = 1 := by
  simp [reHolonomy, holonomyElemInv, holonomyElem, periodicPlaquetteHolonomy, AdalyFormal.Balaban.CovariantHjMinimizer.trivialU]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

theorem flat_imHolonomy (p : PeriodicLatticePlaquette L) :
    imHolonomy (trivialU L) p = 0 := by
  simp [imHolonomy, holonomyElemInv, holonomyElem, periodicPlaquetteHolonomy, AdalyFormal.Balaban.CovariantHjMinimizer.trivialU]

theorem correction_flat_zero (A B : H L) : correctionBil (trivialU L) A B = 0 := by
  simp only [correctionBil_apply, deltaPrimeBil_apply, deltaPrimeBilRaw_apply,
    bilPlaq_apply, firstBilPlaq_apply, secondBilPlaq_apply, pairBil_apply,
    flat_reHolonomy, flat_imHolonomy, sub_self, mul_zero, Matrix.trace_zero,
    Complex.zero_re, add_zero, Finset.sum_const_zero]

theorem deltaU_flat_energy (A : H L) :
    (inner ℝ A (deltaU (trivialU L) A) : ℝ) = ‖covCurl (trivialU L) A‖^2 := by
  simp only [deltaU, _root_.add_apply, inner_add_right, inner_fromBil, correction_flat_zero,
    add_zero, curlSquare_energy]
theorem flatCurl_grad (f : S L) : covCurl (trivialU L) (covGrad (trivialU L) f) = 0 := by
  apply (HConstruction.Covariance.fiberEquiv _).injective
  funext p
  simp [covCurl,covGrad,AdalyFormal.Balaban.CovariantOperators.curlCovariantLM,
    AdalyFormal.Balaban.CovariantOperators.curlValueCovariant,
    AdalyFormal.Balaban.CovariantOperators.gradCovariantLM,
    AdalyFormal.Balaban.CovariantOperators.gradValueCovariant,
    AdalyFormal.Balaban.CovariantHjMinimizer.trivialU,
    AdalyFormal.Balaban.CovariantOperators.RMap_one]
  rw [AdalyFormal.Balaban.LatticeOperators.periodicLatticeShift_comm p.1 (ne_of_lt p.2.2)]
  module

theorem deltaU_flat_bilinear (A B : H L) :
    (inner ℝ A (deltaU (trivialU L) B) : ℝ) =
      inner ℝ (covCurl (trivialU L) A) (covCurl (trivialU L) B) := by
  simp only [deltaU, _root_.add_apply, inner_add_right, inner_fromBil,
    correction_flat_zero, add_zero, curlSquare, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

end HConstruction.DK3.FineScale.Physical
namespace HConstruction.DK3.FineScale
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open Physical (covGrad covCurl deltaU siteDeltaU deltaU_selfAdjoint deltaU_flat_bilinear flatCurl_grad)
/-- The site potential solving L lambda = R x with Q' lambda = 0.
Only D lambda, and not an arbitrary choice of lambda, is used below. -/
def gaugePotential (t : ℝ) : SF →L[ℝ] SF :=
  Classical.choose (HConstruction.G0CoerceFinal.projection_lift_exists (siteDeltaU (U t)) (LinearMap.ker (siteQU t)))

theorem gaugePotential_kernel (t : ℝ) (X : SF) :
    siteQU t (gaugePotential t X) = 0 :=
  (Classical.choose_spec (HConstruction.G0CoerceFinal.projection_lift_exists (siteDeltaU (U t))
    (LinearMap.ker (siteQU t)))).1 X

theorem gaugePotential_solve (t : ℝ) (X : SF) :
    siteDeltaU (U t) (gaugePotential t X) = siteRU t X :=
  (Classical.choose_spec (HConstruction.G0CoerceFinal.projection_lift_exists (siteDeltaU (U t))
    (LinearMap.ker (siteQU t)))).2 X

attribute [local irreducible] gaugePotential

/-- The bond operator in (3.119), NOT the orthogonal bond gauge projector and
NOT the Neumann perturbation. It uses the actual site R and actual covariant D. -/
def gaugePi (t : ℝ) : F →L[ℝ] F :=
  ContinuousLinearMap.id ℝ (F) -
    (covGrad (U t)).comp ((gaugePotential t).comp (covGrad (U t)).adjoint)

theorem gaugePi_apply (t : ℝ) (A : F) :
    gaugePi t A = A - covGrad (U t) (gaugePotential t ((covGrad (U t)).adjoint A)) := rfl

theorem covGrad_eq_of_siteDelta_eq (t : ℝ) (X Y : SF)
    (h : siteDeltaU (U t) X = siteDeltaU (U t) Y) : covGrad (U t) X = covGrad (U t) Y := by
  have hz : siteDeltaU (U t) (X-Y) = 0 := by rw [map_sub, h, sub_self]
  have he : (inner ℝ (X-Y) (siteDeltaU (U t) (X-Y)) : ℝ) = 0 := by rw [hz, inner_zero_right]
  change inner ℝ (X-Y) ((covGrad (U t)).adjoint (covGrad (U t) (X-Y))) = 0 at he
  rw [ContinuousLinearMap.adjoint_inner_right] at he
  exact sub_eq_zero.mp (by simpa only [map_sub] using (inner_self_eq_zero.mp he))

/-- Canonical source identification: any Q'-null solution of the site equation
gives exactly this Pi. Thus the choice of linear lift cannot change Pi. -/
theorem gaugePi_eq_of_solution (t : ℝ) (A : F) (X : SF)
    (hX : siteDeltaU (U t) X = gaugeConstraintU t A) :
    gaugePi t A = A - covGrad (U t) X := by
  rw [gaugePi_apply]
  congr 1
  apply covGrad_eq_of_siteDelta_eq
  rw [gaugePotential_solve]
  exact hX.symm

theorem gaugePi_constraint (t : ℝ) (A : F) :
    gaugeConstraintU t (gaugePi t A) = 0 := by
  have hR : siteRU t (siteRU t ((covGrad (U t)).adjoint A)) =
      siteRU t ((covGrad (U t)).adjoint A) :=
    congrArg (fun T : SF →L[ℝ] SF => T ((covGrad (U t)).adjoint A)) (siteRU_idempotent t)
  rw [gaugePi_apply]
  change siteRU t ((covGrad (U t)).adjoint (A - covGrad (U t) (gaugePotential t ((covGrad (U t)).adjoint A)))) = 0
  rw [map_sub, map_sub]
  change siteRU t ((covGrad (U t)).adjoint A) -
    siteRU t (siteDeltaU (U t) (gaugePotential t ((covGrad (U t)).adjoint A))) = 0
  rw [gaugePotential_solve, hR, sub_self]

theorem gaugePi_slice (t : ℝ) (A : F) (hA : gaugeConstraintU t A = 0) :
    gaugePi t A = A := by
  have h := gaugePi_eq_of_solution t A 0 (by simpa only [map_zero] using hA.symm)
  simpa only [map_zero, sub_zero] using h

theorem gaugePi_idempotent (t : ℝ) : (gaugePi t).comp (gaugePi t) = gaugePi t := by
  ext A
  exact gaugePi_slice t _ (gaugePi_constraint t A)

theorem gaugePi_gauge_zero (t : ℝ) (X : SF) (hX : siteQU t X = 0) :
    gaugePi t (covGrad (U t) X) = 0 := by
  have hm : siteDeltaU (U t) X ∈ gaugeImageU t := ⟨X,hX,rfl⟩
  have he : siteRU t (siteDeltaU (U t) X) = siteDeltaU (U t) X :=
    Submodule.starProjection_eq_self_iff.mpr hm
  rw [gaugePi_eq_of_solution t (covGrad (U t) X) X he.symm, sub_self]

attribute [local irreducible] gaugePi deltaU covGrad siteQU

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
def sandwich (P D : E →L[ℝ] E) : E →L[ℝ] E := P.adjoint.comp (D.comp P)
theorem sandwich_bilinear (P D : E →L[ℝ] E) (A B : E) :
    (inner ℝ A (sandwich P D B) : ℝ) = inner ℝ (P A) (D (P B)) :=
  ContinuousLinearMap.adjoint_inner_right P A (D (P B))
end Algebra

/-- Exact gauge-extended Hessian (3.119). -/
def deltaPi (t : ℝ) : F →L[ℝ] F := sandwich (gaugePi t) (deltaU (U t))

/-- The FIRST source Neumann correction (3.120); it is not correctionBil. -/
def deltaPrimePi (t : ℝ) : F →L[ℝ] F := deltaU (U t) - deltaPi t

theorem deltaPi_bilinear (t : ℝ) (A B : F) :
    (inner ℝ A (deltaPi t B) : ℝ) = inner ℝ (gaugePi t A) (deltaU (U t) (gaugePi t B)) :=
  sandwich_bilinear (gaugePi t) (deltaU (U t)) A B

theorem deltaPi_selfAdjoint (t : ℝ) (A B : F) :
    (inner ℝ (deltaPi t A) B : ℝ) = inner ℝ A (deltaPi t B) := by
  rw [real_inner_comm, deltaPi_bilinear, ← deltaU_selfAdjoint, real_inner_comm,
    ← deltaPi_bilinear]

theorem deltaPrimePi_selfAdjoint (t : ℝ) (A B : F) :
    (inner ℝ (deltaPrimePi t A) B : ℝ) = inner ℝ A (deltaPrimePi t B) := by
  simp only [deltaPrimePi, _root_.sub_apply, inner_sub_left, inner_sub_right,
    deltaU_selfAdjoint, deltaPi_selfAdjoint]

theorem deltaPi_slice_energy (t : ℝ) (A : F)
    (hA : gaugeConstraintU t A = 0) :
    (inner ℝ A (deltaPi t A) : ℝ) = inner ℝ A (deltaU (U t) A) := by
  rw [deltaPi_bilinear, gaugePi_slice t A hA]

theorem flatCurl_gaugePi (A : F) :
    covCurl (trivialU fineL) (gaugePi 0 A) = covCurl (trivialU fineL) A := by
  rw [gaugePi_apply, U_zero, map_sub, flatCurl_grad, sub_zero]

theorem deltaPrimePi_zero : deltaPrimePi 0 = 0 := by
  ext A
  apply ext_inner_left ℝ
  intro B
  simp only [deltaPrimePi, _root_.sub_apply, inner_sub_right, deltaPi_bilinear,
    U_zero, deltaU_flat_bilinear, flatCurl_gaugePi, sub_self, _root_.zero_apply, inner_zero_right]

#print axioms gaugePi_constraint
#print axioms gaugePi_gauge_zero
#print axioms deltaPrimePi_zero
end HConstruction.DK3.FineScale
