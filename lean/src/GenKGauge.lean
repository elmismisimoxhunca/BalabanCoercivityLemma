import GenKComposite
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace HConstruction.GenK
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU coarseRestrictSiteCovariant coarseRestrictSiteCovariantLM)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)

variable (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n)
attribute [local irreducible] incoming curl H
abbrev Site := PiLp 2 (fun _ : PeriodicLatticeSite (fineExtent M n) => SuTwo)
abbrev Centers := {x : PeriodicLatticeSite (fineExtent M n) // x ∈ CoarseLattice (fineExtent M n) n}

def grad : Site M (n := n) →L[ℝ] Fine M (n := n) := LinearMap.toContinuousLinearMap {
  toFun := fun f => bfl2Equiv.symm (fun b => (n:ℝ) • (f (periodicLatticeShift b.1 b.2) - f b.1))
  map_add' := by
    intro f g; apply bfl2Equiv.injective; funext b
    simp only [LinearEquiv.apply_symm_apply,map_add,Pi.add_apply]
    change (n:ℝ) • ((f _+g _)-(f _+g _)) = _
    module
  map_smul' := by
    intro r f; apply bfl2Equiv.injective; funext b
    simp only [LinearEquiv.apply_symm_apply,map_smul,Pi.smul_apply,RingHom.id_apply]
    change (n:ℝ) • (r • f _ - r • f _) = r • ((n:ℝ) • (f _-f _))
    module }

lemma grad_apply (f : Site M (n := n)) (b : Bond (fineExtent M n)) :
    bfl2Equiv (grad M f) b = (n:ℝ) • (f (periodicLatticeShift b.1 b.2)-f b.1) := rfl

/-- Genuine block-n site average Q', sampled at every coarse center. -/
def siteAverage : Site M (n := n) →ₗ[ℝ] (Centers M (n := n) → SuTwo) :=
  (LinearMap.pi (fun y : Centers M (n := n) => LinearMap.proj y.1)).comp
    ((coarseRestrictSiteCovariantLM (fineExtent M n) n).comp (WithLp.linearEquiv 2 ℝ _).toLinearMap)

lemma siteAverage_apply (f : Site M (n := n)) (y : Centers M (n := n)) :
    siteAverage M f y = coarseRestrictSiteCovariant n (fun x => f x) y.1 := rfl

lemma incoming_grad_kernel (f : Site M (n := n)) (hf : siteAverage M f = 0) :
    incoming M hn (grad M f) = 0 := by
  have hg : bfl2Equiv (grad M f) = (n:ℝ) • gradValueCovariant (trivialU (fineExtent M n)) (fun x => f x) := by
    funext b
    rw [grad_apply]
    simp only [Pi.smul_apply,gradValueCovariant,trivialU,RMap_one,LinearMap.id_apply]
  apply bfl2Equiv.injective; funext b
  rw [incoming_apply]
  rw [← lineCoarseRestrictCov_trivialU,hg,lineCoarseRestrictCov_smul]
  change (n:ℝ) • lineCoarseRestrictCov (trivialU (fineExtent M n)) n
    (gradValueCovariant (trivialU (fineExtent M n)) (fun x => f x)) (sites M hn b.1,b.2) = _
  rw [lineCoarseRestrictCov_gradCovariant_trivialU_intertwines hn (fineTiling M hn b.2) (sites M hn b.1).2]
  have h0 := congrFun hf (sites M hn b.1)
  have h1 := congrFun hf (⟨coarseShift (sites M hn b.1).1 n b.2,
    coarseShift_mem_coarseLattice (fineTiling M hn) (sites M hn b.1).2 b.2⟩ : Centers M (n := n))
  rw [siteAverage_apply] at h0 h1
  simp only [Pi.zero_apply] at h0 h1
  simp only [h0,h1,sub_self,smul_zero,map_zero,Pi.zero_apply]

lemma curl_grad (f : Site M (n := n)) : curl M (grad M f) = 0 := by
  apply (WithLp.linearEquiv 2 ℝ _).injective
  funext p
  change curl M (grad M f) p = 0
  rw [curl_apply]
  unfold flatCurlValue
  simp only [grad_apply]
  rw [AdalyFormal.Balaban.LatticeOperators.periodicLatticeShift_comm p.1 (ne_of_lt p.2.2)]
  module

/-- R is the projection onto Delta_site(ker Q'), exactly the flat gauge geometry. -/
def siteNull : Submodule ℝ (Site M (n := n)) := (siteAverage M (n := n)).ker

def siteDelta : Site M (n := n) →L[ℝ] Site M (n := n) := (grad M).adjoint.comp (grad M)

def restrictedSiteDelta : siteNull M (n := n) →ₗ[ℝ] Site M (n := n) :=
  (siteDelta M).toLinearMap.comp (siteNull M).subtype

def gaugeImage : Submodule ℝ (Site M (n := n)) := (restrictedSiteDelta M).range

def R : Site M (n := n) →L[ℝ] Site M (n := n) := (gaugeImage M).starProjection

def gaugeConstraint : Fine M (n := n) →L[ℝ] Site M (n := n) := (R M).comp (grad M).adjoint

def gaugeSection : gaugeImage M (n := n) →ₗ[ℝ] siteNull M (n := n) :=
  Classical.choose ((restrictedSiteDelta M).rangeRestrict.exists_rightInverse_of_surjective
    (restrictedSiteDelta M).range_rangeRestrict)

lemma gaugeSection_right (v : gaugeImage M (n := n)) :
    restrictedSiteDelta M (gaugeSection M v) = v := by
  have h := Classical.choose_spec ((restrictedSiteDelta M (n := n)).rangeRestrict.exists_rightInverse_of_surjective
    (restrictedSiteDelta M).range_rangeRestrict)
  exact congrArg Subtype.val (LinearMap.congr_fun h v)

def gaugePotential : Fine M (n := n) →L[ℝ] Site M (n := n) :=
  (siteNull M).subtypeL.comp ((gaugeSection M).toContinuousLinearMap.comp
    ((gaugeImage M).orthogonalProjectionOnto.comp (grad M).adjoint))

def gaugePi : Fine M (n := n) →L[ℝ] Fine M (n := n) :=
  ContinuousLinearMap.id ℝ _ - (grad M).comp (gaugePotential M)

lemma potential_kernel (A : Fine M (n := n)) : siteAverage M (gaugePotential M A) = 0 :=
  (gaugeSection M ((gaugeImage M).orthogonalProjectionOnto ((grad M).adjoint A))).2

lemma potential_laplacian (A : Fine M (n := n)) :
    siteDelta M (gaugePotential M A) = R M ((grad M).adjoint A) := gaugeSection_right M _

lemma gaugePi_incoming (A : Fine M (n := n)) : incoming M hn (gaugePi M A) = incoming M hn A := by
  change incoming M hn (A-grad M (gaugePotential M A)) = _
  rw [map_sub,incoming_grad_kernel M hn _ (potential_kernel M A),sub_zero]

lemma gaugePi_curl (A : Fine M (n := n)) : curl M (gaugePi M A) = curl M A := by
  change curl M (A-grad M (gaugePotential M A)) = _
  rw [map_sub,curl_grad,sub_zero]

lemma gaugePi_feasible (A : Fine M (n := n)) : gaugeConstraint M (gaugePi M A) = 0 := by
  change R M ((grad M).adjoint (A-grad M (gaugePotential M A))) = 0
  rw [map_sub,map_sub]
  change R M ((grad M).adjoint A) - R M (siteDelta M (gaugePotential M A)) = 0
  rw [potential_laplacian]
  have hid := congrArg (fun T : Site M (n := n) →L[ℝ] Site M (n := n) => T ((grad M).adjoint A))
    (Submodule.isIdempotentElem_starProjection (gaugeImage M))
  change R M (R M ((grad M).adjoint A)) = R M ((grad M).adjoint A) at hid
  rw [hid,sub_self]

/-- The genuine flat simultaneous minimizer; both incoming and gauge constraints
are proved, with no assumed Ward identity. -/
def physicalH : Unit M →L[ℝ] Fine M (n := n) := (gaugePi M).comp (H M hn)

theorem physicalH_Q (B : Unit M) : incoming M hn (physicalH M hn B) = B := by
  rw [physicalH,ContinuousLinearMap.comp_apply,gaugePi_incoming,H_interpolates]

theorem physicalH_gauge (B : Unit M) : gaugeConstraint M (physicalH M hn B) = 0 :=
  gaugePi_feasible M _

/-- Same Delta, now an exact pullback through the gauge-feasible minimizer. -/
theorem physical_pullback (B : Unit M) :
    (inner ℝ B (Delta M hn B) : ℝ) = fineEnergy M (physicalH M hn B) := by
  rw [pullback,fineEnergy,fineEnergy]
  change _ = (1/(n:ℝ))*‖curl M (gaugePi M (H M hn B))‖^2
  rw [gaugePi_curl]

theorem simultaneous_minimum (B : Unit M) :
    incoming M hn (physicalH M hn B) = B ∧ gaugeConstraint M (physicalH M hn B) = 0 ∧
    ∀ A : Fine M (n := n), incoming M hn A = B → gaugeConstraint M A = 0 →
      fineEnergy M (physicalH M hn B) ≤ fineEnergy M A := by
  refine ⟨physicalH_Q M hn B,physicalH_gauge M hn B,?_⟩
  intro A hq _
  rw [← physical_pullback,pullback]
  exact minimum M hn A B hq

/-- Flat (3.128) with a=1: curl energy, physical gauge penalty, and mass.
The source vanishes at U=1; no mass subtraction is dropped. -/
def massiveAction (A : Fine M (n := n)) : ℝ := fineEnergy M A +
  (1/(n:ℝ)^3)*‖gaugeConstraint M A‖^2 + ‖incoming M hn A‖^2

lemma massive_at_minimum (B : Unit M) : massiveAction M hn (physicalH M hn B) =
    (inner ℝ B (Delta M hn B) : ℝ) + ‖B‖^2 := by
  rw [massiveAction,physicalH_gauge,physicalH_Q,norm_zero,zero_pow (by decide : 2 ≠ 0),
    mul_zero,add_zero,← physical_pullback]

/-- The full gauge-extended massive minimum, with all feasibility gates paid.
Subtracting the mass recovers exactly the pullback Delta, not Delta minus mass. -/
theorem massive_minimum (A : Fine M (n := n)) (B : Unit M)
    (hq : incoming M hn A = B) :
    massiveAction M hn (physicalH M hn B) ≤ massiveAction M hn A := by
  have h := minimum M hn A B hq
  rw [massive_at_minimum,pullback,massiveAction,hq]
  have hg : (0:ℝ) ≤ (1/(n:ℝ)^3)*‖gaugeConstraint M A‖^2 := by positivity
  linarith

#print axioms massive_at_minimum
#print axioms massive_minimum
#print axioms incoming_grad_kernel
#print axioms curl_grad
#print axioms gaugePi_feasible
#print axioms physical_pullback
#print axioms simultaneous_minimum
end HConstruction.GenK
