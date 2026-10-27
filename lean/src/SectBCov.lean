import SectBResolvent
import AdalyFormal.Balaban.CoarseRestrictTransported
import AdalyFormal.Balaban.RMapLipschitz
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HConstruction.SectBP1
open HConstruction.GenK HConstruction.SectBBase
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap gradValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoarseRestrictTransported (coarseRestrictSiteCovariantU)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable (M : PeriodicLatticeExtent) {n : ℕ}
abbrev Links := PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (fineExtent M n)

/-- The physical lattice-spacing covariant site gradient of (3.23), on GenK's sites. -/
def covGrad (U : Links M (n := n)) : Site M (n := n) →L[ℝ] Fine M (n := n) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun f => bfl2Equiv.symm (fun b => (n:ℝ) •
      (RMap (U b) (f (periodicLatticeShift b.1 b.2)) - f b.1))
    map_add' := by
      intro f g; apply bfl2Equiv.injective; funext b
      simp only [LinearEquiv.apply_symm_apply, map_add, Pi.add_apply]
      change (n:ℝ) • (RMap (U b) (f (periodicLatticeShift b.1 b.2) + g (periodicLatticeShift b.1 b.2)) - (f b.1 + g b.1)) =
        (n:ℝ) • (RMap (U b) (f (periodicLatticeShift b.1 b.2)) - f b.1) +
        (n:ℝ) • (RMap (U b) (g (periodicLatticeShift b.1 b.2)) - g b.1)
      simp only [map_add]
      module
    map_smul' := by
      intro r f; apply bfl2Equiv.injective; funext b
      simp only [LinearEquiv.apply_symm_apply, map_smul, Pi.smul_apply, RingHom.id_apply]
      change (n:ℝ) • (RMap (U b) (r • f (periodicLatticeShift b.1 b.2)) - r • f b.1) =
        r • ((n:ℝ) • (RMap (U b) (f (periodicLatticeShift b.1 b.2)) - f b.1))
      simp only [map_smul]
      module }

theorem covGrad_apply (U : Links M (n := n)) (f : Site M (n := n))
    (b : Bond (fineExtent M n)) :
    bfl2Equiv (covGrad M U f) b = (n:ℝ) •
      (RMap (U b) (f (periodicLatticeShift b.1 b.2)) - f b.1) := rfl

theorem covGrad_trivialU : covGrad M (trivialU (fineExtent M n)) = grad M := by
  ext f; apply bfl2Equiv.injective; funext b
  rw [covGrad_apply, grad_apply]
  simp [trivialU, AdalyFormal.Balaban.CovariantOperators.RMap_one]

/-- The ordered-staircase single-block transported average, not a replacement for
CMP99b's unresolved hierarchical k-fold contour when k ≥ 2. -/
def covQPrime (U : Links M (n := n)) : Site M (n := n) →L[ℝ] CoarseSites M n :=
  LinearMap.toContinuousLinearMap {
    toFun := fun f => (WithLp.linearEquiv 2 ℝ _).symm
      (fun y => coarseRestrictSiteCovariantU U n (fun x => f x) y.1)
    map_add' := by
      intro f g; apply (WithLp.linearEquiv 2 ℝ _).injective; funext y
      exact AdalyFormal.Balaban.CoarseRestrictTransported.coarseRestrictSiteCovariantU_add U n _ _ _
    map_smul' := by
      intro r f; apply (WithLp.linearEquiv 2 ℝ _).injective; funext y
      exact AdalyFormal.Balaban.CoarseRestrictTransported.coarseRestrictSiteCovariantU_smul U n r _ _ }

theorem covQPrime_apply (U : Links M (n := n)) (f : Site M (n := n))
    (y : Centers M (n := n)) :
    covQPrime M U f y = coarseRestrictSiteCovariantU U n (fun x => f x) y.1 := rfl

theorem covQPrime_trivialU : covQPrime M (trivialU (fineExtent M n)) = flatQPrime M := by
  apply ContinuousLinearMap.ext; intro f
  apply (WithLp.linearEquiv 2 ℝ _).injective
  funext y
  change coarseRestrictSiteCovariantU (trivialU _) n (fun x => f x) y.1 =
    AdalyFormal.Balaban.CovariantHjMinimizer.coarseRestrictSiteCovariant n _ _
  exact AdalyFormal.Balaban.CoarseRestrictTransported.coarseRestrictSiteCovariantU_trivialU n _ _

/-- (3.23)+(3.24), single occupied top stratum, counting-measure version. -/
def covDeltaPrime (U : Links M (n := n)) (k : ℕ) :
    Site M (n := n) →L[ℝ] Site M (n := n) :=
  (covGrad M U).adjoint.comp (covGrad M U) +
    (topWeight k*(n:ℝ)^3) • ((covQPrime M U).adjoint.comp (covQPrime M U))

theorem covDeltaPrime_trivialU (k : ℕ) :
    covDeltaPrime M (trivialU (fineExtent M n)) k = flatDeltaPrime M k := by
  simp [covDeltaPrime, flatDeltaPrime, siteDelta, covGrad_trivialU, covQPrime_trivialU]

theorem covDeltaPrime_form (U : Links M (n := n)) (k : ℕ) (f : Site M (n := n)) :
    (inner ℝ f (covDeltaPrime M U k f) : ℝ) =
      ‖covGrad M U f‖^2 + (topWeight k*(n:ℝ)^3)*‖covQPrime M U f‖^2 := by
  simp only [covDeltaPrime, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    inner_add_right, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]
end HConstruction.SectBP1
