import CircleActions
import SourcePrecision
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
namespace HConstruction.Circle
open HConstruction.NfRepair.Reproduced HConstruction.SmallNF
open HConstruction.Covariance HConstruction.Nonflat
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL Bond blockOf)
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)

def axisLM : SuTwo →ₗ[ℝ] ℝ where
  toFun := axisCoord
  map_add' X Y := by simp [axisCoord]
  map_smul' r X := by simp [axisCoord, Complex.real_smul]

def axisProjection : SuTwo →ₗ[ℝ] SuTwo := (LinearMap.toSpanSingleton ℝ SuTwo pauliE2).comp axisLM

@[simp] theorem axisProjection_apply (X : SuTwo) :
    axisProjection X = axisCoord X • pauliE2 := rfl

@[simp] theorem axisCoord_axis (a : ℝ) : axisCoord (a • pauliE2) = a := by
  simpa [assemble] using axisCoord_assemble 0 a 0

@[simp] theorem transverseCoord_axis (a : ℝ) : transverseCoord (a • pauliE2) = 0 := by
  change transverseCoord (a • pauliE2) = (⟨0, 0⟩ : ℂ)
  simpa [assemble] using transverseCoord_assemble 0 a 0

def transverseProjection : SuTwo →ₗ[ℝ] SuTwo := LinearMap.id - axisProjection

/-- The one-link adjoint fixes the axial part and cannot mix either sector. -/
theorem nonflat_link_axis (t : ℝ) (b : Bond witnessL) (X : SuTwo) :
    RMap (nonflatU t b) (axisProjection X) = axisProjection X ∧
    axisProjection (RMap (nonflatU t b) X) = axisProjection X := by
  by_cases hb : b = (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, 0)
  · rw [hb, nonflatU_at_x_mu]
    constructor
    · exact RMap_rot_axis t _
    · simp only [axisProjection_apply, (RMap_rot_coordinates t X).1]
  · rw [nonflatU_elsewhere _ hb, RMap_one]
    exact ⟨rfl,rfl⟩

theorem rot_pow_axis (t : ℝ) (n : ℕ) (X : SuTwo) :
    RMap ((rotElem t)^n) (axisProjection X) = axisProjection X ∧
    axisProjection (RMap ((rotElem t)^n) X) = axisProjection X := by
  induction n generalizing X with
  | zero => simp [RMap_one]
  | succ n ih =>
    rw [pow_succ, RMap_mul]
    change RMap ((rotElem t)^n) (RMap (rotElem t) (axisProjection X)) = _ ∧
      axisProjection (RMap ((rotElem t)^n) (RMap (rotElem t) X)) = _
    constructor
    · rw [axisProjection_apply, RMap_rot_axis]
      exact (ih X).1
    · have h := ih (RMap (rotElem t) X)
      rw [h.2]
      simp only [axisProjection_apply, (RMap_rot_coordinates t X).1]

def siteAxis : S →ₗ[ℝ] S :=
  (fiberEquiv (PeriodicLatticeSite witnessL)).symm.toLinearMap.comp
    ((LinearMap.pi fun x => axisProjection.comp (LinearMap.proj x)).comp
      (fiberEquiv _).toLinearMap)

def bondAxis : H →ₗ[ℝ] H :=
  bfl2Equiv.symm.toLinearMap.comp
    ((LinearMap.pi fun b => axisProjection.comp (LinearMap.proj b)).comp bfl2Equiv.toLinearMap)

@[simp] theorem siteAxis_value (X : S) (x : PeriodicLatticeSite witnessL) :
    fiberEquiv _ (siteAxis X) x = axisProjection (fiberEquiv _ X x) := rfl

@[simp] theorem bondAxis_value (X : H) (b : Bond witnessL) :
    bfl2Equiv (bondAxis X) b = axisProjection (bfl2Equiv X b) := rfl

theorem covGrad_value (U : PeriodicLinkConfiguration SU2 witnessL) (X : S) (b : Bond witnessL) :
    bfl2Equiv (covGrad U X) b =
      (2:ℝ) • (RMap (U b) (fiberEquiv _ X (periodicLatticeShift b.1 b.2)) - fiberEquiv _ X b.1) := by
  rfl

/-- Exact factor two retained, on actual Hilbert carriers. -/
theorem covGrad_axis_flat (t : ℝ) (X : S) :
    covGrad (nonflatU t) (siteAxis X) = flatGrad (siteAxis X) := by
  apply bfl2Equiv.injective
  funext b
  rw [← covGrad_flat, covGrad_value, covGrad_value, siteAxis_value, siteAxis_value]
  rw [(nonflat_link_axis t b _).1]
  simp [trivialU, RMap_one]

theorem covGrad_axis_commute (t : ℝ) (X : S) :
    covGrad (nonflatU t) (siteAxis X) = bondAxis (covGrad (nonflatU t) X) := by
  apply bfl2Equiv.injective
  funext b
  rw [bondAxis_value, covGrad_value, covGrad_value, siteAxis_value, siteAxis_value]
  simp only [map_smul, map_sub]
  rw [(nonflat_link_axis t b _).1, (nonflat_link_axis t b _).2]

def siteTransverse : S →ₗ[ℝ] S := LinearMap.id - siteAxis
def bondTransverse : H →ₗ[ℝ] H := LinearMap.id - bondAxis

theorem covGrad_transverse_commute (t : ℝ) (X : S) :
    covGrad (nonflatU t) (siteTransverse X) = bondTransverse (covGrad (nonflatU t) X) := by
  change covGrad (nonflatU t) (X - siteAxis X) = covGrad (nonflatU t) X - bondAxis (covGrad (nonflatU t) X)
  rw [map_sub, covGrad_axis_commute]

@[simp] theorem axisProjection_idempotent (X : SuTwo) :
    axisProjection (axisProjection X) = axisProjection X := by
  simp only [axisProjection_apply, axisCoord_axis]

theorem axisProjection_selfAdjoint (X Y : SuTwo) :
    (inner ℝ (axisProjection X) Y : ℝ) = inner ℝ X (axisProjection Y) := by
  simp only [inner_axis_transverse, axisProjection_apply, axisCoord_axis,
    transverseCoord_axis]
  simp

@[simp] theorem siteAxis_idempotent (X : S) : siteAxis (siteAxis X) = siteAxis X := by
  apply (fiberEquiv _).injective
  funext x
  simp only [siteAxis_value, axisProjection_idempotent]

@[simp] theorem bondAxis_idempotent (X : H) : bondAxis (bondAxis X) = bondAxis X := by
  apply bfl2Equiv.injective
  funext b
  simp only [bondAxis_value, axisProjection_idempotent]

theorem siteAxis_selfAdjoint (X Y : S) :
    (inner ℝ (siteAxis X) Y : ℝ) = inner ℝ X (siteAxis Y) := by
  change (∑ x, inner ℝ (axisProjection (fiberEquiv _ X x)) (fiberEquiv _ Y x)) =
    ∑ x, inner ℝ (fiberEquiv _ X x) (axisProjection (fiberEquiv _ Y x))
  exact Finset.sum_congr rfl (fun x _ => axisProjection_selfAdjoint _ _)

theorem bondAxis_selfAdjoint (X Y : H) :
    (inner ℝ (bondAxis X) Y : ℝ) = inner ℝ X (bondAxis Y) := by
  change (∑ b, inner ℝ (axisProjection (bfl2Equiv X b)) (bfl2Equiv Y b)) =
    ∑ b, inner ℝ (bfl2Equiv X b) (axisProjection (bfl2Equiv Y b))
  exact Finset.sum_congr rfl (fun b _ => axisProjection_selfAdjoint _ _)

theorem covGrad_adjoint_axis_commute (t : ℝ) (A : H) :
    (covGrad (nonflatU t)).adjoint (bondAxis A) =
      siteAxis ((covGrad (nonflatU t)).adjoint A) := by
  apply ext_inner_left ℝ
  intro X
  rw [ContinuousLinearMap.adjoint_inner_right, ← bondAxis_selfAdjoint,
    ← covGrad_axis_commute, ← ContinuousLinearMap.adjoint_inner_right,
    siteAxis_selfAdjoint]

theorem siteDelta_axis_commute (t : ℝ) (X : S) :
    siteDeltaU (nonflatU t) (siteAxis X) = siteAxis (siteDeltaU (nonflatU t) X) := by
  simp only [siteDeltaU, ContinuousLinearMap.comp_apply, covGrad_axis_commute,
    covGrad_adjoint_axis_commute]

def coarseSiteAxis : (CS → SuTwo) →ₗ[ℝ] (CS → SuTwo) :=
  LinearMap.pi fun y => axisProjection.comp (LinearMap.proj y)

theorem siteQU_value (U : PeriodicLinkConfiguration SU2 witnessL) (X : S) (y : CS) :
    siteQU U X y = (1/8 : ℝ) • ∑ x ∈ blockOf y.1 2,
      RMap (coarsePathHolonomy 1 U y.1 (coarseGammaPath 1 y.1 x)) (fiberEquiv _ X x) := by
  simp [siteQU, LinearMap.sum_apply]

theorem siteQU_axis_commute (t : ℝ) (X : S) :
    siteQU (nonflatU t) (siteAxis X) = coarseSiteAxis (siteQU (nonflatU t) X) := by
  funext y
  change siteQU (nonflatU t) (siteAxis X) y = axisProjection (siteQU (nonflatU t) X y)
  simp only [siteQU_value, siteAxis_value, map_smul, map_sum, path_word]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [(rot_pow_axis t _ _).1, (rot_pow_axis t _ _).2]

theorem siteQU_axis_flat (t : ℝ) (X : S) :
    siteQU (nonflatU t) (siteAxis X) = siteQU (trivialU witnessL) (siteAxis X) := by
  funext y
  simp only [siteQU_value, siteAxis_value, path_word]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [(rot_pow_axis t _ _).1]
  simp only [AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy_trivialU,
    RMap_one, LinearMap.id_apply]

theorem siteAxis_transverse_orthogonal (X Y : S) :
    (inner ℝ (siteAxis X) (siteTransverse Y) : ℝ) = 0 := by
  change inner ℝ (siteAxis X) (Y - siteAxis Y) = 0
  rw [inner_sub_right, ← siteAxis_selfAdjoint, siteAxis_idempotent, sub_self]

theorem bondAxis_transverse_orthogonal (X Y : H) :
    (inner ℝ (bondAxis X) (bondTransverse Y) : ℝ) = 0 := by
  change inner ℝ (bondAxis X) (Y - bondAxis Y) = 0
  rw [inner_sub_right, ← bondAxis_selfAdjoint, bondAxis_idempotent, sub_self]

theorem covGrad_adjoint_transverse_commute (t : ℝ) (A : H) :
    (covGrad (nonflatU t)).adjoint (bondTransverse A) =
      siteTransverse ((covGrad (nonflatU t)).adjoint A) := by
  change (covGrad (nonflatU t)).adjoint (A - bondAxis A) =
    (covGrad (nonflatU t)).adjoint A - siteAxis ((covGrad (nonflatU t)).adjoint A)
  rw [map_sub, covGrad_adjoint_axis_commute]

theorem covGrad_adjoint_axis_flat (t : ℝ) (A : H) :
    (covGrad (nonflatU t)).adjoint (bondAxis A) = flatGrad.adjoint (bondAxis A) := by
  apply ext_inner_left ℝ
  intro X
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    ← bondAxis_selfAdjoint, ← bondAxis_selfAdjoint, ← covGrad_axis_commute,
    covGrad_axis_flat]
  have h := covGrad_axis_commute 0 X
  rw [nonflatU_zero_eq_trivial] at h
  change covGrad (trivialU witnessL) (siteAxis X) = bondAxis (covGrad (trivialU witnessL) X) at h
  rw [covGrad_flat] at h
  rw [h]

theorem siteDelta_axis_flat (t : ℝ) (X : S) :
    siteDeltaU (nonflatU t) (siteAxis X) = flatSiteDelta (siteAxis X) := by
  change (covGrad (nonflatU t)).adjoint (covGrad (nonflatU t) (siteAxis X)) =
    flatGrad.adjoint (flatGrad (siteAxis X))
  rw [covGrad_axis_flat]
  have h := covGrad_axis_commute 0 X
  rw [nonflatU_zero_eq_trivial] at h
  change covGrad (trivialU witnessL) (siteAxis X) = bondAxis (covGrad (trivialU witnessL) X) at h
  rw [covGrad_flat] at h
  rw [h, covGrad_adjoint_axis_flat]

theorem siteDelta_transverse_commute (t : ℝ) (X : S) :
    siteDeltaU (nonflatU t) (siteTransverse X) = siteTransverse (siteDeltaU (nonflatU t) X) := by
  change siteDeltaU (nonflatU t) (X - siteAxis X) =
    siteDeltaU (nonflatU t) X - siteAxis (siteDeltaU (nonflatU t) X)
  rw [map_sub, siteDelta_axis_commute]

theorem siteQU_flat (X : S) : siteQU (trivialU witnessL) X = flatSiteQ X := by
  funext y
  rw [siteQU_value]
  simp only [AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy_trivialU,
    RMap_one, LinearMap.id_apply]
  change (1/8 : ℝ) • (∑ x ∈ blockOf y.1 2, fiberEquiv _ X x) =
    (1/(2:ℝ)^3) • (∑ x ∈ blockOf y.1 2, fiberEquiv _ X x)
  norm_num

theorem siteQU_axis_flatSiteQ (t : ℝ) (X : S) :
    siteQU (nonflatU t) (siteAxis X) = flatSiteQ (siteAxis X) := by
  rw [siteQU_axis_flat, siteQU_flat]

def coarseSiteTransverse : (CS → SuTwo) →ₗ[ℝ] (CS → SuTwo) :=
  LinearMap.id - coarseSiteAxis

theorem siteQU_transverse_commute (t : ℝ) (X : S) :
    siteQU (nonflatU t) (siteTransverse X) = coarseSiteTransverse (siteQU (nonflatU t) X) := by
  change siteQU (nonflatU t) (X - siteAxis X) =
    siteQU (nonflatU t) X - coarseSiteAxis (siteQU (nonflatU t) X)
  rw [map_sub, siteQU_axis_commute]

theorem siteQU_ker_axis_invariant (t : ℝ) (X : S)
    (hX : X ∈ LinearMap.ker (siteQU (nonflatU t))) :
    siteAxis X ∈ LinearMap.ker (siteQU (nonflatU t)) := by
  change siteQU (nonflatU t) (siteAxis X) = 0
  rw [siteQU_axis_commute, LinearMap.mem_ker.mp hX, map_zero]

theorem gaugeImage_axis_invariant (t : ℝ) (X : S)
    (hX : X ∈ gaugeImageU (nonflatU t)) : siteAxis X ∈ gaugeImageU (nonflatU t) := by
  obtain ⟨Y, hY, rfl⟩ := hX
  exact ⟨siteAxis Y, siteQU_ker_axis_invariant t Y hY, siteDelta_axis_commute t Y⟩

theorem gaugeImage_transverse_invariant (t : ℝ) (X : S)
    (hX : X ∈ gaugeImageU (nonflatU t)) : siteTransverse X ∈ gaugeImageU (nonflatU t) :=
  (gaugeImageU (nonflatU t)).sub_mem hX (gaugeImage_axis_invariant t X hX)

#print axioms covGrad_adjoint_axis_flat
#print axioms siteDelta_axis_flat
#print axioms siteQU_axis_flatSiteQ
#print axioms gaugeImage_axis_invariant
#print axioms gaugeImage_transverse_invariant
#print axioms siteAxis_transverse_orthogonal
#print axioms bondAxis_transverse_orthogonal
#print axioms siteAxis_selfAdjoint
#print axioms bondAxis_selfAdjoint
#print axioms covGrad_adjoint_axis_commute
#print axioms siteDelta_axis_commute
#print axioms siteQU_axis_commute
#print axioms siteQU_axis_flat
#print axioms nonflat_link_axis
#print axioms rot_pow_axis
#print axioms covGrad_axis_flat
#print axioms covGrad_axis_commute
#print axioms covGrad_transverse_commute
end HConstruction.Circle
