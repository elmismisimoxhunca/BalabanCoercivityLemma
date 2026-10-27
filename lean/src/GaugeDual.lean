import MaskedBaseline
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section
namespace HConstruction.TransversePos
open HConstruction.Covariance HConstruction.SmallNF HConstruction.Carrier HConstruction.Nonflat
open HConstruction.NfRepair.Reproduced HConstruction.G0Final.Locality HConstruction.Circle
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL witnessY blockOf)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU coarseRestrictSiteCovariant)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf_one)

/-- Undo the single nontrivial tree transport. This is a SITE map, not bond Q. -/
def siteFrame (t : ℝ) : S →L[ℝ] S :=
  LinearMap.toContinuousLinearMap
    ((fiberEquiv Site).symm.toLinearMap.comp
      ((LinearMap.pi fun x =>
        (if x = specialEndpoint then RMap ((rotElem t)⁻¹) else LinearMap.id).comp
          (LinearMap.proj x)).comp (fiberEquiv _).toLinearMap))

theorem siteFrame_value (t : ℝ) (X : S) (x : Site) :
    fiberEquiv _ (siteFrame t X) x =
      if x = specialEndpoint then RMap ((rotElem t)⁻¹) (fiberEquiv _ X x)
      else fiberEquiv _ X x := by
  classical
  change (if x = specialEndpoint then RMap ((rotElem t)⁻¹) else LinearMap.id) _ = _
  split_ifs <;> rfl

theorem endpoint_block : ∀ y : HConstruction.SmallNF.CS,
    specialEndpoint ∈ blockOf y.1 2 → y.1 = witnessY := by decide +kernel

theorem siteQU_frame (t : ℝ) (X : S) : siteQU (nonflatU t) (siteFrame t X) = flatSiteQ X := by
  funext y
  simp only [siteQU, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  change (1/8 : ℝ) • (∑ x ∈ blockOf y.1 2,
    RMap (coarsePathHolonomy 1 (nonflatU t) y.1 (coarseGammaPath 1 y.1 x))
      (fiberEquiv _ (siteFrame t X) x)) = coarseRestrictSiteCovariant 2 (fiberEquiv _ X) y.1
  unfold coarseRestrictSiteCovariant
  norm_num only [Nat.cast_ofNat, show (2:ℝ)^3 = 8 by norm_num]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [siteFrame_value, tree_holonomy t (y,0) x (by simpa [stepBlockOf_one] using hx)]
  by_cases he : x = specialEndpoint
  · have hy := endpoint_block y (by simpa [he] using hx)
    rw [if_pos he, if_pos ⟨hy, he⟩, RMap_mul_apply, mul_inv_cancel, RMap_one]
    rfl
  · rw [if_neg he, if_neg (by tauto), RMap_one]
    rfl


theorem siteFrame_zero : siteFrame 0 = ContinuousLinearMap.id ℝ S := by
  ext X
  apply (fiberEquiv _).injective
  funext x
  rw [siteFrame_value, (rotElem_eq_one_iff 0).mpr rfl, inv_one]
  split_ifs <;> simp [RMap_one]

def kernelProjection : S →L[ℝ] S := (LinearMap.ker flatSiteQ).starProjection

/-- A continuous spanning-map construction; no continuity of the range projector
is presumed. Its image is contained in the actual nonflat gauge image. -/
def gaugeSpan (t : ℝ) : S →L[ℝ] S :=
  (siteDeltaU (nonflatU t)).comp ((siteFrame t).comp kernelProjection)

theorem gaugeSpan_mem (t : ℝ) (X : S) : gaugeSpan t X ∈ gaugeImageU (nonflatU t) := by
  refine ⟨siteFrame t (kernelProjection X), ?_, rfl⟩
  change siteQU (nonflatU t) (siteFrame t (kernelProjection X)) = 0
  rw [siteQU_frame]
  exact LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem (LinearMap.ker flatSiteQ) X)

theorem gaugeSpan_zero_range : LinearMap.range (gaugeSpan 0).toLinearMap = gaugeImage := by
  ext X
  constructor
  · rintro ⟨Y,rfl⟩
    have h := gaugeSpan_mem 0 Y
    rw [nonflatU_zero_eq_trivial] at h
    change gaugeSpan 0 Y ∈ gaugeImageU (trivialU witnessL) at h
    rwa [gaugeImageU_flat] at h
  · rintro ⟨Y,hY,rfl⟩
    refine ⟨Y, ?_⟩
    change siteDeltaU (nonflatU 0) (siteFrame 0 (kernelProjection Y)) = flatSiteDelta Y
    rw [nonflatU_zero_eq_trivial]
    change siteDeltaU (trivialU witnessL) (siteFrame 0 (kernelProjection Y)) = flatSiteDelta Y
    rw [siteDeltaU_flat, siteFrame_zero, ContinuousLinearMap.id_apply]
    congr 1
    exact Submodule.starProjection_eq_self_iff.mpr hY

theorem gaugeSpan_projection (t : ℝ) (X : S) :
    (gaugeSpan t).adjoint (siteRU (nonflatU t) X) = (gaugeSpan t).adjoint X := by
  apply ext_inner_left ℝ
  intro Y
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (gaugeSpan t Y) ((gaugeImageU (nonflatU t)).starProjection X) = _
  rw [← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (gaugeSpan_mem t Y)]

/-- A rigorous projection-free LOWER gauge energy, valid at all parameters. -/
theorem gauge_dual_bound (t : ℝ) (A : H) :
    ‖(gaugeSpan t).adjoint ((covGrad (nonflatU t)).adjoint A)‖^2 ≤
      (1 + ‖gaugeSpan t‖^2) * ‖gaugeConstraintU (nonflatU t) A‖^2 := by
  have hn := (gaugeSpan t).adjoint.le_opNorm (gaugeConstraintU (nonflatU t) A)
  rw [ContinuousLinearMap.adjoint.norm_map] at hn
  change ‖(gaugeSpan t).adjoint (siteRU (nonflatU t) ((covGrad (nonflatU t)).adjoint A))‖ ≤ _ at hn
  rw [gaugeSpan_projection] at hn
  nlinarith [sq_nonneg ‖gaugeConstraintU (nonflatU t) A‖,
    norm_nonneg ((gaugeSpan t).adjoint ((covGrad (nonflatU t)).adjoint A)),
    mul_nonneg (norm_nonneg (gaugeSpan t)) (norm_nonneg (gaugeConstraintU (nonflatU t) A))]

def dualGauge (t : ℝ) : H →L[ℝ] S :=
  (gaugeSpan t).adjoint.comp (covGrad (nonflatU t)).adjoint

theorem dualGauge_zero_kernel (A : H) (hA : dualGauge 0 A = 0) : gaugeConstraint A = 0 := by
  change siteR (flatGrad.adjoint A) = 0
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.zero_mem _
  intro Y hY
  rw [sub_zero]
  rw [← gaugeSpan_zero_range] at hY
  obtain ⟨Z,rfl⟩ := hY
  change inner ℝ (flatGrad.adjoint A) (gaugeSpan 0 Z) = 0
  rw [← ContinuousLinearMap.adjoint_inner_left (gaugeSpan 0)]
  have he : (gaugeSpan 0).adjoint (flatGrad.adjoint A) = 0 := by
    change (gaugeSpan 0).adjoint ((covGrad (nonflatU 0)).adjoint A) = 0 at hA
    rw [nonflatU_zero_eq_trivial] at hA
    exact hA
  rw [he, inner_zero_left]

#print axioms siteQU_frame
#print axioms gaugeSpan_mem
#print axioms gaugeSpan_zero_range
#print axioms gaugeSpan_projection
#print axioms gauge_dual_bound
#print axioms dualGauge_zero_kernel
end HConstruction.TransversePos
