import SiteConst

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
noncomputable section
namespace HConstruction.G0CoerceFinal
open HConstruction.Covariance HConstruction.SmallNF HConstruction.TransversePos HConstruction.Circle
open HConstruction.DRepair HConstruction.Nonflat HConstruction.NfRepair.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL witnessY)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)

/-- The flat site Laplacian is injective on the actual Q'-null domain. -/
theorem flatSiteDelta_kernel_zero (X : S) (hQ : flatSiteQ X = 0)
    (hL : flatSiteDelta X = 0) : X = 0 := by
  have hG : flatGrad X = 0 := by
    have he : (inner ℝ X (flatSiteDelta X) : ℝ) = 0 := by rw [hL, inner_zero_right]
    change inner ℝ X (flatGrad.adjoint (flatGrad X)) = 0 at he
    rw [ContinuousLinearMap.adjoint_inner_right] at he
    exact inner_self_eq_zero.mp he
  have hg : gradValueCovariant (trivialU witnessL) (fiberEquiv _ X) = 0 := by
    funext b
    have hp := congrArg (fun A : H => bfl2Equiv A b) hG
    change (2 : ℝ) • gradValueCovariant (trivialU witnessL) (fiberEquiv _ X) b = 0 at hp
    exact (smul_eq_zero.mp hp).resolve_left (by norm_num)
  have hconst : X = constSite (fiberEquiv _ X witnessY) := by
    apply (fiberEquiv _).injective
    funext x
    exact Reproduced.const_of_grad_eq_zero _ hg x witnessY
  have hv : fiberEquiv _ X witnessY = 0 := by
    have he := congrFun hQ csOrigin
    rw [hconst, flatSiteQ_const] at he
    exact he
  rw [hconst, hv]
  apply (fiberEquiv _).injective
  rfl

abbrev GaugeDomain := LinearMap.ker flatSiteQ

def kernelInclusion : GaugeDomain →L[ℝ] S := GaugeDomain.subtype.toContinuousLinearMap

def transportedKernel (t : ℝ) : GaugeDomain →L[ℝ] S := (siteFrame t).comp kernelInclusion

def laplacianSpan (t : ℝ) : GaugeDomain →L[ℝ] S :=
  (siteDeltaU (nonflatU t)).comp (transportedKernel t)

def gaugeGram (t : ℝ) : GaugeDomain →L[ℝ] GaugeDomain :=
  (laplacianSpan t).adjoint.comp (laplacianSpan t)

attribute [local irreducible] gaugePotential gaugePi

theorem siteFrame_surjective (t : ℝ) : Function.Surjective (siteFrame t) := by
  have hi : Function.Injective (siteFrame t) := by
    intro X Y h
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [← siteFrame_norm t, map_sub, h, sub_self, norm_zero]
  exact (LinearMap.injective_iff_surjective).mp hi

theorem laplacianSpan_range (t : ℝ) :
    LinearMap.range (laplacianSpan t).toLinearMap = gaugeImageU (nonflatU t) := by
  ext X
  constructor
  · rintro ⟨Y,rfl⟩
    refine ⟨siteFrame t Y, ?_, rfl⟩
    change siteQU (nonflatU t) (siteFrame t Y) = 0
    rw [siteQU_frame]
    exact Y.property
  · rintro ⟨Y,hY,rfl⟩
    obtain ⟨Z,rfl⟩ := siteFrame_surjective t Y
    have hZ : flatSiteQ Z = 0 := by
      change siteQU (nonflatU t) (siteFrame t Z) = 0 at hY
      rwa [siteQU_frame] at hY
    exact ⟨⟨Z,hZ⟩, rfl⟩

theorem laplacianSpan_zero_injective : Function.Injective (laplacianSpan 0) := by
  intro X Y h
  have hz : laplacianSpan 0 (X-Y) = 0 := by rw [map_sub, h, sub_self]
  have hL : flatSiteDelta ((X-Y : GaugeDomain) : S) = 0 := by
    change siteDeltaU (nonflatU 0) (siteFrame 0 ((X-Y : GaugeDomain) : S)) = 0 at hz
    rw [nonflatU_zero_eq_trivial] at hz
    change siteDeltaU (trivialU witnessL) (siteFrame 0 ((X-Y : GaugeDomain) : S)) = 0 at hz
    rw [siteDeltaU_flat, siteFrame_zero, ContinuousLinearMap.id_apply] at hz
    exact hz
  exact sub_eq_zero.mp (Subtype.ext (flatSiteDelta_kernel_zero _ (X-Y).property hL))

theorem gaugeGram_zero_positive (X : GaugeDomain) (hX : X ≠ 0) :
    (0 : ℝ) < inner ℝ X (gaugeGram 0 X) := by
  change 0 < inner ℝ X ((laplacianSpan 0).adjoint (laplacianSpan 0 X))
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro h
  apply hX
  apply laplacianSpan_zero_injective
  simpa only [map_zero] using h

theorem gaugeGram_zero_isUnit : IsUnit (gaugeGram 0) := by
  obtain ⟨G,hR,hL,_⟩ := positive_inverse (gaugeGram 0) gaugeGram_zero_positive
  refine ⟨⟨gaugeGram 0, G, ?_, ?_⟩, rfl⟩
  · apply ContinuousLinearMap.ext
    exact hR
  · apply ContinuousLinearMap.ext
    exact hL

/-- Totalized only as an auxiliary formula; identified with the physical Pi ONLY
where the genuine Gram invertibility theorem applies. -/
def formulaPi (t : ℝ) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H - (covGrad (nonflatU t)).comp
    ((transportedKernel t).comp ((Ring.inverse (gaugeGram t)).comp
      ((laplacianSpan t).adjoint.comp (covGrad (nonflatU t)).adjoint)))

theorem gaugePi_eq_formula (t : ℝ) (ht : IsUnit (gaugeGram t)) :
    gaugePi (nonflatU t) = formulaPi t := by
  have hsolve (X : GaugeDomain) : (laplacianSpan t).adjoint
      (laplacianSpan t (Ring.inverse (gaugeGram t) X)) = X :=
    congrArg (fun T : GaugeDomain →L[ℝ] GaugeDomain => T X)
      (Ring.mul_inverse_cancel _ ht)
  have hR (X : S) : siteRU (nonflatU t) X = laplacianSpan t
      (Ring.inverse (gaugeGram t) ((laplacianSpan t).adjoint X)) := by
    have he := HConstruction.G0Final.starProjection_range_of_gram_solve
      (laplacianSpan t) (Ring.inverse (gaugeGram t)) hsolve X
    simpa only [laplacianSpan_range, siteRU] using he
  ext A
  apply gaugePi_eq_of_solution
  exact (hR _).symm

theorem smooth_transportedKernel : ContDiff ℝ ⊤ transportedKernel :=
  smooth_siteFrame.clm_comp contDiff_const

theorem smooth_laplacianSpan : ContDiff ℝ ⊤ laplacianSpan := by
  unfold laplacianSpan siteDeltaU
  exact (((ContinuousLinearMap.adjoint : (S →L[ℝ] H) ≃ₗᵢ[ℝ] (H →L[ℝ] S)).contDiff.comp
    smooth_covGrad).clm_comp smooth_covGrad).clm_comp smooth_transportedKernel

theorem smooth_gaugeGram : ContDiff ℝ ⊤ gaugeGram := by
  unfold gaugeGram
  exact ((ContinuousLinearMap.adjoint : (GaugeDomain →L[ℝ] S) ≃ₗᵢ[ℝ]
    (S →L[ℝ] GaugeDomain)).contDiff.comp smooth_laplacianSpan).clm_comp smooth_laplacianSpan

theorem eventually_gaugeGram_isUnit : ∀ᶠ t in nhds (0 : ℝ), IsUnit (gaugeGram t) :=
  smooth_gaugeGram.continuous.continuousAt.eventually
    ((Units.isOpen (R := GaugeDomain →L[ℝ] GaugeDomain)).mem_nhds gaugeGram_zero_isUnit)

theorem smoothAt_formulaPi : ContDiffAt ℝ ⊤ formulaPi 0 := by
  have hinv : ContDiffAt ℝ ⊤ (fun t => Ring.inverse (gaugeGram t)) 0 := by
    obtain ⟨u,hu⟩ := gaugeGram_zero_isUnit
    have hi : ContDiffAt ℝ ⊤ Ring.inverse (gaugeGram 0) := by
      rw [← hu]
      exact contDiffAt_ringInverse ℝ (R := GaugeDomain →L[ℝ] GaugeDomain) u
    exact hi.comp 0 smooth_gaugeGram.contDiffAt
  unfold formulaPi
  exact contDiffAt_const.sub (smooth_covGrad.contDiffAt.clm_comp
    (smooth_transportedKernel.contDiffAt.clm_comp (hinv.clm_comp
      (((ContinuousLinearMap.adjoint : (GaugeDomain →L[ℝ] S) ≃ₗᵢ[ℝ]
        (S →L[ℝ] GaugeDomain)).contDiff.comp smooth_laplacianSpan).contDiffAt.clm_comp
          ((ContinuousLinearMap.adjoint : (S →L[ℝ] H) ≃ₗᵢ[ℝ] (H →L[ℝ] S)).contDiff.comp
            smooth_covGrad).contDiffAt))))

/-- The genuine source gauge extension is smooth near zero, not just an arbitrary
Gram formula. The exact range/projection identification discharges the bridge. -/
theorem smoothAt_gaugePi : ContDiffAt ℝ ⊤ (fun t => gaugePi (nonflatU t)) 0 := by
  apply smoothAt_formulaPi.congr_of_eventuallyEq
  filter_upwards [eventually_gaugeGram_isUnit] with t ht
  exact gaugePi_eq_formula t ht

theorem smoothAt_deltaPrimePi : ContDiffAt ℝ ⊤ (fun t => deltaPrimePi (nonflatU t)) 0 := by
  unfold deltaPrimePi deltaPi
  exact smooth_deltaU.contDiffAt.sub
    (((ContinuousLinearMap.adjoint : (H →L[ℝ] H) ≃ₗᵢ[ℝ] (H →L[ℝ] H)).contDiff.contDiffAt.comp
      0 smoothAt_gaugePi).clm_comp (smooth_deltaU.contDiffAt.clm_comp smoothAt_gaugePi))

#print axioms flatSiteDelta_kernel_zero
#print axioms laplacianSpan_range
#print axioms gaugeGram_zero_isUnit
#print axioms gaugePi_eq_formula
#print axioms smoothAt_gaugePi
#print axioms smoothAt_deltaPrimePi
end HConstruction.G0CoerceFinal
