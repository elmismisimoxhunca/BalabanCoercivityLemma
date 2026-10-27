import CircleSectors
import GaugeProjection
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.Circle
open HConstruction.NfRepair.Reproduced HConstruction.SmallNF
open HConstruction.Covariance HConstruction.Nonflat HConstruction.G0Final
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

/-- Actual orthogonal gauge projector preserves the source axial sector. -/
theorem siteRU_axis_commute (t : ℝ) (X : S) :
    siteRU (nonflatU t) (siteAxis X) = siteAxis (siteRU (nonflatU t) X) :=
  starProjection_commutes_selfAdjoint siteAxis.toContinuousLinearMap
    (gaugeImageU (nonflatU t)) siteAxis_selfAdjoint (gaugeImage_axis_invariant t) X

theorem siteRU_transverse_commute (t : ℝ) (X : S) :
    siteRU (nonflatU t) (siteTransverse X) = siteTransverse (siteRU (nonflatU t) X) := by
  change siteRU (nonflatU t) (X - siteAxis X) =
    siteRU (nonflatU t) X - siteAxis (siteRU (nonflatU t) X)
  rw [map_sub, siteRU_axis_commute]

theorem siteDeltaU_flat : siteDeltaU (trivialU witnessL) = flatSiteDelta := by
  simp only [siteDeltaU, covGrad_flat, flatSiteDelta]

theorem gaugeImageU_flat : gaugeImageU (trivialU witnessL) = gaugeImage := by
  unfold gaugeImageU gaugeImage
  rw [siteDeltaU_flat]
  congr 1
  exact congrArg LinearMap.ker (LinearMap.ext siteQU_flat)

theorem siteRU_flat : siteRU (trivialU witnessL) = siteR := by
  unfold siteRU siteR
  simp only [gaugeImageU_flat]

theorem flatSiteDelta_axis_commute (X : S) :
    flatSiteDelta (siteAxis X) = siteAxis (flatSiteDelta X) := by
  have h := siteDelta_axis_commute 0 X
  rw [nonflatU_zero_eq_trivial] at h
  change siteDeltaU (trivialU witnessL) (siteAxis X) =
    siteAxis (siteDeltaU (trivialU witnessL) X) at h
  simpa only [siteDeltaU_flat] using h

theorem siteR_axis_commute (X : S) : siteR (siteAxis X) = siteAxis (siteR X) := by
  have h := siteRU_axis_commute 0 X
  rw [nonflatU_zero_eq_trivial] at h
  change siteRU (trivialU witnessL) (siteAxis X) =
    siteAxis (siteRU (trivialU witnessL) X) at h
  simpa only [siteRU_flat] using h

/-- The axial images of the two actual gauge subspaces coincide. -/
theorem gaugeImage_axis_flat (t : ℝ) (X : S) :
    siteAxis X ∈ gaugeImageU (nonflatU t) ↔ siteAxis X ∈ gaugeImage := by
  constructor
  · rintro ⟨Y, hY, hYX⟩
    refine ⟨siteAxis Y, ?_, ?_⟩
    · change flatSiteQ (siteAxis Y) = 0
      rw [← siteQU_axis_flatSiteQ t Y, siteQU_axis_commute,
        LinearMap.mem_ker.mp hY, map_zero]
    · change flatSiteDelta (siteAxis Y) = siteAxis X
      rw [← siteDelta_axis_flat t Y, siteDelta_axis_commute]
      change siteDeltaU (nonflatU t) Y = siteAxis X at hYX
      rw [hYX, siteAxis_idempotent]
  · rintro ⟨Y, hY, hYX⟩
    refine ⟨siteAxis Y, ?_, ?_⟩
    · change siteQU (nonflatU t) (siteAxis Y) = 0
      rw [siteQU_axis_flatSiteQ]
      have h := siteQU_axis_commute 0 Y
      rw [nonflatU_zero_eq_trivial] at h
      change siteQU (trivialU witnessL) (siteAxis Y) =
        coarseSiteAxis (siteQU (trivialU witnessL) Y) at h
      rw [siteQU_flat, siteQU_flat] at h
      rw [h, LinearMap.mem_ker.mp hY, map_zero]
    · change siteDeltaU (nonflatU t) (siteAxis Y) = siteAxis X
      rw [siteDelta_axis_flat, flatSiteDelta_axis_commute]
      change flatSiteDelta Y = siteAxis X at hYX
      rw [hYX, siteAxis_idempotent]

/-- On the axis the SOURCE orthogonal projector, not merely its defining
Laplacian, equals the flat orthogonal gauge projector. -/
theorem siteRU_axis_flat (t : ℝ) (X : S) :
    siteRU (nonflatU t) (siteAxis X) = siteR (siteAxis X) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [siteR_axis_commute]
    apply (gaugeImage_axis_flat t (siteR X)).mpr
    rw [← siteR_axis_commute]
    exact Submodule.starProjection_apply_mem gaugeImage _
  · intro Y hY
    have hPY : siteAxis Y ∈ gaugeImage :=
      (gaugeImage_axis_flat t Y).mp (gaugeImage_axis_invariant t Y hY)
    have hfix : siteAxis (siteAxis X - siteR (siteAxis X)) =
        siteAxis X - siteR (siteAxis X) := by
      rw [map_sub, siteAxis_idempotent, ← siteR_axis_commute, siteAxis_idempotent]
    rw [← hfix, siteAxis_selfAdjoint]
    exact Submodule.starProjection_inner_eq_zero (K := gaugeImage) (siteAxis X) (siteAxis Y) hPY

theorem flatGrad_adjoint_axis_commute (A : H) :
    flatGrad.adjoint (bondAxis A) = siteAxis (flatGrad.adjoint A) := by
  have h := covGrad_adjoint_axis_commute 0 A
  rw [nonflatU_zero_eq_trivial] at h
  change (covGrad (trivialU witnessL)).adjoint (bondAxis A) =
    siteAxis ((covGrad (trivialU witnessL)).adjoint A) at h
  simpa only [covGrad_flat] using h

theorem gaugeConstraint_axis_commute (t : ℝ) (A : H) :
    gaugeConstraintU (nonflatU t) (bondAxis A) =
      siteAxis (gaugeConstraintU (nonflatU t) A) := by
  simp only [gaugeConstraintU, ContinuousLinearMap.comp_apply,
    covGrad_adjoint_axis_commute, siteRU_axis_commute]

/-- Equality of the full physical gauge term on the axis, on the actual
unweighted Hilbert carriers; neither projection is replaced by a surrogate. -/
theorem gaugeTerm_axis_flat (t : ℝ) (A : H) :
    covGrad (nonflatU t) (siteRU (nonflatU t) ((covGrad (nonflatU t)).adjoint (bondAxis A))) =
      flatGrad (siteR (flatGrad.adjoint (bondAxis A))) := by
  rw [covGrad_adjoint_axis_flat, flatGrad_adjoint_axis_commute, siteRU_axis_flat,
    siteR_axis_commute, covGrad_axis_flat]

theorem gaugeTerm_axis_commute (t : ℝ) (A : H) :
    covGrad (nonflatU t) (siteRU (nonflatU t) ((covGrad (nonflatU t)).adjoint (bondAxis A))) =
      bondAxis (covGrad (nonflatU t) (siteRU (nonflatU t) ((covGrad (nonflatU t)).adjoint A))) := by
  rw [covGrad_adjoint_axis_commute, siteRU_axis_commute, covGrad_axis_commute]

#print axioms gaugeConstraint_axis_commute
#print axioms gaugeTerm_axis_flat
#print axioms gaugeTerm_axis_commute
#print axioms siteRU_axis_commute
#print axioms siteRU_transverse_commute
#print axioms gaugeImage_axis_flat
#print axioms siteRU_axis_flat
#print axioms siteRU_flat
end HConstruction.Circle
