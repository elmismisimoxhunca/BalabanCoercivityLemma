import RationalAnchor

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.G0Final
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace E] [CompleteSpace F]

/-- A CHECKED Gram solve identifies the genuine orthogonal projector. This does
not identify a totalized inverse with a Gram inverse without its equation. -/
theorem starProjection_range_of_gram_solve
    (B : F →L[ℝ] E) (C : F →L[ℝ] F)
    [(LinearMap.range B.toLinearMap).HasOrthogonalProjection]
    (hsolve : ∀ z, B.adjoint (B (C z)) = z) (x : E) :
    (LinearMap.range B.toLinearMap).starProjection x = B (C (B.adjoint x)) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨C (B.adjoint x), rfl⟩
  · intro y hy
    obtain ⟨z, rfl⟩ := hy
    change (inner ℝ (x - B (C (B.adjoint x))) (B z) : ℝ) = 0
    rw [← ContinuousLinearMap.adjoint_inner_left, map_sub, hsolve, sub_self,
      inner_zero_left]

/-- Source-specific identification of R_U from an exact kernel spanning map and
its Gram solve. N is not assumed orthonormal and no rank is inferred numerically. -/
theorem siteRU_of_kernel_gram [FiniteDimensional ℝ F]
    (U : AdalyFormal.Target.ClayStatement.PeriodicLinkConfiguration
      AdalyFormal.Balaban.SuTwoLogExp.SU2
      AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
    (N : F →L[ℝ] HConstruction.Covariance.S) (C : F →L[ℝ] F)
    (hker : LinearMap.range N.toLinearMap = LinearMap.ker (HConstruction.SmallNF.siteQU U))
    (hsolve : ∀ z,
      ((HConstruction.SmallNF.siteDeltaU U).comp N).adjoint
        ((HConstruction.SmallNF.siteDeltaU U) (N (C z))) = z)
    (x : HConstruction.Covariance.S) :
    HConstruction.SmallNF.siteRU U x =
      (HConstruction.SmallNF.siteDeltaU U)
        (N (C (((HConstruction.SmallNF.siteDeltaU U).comp N).adjoint x))) := by
  have hr : LinearMap.range ((HConstruction.SmallNF.siteDeltaU U).comp N).toLinearMap =
      HConstruction.SmallNF.gaugeImageU U := by
    change LinearMap.range ((HConstruction.SmallNF.siteDeltaU U).toLinearMap.comp N.toLinearMap) = _
    rw [LinearMap.range_comp, hker]
    rfl
  have hp := starProjection_range_of_gram_solve
    ((HConstruction.SmallNF.siteDeltaU U).comp N) C hsolve x
  simpa only [hr, HConstruction.SmallNF.siteRU, ContinuousLinearMap.comp_apply] using hp

/-- Two-sided invariance of a subspace under an isometry yields equivariance of
its orthogonal projector. Applied to the source gauge image this is the needed
projection symmetry, not an inference from a numerical matrix. -/
theorem starProjection_intertwines
    (W : E ≃ₗᵢ[ℝ] E) (M : Submodule ℝ E) [M.HasOrthogonalProjection]
    (hinv : M.map W.toLinearEquiv.toLinearMap = M) (x : E) :
    W (M.starProjection x) = M.starProjection (W x) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · have hm : W (M.starProjection x) ∈ M.map W.toLinearEquiv.toLinearMap :=
      ⟨M.starProjection x, Submodule.starProjection_apply_mem M x, rfl⟩
    simpa only [hinv] using hm
  · intro y hy
    rw [← hinv] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    change (inner ℝ (W x - W (M.starProjection x)) (W z) : ℝ) = 0
    rw [← map_sub, W.inner_map_map]
    exact Submodule.starProjection_inner_eq_zero (K := M) x z hz

/-- A self-adjoint invariant-sector projector commutes with the orthogonal
projection onto any subspace it preserves. No full lattice matrix is assembled. -/
theorem starProjection_commutes_selfAdjoint
    (P : E →L[ℝ] E) (M : Submodule ℝ E) [M.HasOrthogonalProjection]
    (hself : ∀ x y, (inner ℝ (P x) y : ℝ) = inner ℝ x (P y))
    (hinv : ∀ x ∈ M, P x ∈ M) (x : E) :
    M.starProjection (P x) = P (M.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hinv _ (Submodule.starProjection_apply_mem M x)
  · intro y hy
    rw [← map_sub, hself]
    exact Submodule.starProjection_inner_eq_zero (K := M) x (P y) (hinv y hy)

/-- Source projection symmetry follows from site-Laplacian intertwining and
kernel invariance of the ACTUAL transported site average. -/
theorem siteRU_commutes_of_source_symmetry
    (U : AdalyFormal.Target.ClayStatement.PeriodicLinkConfiguration
      AdalyFormal.Balaban.SuTwoLogExp.SU2
      AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
    (P : HConstruction.Covariance.S →L[ℝ] HConstruction.Covariance.S)
    (hself : ∀ x y, (inner ℝ (P x) y : ℝ) = inner ℝ x (P y))
    (hL : ∀ x, P (HConstruction.SmallNF.siteDeltaU U x) =
      HConstruction.SmallNF.siteDeltaU U (P x))
    (hQ : ∀ x, HConstruction.SmallNF.siteQU U x = 0 →
      HConstruction.SmallNF.siteQU U (P x) = 0) (x : HConstruction.Covariance.S) :
    HConstruction.SmallNF.siteRU U (P x) = P (HConstruction.SmallNF.siteRU U x) := by
  apply starProjection_commutes_selfAdjoint P (HConstruction.SmallNF.gaugeImageU U) hself
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  refine ⟨P z, hQ z hz, ?_⟩
  exact (hL z).symm

#print axioms starProjection_commutes_selfAdjoint
#print axioms siteRU_commutes_of_source_symmetry
#print axioms starProjection_range_of_gram_solve
#print axioms siteRU_of_kernel_gram
#print axioms starProjection_intertwines
end HConstruction.G0Final
