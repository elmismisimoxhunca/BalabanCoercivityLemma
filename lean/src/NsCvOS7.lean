import NsCvOS6

/-!
# CvOS7 -- `starProjection (lap '' N) = g⁻¹ • Rhat` when `g = det (C m C*) ≠ 0` (lane omega/near2/struct)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega.Struct

open scoped RealInnerProductSpace

section Proj
variable {Sg W : Type*} [NormedAddCommGroup Sg] [InnerProductSpace ℝ Sg] [FiniteDimensional ℝ Sg]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
variable (m lap Lm : Sg →L[ℝ] Sg) (B : Sg →L[ℝ] W)
variable (hms : ∀ f g, ⟪m f, g⟫ = ⟪f, m g⟫) (hmi : ∀ f, m (m f) = m f)
  (hLu : IsUnit Lm) (hLd : ∀ f, Lm f = lap f + (f - m f)) (hl1 : ∀ f, m (lap f) = lap f) (hl2 : ∀ f, lap (m f) = lap f)
include hms hmi hLu hLd hl1 hl2

theorem starProjection_eq_Rhat (hg : cdet (Gm m Lm B) ≠ 0) :
    (Submodule.map (lap : Sg →ₗ[ℝ] Sg) (Nsub m B)).starProjection
      = (cdet (Gm m Lm B))⁻¹ • Rhat m Lm B := by
  set K := Submodule.map (lap : Sg →ₗ[ℝ] Sg) (Nsub m B) with hK
  set C := Cc Lm B with hC
  have hGu : IsUnit (Gm m Lm B) := isUnit_of_cdet_ne _ hg
  set Gi := Ring.inverse (Gm m Lm B) with hGi
  have hGG : ∀ y, Gm m Lm B (Gi y) = y := fun y => by
    have := Ring.mul_inverse_cancel (Gm m Lm B) hGu
    exact congrArg (fun T : W →L[ℝ] W => T y) this
  have hGi' : Gi = (cdet (Gm m Lm B))⁻¹ • cadj (Gm m Lm B) := inverse_eq_cadj _ hg
  ext1 v
  have hv' : ((cdet (Gm m Lm B))⁻¹ • Rhat m Lm B) v
      = m v - m (ContinuousLinearMap.adjoint C (Gi (C (m v)))) := by
    rw [hGi']
    simp [Rhat, hC, smul_sub, smul_smul, hg]
  rw [hv']
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [mem_map_iff m lap Lm B hms hmi hLu hLd hl1 hl2]
    constructor
    · rw [map_sub, hmi, hmi]
    · have e1 : C (m (m v - m (ContinuousLinearMap.adjoint C (Gi (C (m v)))))) = C (m v) - Gm m Lm B (Gi (C (m v))) := by
        rw [map_sub, hmi, hmi, map_sub]; rfl
      show C (m v - m (ContinuousLinearMap.adjoint C (Gi (C (m v))))) = 0
      have e2 : C (m v - m (ContinuousLinearMap.adjoint C (Gi (C (m v))))) = C (m v) - Gm m Lm B (Gi (C (m v))) := by
        rw [map_sub]; rfl
      rw [e2, hGG, sub_self]
  · intro w hw
    rw [mem_map_iff m lap Lm B hms hmi hLu hLd hl1 hl2] at hw
    obtain ⟨hw1, hw2⟩ := hw
    have e : v - (m v - m (ContinuousLinearMap.adjoint C (Gi (C (m v))))) =
        (v - m v) + m (ContinuousLinearMap.adjoint C (Gi (C (m v)))) := by abel
    rw [e, inner_add_left, inner_sub_left, hms v w, hw1, hms, hw1, ContinuousLinearMap.adjoint_inner_left]
    have : C w = 0 := hw2
    rw [this]; simp

end Proj

end AdalyFormal.CoverOmega.Struct
