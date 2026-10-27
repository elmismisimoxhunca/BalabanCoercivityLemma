import NsCvOS9

/-!
# CvOS13 -- row independence: `gOf ≠ 0` from triviality of the cokernel of the `Q'` constraints on `Om0`-supported fields (lane omega/near2/struct)

Abstract part: `cdet (Gm m Lm B) ≠ 0` as soon as every `w` orthogonal to `B(V)` vanishes.
Concrete part (`Bq_cokernel_trivial`): for ANY link configuration `U`, if the `Λ_j` consist of `ell^j`-aligned sites, lie in `Om0`, and are
pairwise disjoint, then `w ⟂ Bq(V)` forces `w = 0`.  Proof: the row of maximal level of `w` is tested against a point mass at its base site, where the
only surviving row is the base row with coefficient `(ell^{-3})^j` (`Qcomp_delta`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

namespace AdalyFormal.CoverOmega.Struct

open scoped RealInnerProductSpace

section Abstract
variable {Sg W : Type*} [NormedAddCommGroup Sg] [InnerProductSpace ℝ Sg] [FiniteDimensional ℝ Sg]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
variable (m lap Lm : Sg →L[ℝ] Sg) (B : Sg →L[ℝ] W)
variable (hms : ∀ f g, ⟪m f, g⟫ = ⟪f, m g⟫) (hmi : ∀ f, m (m f) = m f)
  (hLu : IsUnit Lm) (hLd : ∀ f, Lm f = lap f + (f - m f)) (hl1 : ∀ f, m (lap f) = lap f) (hl2 : ∀ f, lap (m f) = lap f)
include hms hmi hLu hLd hl1 hl2

theorem Gm_cdet_ne_of_cokernel
    (H : ∀ w : W, (∀ f : Sg, m f = f → ⟪B f, w⟫ = 0) → w = 0) : cdet (Gm m Lm B) ≠ 0 := by
  have hLi1 : ∀ f, Lm (Ring.inverse Lm f) = f := fun f => by
    have := Ring.mul_inverse_cancel Lm hLu
    exact congrArg (fun T : Sg →L[ℝ] Sg => T f) this
  have hLi2 : ∀ f, Ring.inverse Lm (Lm f) = f := fun f => by
    have := Ring.inverse_mul_cancel Lm hLu
    exact congrArg (fun T : Sg →L[ℝ] Sg => T f) this
  have hinj : Function.Injective (Gm m Lm B) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    set C := Cc Lm B with hC
    have h1 : ⟪w, Gm m Lm B w⟫ = 0 := by rw [hw, inner_zero_right]
    have h2 : ⟪w, Gm m Lm B w⟫ = ⟪m (ContinuousLinearMap.adjoint C w), m (ContinuousLinearMap.adjoint C w)⟫ := by
      show ⟪w, C (m (ContinuousLinearMap.adjoint C w))⟫ = _
      rw [← ContinuousLinearMap.adjoint_inner_left, hms, hmi]
    have h3 : m (ContinuousLinearMap.adjoint C w) = 0 := by
      rw [h1] at h2
      exact inner_self_eq_zero.mp h2.symm
    apply H w
    intro f hf
    have hcomm : Lm (m f) = m (Lm f) := by
      rw [hLd, hLd, hl2, map_add, hl1, map_sub, hmi]
    have hmu : m (Lm f) = Lm f := by rw [← hcomm, hf]
    have hCu : C (Lm f) = B f := by
      show B (Ring.inverse Lm (Lm f)) = B f
      rw [hLi2]
    calc ⟪B f, w⟫ = ⟪C (Lm f), w⟫ := by rw [hCu]
      _ = ⟪Lm f, ContinuousLinearMap.adjoint C w⟫ := by
          rw [real_inner_comm, ← ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
      _ = ⟪m (Lm f), ContinuousLinearMap.adjoint C w⟫ := by rw [hmu]
      _ = ⟪Lm f, m (ContinuousLinearMap.adjoint C w)⟫ := hms _ _
      _ = 0 := by rw [h3, inner_zero_right]
  have hbij : Function.Bijective (Gm m Lm B) :=
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (Gm m Lm B : W →ₗ[ℝ] W))).mp hinj⟩
  exact cdet_ne_of_isUnit _ ((ContinuousLinearMap.isUnit_iff_bijective).mpr hbij)

end Abstract

end AdalyFormal.CoverOmega.Struct
