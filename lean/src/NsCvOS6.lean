import NsCvOS5

/-!
# CvOS6 -- the orthogonal projection onto `lap(N)`, `N = {f : m f = f ∧ B f = 0}`, as a cleared-denominator formula
(lane omega/near2/struct)

Abstract setting: `m` orthogonal projection (symmetric idempotent), `lap` with `m lap = lap = lap m`, `Lm = lap + (1 - m)` a unit,
`B : Sg → W`.  With `C = B Lm⁻¹`, `Gm = C m C*` (an endomorphism of `W`), `g = det Gm`:
`g ≠ 0 → starProjection (lap '' N) = g⁻¹ • Rhat`,  `Rhat = g • m - m C* adj(Gm) C m`  (polynomial in the data).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega.Struct

open scoped RealInnerProductSpace

section Proj
variable {Sg W : Type*} [NormedAddCommGroup Sg] [InnerProductSpace ℝ Sg] [FiniteDimensional ℝ Sg]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- `N = {f | m f = f ∧ B f = 0}`. -/
def Nsub (m : Sg →L[ℝ] Sg) (B : Sg →L[ℝ] W) : Submodule ℝ Sg where
  carrier := {f | m f = f ∧ B f = 0}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := fun {f g} hf hg => ⟨by simp [hf.1, hg.1], by simp [hf.2, hg.2]⟩
  smul_mem' := fun c f hf => ⟨by simp [hf.1], by simp [hf.2]⟩

/-- `C = B Lm⁻¹`. -/
noncomputable def Cc (Lm : Sg →L[ℝ] Sg) (B : Sg →L[ℝ] W) : Sg →L[ℝ] W := B.comp (Ring.inverse Lm)

/-- `Gm = C m C*`. -/
noncomputable def Gm (m Lm : Sg →L[ℝ] Sg) (B : Sg →L[ℝ] W) : W →L[ℝ] W :=
  ((Cc Lm B).comp m).comp (ContinuousLinearMap.adjoint (Cc Lm B))

/-- the cleared projection `Rhat = g m - m C* adj(Gm) C m`. -/
noncomputable def Rhat (m Lm : Sg →L[ℝ] Sg) (B : Sg →L[ℝ] W) : Sg →L[ℝ] Sg :=
  cdet (Gm m Lm B) • m - ((m.comp (ContinuousLinearMap.adjoint (Cc Lm B))).comp (cadj (Gm m Lm B))).comp ((Cc Lm B).comp m)

variable (m lap Lm : Sg →L[ℝ] Sg) (B : Sg →L[ℝ] W)

section
variable (hms : ∀ f g, ⟪m f, g⟫ = ⟪f, m g⟫) (hmi : ∀ f, m (m f) = m f)
  (hLu : IsUnit Lm) (hLd : ∀ f, Lm f = lap f + (f - m f)) (hl1 : ∀ f, m (lap f) = lap f) (hl2 : ∀ f, lap (m f) = lap f)
include hmi hLd hl1 hl2

theorem Lm_comm_m (f : Sg) : Lm (m f) = m (Lm f) := by
  rw [hLd, hLd, hl2, map_add, hl1, map_sub, hmi]

end

section
variable (hms : ∀ f g, ⟪m f, g⟫ = ⟪f, m g⟫) (hmi : ∀ f, m (m f) = m f)
  (hLu : IsUnit Lm) (hLd : ∀ f, Lm f = lap f + (f - m f)) (hl1 : ∀ f, m (lap f) = lap f) (hl2 : ∀ f, lap (m f) = lap f)
include hms hmi hLu hLd hl1 hl2

theorem mem_map_iff (w : Sg) :
    w ∈ Submodule.map (lap : Sg →ₗ[ℝ] Sg) (Nsub m B) ↔ m w = w ∧ Cc Lm B w = 0 := by
  have hLi1 : ∀ f, Lm (Ring.inverse Lm f) = f := fun f => by
    have := Ring.mul_inverse_cancel Lm hLu
    exact congrArg (fun T : Sg →L[ℝ] Sg => T f) this
  have hLi2 : ∀ f, Ring.inverse Lm (Lm f) = f := fun f => by
    have := Ring.inverse_mul_cancel Lm hLu
    exact congrArg (fun T : Sg →L[ℝ] Sg => T f) this
  have hcomm : ∀ w, m (Ring.inverse Lm w) = Ring.inverse Lm (m w) := fun w => by
    have h1 := Lm_comm_m m lap Lm hmi hLd hl1 hl2 (Ring.inverse Lm w)
    rw [hLi1] at h1
    calc m (Ring.inverse Lm w) = Ring.inverse Lm (Lm (m (Ring.inverse Lm w))) := (hLi2 _).symm
      _ = Ring.inverse Lm (m w) := by rw [h1]
  constructor
  · rintro ⟨f, ⟨hf1, hf2⟩, rfl⟩
    refine ⟨hl1 f, ?_⟩
    have : Lm f = lap f := by rw [hLd, hf1]; simp
    show B (Ring.inverse Lm (lap f)) = 0
    rw [← this, hLi2]; exact hf2
  · rintro ⟨h1, h2⟩
    have hm' : m (Ring.inverse Lm w) = Ring.inverse Lm w := by rw [hcomm, h1]
    refine ⟨Ring.inverse Lm w, ⟨hm', h2⟩, ?_⟩
    show lap (Ring.inverse Lm w) = w
    have := hLd (Ring.inverse Lm w)
    rw [hLi1, hm'] at this
    simpa using this.symm

end

end Proj

end AdalyFormal.CoverOmega.Struct
