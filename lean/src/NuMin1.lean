import Mathlib

/-!
# NuMin1 -- abstract Dirichlet-type principle for `⟨y, (Q A⁻¹ Q*)⁻¹ y⟩` on an invariant pair of subspaces (lane ncwdh_ell2_20261018)

`A : E → E` symmetric unit, `Q : E → F` with adjoint `Qs`, `N = Q A⁻¹ Qs` a unit.  If `W ⊆ E`, `Z ⊆ F` are subspaces with `A W ⊆ W`, `Qs Z ⊆ W`, `Q W ⊆ Z`, `y ∈ Z`, and
`⟨d, A d⟩ ≥ 0` for every `d ∈ W` with `Q d = 0`, then for every `x ∈ W` with `Q x = y`:  `⟨y, N⁻¹ y⟩ ≤ ⟨x, A x⟩`.
`split_inner`: for `y0 ∈ Z`, `y1 ⊥ Z`: `⟨y0+y1, N⁻¹(y0+y1)⟩ = ⟨y0, N⁻¹ y0⟩ + ⟨y1, N⁻¹ y1⟩`.
-/
set_option autoImplicit false

namespace AdalyNcwdhTwo.Min

open scoped RealInnerProductSpace

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]

theorem ainv_symm {A : E →L[ℝ] E} (hAs : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫) (hA : IsUnit A) (x y : E) :
    ⟪(Ring.inverse A) x, y⟫ = ⟪x, (Ring.inverse A) y⟫ := by
  have h1 : ∀ z, A (Ring.inverse A z) = z := fun z =>
    congrArg (fun S : E →L[ℝ] E => S z) (Ring.mul_inverse_cancel A hA)
  calc ⟪(Ring.inverse A) x, y⟫ = ⟪(Ring.inverse A) x, A (Ring.inverse A y)⟫ := by rw [h1]
    _ = ⟪A (Ring.inverse A x), (Ring.inverse A) y⟫ := (hAs _ _).symm
    _ = ⟪x, (Ring.inverse A) y⟫ := by rw [h1]

theorem ainv_mem {A : E →L[ℝ] E} (hA : IsUnit A) (W : Submodule ℝ E) (hAW : ∀ x ∈ W, A x ∈ W) {w : E} (hw : w ∈ W) :
    (Ring.inverse A) w ∈ W := by
  have h2 : ∀ z, (Ring.inverse A) (A z) = z := fun z =>
    congrArg (fun S : E →L[ℝ] E => S z) (Ring.inverse_mul_cancel A hA)
  let f : W →ₗ[ℝ] W := (A : E →ₗ[ℝ] E).restrict hAW
  have hinj : Function.Injective f := by
    intro a b hab
    have : A (a : E) = A (b : E) := by
      have := congrArg (fun z : W => (z : E)) hab
      simpa [f] using this
    have h3 : (a : E) = (b : E) := by
      have := congrArg (fun z => (Ring.inverse A) z) this
      rwa [h2, h2] at this
    exact Subtype.ext h3
  have hsurj : Function.Surjective f := (LinearMap.injective_iff_surjective).mp hinj
  obtain ⟨w', hw'⟩ := hsurj ⟨w, hw⟩
  have : A (w' : E) = w := by
    have := congrArg (fun z : W => (z : E)) hw'
    simpa [f] using this
  rw [← this, h2]
  exact w'.2

theorem minPrinciple {A : E →L[ℝ] E} (hAs : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫) (hA : IsUnit A)
    {Q : E →L[ℝ] F} {Qs : F →L[ℝ] E} (hQ : ∀ x y, ⟪Q x, y⟫ = ⟪x, Qs y⟫)
    (hN : IsUnit (Q.comp ((Ring.inverse A).comp Qs)))
    (W : Submodule ℝ E) (Z : Submodule ℝ F) (hAW : ∀ x ∈ W, A x ∈ W) (hQsZ : ∀ z ∈ Z, Qs z ∈ W)
    (hQW : ∀ x ∈ W, Q x ∈ Z) {y : F} (hy : y ∈ Z) {x : E} (hx : x ∈ W) (hQx : Q x = y)
    (hpsd : ∀ d ∈ W, Q d = 0 → 0 ≤ ⟪d, A d⟫) :
    ⟪y, (Ring.inverse (Q.comp ((Ring.inverse A).comp Qs))) y⟫ ≤ ⟪x, A x⟫ := by
  set N := Q.comp ((Ring.inverse A).comp Qs) with hNdef
  have h1 : ∀ z, A (Ring.inverse A z) = z := fun z =>
    congrArg (fun S : E →L[ℝ] E => S z) (Ring.mul_inverse_cancel A hA)
  have hNZ : ∀ z ∈ Z, N z ∈ Z := fun z hz => by
    simp only [hNdef, ContinuousLinearMap.comp_apply]
    exact hQW _ (ainv_mem hA W hAW (hQsZ z hz))
  -- N is injective, hence bijective on Z
  have h2N : ∀ z, (Ring.inverse N) (N z) = z := fun z =>
    congrArg (fun S : F →L[ℝ] F => S z) (Ring.inverse_mul_cancel N hN)
  let f : Z →ₗ[ℝ] Z := (N : F →ₗ[ℝ] F).restrict hNZ
  have hinj : Function.Injective f := by
    intro a b hab
    have : N (a : F) = N (b : F) := by
      have := congrArg (fun z : Z => (z : F)) hab
      simpa [f] using this
    have h3 : (a : F) = (b : F) := by
      have := congrArg (fun z => (Ring.inverse N) z) this
      rwa [h2N, h2N] at this
    exact Subtype.ext h3
  have hsurj : Function.Surjective f := (LinearMap.injective_iff_surjective).mp hinj
  obtain ⟨v', hv'⟩ := hsurj ⟨y, hy⟩
  set v : F := (v' : F) with hv
  have hNv : N v = y := by
    have := congrArg (fun z : Z => (z : F)) hv'
    simpa [f] using this
  have hNinvy : (Ring.inverse N) y = v := by rw [← hNv, h2N]
  rw [hNinvy]
  have hvZ : v ∈ Z := v'.2
  set xs := (Ring.inverse A) (Qs v) with hxs
  have hxsW : xs ∈ W := ainv_mem hA W hAW (hQsZ v hvZ)
  have hAxs : A xs = Qs v := h1 _
  have hQxs : Q xs = y := by rw [← hNv]; simp [hNdef, hxs]
  set d := x - xs with hd
  have hdW : d ∈ W := W.sub_mem hx hxsW
  have hQd : Q d = 0 := by rw [hd, map_sub, hQx, hQxs, sub_self]
  have hdAxs : ⟪d, A xs⟫ = 0 := by rw [hAxs, ← hQ, hQd, inner_zero_left]
  have hxsAxs : ⟪xs, A xs⟫ = ⟪y, v⟫ := by rw [hAxs, ← hQ, hQxs]
  have hexp : ⟪x, A x⟫ = ⟪xs, A xs⟫ + 2 * ⟪d, A xs⟫ + ⟪d, A d⟫ := by
    have hxe : x = xs + d := by rw [hd]; abel
    have hsym : ⟪xs, A d⟫ = ⟪d, A xs⟫ := by
      rw [← hAs xs d, real_inner_comm]
    conv_lhs => rw [hxe]
    simp only [map_add, inner_add_left, inner_add_right]
    rw [hsym]; ring
  have := hpsd d hdW hQd
  rw [hexp, hdAxs, hxsAxs]
  linarith

theorem split_inner {A : E →L[ℝ] E} (hAs : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫) (hA : IsUnit A)
    {Q : E →L[ℝ] F} {Qs : F →L[ℝ] E} (hQ : ∀ x y, ⟪Q x, y⟫ = ⟪x, Qs y⟫)
    (hN : IsUnit (Q.comp ((Ring.inverse A).comp Qs)))
    (W : Submodule ℝ E) (Z : Submodule ℝ F) (hAW : ∀ x ∈ W, A x ∈ W) (hQsZ : ∀ z ∈ Z, Qs z ∈ W)
    (hQW : ∀ x ∈ W, Q x ∈ Z) {y0 y1 : F} (hy0 : y0 ∈ Z) (horth : ∀ z ∈ Z, ⟪y1, z⟫ = 0) :
    ⟪y0 + y1, (Ring.inverse (Q.comp ((Ring.inverse A).comp Qs))) (y0 + y1)⟫ =
      ⟪y0, (Ring.inverse (Q.comp ((Ring.inverse A).comp Qs))) y0⟫ +
        ⟪y1, (Ring.inverse (Q.comp ((Ring.inverse A).comp Qs))) y1⟫ := by
  set N := Q.comp ((Ring.inverse A).comp Qs) with hNdef
  have hNs : ∀ a b, ⟪N a, b⟫ = ⟪a, N b⟫ := by
    intro a b
    simp only [hNdef, ContinuousLinearMap.comp_apply]
    have hQ' : ∀ (y : F) (x : E), ⟪Qs y, x⟫ = ⟪y, Q x⟫ := fun y x => by
      rw [real_inner_comm, ← hQ, real_inner_comm]
    rw [hQ, ainv_symm hAs hA, hQ']
  have hNZ : ∀ z ∈ Z, N z ∈ Z := fun z hz => by
    simp only [hNdef, ContinuousLinearMap.comp_apply]
    exact hQW _ (ainv_mem hA W hAW (hQsZ z hz))
  have h2N : ∀ z, (Ring.inverse N) (N z) = z := fun z =>
    congrArg (fun S : F →L[ℝ] F => S z) (Ring.inverse_mul_cancel N hN)
  have h1N : ∀ z, N (Ring.inverse N z) = z := fun z =>
    congrArg (fun S : F →L[ℝ] F => S z) (Ring.mul_inverse_cancel N hN)
  have hNis : ∀ a b, ⟪(Ring.inverse N) a, b⟫ = ⟪a, (Ring.inverse N) b⟫ := by
    intro a b
    calc ⟪(Ring.inverse N) a, b⟫ = ⟪(Ring.inverse N) a, N (Ring.inverse N b)⟫ := by rw [h1N]
      _ = ⟪N (Ring.inverse N a), (Ring.inverse N) b⟫ := (hNs _ _).symm
      _ = ⟪a, (Ring.inverse N) b⟫ := by rw [h1N]
  -- N⁻¹ y0 ∈ Z
  have hNZ' : (Ring.inverse N) y0 ∈ Z := by
    let f : Z →ₗ[ℝ] Z := (N : F →ₗ[ℝ] F).restrict hNZ
    have hinj : Function.Injective f := by
      intro a b hab
      have : N (a : F) = N (b : F) := by
        have := congrArg (fun z : Z => (z : F)) hab
        simpa [f] using this
      have h3 : (a : F) = (b : F) := by
        have := congrArg (fun z => (Ring.inverse N) z) this
        rwa [h2N, h2N] at this
      exact Subtype.ext h3
    have hsurj : Function.Surjective f := (LinearMap.injective_iff_surjective).mp hinj
    obtain ⟨v', hv'⟩ := hsurj ⟨y0, hy0⟩
    have hNv : N (v' : F) = y0 := by
      have := congrArg (fun z : Z => (z : F)) hv'
      simpa [f] using this
    rw [← hNv, h2N]
    exact v'.2
  have hc1 : ⟪y1, (Ring.inverse N) y0⟫ = 0 := horth _ hNZ'
  have hc2 : ⟪y0, (Ring.inverse N) y1⟫ = 0 := by
    rw [← hNis, real_inner_comm]; exact horth _ hNZ'
  simp only [map_add, inner_add_left, inner_add_right]
  rw [hc1, hc2]; ring

end

end AdalyNcwdhTwo.Min
