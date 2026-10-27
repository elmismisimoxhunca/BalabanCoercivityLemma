import Mathlib

/-!
# GdAlg -- the Dirichlet principle for `⟨b, (Q M⁻¹ Q*)⁻¹ b⟩` (generic finite-dimensional real Hilbert spaces).

`M` a symmetric unit on `E`, `Q : E → F` with adjoint `Qs`, `N = Q M⁻¹ Qs` a unit.  For `b : F` put `z = N⁻¹ b`, `x₀ = M⁻¹ Qs z`.
* `dirichlet_value`: `Q x₀ = b`, `M x₀ = Qs z`, `⟨b, N⁻¹ b⟩ = ⟨x₀, M x₀⟩`.
* `dirichlet_min`: if `⟨x, M x⟩ ≥ 0` for all `x`, then `⟨b, N⁻¹ b⟩ ≤ ⟨x, M x⟩` for every `x` with `Q x = b`.
* `compare_inverse_forms`: two such pairs `(M₁,N₁)`, `(M₂,N₂)` with `M₂` positive semidefinite and `⟨x₀, M₂ x₀⟩ ≤ ⟨x₀, M₁ x₀⟩` at the stationary point `x₀`
  of the first give `⟨b, N₂⁻¹ b⟩ ≤ ⟨b, N₁⁻¹ b⟩`.
(Same mathematics as `ncwdh_ell2_20261018/src/NuMin1.lean`; re-derived here in the exact shape needed, ~60 lines.)
-/
set_option autoImplicit false

namespace AdalyFormal.D1Guarded.Alg

open scoped RealInnerProductSpace

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- the stationary point `x₀ = M⁻¹ Qs N⁻¹ b`. -/
noncomputable def stat (M : E →L[ℝ] E) (Q : E →L[ℝ] F) (Qs : F →L[ℝ] E) (b : F) : E :=
  Ring.inverse M (Qs (Ring.inverse ((Q.comp (Ring.inverse M)).comp Qs) b))

theorem dirichlet_value {M : E →L[ℝ] E} (hM : IsUnit M) {Q : E →L[ℝ] F} {Qs : F →L[ℝ] E}
    (hQ : ∀ x y, ⟪Q x, y⟫ = ⟪x, Qs y⟫) (hN : IsUnit ((Q.comp (Ring.inverse M)).comp Qs)) (b : F) :
    Q (stat M Q Qs b) = b ∧ M (stat M Q Qs b) = Qs (Ring.inverse ((Q.comp (Ring.inverse M)).comp Qs) b) ∧
      ⟪b, Ring.inverse ((Q.comp (Ring.inverse M)).comp Qs) b⟫ = ⟪stat M Q Qs b, M (stat M Q Qs b)⟫ := by
  set N := (Q.comp (Ring.inverse M)).comp Qs with hNdef
  set z := Ring.inverse N b with hz
  have hl : ∀ x, M (Ring.inverse M x) = x := fun x =>
    congrArg (fun S : E →L[ℝ] E => S x) (Ring.mul_inverse_cancel M hM)
  have hNz : N z = b := congrArg (fun S : F →L[ℝ] F => S b) (Ring.mul_inverse_cancel N hN)
  have hMx : M (stat M Q Qs b) = Qs z := hl _
  have hQx : Q (stat M Q Qs b) = b := by
    have h0 : Q (stat M Q Qs b) = N z := rfl
    rw [h0, hNz]
  refine ⟨hQx, hMx, ?_⟩
  rw [hMx, ← hQ, hQx]

theorem dirichlet_min {M : E →L[ℝ] E} (hs : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫) (hM : IsUnit M) {Q : E →L[ℝ] F} {Qs : F →L[ℝ] E}
    (hQ : ∀ x y, ⟪Q x, y⟫ = ⟪x, Qs y⟫) (hN : IsUnit ((Q.comp (Ring.inverse M)).comp Qs))
    (hp : ∀ x, 0 ≤ ⟪x, M x⟫) (b : F) {x : E} (hx : Q x = b) :
    ⟪b, Ring.inverse ((Q.comp (Ring.inverse M)).comp Qs) b⟫ ≤ ⟪x, M x⟫ := by
  obtain ⟨h1, h2, h3⟩ := dirichlet_value hM hQ hN b
  set x0 := stat M Q Qs b with hx0
  set z := Ring.inverse ((Q.comp (Ring.inverse M)).comp Qs) b with hz
  set d := x - x0 with hd
  have hQd : Q d = 0 := by rw [hd, map_sub, hx, h1, sub_self]
  have hdx : ⟪d, M x0⟫ = 0 := by rw [h2, ← hQ, hQd, inner_zero_left]
  have hexp : ⟪x, M x⟫ = ⟪x0, M x0⟫ + 2 * ⟪d, M x0⟫ + ⟪d, M d⟫ := by
    have hxe : x = x0 + d := by rw [hd]; abel
    conv_lhs => rw [hxe]
    simp only [map_add, inner_add_left, inner_add_right]
    have h5 : ⟪x0, M d⟫ = ⟪d, M x0⟫ := by
      rw [real_inner_comm, ← hs]
    rw [h5]; ring
  rw [h3, hexp, hdx]
  have := hp d
  linarith

theorem compare_inverse_forms {M₁ M₂ : E →L[ℝ] E} (hM₁ : IsUnit M₁)
    (hs₂ : ∀ x y, ⟪M₂ x, y⟫ = ⟪x, M₂ y⟫) (hM₂ : IsUnit M₂) {Q : E →L[ℝ] F} {Qs : F →L[ℝ] E}
    (hQ : ∀ x y, ⟪Q x, y⟫ = ⟪x, Qs y⟫) (hN₁ : IsUnit ((Q.comp (Ring.inverse M₁)).comp Qs))
    (hN₂ : IsUnit ((Q.comp (Ring.inverse M₂)).comp Qs)) (hp₂ : ∀ x, 0 ≤ ⟪x, M₂ x⟫) (b : F)
    (hle : ⟪stat M₁ Q Qs b, M₂ (stat M₁ Q Qs b)⟫ ≤ ⟪stat M₁ Q Qs b, M₁ (stat M₁ Q Qs b)⟫) :
    ⟪b, Ring.inverse ((Q.comp (Ring.inverse M₂)).comp Qs) b⟫ ≤ ⟪b, Ring.inverse ((Q.comp (Ring.inverse M₁)).comp Qs) b⟫ := by
  obtain ⟨h1, -, h3⟩ := dirichlet_value hM₁ hQ hN₁ b
  have hmin := dirichlet_min hs₂ hM₂ hQ hN₂ hp₂ b h1
  rw [h3]
  exact le_trans hmin hle

/-- the same with the second pair given by equalities (so that no unification between concrete operators is ever needed). -/
theorem compare_firstterm_forms {M₁ M₂ : E →L[ℝ] E} {Q₁ Q₂ : E →L[ℝ] F} {Qs₁ Qs₂ : F →L[ℝ] E} (hQ : Q₂ = Q₁)
    (hQs : Qs₂ = Qs₁) (hM₁ : IsUnit M₁) (hs₂ : ∀ x y, ⟪M₂ x, y⟫ = ⟪x, M₂ y⟫) (hM₂ : IsUnit M₂)
    (hadj : ∀ x y, ⟪Q₁ x, y⟫ = ⟪x, Qs₁ y⟫) (hN₁ : IsUnit ((Q₁.comp (Ring.inverse M₁)).comp Qs₁))
    (hN₂ : IsUnit ((Q₂.comp (Ring.inverse M₂)).comp Qs₂)) (hp₂ : ∀ x, 0 ≤ ⟪x, M₂ x⟫) (b : F)
    (hle : ⟪stat M₁ Q₁ Qs₁ b, M₂ (stat M₁ Q₁ Qs₁ b)⟫ ≤ ⟪stat M₁ Q₁ Qs₁ b, M₁ (stat M₁ Q₁ Qs₁ b)⟫) :
    ⟪b, Ring.inverse ((Q₂.comp (Ring.inverse M₂)).comp Qs₂) b⟫ ≤ ⟪b, Ring.inverse ((Q₁.comp (Ring.inverse M₁)).comp Qs₁) b⟫ := by
  subst hQ hQs
  exact compare_inverse_forms hM₁ hs₂ hM₂ hadj hN₁ hN₂ hp₂ b hle

/-- the same, with the two operators `N₁`, `N₂` given by equalities (so that no concrete operator is ever rewritten). -/
theorem compare_firstterm_N {M₁ M₂ : E →L[ℝ] E} {Q₁ Q₂ : E →L[ℝ] F} {Qs₁ Qs₂ : F →L[ℝ] E} {N₁ N₂ : F →L[ℝ] F}
    (hQ : Q₂ = Q₁) (hQs : Qs₂ = Qs₁) (hN₁eq : N₁ = (Q₁.comp (Ring.inverse M₁)).comp Qs₁)
    (hN₂eq : N₂ = (Q₂.comp (Ring.inverse M₂)).comp Qs₂) (hM₁ : IsUnit M₁)
    (hs₂ : ∀ x y, ⟪M₂ x, y⟫ = ⟪x, M₂ y⟫) (hM₂ : IsUnit M₂) (hadj : ∀ x y, ⟪Q₁ x, y⟫ = ⟪x, Qs₁ y⟫)
    (hN₁ : IsUnit N₁) (hN₂ : IsUnit N₂) (hp₂ : ∀ x, 0 ≤ ⟪x, M₂ x⟫) (b : F)
    (hle : ⟪stat M₁ Q₁ Qs₁ b, M₂ (stat M₁ Q₁ Qs₁ b)⟫ ≤ ⟪stat M₁ Q₁ Qs₁ b, M₁ (stat M₁ Q₁ Qs₁ b)⟫) :
    ⟪b, Ring.inverse N₂ b⟫ ≤ ⟪b, Ring.inverse N₁ b⟫ := by
  subst hN₁eq hN₂eq
  exact compare_firstterm_forms hQ hQs hM₁ hs₂ hM₂ hadj hN₁ hN₂ hp₂ b hle

end

#print axioms dirichlet_value
#print axioms dirichlet_min
#print axioms compare_inverse_forms
#print axioms compare_firstterm_forms
#print axioms compare_firstterm_N

end AdalyFormal.D1Guarded.Alg
