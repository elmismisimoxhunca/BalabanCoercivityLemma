import Mathlib

/-!
# NuMono1 -- the monotone-resolvent lemma (lane ncwdh_ell2_20261018)

`H(c) = H0 + c B` a pencil of symmetric operators with `B ≥ 0` and `N(c) = Q H(c)⁻¹ Q*`.  On an interval where `H(c)` and `N(c)` are units, the real function
`c ↦ ⟨y, N(c)⁻¹ y⟩` is monotone NON-DECREASING: its derivative is `⟨B G Q* z, G Q* z⟩ ≥ 0` with `G = H⁻¹`, `z = N⁻¹ y`.
(Consequence used in the lane: away from a pole of `N⁻¹` every other pole of `⟨y,N⁻¹y⟩` can only help: on the right of a pole the value is `-∞`.)
All hypotheses are about abstract operators on real Hilbert spaces; no tower, no gauge field.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AdalyNcwdhTwo.Mono

open scoped RealInnerProductSpace
open ContinuousLinearMap

/-- an operator is symmetric. -/
def Sym {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] (T : Z →L[ℝ] Z) : Prop :=
  ∀ a b, ⟪T a, b⟫ = ⟪a, T b⟫

/-- the inverse of a symmetric unit is symmetric. -/
theorem Sym.inverse {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] {T : Z →L[ℝ] Z}
    (hT : Sym T) (hu : IsUnit T) : Sym (Ring.inverse T) := by
  intro a b
  have h1 : T (Ring.inverse T b) = b := by
    have := Ring.mul_inverse_cancel T hu
    exact congrArg (fun S : Z →L[ℝ] Z => S b) this
  have h2 : T (Ring.inverse T a) = a := by
    have := Ring.mul_inverse_cancel T hu
    exact congrArg (fun S : Z →L[ℝ] Z => S a) this
  calc ⟪Ring.inverse T a, b⟫ = ⟪Ring.inverse T a, T (Ring.inverse T b)⟫ := by rw [h1]
    _ = ⟪T (Ring.inverse T a), Ring.inverse T b⟫ := (hT _ _).symm
    _ = ⟪a, Ring.inverse T b⟫ := by rw [h2]

theorem hasDerivAt_ringInv {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra ℝ R]
    {f : ℝ → R} {f' : R} {c : ℝ} (hf : HasDerivAt f f' c) (hu : IsUnit (f c)) :
    HasDerivAt (fun c => Ring.inverse (f c)) (-(Ring.inverse (f c) * f' * Ring.inverse (f c))) c := by
  obtain ⟨u, hu'⟩ := hu
  have h1 := (hasFDerivAt_ringInverse (𝕜 := ℝ) u).comp_hasDerivAt_of_eq c hf hu'
  have h3 : Ring.inverse (f c) = ↑u⁻¹ := by rw [← hu']; exact Ring.inverse_unit u
  rw [h3]
  have h4 : HasDerivAt (Ring.inverse ∘ f) (-(↑u⁻¹ * f' * ↑u⁻¹ : R)) c := by
    simpa [mulLeftRight_apply] using h1
  exact h4

section
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- the pencil `H(c) = H0 + c B`. -/
noncomputable def Hc (H0 B : X →L[ℝ] X) (c : ℝ) : X →L[ℝ] X := H0 + c • B

/-- `N(c) = Q H(c)⁻¹ Q*`. -/
noncomputable def Nc (H0 B : X →L[ℝ] X) (Q : X →L[ℝ] Y) (Qs : Y →L[ℝ] X) (c : ℝ) : Y →L[ℝ] Y :=
  Q.comp ((Ring.inverse (Hc H0 B c)).comp Qs)

/-- `φ(c) = ⟨y, N(c)⁻¹ y⟩`. -/
noncomputable def phi (H0 B : X →L[ℝ] X) (Q : X →L[ℝ] Y) (Qs : Y →L[ℝ] X) (y : Y) (c : ℝ) : ℝ :=
  ⟪y, Ring.inverse (Nc H0 B Q Qs c) y⟫

theorem hasDerivAt_Hc (H0 B : X →L[ℝ] X) (c : ℝ) : HasDerivAt (Hc H0 B) B c := by
  unfold Hc
  have h1 : HasDerivAt (fun c : ℝ => c • B) ((1 : ℝ) • B) c := (hasDerivAt_id c).smul_const B
  simpa using h1.const_add H0

/-- the linear map `T ↦ Q T Q*`. -/
noncomputable def Phi (Q : X →L[ℝ] Y) (Qs : Y →L[ℝ] X) : (X →L[ℝ] X) →L[ℝ] (Y →L[ℝ] Y) :=
  (compL ℝ Y X Y Q).comp ((compL ℝ Y X X).flip Qs)

theorem Phi_apply (Q : X →L[ℝ] Y) (Qs : Y →L[ℝ] X) (T : X →L[ℝ] X) : Phi Q Qs T = Q.comp (T.comp Qs) := by
  simp [Phi]

theorem hasDerivAt_Nc (H0 B : X →L[ℝ] X) (Q : X →L[ℝ] Y) (Qs : Y →L[ℝ] X) {c : ℝ} (hc : IsUnit (Hc H0 B c)) :
    HasDerivAt (Nc H0 B Q Qs)
      (Q.comp ((-(Ring.inverse (Hc H0 B c) * B * Ring.inverse (Hc H0 B c))).comp Qs)) c := by
  have h1 := hasDerivAt_ringInv (hasDerivAt_Hc H0 B c) hc
  have h2 := (Phi Q Qs).hasFDerivAt.comp_hasDerivAt c h1
  have h3 : (Phi Q Qs) ∘ (fun c => Ring.inverse (Hc H0 B c)) = Nc H0 B Q Qs := by
    funext c'; simp [Function.comp, Phi_apply, Nc]
  rw [h3] at h2
  simpa [Phi_apply] using h2

theorem hasDerivAt_phi (H0 B : X →L[ℝ] X) (Q : X →L[ℝ] Y) (Qs : Y →L[ℝ] X) (y : Y) {c : ℝ}
    (hH : IsUnit (Hc H0 B c)) (hN : IsUnit (Nc H0 B Q Qs c)) :
    HasDerivAt (phi H0 B Q Qs y)
      ⟪y, (Ring.inverse (Nc H0 B Q Qs c))
        (Q ((Ring.inverse (Hc H0 B c)) (B ((Ring.inverse (Hc H0 B c)) (Qs ((Ring.inverse (Nc H0 B Q Qs c)) y))))))⟫ c := by
  have h1 := hasDerivAt_ringInv (hasDerivAt_Nc H0 B Q Qs hH) hN
  have h2 := h1.clm_apply (hasDerivAt_const c y)
  have h3 := (hasDerivAt_const c y).inner ℝ h2
  simp at h3
  exact h3

/-- the derivative is `⟨B G Q* z, G Q* z⟩ ≥ 0`. -/
theorem deriv_phi_nonneg (H0 B : X →L[ℝ] X) (Q : X →L[ℝ] Y) (Qs : Y →L[ℝ] X) (y : Y) {c : ℝ}
    (hH : IsUnit (Hc H0 B c)) (hN : IsUnit (Nc H0 B Q Qs c))
    (hH0 : Sym H0) (hB : Sym B) (hBpsd : ∀ a, 0 ≤ ⟪a, B a⟫) (hQ : ∀ a b, ⟪Q a, b⟫ = ⟪a, Qs b⟫) :
    0 ≤ ⟪y, (Ring.inverse (Nc H0 B Q Qs c))
        (Q ((Ring.inverse (Hc H0 B c)) (B ((Ring.inverse (Hc H0 B c)) (Qs ((Ring.inverse (Nc H0 B Q Qs c)) y))))))⟫ := by
  have hHs : Sym (Hc H0 B c) := by
    intro a b
    simp only [Hc, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hH0 a b, hB a b]
  have hG : Sym (Ring.inverse (Hc H0 B c)) := hHs.inverse hH
  have hQ' : ∀ (a : Y) (w : X), ⟪a, Q w⟫ = ⟪Qs a, w⟫ := fun a w => by
    rw [real_inner_comm, hQ, real_inner_comm]
  have hNs : Sym (Nc H0 B Q Qs c) := by
    intro a b
    simp only [Nc, ContinuousLinearMap.comp_apply]
    rw [hQ, hQ', hG]
  have hNi : Sym (Ring.inverse (Nc H0 B Q Qs c)) := hNs.inverse hN
  set z : Y := (Ring.inverse (Nc H0 B Q Qs c)) y with hz
  set w : X := (Ring.inverse (Hc H0 B c)) (Qs z) with hw
  calc (0 : ℝ) ≤ ⟪w, B w⟫ := hBpsd w
    _ = ⟪z, Q ((Ring.inverse (Hc H0 B c)) (B w))⟫ := by
        rw [hQ', hG]
    _ = ⟪y, (Ring.inverse (Nc H0 B Q Qs c)) (Q ((Ring.inverse (Hc H0 B c)) (B w)))⟫ := by
        rw [hz, hNi]

theorem monotoneOn_phi (H0 B : X →L[ℝ] X) (Q : X →L[ℝ] Y) (Qs : Y →L[ℝ] X) (y : Y) {lo hi : ℝ}
    (hunit : ∀ c ∈ Set.Icc lo hi, IsUnit (Hc H0 B c) ∧ IsUnit (Nc H0 B Q Qs c))
    (hH0 : Sym H0) (hB : Sym B) (hBpsd : ∀ a, 0 ≤ ⟪a, B a⟫) (hQ : ∀ a b, ⟪Q a, b⟫ = ⟪a, Qs b⟫) :
    MonotoneOn (phi H0 B Q Qs y) (Set.Icc lo hi) := by
  have hd : ∀ c ∈ Set.Icc lo hi, HasDerivAt (phi H0 B Q Qs y) _ c := fun c hc =>
    hasDerivAt_phi H0 B Q Qs y (hunit c hc).1 (hunit c hc).2
  refine monotoneOn_of_deriv_nonneg (convex_Icc lo hi) ?_ ?_ ?_
  · exact fun c hc => (hd c hc).continuousAt.continuousWithinAt
  · intro c hc
    exact (hd c (interior_subset hc)).differentiableAt.differentiableWithinAt
  · intro c hc
    have hc' := interior_subset hc
    rw [(hd c hc').deriv]
    exact deriv_phi_nonneg H0 B Q Qs y (hunit c hc').1 (hunit c hc').2 hH0 hB hBpsd hQ

#print axioms monotoneOn_phi

end

end AdalyNcwdhTwo.Mono
