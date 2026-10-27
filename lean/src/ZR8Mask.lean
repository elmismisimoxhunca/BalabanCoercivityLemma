import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# ZR8Mask -- derivatives of a function that reads its argument only through a projection `χ`

If `g x = g (χ x)` for a continuous linear `χ`, then `D g(0) v = D g(0) (χ v)` (no differentiability hypothesis: when `g` is not
differentiable both sides are Mathlib's junk `0`), and, if `χ` is idempotent, `D² g(0)(v,w) = D² g(0)(χ v, χ w)`.
Used with `χ` = restriction of a coordinate field to the bonds a component of the averaging map actually reads.
-/
set_option autoImplicit false
namespace AdalyFormal.StatementLaneR8

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- first order: the derivative at `0` of a function of `χ x` only sees `χ v`. -/
theorem fderiv_mask (χ : E →L[ℝ] E) (g : E → F) (hg : ∀ x, g x = g (χ x)) (v : E) :
    fderiv ℝ g 0 v = fderiv ℝ g 0 (χ v) := by
  by_cases hd : DifferentiableAt ℝ g 0
  · have hgc : g = g ∘ χ := funext hg
    have hD : fderiv ℝ g 0 = (fderiv ℝ g 0).comp χ := by
      have h1 : fderiv ℝ (g ∘ χ) 0 = (fderiv ℝ g (χ 0)).comp (fderiv ℝ χ 0) :=
        fderiv_comp 0 (by rw [map_zero]; exact hd) χ.differentiableAt
      rw [map_zero, ContinuousLinearMap.fderiv, ← hgc] at h1
      exact h1
    calc fderiv ℝ g 0 v = ((fderiv ℝ g 0).comp χ) v := by rw [← hD]
      _ = fderiv ℝ g 0 (χ v) := rfl
  · rw [fderiv_zero_of_not_differentiableAt hd]; rfl

/-- translation: `g` has the same germ at `x` and at `χ x`. -/
theorem germ_mask (χ : E →L[ℝ] E) (hχ : ∀ x, χ (χ x) = χ x) (g : E → F) (hg : ∀ x, g x = g (χ x)) (x : E) :
    (fun h => g (h + x)) = (fun h => g (h + χ x)) := by
  funext h
  rw [hg (h + x), hg (h + χ x), map_add, map_add, hχ]

theorem fderiv_eq_mask (χ : E →L[ℝ] E) (hχ : ∀ x, χ (χ x) = χ x) (g : E → F) (hg : ∀ x, g x = g (χ x)) (x : E) :
    fderiv ℝ g x = fderiv ℝ g (χ x) := by
  have h1 := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := (0 : E)) x
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := (0 : E)) (χ x)
  rw [zero_add] at h1 h2
  rw [← h1, ← h2, germ_mask χ hχ g hg x]

theorem differentiableAt_mask_iff (χ : E →L[ℝ] E) (hχ : ∀ x, χ (χ x) = χ x) (g : E → F) (hg : ∀ x, g x = g (χ x))
    (x : E) : DifferentiableAt ℝ g x ↔ DifferentiableAt ℝ g (χ x) := by
  have h1 := differentiableAt_comp_add_right (𝕜 := ℝ) (f := g) (x := (0 : E)) x
  have h2 := differentiableAt_comp_add_right (𝕜 := ℝ) (f := g) (x := (0 : E)) (χ x)
  rw [zero_add] at h1 h2
  rw [← h1, ← h2, germ_mask χ hχ g hg x]

/-- the derivative at every point annihilates `ker χ`: `D g(x) = D g(x) ∘ χ`. -/
theorem fderiv_comp_mask (χ : E →L[ℝ] E) (hχ : ∀ x, χ (χ x) = χ x) (g : E → F) (hg : ∀ x, g x = g (χ x)) (x : E) :
    fderiv ℝ g x = (fderiv ℝ g x).comp χ := by
  by_cases hd : DifferentiableAt ℝ g x
  · have hgc : g = g ∘ χ := funext hg
    have hd' : DifferentiableAt ℝ g (χ x) := (differentiableAt_mask_iff χ hχ g hg x).mp hd
    have h1 : fderiv ℝ (g ∘ χ) x = (fderiv ℝ g (χ x)).comp (fderiv ℝ χ x) :=
      fderiv_comp x hd' χ.differentiableAt
    rw [ContinuousLinearMap.fderiv, ← hgc, ← fderiv_eq_mask χ hχ g hg x] at h1
    exact h1
  · rw [fderiv_zero_of_not_differentiableAt hd]; rfl

/-- second order: `D² g(0)(v,w) = D² g(0)(χ v, χ w)` for idempotent `χ`. -/
theorem fderiv2_mask (χ : E →L[ℝ] E) (hχ : ∀ x, χ (χ x) = χ x) (g : E → F) (hg : ∀ x, g x = g (χ x)) (v w : E) :
    fderiv ℝ (fderiv ℝ g) 0 v w = fderiv ℝ (fderiv ℝ g) 0 (χ v) (χ w) := by
  -- step 1: `Φ = fderiv g` reads `x` only through `χ x`
  have h1 : fderiv ℝ (fderiv ℝ g) 0 v = fderiv ℝ (fderiv ℝ g) 0 (χ v) :=
    fderiv_mask χ (fderiv ℝ g) (fderiv_eq_mask χ hχ g hg) v
  rw [h1]
  -- step 2: `Φ x = (Φ x) ∘ χ` for every `x`, so the derivative of `Φ` takes values in `{T | T = T ∘ χ}`
  set u := χ v
  let Cχ : (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) := (ContinuousLinearMap.compL ℝ E E F).flip χ
  have hCχ : ∀ T : E →L[ℝ] F, Cχ T = T.comp χ := fun T => rfl
  have hΦ : fderiv ℝ g = Cχ ∘ fderiv ℝ g := by
    funext x; rw [Function.comp_apply, hCχ]; exact fderiv_comp_mask χ hχ g hg x
  by_cases hd : DifferentiableAt ℝ (fderiv ℝ g) 0
  · have h2 : fderiv ℝ (Cχ ∘ fderiv ℝ g) 0 = (fderiv ℝ Cχ (fderiv ℝ g 0)).comp (fderiv ℝ (fderiv ℝ g) 0) :=
      fderiv_comp 0 Cχ.differentiableAt hd
    rw [ContinuousLinearMap.fderiv, ← hΦ] at h2
    have h3 : fderiv ℝ (fderiv ℝ g) 0 u = Cχ (fderiv ℝ (fderiv ℝ g) 0 u) := by
      conv_lhs => rw [h2]
      rfl
    calc fderiv ℝ (fderiv ℝ g) 0 u w = (Cχ (fderiv ℝ (fderiv ℝ g) 0 u)) w := by rw [← h3]
      _ = fderiv ℝ (fderiv ℝ g) 0 u (χ w) := rfl
  · rw [fderiv_zero_of_not_differentiableAt hd]; rfl

#print axioms fderiv_mask
#print axioms fderiv_eq_mask
#print axioms fderiv_comp_mask
#print axioms fderiv2_mask

end AdalyFormal.StatementLaneR8
