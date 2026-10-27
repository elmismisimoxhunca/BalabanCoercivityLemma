import NuB1
import NuBridge

/-!
# NuB2 -- the pencil structure on the fixed space: `Qs` is `t`-independent on `Ad_h`-fixed vectors; `Q` on sigma_3 fields (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyNcwdhTwo.Bridge

open scoped RealInnerProductSpace
open AdalyNcwdhTwo.Mono

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]

/-- two equivariant operators that agree on the fixed space have adjoints that agree on the fixed space. -/
theorem Qs_fixed_of_Q {TE : E →L[ℝ] E} {TF : F →L[ℝ] F} (hTE2 : ∀ x, TE (TE x) = x) (hTF2 : ∀ y, TF (TF y) = y)
    (hTFs : Sym TF)
    {Q Q' : E →L[ℝ] F} {Qs Qs' : F →L[ℝ] E} (hQ : ∀ x y, ⟪Q x, y⟫ = ⟪x, Qs y⟫) (hQ' : ∀ x y, ⟪Q' x, y⟫ = ⟪x, Qs' y⟫)
    (hQc : ∀ x, Q (TE x) = TF (Q x)) (hQc' : ∀ x, Q' (TE x) = TF (Q' x))
    (hQeq : ∀ x, TE x = x → Q x = Q' x) {y : F} (hy : TF y = y) : Qs y = Qs' y := by
  apply ext_inner_left ℝ
  intro x
  rw [← hQ, ← hQ']
  set x1 : E := Pr TE x with hx1
  set x2 : E := x - Pr TE x with hx2
  have hx1f : TE x1 = x1 := TE_Pr hTE2 x
  have hx2a : TE x2 = -x2 := TE_decomp hTE2 x
  have hsplit : x = x1 + x2 := by rw [hx1, hx2]; abel
  have e1 : Q x1 = Q' x1 := hQeq x1 hx1f
  set u : F := Q x2 - Q' x2 with hu
  have hTu : TF u = -u := by
    rw [hu, map_sub, ← hQc, ← hQc', hx2a, map_neg, map_neg]; abel
  have hu0 : ⟪u, y⟫ = 0 := by
    have h1 : ⟪TF u, y⟫ = ⟪u, TF y⟫ := hTFs u y
    rw [hTu, hy, inner_neg_left] at h1
    linarith
  have : ⟪Q x, y⟫ - ⟪Q' x, y⟫ = 0 := by
    rw [hsplit, map_add, map_add, inner_add_left, inner_add_left, e1]
    have : ⟪Q x2, y⟫ - ⟪Q' x2, y⟫ = ⟪u, y⟫ := by rw [hu, inner_sub_left]
    linarith
  linarith

end

end AdalyNcwdhTwo.Bridge
