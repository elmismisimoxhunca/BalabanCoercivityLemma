import TL3c

set_option autoImplicit false
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace

section riesz
variable {D X Xt Y Yt : Type} [Fintype D] [Fintype X] [Fintype Xt] [Fintype Y] [Fintype Yt]
  [DecidableEq X] [DecidableEq Xt] [DecidableEq Y] [DecidableEq Yt]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A deck-equivariant `Ot`, whose periodic–periodic form is `N` times that of `O`, descends to `O`. -/
theorem desc_of_riesz [Nonempty D] (cX : Cov D Xt X)
    (O : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : X => E))
    (Ot : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Xt => E))
    (c1 : ∀ d u v, ⟪cX.pull d u, Ot (cX.pull d v)⟫ = ⟪u, Ot v⟫)
    (c2 : ∀ y x, ⟪cX.ell y, Ot (cX.ell x)⟫ = (Fintype.card D : ℝ) * ⟪y, O x⟫) : Desc cX cX O Ot := by
  have hequi : Equi cX cX Ot := by
    intro d
    ext1 v
    simp only [ContinuousLinearMap.comp_apply]
    refine ext_inner_left ℝ (fun u => ?_)
    have h1 := c1 d (liftF (⇑(cX.τ d).symm) u) v
    rw [liftF_perm_cancel] at h1
    rw [h1, ← inner_liftF_perm]
  have hN : (Fintype.card D : ℝ) ≠ 0 := by
    have : 0 < Fintype.card D := Fintype.card_pos
    positivity
  have he1 : E1 cX cX O Ot := by
    ext1 x
    simp only [ContinuousLinearMap.comp_apply]
    -- Ot (ell x) is deck invariant
    have hinv : ∀ d, cX.pull d (Ot (cX.ell x)) = Ot (cX.ell x) := by
      intro d
      have := congrArg (fun T => T (cX.ell x)) (hequi d)
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [cX.pull_ell] at this
      exact this.symm
    have hsum : cX.ell (cX.sig (Ot (cX.ell x))) = (Fintype.card D : ℝ) • Ot (cX.ell x) := by
      rw [← cX.sum_pull]
      simp only [hinv, Finset.sum_const, Finset.card_univ]
      exact (Nat.cast_smul_eq_nsmul ℝ _ _).symm
    have hz : cX.sig (Ot (cX.ell x)) = (Fintype.card D : ℝ) • O x := by
      refine ext_inner_left ℝ (fun y => ?_)
      rw [real_inner_smul_right, ← cX.inner_ell_left, c2]
    rw [hz, map_smul] at hsum
    have := congrArg (fun w => (Fintype.card D : ℝ)⁻¹ • w) hsum
    simp only [smul_smul, inv_mul_cancel₀ hN, one_smul] at this
    exact this.symm
  exact desc_of_e1_equi he1 hequi

end riesz

end AdalyFormal.Thin
