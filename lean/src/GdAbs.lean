import D2Cons

/-!
# GdAbs -- generic Hilbert-space lemma: if the source `J` lies in the range of `Q*` with a preimage `j0` orthogonal to every value of `C2`,
then `Delta2 = 0` and `G1inv = Ginv`.  (`<H f, Q* j0> = <Q H f, j0> = <f, j0>` when `Q G Q*` is a unit, and `H = 0` otherwise.)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2

section generic
variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable (D : BaseDataS E S F)

/-- `Q (H f) = f` whenever `Q G Q*` is a unit. -/
theorem Q_H_apply (hN : IsUnit ((D.Q.comp D.G).comp D.Qs)) (f : F) : D.Q (D.H f) = f := by
  unfold BaseDataS.H
  simp only [ContinuousLinearMap.comp_apply]
  have h := ContinuousLinearMap.ext_iff.mp (Ring.mul_inverse_cancel _ hN) f
  simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply] using h

theorem inner_H_Qs (j0 f : F) (hf : ⟪f, j0⟫ = 0) : ⟪D.H f, D.Qs j0⟫ = 0 := by
  by_cases hN : IsUnit ((D.Q.comp D.G).comp D.Qs)
  · rw [← D.Q_adj, Q_H_apply D hN f]; exact hf
  · have : D.H = 0 := by
      unfold BaseDataS.H
      rw [Ring.inverse_non_unit _ hN]
      simp only [ContinuousLinearMap.comp_zero]
    rw [this]; simp

theorem Delta2_eq_zero (hL : D.Laws) (j0 : F) (hJ : D.J = D.Qs j0) (hC : ∀ A, ⟪D.C2 A, j0⟫ = 0) :
    D.Delta2 hL = 0 := by
  obtain ⟨hs, hf⟩ := D.Delta2_spec hL
  refine symm_unique hs (fun x y => by simp) (fun A => ?_)
  rw [hf A, hJ, inner_H_Qs D j0 _ (hC A)]
  simp

theorem G1inv_eq_Ginv_of (hL : D.Laws) (j0 : F) (hJ : D.J = D.Qs j0) (hC : ∀ A, ⟪D.C2 A, j0⟫ = 0)
    {G1inv : E →L[ℝ] E} (hG : D.IsG1inv G1inv) : G1inv = D.Ginv := by
  have h := D.G1inv_unique hG (D.isG1inv_sub hL)
  rw [h, Delta2_eq_zero D hL j0 hJ hC]; simp

theorem inner_H1_Qs (G1inv : E →L[ℝ] E) (j0 f : F) (hf : ⟪f, j0⟫ = 0) : ⟪D.H1 G1inv f, D.Qs j0⟫ = 0 := by
  by_cases hN : IsUnit ((D.Q.comp (D.G1 G1inv)).comp D.Qs)
  · rw [← D.Q_adj]
    have : D.Q (D.H1 G1inv f) = f := by
      unfold BaseDataS.H1
      simp only [ContinuousLinearMap.comp_apply]
      have h := ContinuousLinearMap.ext_iff.mp (Ring.mul_inverse_cancel _ hN) f
      simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply] using h
    rw [this]; exact hf
  · have : D.H1 G1inv = 0 := by
      unfold BaseDataS.H1
      rw [Ring.inverse_non_unit _ hN]
      simp only [ContinuousLinearMap.comp_zero]
    rw [this]; simp

end generic

#print axioms inner_H1_Qs
#print axioms Delta2_eq_zero
#print axioms G1inv_eq_Ginv_of

#print axioms Q_H_apply
#print axioms inner_H_Qs

end AdalyFormal.D1Guarded
