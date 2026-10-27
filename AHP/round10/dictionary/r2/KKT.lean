import DrEquiv
/-! Inverse-free certificates for the actual frozen constrained source multiplier.
The hypotheses about the two units are the flat-point facts supplied by round 9.
The certificate identities themselves still have to be checked on a physical lift. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.Round10.Dictionary.KKT
open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2
variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The full constraint matrix, not a boundary compression. -/
def N (D : BaseDataS E S F) : F →L[ℝ] F := (D.Q.comp D.G).comp D.Qs

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ S] [FiniteDimensional ℝ F] in
theorem Q_H (D : BaseDataS E S F) (hN : IsUnit (N D)) (z : F) : D.Q (D.H z) = z := by
  have h := congrArg (fun A : F →L[ℝ] F => A z) (Ring.mul_inverse_cancel (N D) hN)
  exact h

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ S] [FiniteDimensional ℝ F] in
theorem Ginv_H (D : BaseDataS E S F) (hB : IsUnit D.Ginv) (z : F) :
    D.Ginv (D.H z) = D.Qs (Ring.inverse (N D) z) := by
  have h := congrArg (fun A : E →L[ℝ] E => A (D.Qs (Ring.inverse (N D) z)))
    (Ring.mul_inverse_cancel D.Ginv hB)
  exact h

/-- A primal residual and a multiplier, checked WITHOUT evaluating any inverse,
identify H*J exactly. This is sufficient for every quadratic jet simultaneously. -/
theorem source_of_certificate (D : BaseDataS E S F) (hL : D.Laws)
    (hB : IsUnit D.Ginv) (hN : IsUnit (N D)) (J x : E) (h : F)
    (hx : D.Q x = 0) (hr : D.Ginv x + D.Qs h = J) :
    ContinuousLinearMap.adjoint D.H J = h := by
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right, ← hr, inner_add_right]
  have hz : ⟪D.H z, D.Ginv x⟫ = 0 := by
    rw [← D.Ginv_symm hL, Ginv_H D hB, real_inner_comm, ← D.Q_adj, hx, inner_zero_left]
  rw [hz, zero_add, ← D.Q_adj, Q_H D hN]

/-- Equivalent weak certificate: only the residual paired with all vectors is needed. -/
theorem source_of_weak_certificate (D : BaseDataS E S F) (hL : D.Laws)
    (hB : IsUnit D.Ginv) (hN : IsUnit (N D)) (J x : E) (h : F)
    (hx : D.Q x = 0)
    (hr : ∀ y : E, ⟪y, D.Ginv x⟫ + ⟪D.Q y, h⟫ = ⟪y, J⟫) :
    ContinuousLinearMap.adjoint D.H J = h := by
  apply source_of_certificate D hL hB hN J x h hx
  apply ext_inner_left ℝ
  intro y
  rw [inner_add_right, ← D.Q_adj]
  exact hr y

/-- Pairing version needs no external translation or kernel-simplicity hypothesis. -/
theorem coupling_of_certificate (D : BaseDataS E S F) (hL : D.Laws)
    (hB : IsUnit D.Ginv) (hN : IsUnit (N D)) (J x : E) (h z : F)
    (hx : D.Q x = 0) (hr : D.Ginv x + D.Qs h = J) :
    2 * ⟪D.H z, J⟫ = 2 * ⟪z, h⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, source_of_certificate D hL hB hN J x h hx hr]

/-- Normalization of the one-dimensional candidate. The physical lift is not
asserted here. If x has two-site entries (a/2,-a/2), the path Laplacian contributes
(3a+left)/2 and -(3a+right)/2. Q* contributes h/8 on both entries. -/
theorem two_site_residual_iff (a left right h d : ℝ) :
    ((3 * a + left) / 2 + h / 8 = d / 2 ∧
     -(3 * a + right) / 2 + h / 8 = -d / 4) ↔
    (6 * a + left + right = (3 / 2 : ℝ) * d ∧
     h = d - 2 * left + 2 * right) := by
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The pair-average constraint is exact with this normalization. -/
theorem alternating_pair_constraint (a : ℝ) : ((a / 2) + (-a / 2)) / 2 = 0 := by ring

/-- The finite recurrence plus multiplier formula gives both fine-site residuals. -/
theorem recurrence_fine_residuals (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ j < n + 1, 6 * a j + (if j = 0 then 0 else a (j - 1)) + a (j + 1) =
      if j = 0 then (3 / 2 : ℝ) else 0) (j : ℕ) (hj : j < n + 1) :
    let l := if j = 0 then 0 else a (j - 1)
    let d : ℝ := if j = 0 then 1 else 0
    let h := d - 2 * l + 2 * a (j + 1)
    ((3 * a j + l) / 2 + h / 8 = d / 2 ∧
      -(3 * a j + a (j + 1)) / 2 + h / 8 = -d / 4) := by
  dsimp only
  apply (two_site_residual_iff _ _ _ _ _).mpr
  refine ⟨?_, rfl⟩
  have hh := ha j hj
  split_ifs at * <;> linarith

#print axioms N
#print axioms Q_H
#print axioms Ginv_H
#print axioms source_of_certificate
#print axioms source_of_weak_certificate
#print axioms coupling_of_certificate
#print axioms two_site_residual_iff
#print axioms alternating_pair_constraint
#print axioms recurrence_fine_residuals
end AdalyFormal.Round10.Dictionary.KKT
