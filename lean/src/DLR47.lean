import DLR42

/-!
# DL47 -- the UPPER bound of the abstract `G⁻¹` form by first-order data (`GinvHyp`)

* `GamHyp.T_le` : `‖T v‖ ≤ ‖D* v‖` — `T = (1 − XΓ⁻¹X*) D*` and `XΓ⁻¹X*` is the orthogonal projection onto `ran X`
  (`⟪y − Xz, Xz⟫ = 0` for `z = Γ⁻¹X*y`, from `Γ Γ⁻¹ = 1`, `Γ = X*X`).
* `GamHyp.Z_unw` : `‖Z v‖ ≤ ‖D*v‖/c`, `‖D Z v‖ ≤ ‖D*v‖/√c`;  `GamHyp.W_unw` : `‖W v‖ ≤ ‖v‖ + ‖D*v‖/√c`.
* **`GinvHyp.Ginv_upper`** : `⟪v,G⁻¹v⟫ ≤ (‖Cv‖ + κ‖D*v‖/c)² + ν(‖v‖ + ‖D*v‖/√c)² + ‖D*v‖² + M‖Q_b v‖²`.
This is what turns a SMOOTH competitor (small `‖Cv‖`, `‖D*v‖` at the scale of `‖v‖/n`) into the sharp lower bound of `N = Q G Q*`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace

namespace GamHyp

variable {S E Y : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y]
variable (G : GamHyp S E Y)

/-- `‖y − XΓ⁻¹X*y‖ ≤ ‖y‖` -/
theorem proj_compl_le (y : S) :
    ‖y - G.H.X (G.Gami (ContinuousLinearMap.adjoint G.H.X y))‖ ≤ ‖y‖ := by
  set z := G.Gami (ContinuousLinearMap.adjoint G.H.X y) with hz
  have hGz : ContinuousLinearMap.adjoint G.H.X (G.H.X z) = ContinuousLinearMap.adjoint G.H.X y := by
    have h := G.Gam_Gami (ContinuousLinearMap.adjoint G.H.X y)
    rw [← hz] at h
    exact h
  have horth : ⟪y - G.H.X z, G.H.X z⟫ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left, map_sub, hGz, sub_self, inner_zero_left]
  have hsq : ‖y‖ ^ 2 = ‖y - G.H.X z‖ ^ 2 + ‖G.H.X z‖ ^ 2 := by
    have e : y = (y - G.H.X z) + G.H.X z := by abel
    conv_lhs => rw [e]
    rw [norm_add_sq_real, horth]; ring
  have h2 : ‖y - G.H.X z‖ ^ 2 ≤ ‖y‖ ^ 2 := by rw [hsq]; nlinarith [sq_nonneg ‖G.H.X z‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

theorem T_le (v : E) : ‖G.T v‖ ≤ ‖ContinuousLinearMap.adjoint G.D v‖ := by
  have e : G.T v = ContinuousLinearMap.adjoint G.D v
      - G.H.X (G.Gami (ContinuousLinearMap.adjoint G.H.X (ContinuousLinearMap.adjoint G.D v))) := by
    simp only [T, F, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_comp]
  rw [e]
  exact G.proj_compl_le _

theorem Z_unw (v : E) : ‖G.Z v‖ ≤ ‖ContinuousLinearMap.adjoint G.D v‖ / G.c
    ∧ ‖G.D (G.Z v)‖ ≤ ‖ContinuousLinearMap.adjoint G.D v‖ / Real.sqrt G.c := by
  have hc := G.hc
  obtain ⟨h1, h2⟩ := G.Linv_unw (G.T v)
  have hT := G.T_le v
  refine ⟨h1.trans (div_le_div_of_nonneg_right hT hc.le), ?_⟩
  exact h2.trans (div_le_div_of_nonneg_right hT (Real.sqrt_nonneg _))

theorem W_unw (v : E) : ‖G.W v‖ ≤ ‖v‖ + ‖ContinuousLinearMap.adjoint G.D v‖ / Real.sqrt G.c := by
  have e : G.W v = v - G.D (G.Z v) := by simp [W]
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (G.Z_unw v).2)

end GamHyp

namespace GinvHyp

variable {S E Y P B : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]
variable (I : GinvHyp S E Y P B)

theorem CW_unw (v : E) : ‖I.C (I.Gm.W v)‖ ≤ ‖I.C v‖ + I.κ * (‖ContinuousLinearMap.adjoint I.D v‖ / I.c) := by
  have e : I.C (I.Gm.W v) = I.C v - (I.C ∘L I.D) (I.Gm.Z v) := by
    have := congrArg (fun T => T v) (I.CW_eq)
    simpa using this
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  exact mul_le_mul I.hKn (I.Gm.Z_unw v).1 (norm_nonneg _) I.hκ

/-- **the upper bound of the `G⁻¹` form** -/
theorem Ginv_upper (v : E) :
    ⟪v, I.Ginv v⟫ ≤ (‖I.C v‖ + I.κ * (‖ContinuousLinearMap.adjoint I.D v‖ / I.c)) ^ 2
      + I.ν * (‖v‖ + ‖ContinuousLinearMap.adjoint I.D v‖ / Real.sqrt I.c) ^ 2
      + ‖ContinuousLinearMap.adjoint I.D v‖ ^ 2 + I.M * ‖I.Qb v‖ ^ 2 := by
  rw [I.Ginv_form]
  have h1 : ‖I.C (I.Gm.W v)‖ ^ 2 ≤ (‖I.C v‖ + I.κ * (‖ContinuousLinearMap.adjoint I.D v‖ / I.c)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (I.CW_unw v) 2
  have h2 : ⟪I.Gm.W v, I.Dp (I.Gm.W v)⟫ ≤ I.ν * (‖v‖ + ‖ContinuousLinearMap.adjoint I.D v‖ / Real.sqrt I.c) ^ 2 := by
    have hW := I.Gm.W_unw v
    have hb : ⟪I.Gm.W v, I.Dp (I.Gm.W v)⟫ ≤ I.ν * ‖I.Gm.W v‖ ^ 2 := by
      refine (real_inner_le_norm _ _).trans ?_
      have := (ContinuousLinearMap.le_opNorm I.Dp (I.Gm.W v)).trans
        (mul_le_mul_of_nonneg_right I.hDpn (norm_nonneg _))
      calc ‖I.Gm.W v‖ * ‖I.Dp (I.Gm.W v)‖ ≤ ‖I.Gm.W v‖ * (I.ν * ‖I.Gm.W v‖) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = I.ν * ‖I.Gm.W v‖ ^ 2 := by ring
    exact hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hW 2) I.hν)
  have h3 : ‖I.Gm.T v‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint I.D v‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (I.Gm.T_le v) 2
  linarith

end GinvHyp

#print axioms GamHyp.proj_compl_le
#print axioms GamHyp.T_le
#print axioms GamHyp.Z_unw
#print axioms GamHyp.W_unw
#print axioms GinvHyp.CW_unw
#print axioms GinvHyp.Ginv_upper

end AdalyFormal.DLayer
