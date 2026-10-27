import DLR10

/-!
# DL11 -- resolvent differences and `X = G'Q'*` under the weights (abstract)

For `H : SiteHyp` and `‖Qp‖ ≤ q`:
* `Linv_le` (unweighted): `c‖G' y‖ ≤ ‖y‖`;  `X_le`: `‖Xu‖ ≤ (q/c)‖u‖`;  `DX_le`: `‖D Xu‖ ≤ (q/√c)‖u‖`.
* `resolvent` : `(G')⁺y − G'y = (G')⁺ ((L − L⁺) G'y)`;  `L_sub_cjpL` : the expansion of `L − L⁺` in the commutators.
* `resolvent_bound` : `‖(G')⁺y − G'y‖ ≤ R0(G'y)`, `‖D((G')⁺y − G'y)‖ ≤ R1(G'y)` with
  `R0(x) = (4/c)δD‖Dx‖ + (√(48/c)δD + (8/c)δD² + (4/c)m(2qδQ+δQ²))‖x‖`,
  `R1(x) = √(12/c)δD‖Dx‖ + (√24 δD + 2√(12/c)δD² + √(12/c)m(2qδQ+δQ²))‖x‖`.
* `Xdiff` : `‖X⁺u − Xu‖ ≤ εX‖u‖`, `DXdiff` : `‖D(X⁺u − Xu)‖ ≤ εDX‖u‖` (explicit `epsX`, `epsDX`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace

namespace SiteHyp

variable {S E Y : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y]
variable (H : SiteHyp S E Y)

theorem L_sym (y z : S) : ⟪H.L y, z⟫ = ⟪y, H.L z⟫ := by
  simp only [L, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

theorem L_Linv (x : S) : H.L (H.Linv x) = x := H.hL1 x
theorem Linv_L (x : S) : H.Linv (H.L x) = x := H.hL2 x

/-- unweighted: `c‖G'y‖ ≤ ‖y‖` -/
theorem Linv_le (y : S) : H.c * ‖H.Linv y‖ ≤ ‖y‖ := by
  set x := H.Linv y
  have h1 : H.c * ‖x‖ ^ 2 ≤ ⟪x, H.L x⟫ := H.hcoer x
  rw [H.L_Linv] at h1
  have h2 : ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm _ _
  by_cases h0 : ‖x‖ = 0
  · rw [h0]; simp
  have hp : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have : H.c * ‖x‖ * ‖x‖ ≤ ‖y‖ * ‖x‖ := by nlinarith
  exact le_of_mul_le_mul_right this hp

theorem cjp_Linv_L (x : S) : cjp H.ωS H.ωS H.Linv (cjp H.ωS H.ωS H.L x) = x := by
  rw [cjp_apply, cjp_apply, H.ωS.wi_w, H.Linv_L, H.ωS.w_wi]

theorem resolvent (y : S) :
    cjp H.ωS H.ωS H.Linv y - H.Linv y = cjp H.ωS H.ωS H.Linv ((H.L - cjp H.ωS H.ωS H.L) (H.Linv y)) := by
  rw [ContinuousLinearMap.sub_apply, map_sub, H.cjp_Linv_L, H.L_Linv]

/-- `L⁺ = (D⁻)* D⁺ + m (Qp⁻)* Qp⁺` -/
theorem cjpL_eq : cjp H.ωS H.ωS H.L = ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D) ∘L cjp H.ωS H.ωE H.D
    + H.m • (ContinuousLinearMap.adjoint (cjm H.ωS H.ωY H.Qp) ∘L cjp H.ωS H.ωY H.Qp) := by
  rw [L, cjp_add, cjp_smul, cjp_comp H.ωS H.ωE H.ωS, cjp_comp H.ωS H.ωY H.ωS, adjoint_cjm, adjoint_cjm]

/-- the expansion of `(L − L⁺)x` in the commutators -/
theorem L_sub_cjpL (x : S) :
    (H.L - cjp H.ωS H.ωS H.L) x
      = -(ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D - H.D) (H.D x)
          + ContinuousLinearMap.adjoint H.D ((cjp H.ωS H.ωE H.D - H.D) x)
          + ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D - H.D) ((cjp H.ωS H.ωE H.D - H.D) x))
        - H.m • (ContinuousLinearMap.adjoint (cjm H.ωS H.ωY H.Qp - H.Qp) (H.Qp x)
          + ContinuousLinearMap.adjoint H.Qp ((cjp H.ωS H.ωY H.Qp - H.Qp) x)
          + ContinuousLinearMap.adjoint (cjm H.ωS H.ωY H.Qp - H.Qp) ((cjp H.ωS H.ωY H.Qp - H.Qp) x)) := by
  rw [ContinuousLinearMap.sub_apply, H.cjpL_eq]
  simp only [L, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub, map_add, map_smul]
  module

theorem norm_adj_sub_le {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [CompleteSpace A] [CompleteSpace B] (T : A →L[ℝ] B) (δ : ℝ) (hT : ‖T‖ ≤ δ) (v : B) :
    ‖ContinuousLinearMap.adjoint T v‖ ≤ δ * ‖v‖ := by
  have := (ContinuousLinearMap.adjoint T).le_opNorm v
  rw [LinearIsometryEquiv.norm_map] at this
  exact this.trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))

theorem norm_op_le {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] (T : A →L[ℝ] B) (δ : ℝ) (hT : ‖T‖ ≤ δ) (v : A) : ‖T v‖ ≤ δ * ‖v‖ :=
  (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))

/-- the weighted `G'` bounds as functions -/
theorem cjpLinv_le (g : S) : ‖cjp H.ωS H.ωS H.Linv g‖ ≤ (4 / H.c) * ‖g‖ := by
  have h := H.Linv_cjp g
  have hc := H.hc
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]; linarith

theorem D_cjpLinv_le (g : S) : ‖H.D (cjp H.ωS H.ωS H.Linv g)‖ ≤ Real.sqrt (12 / H.c) * ‖g‖ := by
  have h := H.D_Linv_cjp g
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg g), ← Real.sqrt_mul (by have := H.hc; positivity)]
  exact Real.sqrt_le_sqrt h

theorem cjpLinvDadj_le (v : E) :
    ‖cjp H.ωS H.ωS H.Linv (ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D) v)‖ ≤ Real.sqrt (48 / H.c) * ‖v‖ ∧
    ‖H.D (cjp H.ωS H.ωS H.Linv (ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D) v))‖ ≤ Real.sqrt 24 * ‖v‖ := by
  obtain ⟨h1, h2⟩ := H.LinvDadj_cjp v
  refine ⟨?_, ?_⟩
  · rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by have := H.hc; positivity)]
    exact Real.sqrt_le_sqrt h1
  · rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt h2

/-- the resolvent difference, bounded -/
theorem resolvent_bound (q : ℝ) (hq : 0 ≤ q) (hQ : ‖H.Qp‖ ≤ q) (y : S) :
    ‖cjp H.ωS H.ωS H.Linv y - H.Linv y‖
        ≤ (4 / H.c) * H.δD * ‖H.D (H.Linv y)‖
          + (Real.sqrt (48 / H.c) * H.δD + (8 / H.c) * H.δD ^ 2 + (4 / H.c) * H.m * (2 * q * H.δQ + H.δQ ^ 2))
            * ‖H.Linv y‖ ∧
    ‖H.D (cjp H.ωS H.ωS H.Linv y - H.Linv y)‖
        ≤ Real.sqrt (12 / H.c) * H.δD * ‖H.D (H.Linv y)‖
          + (Real.sqrt 24 * H.δD + 2 * Real.sqrt (12 / H.c) * H.δD ^ 2
              + Real.sqrt (12 / H.c) * H.m * (2 * q * H.δQ + H.δQ ^ 2)) * ‖H.Linv y‖ := by
  set x := H.Linv y with hx
  set eP := cjp H.ωS H.ωE H.D - H.D
  set eM := cjm H.ωS H.ωE H.D - H.D
  set fP := cjp H.ωS H.ωY H.Qp - H.Qp
  set fM := cjm H.ωS H.ωY H.Qp - H.Qp
  have hres := H.resolvent y
  rw [← hx, H.L_sub_cjpL x] at hres
  -- D* (eP x) = (D⁻)*(eP x) − eM*(eP x)
  have hDadj : ContinuousLinearMap.adjoint H.D (eP x)
      = ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D) (eP x) - ContinuousLinearMap.adjoint eM (eP x) := by
    simp only [eM, map_sub, ContinuousLinearMap.sub_apply]; abel
  set Gp := cjp H.ωS H.ωS H.Linv
  -- the six pieces
  set t1 := Gp (ContinuousLinearMap.adjoint eM (H.D x))
  set t2 := Gp (ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D) (eP x))
  set t2' := Gp (ContinuousLinearMap.adjoint eM (eP x))
  set t3 := Gp (ContinuousLinearMap.adjoint eM (eP x))
  set u1 := Gp (ContinuousLinearMap.adjoint fM (H.Qp x))
  set u2 := Gp (ContinuousLinearMap.adjoint H.Qp (fP x))
  set u3 := Gp (ContinuousLinearMap.adjoint fM (fP x))
  have hsplit : Gp ((-(ContinuousLinearMap.adjoint eM (H.D x) + ContinuousLinearMap.adjoint H.D (eP x)
          + ContinuousLinearMap.adjoint eM (eP x)))
        - H.m • (ContinuousLinearMap.adjoint fM (H.Qp x) + ContinuousLinearMap.adjoint H.Qp (fP x)
          + ContinuousLinearMap.adjoint fM (fP x)))
      = -(t1 + (t2 - t2') + t3) - H.m • (u1 + u2 + u3) := by
    rw [hDadj]
    simp only [map_sub, map_neg, map_add, map_smul, t1, t2, t2', t3, u1, u2, u3]
  rw [hsplit] at hres
  have hδD := H.hδD
  have hδQ := H.hδQ
  have hc := H.hc
  have hm := H.hm
  -- norms of the commutator vectors
  have nePx : ‖eP x‖ ≤ H.δD * ‖x‖ := norm_op_le eP H.δD H.hDp x
  have nfPx : ‖fP x‖ ≤ H.δQ * ‖x‖ := norm_op_le fP H.δQ H.hQp x
  have nQx : ‖H.Qp x‖ ≤ q * ‖x‖ := norm_op_le H.Qp q hQ x
  -- bounds of each piece (value and D)
  have bt1 : ‖t1‖ ≤ (4 / H.c) * (H.δD * ‖H.D x‖) :=
    (H.cjpLinv_le _).trans (mul_le_mul_of_nonneg_left (norm_adj_sub_le eM H.δD H.hDm _) (by positivity))
  have dt1 : ‖H.D t1‖ ≤ Real.sqrt (12 / H.c) * (H.δD * ‖H.D x‖) :=
    (H.D_cjpLinv_le _).trans (mul_le_mul_of_nonneg_left (norm_adj_sub_le eM H.δD H.hDm _) (by positivity))
  obtain ⟨bt2a, dt2a⟩ := H.cjpLinvDadj_le (eP x)
  have bt2 : ‖t2‖ ≤ Real.sqrt (48 / H.c) * (H.δD * ‖x‖) :=
    bt2a.trans (mul_le_mul_of_nonneg_left nePx (Real.sqrt_nonneg _))
  have dt2 : ‖H.D t2‖ ≤ Real.sqrt 24 * (H.δD * ‖x‖) :=
    dt2a.trans (mul_le_mul_of_nonneg_left nePx (Real.sqrt_nonneg _))
  have hePM : ‖ContinuousLinearMap.adjoint eM (eP x)‖ ≤ H.δD * (H.δD * ‖x‖) :=
    (norm_adj_sub_le eM H.δD H.hDm _).trans (mul_le_mul_of_nonneg_left nePx hδD)
  have bt2' : ‖t2'‖ ≤ (4 / H.c) * (H.δD * (H.δD * ‖x‖)) :=
    (H.cjpLinv_le _).trans (mul_le_mul_of_nonneg_left hePM (by positivity))
  have dt2' : ‖H.D t2'‖ ≤ Real.sqrt (12 / H.c) * (H.δD * (H.δD * ‖x‖)) :=
    (H.D_cjpLinv_le _).trans (mul_le_mul_of_nonneg_left hePM (by positivity))
  have bu1 : ‖u1‖ ≤ (4 / H.c) * (H.δQ * (q * ‖x‖)) :=
    (H.cjpLinv_le _).trans (mul_le_mul_of_nonneg_left ((norm_adj_sub_le fM H.δQ H.hQm _).trans
      (mul_le_mul_of_nonneg_left nQx hδQ)) (by positivity))
  have du1 : ‖H.D u1‖ ≤ Real.sqrt (12 / H.c) * (H.δQ * (q * ‖x‖)) :=
    (H.D_cjpLinv_le _).trans (mul_le_mul_of_nonneg_left ((norm_adj_sub_le fM H.δQ H.hQm _).trans
      (mul_le_mul_of_nonneg_left nQx hδQ)) (Real.sqrt_nonneg _))
  have hQadj : ‖ContinuousLinearMap.adjoint H.Qp (fP x)‖ ≤ q * (H.δQ * ‖x‖) :=
    (norm_adj_sub_le H.Qp q hQ _).trans (mul_le_mul_of_nonneg_left nfPx hq)
  have bu2 : ‖u2‖ ≤ (4 / H.c) * (q * (H.δQ * ‖x‖)) :=
    (H.cjpLinv_le _).trans (mul_le_mul_of_nonneg_left hQadj (by positivity))
  have du2 : ‖H.D u2‖ ≤ Real.sqrt (12 / H.c) * (q * (H.δQ * ‖x‖)) :=
    (H.D_cjpLinv_le _).trans (mul_le_mul_of_nonneg_left hQadj (Real.sqrt_nonneg _))
  have hfMP : ‖ContinuousLinearMap.adjoint fM (fP x)‖ ≤ H.δQ * (H.δQ * ‖x‖) :=
    (norm_adj_sub_le fM H.δQ H.hQm _).trans (mul_le_mul_of_nonneg_left nfPx hδQ)
  have bu3 : ‖u3‖ ≤ (4 / H.c) * (H.δQ * (H.δQ * ‖x‖)) :=
    (H.cjpLinv_le _).trans (mul_le_mul_of_nonneg_left hfMP (by positivity))
  have du3 : ‖H.D u3‖ ≤ Real.sqrt (12 / H.c) * (H.δQ * (H.δQ * ‖x‖)) :=
    (H.D_cjpLinv_le _).trans (mul_le_mul_of_nonneg_left hfMP (Real.sqrt_nonneg _))
  have ht23 : t3 = t2' := rfl
  -- assemble
  have hnorm : ‖-(t1 + (t2 - t2') + t3) - H.m • (u1 + u2 + u3)‖
      ≤ ‖t1‖ + ‖t2‖ + ‖t2'‖ + ‖t3‖ + H.m * (‖u1‖ + ‖u2‖ + ‖u3‖) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hm]
    have a1 := norm_add_le (t1 + (t2 - t2')) t3
    have a2 := norm_add_le t1 (t2 - t2')
    have a3 := norm_sub_le t2 t2'
    have a4 := norm_add_le (u1 + u2) u3
    have a5 := norm_add_le u1 u2
    have := mul_le_mul_of_nonneg_left (show ‖u1 + u2 + u3‖ ≤ ‖u1‖ + ‖u2‖ + ‖u3‖ by linarith) hm
    linarith
  have hDnorm : ‖H.D (-(t1 + (t2 - t2') + t3) - H.m • (u1 + u2 + u3))‖
      ≤ ‖H.D t1‖ + ‖H.D t2‖ + ‖H.D t2'‖ + ‖H.D t3‖ + H.m * (‖H.D u1‖ + ‖H.D u2‖ + ‖H.D u3‖) := by
    simp only [map_sub, map_neg, map_add, map_smul]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hm]
    have a1 := norm_add_le (H.D t1 + (H.D t2 - H.D t2')) (H.D t3)
    have a2 := norm_add_le (H.D t1) (H.D t2 - H.D t2')
    have a3 := norm_sub_le (H.D t2) (H.D t2')
    have a4 := norm_add_le (H.D u1 + H.D u2) (H.D u3)
    have a5 := norm_add_le (H.D u1) (H.D u2)
    have := mul_le_mul_of_nonneg_left
      (show ‖H.D u1 + H.D u2 + H.D u3‖ ≤ ‖H.D u1‖ + ‖H.D u2‖ + ‖H.D u3‖ by linarith) hm
    linarith
  rw [hres]
  have hmu := mul_le_mul_of_nonneg_left (add_le_add (add_le_add bu1 bu2) bu3) hm
  have hmd := mul_le_mul_of_nonneg_left (add_le_add (add_le_add du1 du2) du3) hm
  refine ⟨hnorm.trans ?_, hDnorm.trans ?_⟩
  · calc ‖t1‖ + ‖t2‖ + ‖t2'‖ + ‖t3‖ + H.m * (‖u1‖ + ‖u2‖ + ‖u3‖)
        ≤ (4 / H.c) * (H.δD * ‖H.D x‖) + Real.sqrt (48 / H.c) * (H.δD * ‖x‖)
          + (4 / H.c) * (H.δD * (H.δD * ‖x‖)) + (4 / H.c) * (H.δD * (H.δD * ‖x‖))
          + H.m * ((4 / H.c) * (H.δQ * (q * ‖x‖)) + (4 / H.c) * (q * (H.δQ * ‖x‖))
              + (4 / H.c) * (H.δQ * (H.δQ * ‖x‖))) := by
          have := add_le_add (add_le_add (add_le_add (add_le_add bt1 bt2) bt2') (ht23 ▸ bt2')) hmu
          exact this
      _ = _ := by ring
  · calc ‖H.D t1‖ + ‖H.D t2‖ + ‖H.D t2'‖ + ‖H.D t3‖ + H.m * (‖H.D u1‖ + ‖H.D u2‖ + ‖H.D u3‖)
        ≤ Real.sqrt (12 / H.c) * (H.δD * ‖H.D x‖) + Real.sqrt 24 * (H.δD * ‖x‖)
          + Real.sqrt (12 / H.c) * (H.δD * (H.δD * ‖x‖)) + Real.sqrt (12 / H.c) * (H.δD * (H.δD * ‖x‖))
          + H.m * (Real.sqrt (12 / H.c) * (H.δQ * (q * ‖x‖)) + Real.sqrt (12 / H.c) * (q * (H.δQ * ‖x‖))
              + Real.sqrt (12 / H.c) * (H.δQ * (H.δQ * ‖x‖))) := by
          have := add_le_add (add_le_add (add_le_add (add_le_add dt1 dt2) dt2') (ht23 ▸ dt2')) hmd
          exact this
      _ = _ := by ring

#print axioms L_sym
#print axioms Linv_le
#print axioms cjp_Linv_L
#print axioms resolvent
#print axioms cjpL_eq
#print axioms L_sub_cjpL
#print axioms norm_adj_sub_le
#print axioms cjpLinv_le
#print axioms D_cjpLinv_le
#print axioms cjpLinvDadj_le
#print axioms resolvent_bound

end SiteHyp

end AdalyFormal.DLayer
