import DLR11

/-!
# DL12 -- `X = G'Q'*` and `Γ = X*X` under the weights (abstract), and the trivial-weight specialisation

* `WPair.one`, `cjp_one`, `SiteHyp.triv` (same operators, identity weights, `δ = 0`): every weighted bound specialises to the unweighted one.
* `Linv_sym`; `X := G' Qp*`; `DX_le` : `‖D Xu‖ ≤ (q/√c)‖u‖`; `X_le` : `‖Xu‖ ≤ (q/c)‖u‖`.
* `cjpX_eq` : `X⁺ = (G')⁺ (Qp⁻)*`;  `Xdiff` : `‖X⁺u − Xu‖ ≤ epsX·‖u‖`,  `DXdiff` : `‖D(X⁺u − Xu)‖ ≤ epsDX·‖u‖`.
* `gamma_cjp_lower` : `⟪u, Γ⁺u⟫ ≥ ½‖Xu‖² − 3 epsX²‖u‖²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace

/-- the identity weight -/
noncomputable def WPair.one (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] : WPair X where
  w := ContinuousLinearMap.id ℝ X
  wi := ContinuousLinearMap.id ℝ X
  w_wi := fun _ => rfl
  wi_w := fun _ => rfl
  w_sym := fun _ _ => rfl
  wi_sym := fun _ _ => rfl

theorem cjp_one {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [NormedAddCommGroup Z]
    [InnerProductSpace ℝ Z] (T : X →L[ℝ] Z) : cjp (WPair.one X) (WPair.one Z) T = T := by
  ext x; rfl

theorem cjm_one {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [NormedAddCommGroup Z]
    [InnerProductSpace ℝ Z] (T : X →L[ℝ] Z) : cjm (WPair.one X) (WPair.one Z) T = T := by
  ext x; rfl

namespace SiteHyp

variable {S E Y : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y]
variable (H : SiteHyp S E Y)

/-- the same operators with identity weights and zero commutators -/
noncomputable def triv : SiteHyp S E Y where
  D := H.D
  Qp := H.Qp
  m := H.m
  Linv := H.Linv
  ωS := WPair.one S
  ωE := WPair.one E
  ωY := WPair.one Y
  c := H.c
  δD := 0
  δQ := 0
  hm := H.hm
  hc := H.hc
  hδD := le_rfl
  hδQ := le_rfl
  hL1 := H.hL1
  hL2 := H.hL2
  hcoer := H.hcoer
  hDp := by rw [cjp_one, sub_self, norm_zero]
  hDm := by rw [cjm_one, sub_self, norm_zero]
  hQp := by rw [cjp_one, sub_self, norm_zero]
  hQm := by rw [cjm_one, sub_self, norm_zero]
  hsmall := by have := H.hc; nlinarith [H.hm]
  hsmallD := by have := H.hc; nlinarith

theorem triv_L : H.triv.L = H.L := rfl

theorem Linv_sym (y z : S) : ⟪H.Linv y, z⟫ = ⟪y, H.Linv z⟫ := by
  have h := H.L_sym (H.Linv y) (H.Linv z)
  rw [H.L_Linv, H.L_Linv] at h
  rw [h]

/-- `X = G' Qp*` -/
noncomputable def X : Y →L[ℝ] S := H.Linv ∘L ContinuousLinearMap.adjoint H.Qp

theorem X_apply (u : Y) : H.X u = H.Linv (ContinuousLinearMap.adjoint H.Qp u) := rfl

theorem X_le (q : ℝ) (hQ : ‖H.Qp‖ ≤ q) (u : Y) : ‖H.X u‖ ≤ (q / H.c) * ‖u‖ := by
  have h1 := H.Linv_le (ContinuousLinearMap.adjoint H.Qp u)
  have h2 := norm_adj_sub_le H.Qp q hQ u
  have hc := H.hc
  rw [X_apply, div_mul_eq_mul_div, le_div_iff₀ hc]
  linarith

theorem DX_le (q : ℝ) (hq : 0 ≤ q) (hQ : ‖H.Qp‖ ≤ q) (u : Y) : ‖H.D (H.X u)‖ ≤ (q / Real.sqrt H.c) * ‖u‖ := by
  set x := H.X u
  have hLx : H.L x = ContinuousLinearMap.adjoint H.Qp u := H.L_Linv _
  have hform : ⟪x, H.L x⟫ = ⟪H.Qp x, u⟫ := by rw [hLx, ContinuousLinearMap.adjoint_inner_right]
  have h1 : ⟪H.Qp x, u⟫ ≤ q * ‖x‖ * ‖u‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (norm_op_le H.Qp q hQ x) (norm_nonneg _))
  have h2 := H.L_form x
  have hm2 : 0 ≤ H.m * ‖H.Qp x‖ ^ 2 := mul_nonneg H.hm (sq_nonneg _)
  have hx := H.X_le q hQ u
  have hc := H.hc
  have hDx2 : ‖H.D x‖ ^ 2 ≤ q * ‖x‖ * ‖u‖ := by nlinarith
  have hDx2' : ‖H.D x‖ ^ 2 ≤ (q / Real.sqrt H.c * ‖u‖) ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt hc.le]
    calc ‖H.D x‖ ^ 2 ≤ q * ‖x‖ * ‖u‖ := hDx2
      _ ≤ q * ((q / H.c) * ‖u‖) * ‖u‖ := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx hq) (norm_nonneg _)
      _ = q ^ 2 / H.c * ‖u‖ ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hDx2'

theorem cjpX_eq : cjp H.ωY H.ωS H.X = cjp H.ωS H.ωS H.Linv ∘L ContinuousLinearMap.adjoint (cjm H.ωS H.ωY H.Qp) := by
  rw [X, cjp_comp H.ωY H.ωS H.ωS, adjoint_cjm]

/-- the weighted-difference constant of `X` -/
noncomputable def K0 (q : ℝ) : ℝ :=
  Real.sqrt (48 / H.c) * H.δD + (8 / H.c) * H.δD ^ 2 + (4 / H.c) * H.m * (2 * q * H.δQ + H.δQ ^ 2)
noncomputable def K1 (q : ℝ) : ℝ :=
  Real.sqrt 24 * H.δD + 2 * Real.sqrt (12 / H.c) * H.δD ^ 2 + Real.sqrt (12 / H.c) * H.m * (2 * q * H.δQ + H.δQ ^ 2)
noncomputable def epsX (q : ℝ) : ℝ :=
  (4 / H.c) * H.δQ + (4 / H.c) * H.δD * (q / Real.sqrt H.c) + H.K0 q * (q / H.c)
noncomputable def epsDX (q : ℝ) : ℝ :=
  Real.sqrt (12 / H.c) * H.δQ + Real.sqrt (12 / H.c) * H.δD * (q / Real.sqrt H.c) + H.K1 q * (q / H.c)

theorem K0_nonneg (q : ℝ) (hq : 0 ≤ q) : 0 ≤ H.K0 q := by
  unfold K0; have := H.hc; have := H.hδD; have := H.hδQ; have := H.hm; positivity
theorem K1_nonneg (q : ℝ) (hq : 0 ≤ q) : 0 ≤ H.K1 q := by
  unfold K1; have := H.hc; have := H.hδD; have := H.hδQ; have := H.hm; positivity

theorem Xdiff (q : ℝ) (hq : 0 ≤ q) (hQ : ‖H.Qp‖ ≤ q) (u : Y) :
    ‖cjp H.ωY H.ωS H.X u - H.X u‖ ≤ H.epsX q * ‖u‖ ∧
    ‖H.D (cjp H.ωY H.ωS H.X u - H.X u)‖ ≤ H.epsDX q * ‖u‖ := by
  set y := ContinuousLinearMap.adjoint H.Qp u
  have e : cjp H.ωY H.ωS H.X u - H.X u
      = cjp H.ωS H.ωS H.Linv (ContinuousLinearMap.adjoint (cjm H.ωS H.ωY H.Qp - H.Qp) u)
        + (cjp H.ωS H.ωS H.Linv y - H.Linv y) := by
    rw [cjpX_eq, ContinuousLinearMap.comp_apply, X_apply, map_sub, ContinuousLinearMap.sub_apply, map_sub]
    abel
  obtain ⟨r0, r1⟩ := H.resolvent_bound q hq hQ y
  have hx : ‖H.Linv y‖ ≤ (q / H.c) * ‖u‖ := H.X_le q hQ u
  have hDx : ‖H.D (H.Linv y)‖ ≤ (q / Real.sqrt H.c) * ‖u‖ := H.DX_le q hq hQ u
  have hadj : ‖ContinuousLinearMap.adjoint (cjm H.ωS H.ωY H.Qp - H.Qp) u‖ ≤ H.δQ * ‖u‖ :=
    norm_adj_sub_le _ H.δQ H.hQm u
  have hc := H.hc
  have hδD := H.hδD
  have hK0 := H.K0_nonneg q hq
  have hK1 := H.K1_nonneg q hq
  refine ⟨?_, ?_⟩
  · rw [e]
    refine (norm_add_le _ _).trans ?_
    have a1 := (H.cjpLinv_le _).trans (mul_le_mul_of_nonneg_left hadj (by positivity : (0:ℝ) ≤ 4 / H.c))
    have a2 : ‖cjp H.ωS H.ωS H.Linv y - H.Linv y‖ ≤ (4 / H.c) * H.δD * ((q / Real.sqrt H.c) * ‖u‖)
        + H.K0 q * ((q / H.c) * ‖u‖) := by
      refine r0.trans ?_
      unfold K0
      have := mul_le_mul_of_nonneg_left hDx (by positivity : (0:ℝ) ≤ 4 / H.c * H.δD)
      have := mul_le_mul_of_nonneg_left hx hK0
      unfold K0 at this
      linarith
    unfold epsX
    nlinarith [a1, a2]
  · rw [e, map_add]
    refine (norm_add_le _ _).trans ?_
    have a1 := (H.D_cjpLinv_le _).trans (mul_le_mul_of_nonneg_left hadj (Real.sqrt_nonneg _))
    have a2 : ‖H.D (cjp H.ωS H.ωS H.Linv y - H.Linv y)‖ ≤ Real.sqrt (12 / H.c) * H.δD * ((q / Real.sqrt H.c) * ‖u‖)
        + H.K1 q * ((q / H.c) * ‖u‖) := by
      refine r1.trans ?_
      have := mul_le_mul_of_nonneg_left hDx (by positivity : (0:ℝ) ≤ Real.sqrt (12 / H.c) * H.δD)
      have := mul_le_mul_of_nonneg_left hx hK1
      unfold K1 at this
      unfold K1
      linarith
    unfold epsDX
    nlinarith [a1, a2]

/-- the same for the inverse weights (`X⁻`) -/
theorem Xdiff_m (q : ℝ) (hq : 0 ≤ q) (hQ : ‖H.Qp‖ ≤ q) (u : Y) :
    ‖cjm H.ωY H.ωS H.X u - H.X u‖ ≤ H.epsX q * ‖u‖ ∧
    ‖H.D (cjm H.ωY H.ωS H.X u - H.X u)‖ ≤ H.epsDX q * ‖u‖ :=
  H.inv.Xdiff q hq hQ u

theorem epsX_nonneg (q : ℝ) (hq : 0 ≤ q) : 0 ≤ H.epsX q := by
  unfold epsX; have := H.hc; have := H.hδD; have := H.hδQ; have := H.K0_nonneg q hq; positivity

/-- `Γ = X*X` -/
noncomputable def Gam : Y →L[ℝ] Y := ContinuousLinearMap.adjoint H.X ∘L H.X

/-- `⟪u, Γ⁺u⟫ ≥ ½‖Xu‖² − 3 epsX²‖u‖²` -/
theorem gamma_cjp_lower (q : ℝ) (hq : 0 ≤ q) (hQ : ‖H.Qp‖ ≤ q) (u : Y) :
    (1 / 2) * ‖H.X u‖ ^ 2 - 3 * H.epsX q ^ 2 * ‖u‖ ^ 2 ≤ ⟪u, cjp H.ωY H.ωY H.Gam u⟫ := by
  have hp : ‖cjp H.ωY H.ωS H.X - H.X‖ ≤ H.epsX q := by
    refine ContinuousLinearMap.opNorm_le_bound _ (H.epsX_nonneg q hq) (fun u => ?_)
    rw [ContinuousLinearMap.sub_apply]; exact (H.Xdiff q hq hQ u).1
  have hm : ‖cjm H.ωY H.ωS H.X - H.X‖ ≤ H.epsX q := by
    refine ContinuousLinearMap.opNorm_le_bound _ (H.epsX_nonneg q hq) (fun u => ?_)
    rw [ContinuousLinearMap.sub_apply]; exact (H.Xdiff_m q hq hQ u).1
  exact xtx_cjp_lower H.ωY H.ωS H.X (H.epsX q) (H.epsX_nonneg q hq) hp hm u

end SiteHyp

#print axioms WPair.one
#print axioms cjp_one
#print axioms SiteHyp.triv
#print axioms SiteHyp.Linv_sym
#print axioms SiteHyp.X_le
#print axioms SiteHyp.DX_le
#print axioms SiteHyp.cjpX_eq
#print axioms SiteHyp.Xdiff
#print axioms SiteHyp.Xdiff_m
#print axioms SiteHyp.gamma_cjp_lower

end AdalyFormal.DLayer
