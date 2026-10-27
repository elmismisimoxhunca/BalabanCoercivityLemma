import Mathlib
import MI1

/-!
# MI4 -- W1 at the Hilbert-space level: first-order IMS for the gauge-fixing square `‖R D* A‖²` (M1 lane E, 2026-10-13)

Abstract setting (no lattice): `Dst : E → S` (the role of `D*`), `X : Y → S`, `R : S → S` linear with `‖R s‖ ≤ ‖s‖` and
`R ∘ X = 0`; a decomposition `Dst A = R (Dst A) + X u`; localisation maps `hE i`, `hS i`, `hY i`.

* `T_loc_le` : `‖R (Dst (hE_i A))‖ ≤ ‖hS_i (R Dst A)‖ + ‖c_i(X) u‖ + ‖c_i(Dst) A‖`,
  `c_i(Dst) = Dst ∘ hE_i − hS_i ∘ Dst`, `c_i(X) = hS_i ∘ X − X ∘ hY_i`.
* `T_ims_upper` : `Σ_i ‖R Dst (hE_i A)‖² ≤ (1+ε)‖R Dst A‖² + 2(1+1/ε)(Σ_i‖c_i(X)u‖² + Σ_i‖c_i(Dst)A‖²)`.
* `commInv` : for `G` a two-sided inverse of `L`: `h ∘ G − G ∘ h = G ∘ (L ∘ h − h ∘ L) ∘ G`.
* `commL_expand` : for `L = D*D + Q*Q` (any `D : S → E`, `Q : S → Y`, adjoints):
  `L h − h L = −(D* c(D) + c(D*) D + Q* c(Q) + c(Q*) Q)` with `c(Z) = h_target Z − Z h_source`.
* `cX_eq` : `c(X) u = −G (D* c(D) f + c(D*) D f + Q* c(Q) f + c(Q*) Q f) + G c(Q*) u`, `X = G Q*`, `f = X u`.
* `f_sq_eq` : `‖X u‖² = ⟪X u, Dst A⟫` (the projection part is orthogonal to the range of `R`) when `R` is self-adjoint.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open Finset

section T
variable {ι E S Y : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- the localised gauge-fixing field, pointwise in `i`. -/
theorem T_loc_le (Dst : E →L[ℝ] S) (X : Y →L[ℝ] S) (R : S →L[ℝ] S) (hR : ∀ s, ‖R s‖ ≤ ‖s‖)
    (hRX : ∀ u, R (X u) = 0) (hE : E →L[ℝ] E) (hS : S →L[ℝ] S) (hY : Y →L[ℝ] Y) (A : E) (u : Y)
    (hdec : Dst A = R (Dst A) + X u) :
    ‖R (Dst (hE A))‖ ≤ ‖hS (R (Dst A))‖ + ‖hS (X u) - X (hY u)‖ + ‖Dst (hE A) - hS (Dst A)‖ := by
  have e1 : Dst (hE A) = hS (R (Dst A)) + (hS (X u) - X (hY u)) + X (hY u) + (Dst (hE A) - hS (Dst A)) := by
    have : hS (Dst A) = hS (R (Dst A)) + hS (X u) := by
      conv_lhs => rw [hdec]
      rw [map_add]
    rw [this]; abel
  have e2 : R (Dst (hE A)) = R (hS (R (Dst A))) + R (hS (X u) - X (hY u)) + R (Dst (hE A) - hS (Dst A)) := by
    conv_lhs => rw [e1]
    rw [map_add, map_add, map_add, hRX, add_zero]
  rw [e2]
  calc ‖R (hS (R (Dst A))) + R (hS (X u) - X (hY u)) + R (Dst (hE A) - hS (Dst A))‖
      ≤ ‖R (hS (R (Dst A)))‖ + ‖R (hS (X u) - X (hY u))‖ + ‖R (Dst (hE A) - hS (Dst A))‖ :=
        (norm_add_le _ _).trans (by linarith [norm_add_le (R (hS (R (Dst A)))) (R (hS (X u) - X (hY u)))])
    _ ≤ _ := by linarith [hR (hS (R (Dst A))), hR (hS (X u) - X (hY u)), hR (Dst (hE A) - hS (Dst A))]

/-- `Σ (a_i + b_i + c_i)² ≤ (1+ε) Σ a_i² + 2(1+1/ε)(Σ b_i² + Σ c_i²)`. -/
theorem sum_sq3_le (a b c : ι → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∑ i, (a i + b i + c i) ^ 2 ≤ (1 + ε) * ∑ i, a i ^ 2 + 2 * (1 + 1 / ε) * (∑ i, b i ^ 2 + ∑ i, c i ^ 2) := by
  rw [mul_sum, mul_add, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  have h1 : 0 ≤ (ε * a i - (b i + c i)) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
  have e1 : (ε * a i - (b i + c i)) ^ 2 / ε = ε * a i ^ 2 - 2 * a i * (b i + c i) + (1 / ε) * (b i + c i) ^ 2 := by
    field_simp; ring
  have h2 : (b i + c i) ^ 2 ≤ 2 * (b i ^ 2 + c i ^ 2) := by nlinarith [sq_nonneg (b i - c i)]
  have h3 : 0 ≤ 1 / ε := by positivity
  have h4 : (1 / ε) * (b i + c i) ^ 2 ≤ (1 / ε) * (2 * (b i ^ 2 + c i ^ 2)) := mul_le_mul_of_nonneg_left h2 h3
  nlinarith

/-- **first-order IMS upper bound for the gauge-fixing square** (abstract W1-T). -/
theorem T_ims_upper (Dst : E →L[ℝ] S) (X : Y →L[ℝ] S) (R : S →L[ℝ] S) (hR : ∀ s, ‖R s‖ ≤ ‖s‖)
    (hRX : ∀ u, R (X u) = 0) (hE : ι → E →L[ℝ] E) (hS : ι → S →L[ℝ] S) (hY : ι → Y →L[ℝ] Y) (A : E) (u : Y)
    (hdec : Dst A = R (Dst A) + X u) (hpart : ∑ i, ‖hS i (R (Dst A))‖ ^ 2 = ‖R (Dst A)‖ ^ 2) (ε : ℝ) (hε : 0 < ε) :
    ∑ i, ‖R (Dst (hE i A))‖ ^ 2 ≤ (1 + ε) * ‖R (Dst A)‖ ^ 2
      + 2 * (1 + 1 / ε) * (∑ i, ‖hS i (X u) - X (hY i u)‖ ^ 2 + ∑ i, ‖Dst (hE i A) - hS i (Dst A)‖ ^ 2) := by
  have hpt : ∀ i, ‖R (Dst (hE i A))‖ ^ 2
      ≤ (‖hS i (R (Dst A))‖ + ‖hS i (X u) - X (hY i u)‖ + ‖Dst (hE i A) - hS i (Dst A)‖) ^ 2 := by
    intro i
    exact pow_le_pow_left₀ (norm_nonneg _) (T_loc_le Dst X R hR hRX (hE i) (hS i) (hY i) A u hdec) 2
  calc ∑ i, ‖R (Dst (hE i A))‖ ^ 2
      ≤ ∑ i, (‖hS i (R (Dst A))‖ + ‖hS i (X u) - X (hY i u)‖ + ‖Dst (hE i A) - hS i (Dst A)‖) ^ 2 :=
        sum_le_sum fun i _ => hpt i
    _ ≤ _ := by
        have := sum_sq3_le (fun i => ‖hS i (R (Dst A))‖) (fun i => ‖hS i (X u) - X (hY i u)‖)
          (fun i => ‖Dst (hE i A) - hS i (Dst A)‖) ε hε
        rw [hpart] at this
        exact this

end T

section Comm
variable {S E Y : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- commutator with an inverse. -/
theorem commInv (L G h : S →L[ℝ] S) (hLG : ∀ s, L (G s) = s) (hGL : ∀ s, G (L s) = s) (s : S) :
    h (G s) - G (h s) = G (L (h (G s)) - h (L (G s))) := by
  rw [map_sub, hGL, hLG]

/-- expansion of `L h − h L` for `L = D*D + Q*Q`. -/
theorem commL_expand (D : S →L[ℝ] E) (Q : S →L[ℝ] Y) (hS : S →L[ℝ] S) (hE : E →L[ℝ] E) (hY : Y →L[ℝ] Y) (f : S) :
    (ContinuousLinearMap.adjoint D ∘L D + ContinuousLinearMap.adjoint Q ∘L Q) (hS f)
      - hS ((ContinuousLinearMap.adjoint D ∘L D + ContinuousLinearMap.adjoint Q ∘L Q) f)
    = -(ContinuousLinearMap.adjoint D (hE (D f) - D (hS f))
        + (hS (ContinuousLinearMap.adjoint D (D f)) - ContinuousLinearMap.adjoint D (hE (D f)))
        + ContinuousLinearMap.adjoint Q (hY (Q f) - Q (hS f))
        + (hS (ContinuousLinearMap.adjoint Q (Q f)) - ContinuousLinearMap.adjoint Q (hY (Q f)))) := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, map_sub, map_add]
  abel

/-- **the commutator of `X = G Q*`** applied to `u`, with `f = X u`. -/
theorem cX_eq (D : S →L[ℝ] E) (Q : S →L[ℝ] Y) (G : S →L[ℝ] S)
    (hLG : ∀ s, (ContinuousLinearMap.adjoint D ∘L D + ContinuousLinearMap.adjoint Q ∘L Q) (G s) = s)
    (hGL : ∀ s, G ((ContinuousLinearMap.adjoint D ∘L D + ContinuousLinearMap.adjoint Q ∘L Q) s) = s)
    (hS : S →L[ℝ] S) (hE : E →L[ℝ] E) (hY : Y →L[ℝ] Y) (u : Y) :
    hS (G (ContinuousLinearMap.adjoint Q u)) - G (ContinuousLinearMap.adjoint Q (hY u))
      = -G (ContinuousLinearMap.adjoint D (hE (D (G (ContinuousLinearMap.adjoint Q u)))
              - D (hS (G (ContinuousLinearMap.adjoint Q u))))
          + (hS (ContinuousLinearMap.adjoint D (D (G (ContinuousLinearMap.adjoint Q u))))
              - ContinuousLinearMap.adjoint D (hE (D (G (ContinuousLinearMap.adjoint Q u)))))
          + ContinuousLinearMap.adjoint Q (hY (Q (G (ContinuousLinearMap.adjoint Q u)))
              - Q (hS (G (ContinuousLinearMap.adjoint Q u))))
          + (hS (ContinuousLinearMap.adjoint Q (Q (G (ContinuousLinearMap.adjoint Q u))))
              - ContinuousLinearMap.adjoint Q (hY (Q (G (ContinuousLinearMap.adjoint Q u))))))
        + G (hS (ContinuousLinearMap.adjoint Q u) - ContinuousLinearMap.adjoint Q (hY u)) := by
  set L := ContinuousLinearMap.adjoint D ∘L D + ContinuousLinearMap.adjoint Q ∘L Q with hL
  set s := ContinuousLinearMap.adjoint Q u
  have h1 := commInv L G hS hLG hGL s
  have h2 := commL_expand D Q hS hE hY (G s)
  rw [← hL, hLG] at h2
  have e : hS (G s) - G (ContinuousLinearMap.adjoint Q (hY u))
      = (hS (G s) - G (hS s)) + G (hS s - ContinuousLinearMap.adjoint Q (hY u)) := by
    rw [map_sub]; abel
  rw [e, h1, hLG, h2, map_neg]

end Comm

section Proj
variable {E S Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- the projection part is orthogonal to the range of `R`: `‖Xu‖² = ⟪Xu, Dst A⟫`. -/
theorem f_sq_eq (Dst : E →L[ℝ] S) (X : Y →L[ℝ] S) (R : S →L[ℝ] S) (hRs : ∀ s t, ⟪R s, t⟫ = ⟪s, R t⟫)
    (hRX : ∀ u, R (X u) = 0) (A : E) (u : Y) (hdec : Dst A = R (Dst A) + X u) :
    ‖X u‖ ^ 2 = ⟪X u, Dst A⟫ := by
  have h0 : ⟪X u, R (Dst A)⟫ = 0 := by rw [← hRs, hRX, inner_zero_left]
  conv_rhs => rw [hdec]
  rw [inner_add_right, h0, zero_add, real_inner_self_eq_norm_sq]

end Proj

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.T_loc_le
#print axioms AdalyFormal.M1IMS.sum_sq3_le
#print axioms AdalyFormal.M1IMS.T_ims_upper
#print axioms AdalyFormal.M1IMS.commInv
#print axioms AdalyFormal.M1IMS.commL_expand
#print axioms AdalyFormal.M1IMS.cX_eq
#print axioms AdalyFormal.M1IMS.f_sq_eq
