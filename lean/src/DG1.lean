import DLR9

/-!
# DG1 -- form-relative Combes–Thomas for a form split into three squares and a small remainder (abstract)

Hilbert-space level (Mathlib + DL9 `WPair`, `cjp`, `cjm`).  `GSplit E F1 F2 F3`:
* a symmetric `Ginv : E → E` whose bilinear form is `⟪Y₁x,Y₁y⟫ + ⟪Y₂x,Y₂y⟫ + ⟪Y₃x,Y₃y⟫ + Δ(x,y)`;
* a norm operator `Nw` with the coercivity `cw ‖Nw f‖² ≤ ⟪f, Ginv f⟫` (the M1 node W4 form);
* weights `ωE` on `E`, `ωᵢ` on `Fᵢ`; the conjugation errors `‖(Yᵢ^± − Yᵢ) x‖ ≤ dᵢ ‖Nw x‖`;
* the remainder, FORM-relatively: `|Δ(x,y)| ≤ cΔ √E(x)√E(y)` and `|Δ(ωE x, ωE⁻¹ y)| ≤ cΔ' √E(x)√E(y)`, `E(x) = ⟪x,Ginv x⟫`.
**`hHB_of_split`** : `|⟪x, (Ginv)⁺ y⟫ − ⟪x, Ginv y⟫| ≤ κ √⟪x,Ginv x⟫ √⟪y,Ginv y⟫` with
`κ = Σᵢ (2 dᵢ s t + dᵢ² t²) + cΔ + cΔ'`, `t = 1/√cw`, `s = √(1 + cΔ)` (this is the `hHB` field of DC2's `WSchur`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.DLayer

/-- the elementary perturbation bound for an inner product. -/
theorem inner_pert_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (a b a' b' : F)
    (X Y cA cB d : ℝ) (hd : 0 ≤ d) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hcB : 0 ≤ cB)
    (ha : ‖a' - a‖ ≤ d * X) (hb : ‖b' - b‖ ≤ d * Y) (hA : ‖a‖ ≤ cA) (hB : ‖b‖ ≤ cB) :
    |⟪a', b'⟫ - ⟪a, b⟫| ≤ d * X * (cB + d * Y) + cA * (d * Y) := by
  have e : ⟪a', b'⟫ - ⟪a, b⟫ = ⟪a' - a, b'⟫ + ⟪a, b' - b⟫ := by
    rw [inner_sub_left, inner_sub_right]; ring
  rw [e]
  have h1 : |⟪a' - a, b'⟫| ≤ ‖a' - a‖ * ‖b'‖ := abs_real_inner_le_norm _ _
  have h2 : |⟪a, b' - b⟫| ≤ ‖a‖ * ‖b' - b‖ := abs_real_inner_le_norm _ _
  have hb' : ‖b'‖ ≤ cB + d * Y := by
    have : b' = b + (b' - b) := by abel
    rw [this]; exact (norm_add_le _ _).trans (add_le_add hB hb)
  have hn1 := norm_nonneg (a' - a)
  have hn2 := norm_nonneg a
  have hn3 := norm_nonneg (b' - b)
  have hn4 := norm_nonneg b'
  calc |⟪a' - a, b'⟫ + ⟪a, b' - b⟫| ≤ |⟪a' - a, b'⟫| + |⟪a, b' - b⟫| := abs_add_le _ _
    _ ≤ ‖a' - a‖ * ‖b'‖ + ‖a‖ * ‖b' - b‖ := add_le_add h1 h2
    _ ≤ (d * X) * (cB + d * Y) + cA * (d * Y) := by
        have := mul_le_mul ha hb' hn4 (by positivity)
        have := mul_le_mul hA hb hn3 ((norm_nonneg a).trans hA)
        linarith

/-- the split structure -/
structure GSplit (E F1 F2 F3 : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F1] [InnerProductSpace ℝ F1] [NormedAddCommGroup F2] [InnerProductSpace ℝ F2]
    [NormedAddCommGroup F3] [InnerProductSpace ℝ F3] where
  Ginv : E →L[ℝ] E
  Nw : E →L[ℝ] E
  ωE : WPair E
  Y1 : E →L[ℝ] F1
  Y2 : E →L[ℝ] F2
  Y3 : E →L[ℝ] F3
  ω1 : WPair F1
  ω2 : WPair F2
  ω3 : WPair F3
  Δ : E → E → ℝ
  cw : ℝ
  cΔ : ℝ
  cΔ' : ℝ
  d1 : ℝ
  d2 : ℝ
  d3 : ℝ
  hcw : 0 < cw
  hcΔ : 0 ≤ cΔ
  hcΔ' : 0 ≤ cΔ'
  hd1 : 0 ≤ d1
  hd2 : 0 ≤ d2
  hd3 : 0 ≤ d3
  hdec : ∀ x y, ⟪x, Ginv y⟫ = ⟪Y1 x, Y1 y⟫ + ⟪Y2 x, Y2 y⟫ + ⟪Y3 x, Y3 y⟫ + Δ x y
  hcoer : ∀ f, cw * ‖Nw f‖ ^ 2 ≤ ⟪f, Ginv f⟫
  hΔ0 : ∀ x y, |Δ x y| ≤ cΔ * (Real.sqrt ⟪x, Ginv x⟫ * Real.sqrt ⟪y, Ginv y⟫)
  hΔ1 : ∀ x y, |Δ (ωE.w x) (ωE.wi y)| ≤ cΔ' * (Real.sqrt ⟪x, Ginv x⟫ * Real.sqrt ⟪y, Ginv y⟫)
  hp1 : ∀ x, ‖(cjp ωE ω1 Y1 - Y1) x‖ ≤ d1 * ‖Nw x‖
  hm1 : ∀ x, ‖(cjm ωE ω1 Y1 - Y1) x‖ ≤ d1 * ‖Nw x‖
  hp2 : ∀ x, ‖(cjp ωE ω2 Y2 - Y2) x‖ ≤ d2 * ‖Nw x‖
  hm2 : ∀ x, ‖(cjm ωE ω2 Y2 - Y2) x‖ ≤ d2 * ‖Nw x‖
  hp3 : ∀ x, ‖(cjp ωE ω3 Y3 - Y3) x‖ ≤ d3 * ‖Nw x‖
  hm3 : ∀ x, ‖(cjm ωE ω3 Y3 - Y3) x‖ ≤ d3 * ‖Nw x‖

namespace GSplit

variable {E F1 F2 F3 : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F1] [InnerProductSpace ℝ F1] [NormedAddCommGroup F2] [InnerProductSpace ℝ F2]
  [NormedAddCommGroup F3] [InnerProductSpace ℝ F3]
variable (J : GSplit E F1 F2 F3)

noncomputable def En (x : E) : ℝ := ⟪x, J.Ginv x⟫

theorem En_nonneg (x : E) : 0 ≤ J.En x := le_trans (by have := J.hcw; positivity) (J.hcoer x)

noncomputable def tt : ℝ := 1 / Real.sqrt J.cw
noncomputable def ss : ℝ := Real.sqrt (1 + J.cΔ)

theorem tt_nonneg : 0 ≤ J.tt := by unfold tt; positivity
theorem ss_nonneg : 0 ≤ J.ss := Real.sqrt_nonneg _

theorem Nw_le (x : E) : ‖J.Nw x‖ ≤ J.tt * Real.sqrt (J.En x) := by
  have h := J.hcoer x
  have hc := J.hcw
  have hsc : 0 < Real.sqrt J.cw := Real.sqrt_pos.mpr hc
  unfold tt
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hsc]
  rw [← Real.sqrt_sq (norm_nonneg (J.Nw x)), ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (by unfold En; rw [mul_comm]; exact h)

/-- `Σᵢ ‖Yᵢ x‖² ≤ (1 + cΔ) E(x)` -/
theorem sq_sum_le (x : E) :
    ‖J.Y1 x‖ ^ 2 + ‖J.Y2 x‖ ^ 2 + ‖J.Y3 x‖ ^ 2 ≤ (1 + J.cΔ) * J.En x := by
  have h := J.hdec x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have hΔ := J.hΔ0 x x
  have hE := J.En_nonneg x
  have hs : Real.sqrt ⟪x, J.Ginv x⟫ * Real.sqrt ⟪x, J.Ginv x⟫ = J.En x := Real.mul_self_sqrt hE
  rw [hs] at hΔ
  have hΔ' : -(J.Δ x x) ≤ J.cΔ * J.En x := (neg_le_abs _).trans hΔ
  unfold En at *
  linarith

theorem Y_le (x : E) (i : Fin 3) :
    (match i with | 0 => ‖J.Y1 x‖ | 1 => ‖J.Y2 x‖ | 2 => ‖J.Y3 x‖) ≤ J.ss * Real.sqrt (J.En x) := by
  have h := J.sq_sum_le x
  have hE := J.En_nonneg x
  have hq : 0 ≤ 1 + J.cΔ := by have := J.hcΔ; positivity
  have key : ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ (1 + J.cΔ) * J.En x → t ≤ J.ss * Real.sqrt (J.En x) := by
    intro t ht h2
    unfold ss
    rw [← Real.sqrt_mul hq, ← Real.sqrt_sq ht]
    exact Real.sqrt_le_sqrt h2
  have n1 := sq_nonneg ‖J.Y1 x‖
  have n2 := sq_nonneg ‖J.Y2 x‖
  have n3 := sq_nonneg ‖J.Y3 x‖
  match i with
  | 0 => exact key _ (norm_nonneg _) (by linarith)
  | 1 => exact key _ (norm_nonneg _) (by linarith)
  | 2 => exact key _ (norm_nonneg _) (by linarith)

/-- the conjugated pairing of one square -/
theorem cj_pair {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (ω : WPair F) (Y : E →L[ℝ] F) (x y : E) :
    ⟪Y (J.ωE.w x), Y (J.ωE.wi y)⟫ = ⟪cjm J.ωE ω Y x, cjp J.ωE ω Y y⟫ := by
  rw [cjp_apply]
  show _ = ⟪ω.wi (Y (J.ωE.w x)), ω.w (Y (J.ωE.wi y))⟫
  rw [ω.wi_sym, ω.wi_w]

/-- one square: `|⟪Y⁻x, Y⁺y⟫ − ⟪Yx,Yy⟫| ≤ (2 d s t + d² t²) √E(x) √E(y)` -/
theorem piece_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (ω : WPair F) (Y : E →L[ℝ] F)
    (d : ℝ) (hd : 0 ≤ d)
    (hp : ∀ x, ‖(cjp J.ωE ω Y - Y) x‖ ≤ d * ‖J.Nw x‖) (hm : ∀ x, ‖(cjm J.ωE ω Y - Y) x‖ ≤ d * ‖J.Nw x‖)
    (hY : ∀ x, ‖Y x‖ ≤ J.ss * Real.sqrt (J.En x)) (x y : E) :
    |⟪cjm J.ωE ω Y x, cjp J.ωE ω Y y⟫ - ⟪Y x, Y y⟫|
      ≤ (2 * d * J.ss * J.tt + d ^ 2 * J.tt ^ 2) * (Real.sqrt (J.En x) * Real.sqrt (J.En y)) := by
  set X := Real.sqrt (J.En x)
  set Yv := Real.sqrt (J.En y)
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hYv : 0 ≤ Yv := Real.sqrt_nonneg _
  have ht := J.tt_nonneg
  have hs := J.ss_nonneg
  have ha : ‖cjm J.ωE ω Y x - Y x‖ ≤ d * (J.tt * X) := by
    have := hm x; rw [ContinuousLinearMap.sub_apply] at this
    exact this.trans (mul_le_mul_of_nonneg_left (J.Nw_le x) hd)
  have hb : ‖cjp J.ωE ω Y y - Y y‖ ≤ d * (J.tt * Yv) := by
    have := hp y; rw [ContinuousLinearMap.sub_apply] at this
    exact this.trans (mul_le_mul_of_nonneg_left (J.Nw_le y) hd)
  have h := inner_pert_le (Y x) (Y y) (cjm J.ωE ω Y x) (cjp J.ωE ω Y y) (J.tt * X) (J.tt * Yv)
    (J.ss * X) (J.ss * Yv) d hd (by positivity) (by positivity) (by positivity) ha hb (hY x) (hY y)
  refine h.trans (le_of_eq ?_)
  ring

/-- the constant `κ` -/
noncomputable def kap : ℝ :=
  (2 * J.d1 * J.ss * J.tt + J.d1 ^ 2 * J.tt ^ 2) + (2 * J.d2 * J.ss * J.tt + J.d2 ^ 2 * J.tt ^ 2)
    + (2 * J.d3 * J.ss * J.tt + J.d3 ^ 2 * J.tt ^ 2) + (J.cΔ + J.cΔ')

theorem kap_nonneg : 0 ≤ J.kap := by
  have := J.hd1; have := J.hd2; have := J.hd3; have := J.hcΔ; have := J.hcΔ'
  have := J.tt_nonneg; have := J.ss_nonneg
  unfold kap; positivity

/-- **the form-relative CT bound** -/
theorem hHB_of_split (x y : E) :
    |⟪x, cjp J.ωE J.ωE J.Ginv y⟫ - ⟪x, J.Ginv y⟫|
      ≤ J.kap * (Real.sqrt ⟪x, J.Ginv x⟫ * Real.sqrt ⟪y, J.Ginv y⟫) := by
  have e1 : ⟪x, cjp J.ωE J.ωE J.Ginv y⟫ = ⟪J.ωE.w x, J.Ginv (J.ωE.wi y)⟫ := by
    rw [cjp_apply, ← J.ωE.w_sym, real_inner_comm, real_inner_comm (J.ωE.w x)]
  have eL : ⟪x, cjp J.ωE J.ωE J.Ginv y⟫ - ⟪x, J.Ginv y⟫
      = (⟪cjm J.ωE J.ω1 J.Y1 x, cjp J.ωE J.ω1 J.Y1 y⟫ - ⟪J.Y1 x, J.Y1 y⟫)
        + (⟪cjm J.ωE J.ω2 J.Y2 x, cjp J.ωE J.ω2 J.Y2 y⟫ - ⟪J.Y2 x, J.Y2 y⟫)
        + (⟪cjm J.ωE J.ω3 J.Y3 x, cjp J.ωE J.ω3 J.Y3 y⟫ - ⟪J.Y3 x, J.Y3 y⟫)
        + (J.Δ (J.ωE.w x) (J.ωE.wi y) - J.Δ x y) := by
    rw [e1, J.hdec (J.ωE.w x) (J.ωE.wi y), J.hdec x y, J.cj_pair J.ω1, J.cj_pair J.ω2, J.cj_pair J.ω3]
    ring
  rw [eL]
  show _ ≤ J.kap * (Real.sqrt (J.En x) * Real.sqrt (J.En y))
  set X := Real.sqrt (J.En x)
  set Yv := Real.sqrt (J.En y)
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hYv : 0 ≤ Yv := Real.sqrt_nonneg _
  have p1 := J.piece_le J.ω1 J.Y1 J.d1 J.hd1 J.hp1 J.hm1 (fun z => J.Y_le z 0) x y
  have p2 := J.piece_le J.ω2 J.Y2 J.d2 J.hd2 J.hp2 J.hm2 (fun z => J.Y_le z 1) x y
  have p3 := J.piece_le J.ω3 J.Y3 J.d3 J.hd3 J.hp3 J.hm3 (fun z => J.Y_le z 2) x y
  have hΔa : |J.Δ (J.ωE.w x) (J.ωE.wi y)| ≤ J.cΔ' * (X * Yv) := J.hΔ1 x y
  have hΔb : |J.Δ x y| ≤ J.cΔ * (X * Yv) := J.hΔ0 x y
  have hsum : |(⟪cjm J.ωE J.ω1 J.Y1 x, cjp J.ωE J.ω1 J.Y1 y⟫ - ⟪J.Y1 x, J.Y1 y⟫)
        + (⟪cjm J.ωE J.ω2 J.Y2 x, cjp J.ωE J.ω2 J.Y2 y⟫ - ⟪J.Y2 x, J.Y2 y⟫)
        + (⟪cjm J.ωE J.ω3 J.Y3 x, cjp J.ωE J.ω3 J.Y3 y⟫ - ⟪J.Y3 x, J.Y3 y⟫)
        + (J.Δ (J.ωE.w x) (J.ωE.wi y) - J.Δ x y)|
      ≤ |⟪cjm J.ωE J.ω1 J.Y1 x, cjp J.ωE J.ω1 J.Y1 y⟫ - ⟪J.Y1 x, J.Y1 y⟫|
        + |⟪cjm J.ωE J.ω2 J.Y2 x, cjp J.ωE J.ω2 J.Y2 y⟫ - ⟪J.Y2 x, J.Y2 y⟫|
        + |⟪cjm J.ωE J.ω3 J.Y3 x, cjp J.ωE J.ω3 J.Y3 y⟫ - ⟪J.Y3 x, J.Y3 y⟫|
        + (|J.Δ (J.ωE.w x) (J.ωE.wi y)| + |J.Δ x y|) := by
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add le_rfl le_rfl)) le_rfl)) (abs_sub _ _))
  refine hsum.trans ?_
  unfold kap
  nlinarith [p1, p2, p3, hΔa, hΔb]

end GSplit

#print axioms inner_pert_le
#print axioms GSplit
#print axioms GSplit.En_nonneg
#print axioms GSplit.Nw_le
#print axioms GSplit.sq_sum_le
#print axioms GSplit.Y_le
#print axioms GSplit.cj_pair
#print axioms GSplit.piece_le
#print axioms GSplit.kap
#print axioms GSplit.kap_nonneg
#print axioms GSplit.hHB_of_split

end AdalyFormal.M1DStrat
