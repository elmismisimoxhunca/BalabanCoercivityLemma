/-
# THE REDUCTION: the unconditional coercivity lemma as a kernel-checked CONDITIONAL.

LANE `compute/thm315_core/`.  Write scope: `compute/thm315_core/` only.

## The target

CMP99b p.428 asserts that `C*Δ_kC` is positive definite "with a lower bound `γ₀ > 0`
independent of `k` and `U`", attributes the `U = 1` case to CMP96 Lemma 2.4, and then DECLINES
that route ("so we will proceed in a different way").  The different way runs pp.429–432 and
ends at Theorem 3.15.  CMP99b (3.158) gives `(C*Δ_kC)⁻¹ = C̃^(k)(Λ) = C^(k)(Λ)↾_{Λ̃}`.

This file wires the pivot chain into that conclusion, and does it TWICE, by two routes with
different deferred inputs.  Both are conditionals: every quantitative input CMP99b does not
supply appears as an explicit hypothesis, and nothing is asserted unconditionally.

## ROUTE A — via Theorem 3.15's kernel decay (the route the brief names)

`Thm 3.15 (3.187)` → `P429Pivot.schur_test` → `Thm315Core.opNorm_kernelOp_le` → `(3.158)` →
`P429Pivot.coercive_of_inverse_opNorm_le` → `γ₀ = 1/S`.

Deferred inputs: **Theorem 3.15 itself**, and **the volume-independence of the Schur constant
`S`** — i.e. that `sup_y ∑_{y'} B₀ e^{-δ₀|y-y'|}` is bounded uniformly in the extent of `Λ`.
Both appear as hypotheses of `coercivity_from_thm315`.

## ROUTE B — via the sandwich (3.185)+(3.186), NO decay

`(3.186)` ⟹ `⟨A, G̃₂A⟩ ≤ ⟨A, G₂A⟩` → `(3.185)` ⟹ `⟨B, C B⟩ ≤ γ_G κ² ‖B‖²` → `(3.158)` →
`formBridge` → `γ₀ = 1/(γ_G κ²)`.

Deferred inputs: a form bound `⟨A, G₂A⟩ ≤ γ_G‖A‖²` on the FINE-level covariance `G₂`, and a
bound `κ` on the right factor `Q*(I + μ*D̄*)`, both uniform in `k`, `U`, `Λ`.
The exponential decay (3.187) is NOT used, the random-walk expansion is NOT used, and no
volume-independent row sum is needed — operator norms have no row-sum problem.  In exchange,
`γ_G` is a quantitative input CMP99b supplies only qualitatively (Theorem 3.11, p.416, gives
positive-definiteness of `G'`, `(Q'G'²Q'*)⁻¹`, `Δ_a`, `G` with NO constant named).

`formBridge` below is a strengthening of `P429Pivot.coercive_of_inverse_opNorm_le`: it consumes
a QUADRATIC-FORM bound on the inverse rather than an operator-norm bound.  Since
`⟨x, Mx⟩ ≤ ‖M‖‖x‖²` always, the form hypothesis is weaker, so Route B needs DIFFERENT machinery -- no decay, no expansion apparatus [S75 2026-08-02, Claude gate: the prior 'strictly less' claim was FALSE: for self-adjoint PSD operators the form bound and opnorm bound are EQUIVALENT (converse kernel-checked at compute/thm315_prosecution/checks/ConverseCheck.lean); Route B's virtue is machinery-avoidance, not hypothesis-weakness] than
Route A's third link.  `formBridge_from_opNorm` records that implication.

## No `sorry`, no `axiom`.  Deferred CMP99b steps are `def : Prop` in `Thm315.lean`.
-/
import Mathlib
import AdalyFormal.Balaban.PivotBridge
import AdalyFormal.Balaban.SchurStep
import AdalyFormal.Balaban.SchurPromotion
import AdalyFormal.Balaban.Thm315

open scoped InnerProductSpace RealInnerProductSpace

namespace Thm315Core

open Finset

/-! ## Part 1 — the form bridge (strengthens `P429Pivot.coercive_of_inverse_opNorm_le`). -/

section Bridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- If `M` is self-adjoint, positive semidefinite and satisfies the QUADRATIC-FORM bound
`⟨x, Mx⟩ ≤ B‖x‖²`, then `‖Mw‖² ≤ B⟨w, Mw⟩`.

Same "complete the square" argument as `P429Pivot.normSq_apply_le_norm_mul_inner`, but with the
form bound `B` in place of the operator norm `‖M‖`; the diagonal step becomes a direct
application of the hypothesis instead of Cauchy–Schwarz plus `le_opNorm`. -/
theorem normSq_apply_le_form_bound (M : H →L[ℝ] H)
    (hsa : ∀ x y : H, ⟪M x, y⟫_ℝ = ⟪x, M y⟫_ℝ)
    (hpos : ∀ x : H, 0 ≤ ⟪x, M x⟫_ℝ)
    (B : ℝ) (hB : 0 < B) (hform : ∀ x : H, ⟪x, M x⟫_ℝ ≤ B * ‖x‖ ^ 2)
    (w : H) :
    ‖M w‖ ^ 2 ≤ B * ⟪w, M w⟫_ℝ := by
  have hzpos : 0 ≤ ⟪M w - B • w, M (M w - B • w)⟫_ℝ := hpos _
  have hMz : M (M w - B • w) = M (M w) - B • M w := by
    simp [map_sub, map_smul]
  have hexp : ⟪M w - B • w, M (M w - B • w)⟫_ℝ
      = ⟪M w, M (M w)⟫_ℝ - B * ⟪M w, M w⟫_ℝ - B * ⟪w, M (M w)⟫_ℝ
        + B * B * ⟪w, M w⟫_ℝ := by
    rw [hMz]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    ring
  have hcross : ⟪w, M (M w)⟫_ℝ = ⟪M w, M w⟫_ℝ := (hsa w (M w)).symm
  have hnormsq : ⟪M w, M w⟫_ℝ = ‖M w‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  -- the diagonal term, straight from the form bound at `M w`
  have hdiag : ⟪M w, M (M w)⟫_ℝ ≤ B * ‖M w‖ ^ 2 := hform (M w)
  rw [hexp, hcross, hnormsq] at hzpos
  have hmain : B * ‖M w‖ ^ 2 ≤ B * (B * ⟪w, M w⟫_ℝ) := by nlinarith [hzpos, hdiag]
  exact le_of_mul_le_mul_left hmain hB

/-- **THE FORM BRIDGE.**  Let `A` be a bounded operator with a self-adjoint, positive
semidefinite bounded LEFT inverse `M`, and suppose the quadratic form of `M` is bounded by `B`:
`⟨x, Mx⟩ ≤ B‖x‖²` with `0 < B`.  Then `A` is coercive with constant `1/B`.

Read against CMP99b: `A := C*Δ_kC`, `M := (C*Δ_kC)⁻¹ = C^(k)(Λ)↾_{Λ̃}` by (3.158), and `B` is a
form bound on the covariance.  The conclusion is exactly the shape of p.428's "positive definite
operator `C*Δ_kC` with a lower bound `γ₀ > 0`", with `γ₀ = 1/B`, and `γ₀`'s independence of `k`
and `U` is INHERITED from `B`'s. -/
theorem formBridge (A M : H →L[ℝ] H)
    (hleft : ∀ v : H, M (A v) = v)
    (hsa : ∀ x y : H, ⟪M x, y⟫_ℝ = ⟪x, M y⟫_ℝ)
    (hpos : ∀ x : H, 0 ≤ ⟪x, M x⟫_ℝ)
    (B : ℝ) (hB : 0 < B) (hform : ∀ x : H, ⟪x, M x⟫_ℝ ≤ B * ‖x‖ ^ 2)
    (v : H) :
    (1 / B) * ‖v‖ ^ 2 ≤ ⟪v, A v⟫_ℝ := by
  have hv : M (A v) = v := hleft v
  have hkey : ‖M (A v)‖ ^ 2 ≤ B * ⟪A v, M (A v)⟫_ℝ :=
    normSq_apply_le_form_bound M hsa hpos B hB hform (A v)
  rw [hv] at hkey
  have hsymm : ⟪A v, v⟫_ℝ = ⟪v, A v⟫_ℝ := real_inner_comm _ _
  rw [hsymm] at hkey
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hB]
  linarith [hkey]

/-- The form hypothesis of `formBridge` is WEAKER than the operator-norm hypothesis of
`P429Pivot.coercive_of_inverse_opNorm_le`: an operator-norm bound always implies the
corresponding form bound.  So Route B's third link demands DIFFERENT machinery -- no decay, no expansion apparatus [S75 2026-08-02, Claude gate: the prior 'strictly less' claim was FALSE: for self-adjoint PSD operators the form bound and opnorm bound are EQUIVALENT (converse kernel-checked at compute/thm315_prosecution/checks/ConverseCheck.lean); Route B's virtue is machinery-avoidance, not hypothesis-weakness] than Route A's. -/
theorem formBridge_from_opNorm (M : H →L[ℝ] H) (B : ℝ) (hMB : ‖M‖ ≤ B) (x : H) :
    ⟪x, M x⟫_ℝ ≤ B * ‖x‖ ^ 2 := by
  calc ⟪x, M x⟫_ℝ ≤ ‖x‖ * ‖M x‖ := real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖M‖ * ‖x‖) := by
        have := M.le_opNorm x
        nlinarith [norm_nonneg x, norm_nonneg (M x)]
    _ ≤ B * ‖x‖ ^ 2 := by nlinarith [norm_nonneg x, hMB, sq_nonneg ‖x‖]

/-- **MUST-FIRE CONTROL (S82 garbage substitution) for `formBridge`.**  The degenerate witness
`M := 0` is self-adjoint, positive semidefinite and satisfies every form bound `⟨x,0x⟩ = 0 ≤
B‖x‖²`; it FAILS the left-inverse hypothesis at every nonzero `v`.  So the hypothesis set is not
satisfiable by the trivial witness and the conclusion is not algebraically forced. -/
theorem formBridge_zero_not_left_inverse (A : H →L[ℝ] H) (v : H) (hv : v ≠ 0) :
    ¬ ((0 : H →L[ℝ] H) (A v) = v) := by
  simpa using hv.symm

/-- **MUST-NOT-FIRE CONTROL (sharpness) for `formBridge`.**  At `A = M = id`, `B = 1`, the
hypotheses all hold and the conclusion is an equality, so the constant `1/B` is optimal. -/
theorem formBridge_sharp_at_identity (v : H) :
    (1 / (1:ℝ)) * ‖v‖ ^ 2 = ⟪v, (ContinuousLinearMap.id ℝ H) v⟫_ℝ := by
  simp [real_inner_self_eq_norm_sq]

end Bridge

/-! ## Part 2 — ROUTE A: coercivity from Theorem 3.15's kernel decay. -/

section RouteA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **ROUTE A, assembled.**  Suppose

* `hthm315` — CMP99b Theorem 3.15's bound (3.187): `|C^(k)(Λ;y,y')| ≤ B₀ e^{-δ₀ dist(y,y')}`;
* `hdist_symm` — the distance is symmetric (true for `|y - y'|`);
* `hS` — **the volume-independent Schur constant**: every row sum of the majorant
  `B₀ e^{-δ₀ dist}` is at most `S`;
* `hSpos` — `0 < S`;
* `hMC` — CMP99b (3.158): the kernel operator of `C^(k)(Λ)` is a left inverse of `C*Δ_kC` on
  `Λ̃`, together with its self-adjointness and positivity.

Then `C*Δ_kC ≥ 1/S` on `Λ̃`, which is p.428's `γ₀` clause with `γ₀ = 1/S`.

The uniformity of `γ₀` in `k` and `U` is inherited from `S`'s, which in turn is inherited from
"`B₀, δ₀` depending on `d` and `L` only" — PROVIDED `hS` holds uniformly.  That proviso is the
route's deferred quantitative input and is NOT proved here. -/
theorem coercivity_from_thm315
    (Ck : ι → ι → ℝ) (dst : ι → ι → ℝ) (B₀ δ₀ S : ℝ)
    (hB₀ : 0 ≤ B₀) (hSpos : 0 < S)
    (hthm315 : ∀ y y', |Ck y y'| ≤ B₀ * Real.exp (-δ₀ * dst y y'))
    (hdist_symm : ∀ y y', dst y y' = dst y' y)
    (hS : ∀ y, ∑ y', B₀ * Real.exp (-δ₀ * dst y y') ≤ S)
    (Aop : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (hleft : ∀ v, kernelOp Ck (Aop v) = v)
    (hsa : ∀ x y, ⟪kernelOp Ck x, y⟫_ℝ = ⟪x, kernelOp Ck y⟫_ℝ)
    (hpos : ∀ x, 0 ≤ ⟪x, kernelOp Ck x⟫_ℝ)
    (v : EuclideanSpace ℝ ι) :
    (1 / S) * ‖v‖ ^ 2 ≤ ⟪v, Aop v⟫_ℝ := by
  have hw : ∀ y y', 0 ≤ B₀ * Real.exp (-δ₀ * dst y y') := fun y y' => by positivity
  have hsymm : ∀ y y', B₀ * Real.exp (-δ₀ * dst y y') = B₀ * Real.exp (-δ₀ * dst y' y) := by
    intro y y'; rw [hdist_symm]
  have hop : ‖kernelOp Ck‖ ≤ S :=
    opNorm_kernelOp_le Ck (fun y y' => B₀ * Real.exp (-δ₀ * dst y y')) S (le_of_lt hSpos)
      hw hthm315 hsymm hS
  exact P429Pivot.coercive_of_inverse_opNorm_le Aop (kernelOp Ck) hleft hsa hpos S hSpos hop v

end RouteA

/-! ## Part 3 — ROUTE B: coercivity from the sandwich (3.185)+(3.186), with no decay. -/

section RouteB

variable {𝔄 𝔅 𝔖' 𝔅t : Type*}
  [NormedAddCommGroup 𝔄] [InnerProductSpace ℝ 𝔄]
  [NormedAddCommGroup 𝔅] [InnerProductSpace ℝ 𝔅]
  [NormedAddCommGroup 𝔖'] [InnerProductSpace ℝ 𝔖']
  [NormedAddCommGroup 𝔅t] [InnerProductSpace ℝ 𝔅t]

/-- **The form bound on `C^(k)(Λ)` from (3.185) + (3.186), with NO exponential decay.**

Chain: (3.186) gives `⟨A, G̃₂A⟩ ≤ ⟨A, G₂A⟩` (Schur complement, `G2tilde_form_le_G2_form`);
the deferred fine-level bound gives `⟨A, G₂A⟩ ≤ γ_G‖A‖²`; (3.185) transports this through the
symmetric sandwich (`sandwich_form`) at the cost of `κ² = ‖Q*(I+μ*D̄*)‖²`. -/
theorem C_form_le_of_3_185_3_186
    (Q : 𝔄 →L[ℝ] 𝔅) (Qs : 𝔅 →L[ℝ] 𝔄) (Db : 𝔖' →L[ℝ] 𝔅) (Dbs : 𝔅 →L[ℝ] 𝔖')
    (mumap : 𝔅 →L[ℝ] 𝔖') (mus : 𝔖' →L[ℝ] 𝔅)
    (G2 : 𝔄 →L[ℝ] 𝔄) (Qt : 𝔄 →L[ℝ] 𝔅t) (Qts : 𝔅t →L[ℝ] 𝔄) (Kt : 𝔅t →L[ℝ] 𝔅t)
    (C : 𝔅 →L[ℝ] 𝔅)
    -- (3.185), with `G̃₂` given by (3.186):
    (hC : C = leftFactor Q Db mumap ∘L G2tilde G2 Qt Qts Kt ∘L rightFactor Qs Dbs mus)
    (hadj : ∀ (A : 𝔄) (B : 𝔅),
      ⟪rightFactor Qs Dbs mus B, A⟫_ℝ = ⟪B, leftFactor Q Db mumap A⟫_ℝ)
    -- (3.186)'s ingredients:
    (hsa : ∀ x y : 𝔄, ⟪G2 x, y⟫_ℝ = ⟪x, G2 y⟫_ℝ)
    (hQadj : ∀ (x : 𝔄) (f : 𝔅t), ⟪Qts f, x⟫_ℝ = ⟪f, Qt x⟫_ℝ)
    (hKpos : ∀ f : 𝔅t, 0 ≤ ⟪f, Kt f⟫_ℝ)
    -- the two DEFERRED quantitative inputs:
    (γG : ℝ) (hγG : 0 ≤ γG) (hG2 : ∀ A : 𝔄, ⟪A, G2 A⟫_ℝ ≤ γG * ‖A‖ ^ 2)
    (κ : ℝ) (hκ : 0 ≤ κ) (hT : ∀ B : 𝔅, ‖rightFactor Qs Dbs mus B‖ ≤ κ * ‖B‖)
    (B : 𝔅) :
    ⟪B, C B⟫_ℝ ≤ (γG * κ ^ 2) * ‖B‖ ^ 2 := by
  have hG2t : ∀ A : 𝔄, ⟪A, G2tilde G2 Qt Qts Kt A⟫_ℝ ≤ γG * ‖A‖ ^ 2 := by
    intro A
    exact le_trans (G2tilde_form_le_G2_form G2 Qt Qts Kt hsa hQadj hKpos A) (hG2 A)
  exact sandwich_form_le Q Qs Db Dbs mumap mus (G2tilde G2 Qt Qts Kt) C hC hadj
    γG hγG hG2t κ hκ hT B

/-- **ROUTE B, assembled: `C*Δ_kC ≥ γ₀` with `γ₀ = 1/(γ_G κ²)`, no decay anywhere.**

`hleft`/`hsaC`/`hposC` package CMP99b (3.158): on `Λ̃`, `C^(k)(Λ)` is a self-adjoint positive
semidefinite left inverse of `C*Δ_kC`.  Here `C` and `Aop` act on the SAME space, which is the
restricted setting `↾_{Λ̃}` of (3.158). -/
theorem coercivity_from_sandwich
    (Q : 𝔄 →L[ℝ] 𝔅) (Qs : 𝔅 →L[ℝ] 𝔄) (Db : 𝔖' →L[ℝ] 𝔅) (Dbs : 𝔅 →L[ℝ] 𝔖')
    (mumap : 𝔅 →L[ℝ] 𝔖') (mus : 𝔖' →L[ℝ] 𝔅)
    (G2 : 𝔄 →L[ℝ] 𝔄) (Qt : 𝔄 →L[ℝ] 𝔅t) (Qts : 𝔅t →L[ℝ] 𝔄) (Kt : 𝔅t →L[ℝ] 𝔅t)
    (C Aop : 𝔅 →L[ℝ] 𝔅)
    (hC : C = leftFactor Q Db mumap ∘L G2tilde G2 Qt Qts Kt ∘L rightFactor Qs Dbs mus)
    (hadj : ∀ (A : 𝔄) (B : 𝔅),
      ⟪rightFactor Qs Dbs mus B, A⟫_ℝ = ⟪B, leftFactor Q Db mumap A⟫_ℝ)
    (hsa : ∀ x y : 𝔄, ⟪G2 x, y⟫_ℝ = ⟪x, G2 y⟫_ℝ)
    (hQadj : ∀ (x : 𝔄) (f : 𝔅t), ⟪Qts f, x⟫_ℝ = ⟪f, Qt x⟫_ℝ)
    (hKpos : ∀ f : 𝔅t, 0 ≤ ⟪f, Kt f⟫_ℝ)
    (γG : ℝ) (hγG : 0 ≤ γG) (hG2 : ∀ A : 𝔄, ⟪A, G2 A⟫_ℝ ≤ γG * ‖A‖ ^ 2)
    (κ : ℝ) (hκ : 0 ≤ κ) (hT : ∀ B : 𝔅, ‖rightFactor Qs Dbs mus B‖ ≤ κ * ‖B‖)
    (hpos : 0 < γG * κ ^ 2)
    (hleft : ∀ v : 𝔅, C (Aop v) = v)
    (hsaC : ∀ x y : 𝔅, ⟪C x, y⟫_ℝ = ⟪x, C y⟫_ℝ)
    (hposC : ∀ x : 𝔅, 0 ≤ ⟪x, C x⟫_ℝ)
    (v : 𝔅) :
    (1 / (γG * κ ^ 2)) * ‖v‖ ^ 2 ≤ ⟪v, Aop v⟫_ℝ := by
  refine formBridge Aop C hleft hsaC hposC (γG * κ ^ 2) hpos ?_ v
  intro x
  exact C_form_le_of_3_185_3_186 Q Qs Db Dbs mumap mus G2 Qt Qts Kt C hC hadj hsa hQadj hKpos
    γG hγG hG2 κ hκ hT x

end RouteB

end Thm315Core
