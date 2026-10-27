/-
# The p.429-pivot bridge: a covariance NORM bound yields the p.428 coercivity constant.

CONTEXT (reading lane `compute/p429_pivot/`). CMP99b p.428 asserts that `C*Δ_kC` is positive
definite "with a lower bound `γ₀ > 0` independent of `k` and `U`", cites CMP96 Lemma 2.4 for the
`U = 1` case, and then DECLINES that route: "so we will proceed in a different way".  The
different way ends at CMP99b Theorem 3.15 (p.432), which bounds the COVARIANCE kernel:
`|C^(k)(Λ; y,y')| ≤ B₀ e^(-δ₀|y-y'|)`, with `B₀, δ₀` "depending on `d` and `L` only".
CMP99b (3.158) states `(C*Δ_kC)⁻¹ = C̃^(k)(Λ) = C^(k)(Λ)↾_Λ̃`.

This file supplies the missing OPERATOR-THEORETIC STEP that turns the second into the first:
if the inverse of `A` has operator norm at most `B`, then `A` is coercive with constant `1/B`.
Nothing here is about lattices; it is the abstract brick, so it is reusable and its
non-vacuity does not depend on any finite-domain artefact.

NOT a claim that Theorem 3.15 is proved, and NOT a claim about the Schur step
(kernel bound → operator-norm bound); those are separate. This is the third link only.

Self-contained: imports Mathlib only.  Write scope: compute/p429_pivot/.
-/
import Mathlib

open scoped InnerProductSpace RealInnerProductSpace

namespace P429Pivot

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Key operator inequality.** If `M` is a self-adjoint, positive semidefinite bounded
operator, then `‖M w‖² ≤ ‖M‖ * ⟪w, M w⟫` for every `w`.

Proof is the elementary "complete the square at `t = ‖M‖`" argument, using only positivity of
the semi-inner product `S(x,y) = ⟪x, M y⟫` at the single vector `M w - ‖M‖ • w`.  No
Cauchy–Schwarz for semidefinite forms and no square roots are needed. -/
theorem normSq_apply_le_norm_mul_inner
    (M : H →L[ℝ] H)
    (hsa : ∀ x y : H, ⟪M x, y⟫_ℝ = ⟪x, M y⟫_ℝ)
    (hpos : ∀ x : H, 0 ≤ ⟪x, M x⟫_ℝ)
    (w : H) :
    ‖M w‖ ^ 2 ≤ ‖M‖ * ⟪w, M w⟫_ℝ := by
  set t : ℝ := ‖M‖ with ht
  have htnn : 0 ≤ t := norm_nonneg _
  -- the test vector
  set z : H := M w - t • w with hz
  have hzpos : 0 ≤ ⟪z, M z⟫_ℝ := hpos z
  -- expand ⟪z, M z⟫
  have hMz : M z = M (M w) - t • M w := by
    simp [hz, map_sub, map_smul]
  have hexp : ⟪z, M z⟫_ℝ
      = ⟪M w, M (M w)⟫_ℝ - t * ⟪M w, M w⟫_ℝ - t * ⟪w, M (M w)⟫_ℝ
        + t * t * ⟪w, M w⟫_ℝ := by
    rw [hz, hMz]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    ring
  -- self-adjointness collapses the two cross terms to ‖M w‖²
  have hcross : ⟪w, M (M w)⟫_ℝ = ⟪M w, M w⟫_ℝ := (hsa w (M w)).symm
  have hnormsq : ⟪M w, M w⟫_ℝ = ‖M w‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
  -- the diagonal term is bounded by ‖M‖ ‖M w‖²
  have hdiag : ⟪M w, M (M w)⟫_ℝ ≤ t * ‖M w‖ ^ 2 := by
    calc ⟪M w, M (M w)⟫_ℝ ≤ ‖M w‖ * ‖M (M w)‖ := real_inner_le_norm _ _
      _ ≤ ‖M w‖ * (‖M‖ * ‖M w‖) := by
          have := M.le_opNorm (M w)
          nlinarith [norm_nonneg (M w), norm_nonneg (M (M w))]
      _ = t * ‖M w‖ ^ 2 := by rw [ht]; ring
  -- assemble: 0 ≤ t‖Mw‖² - 2t‖Mw‖² + t²⟪w,Mw⟫  ⟹  t‖Mw‖² ≤ t²⟪w,Mw⟫
  have hmain : t * ‖M w‖ ^ 2 ≤ t * (t * ⟪w, M w⟫_ℝ) := by
    rw [hexp, hcross, hnormsq] at hzpos
    nlinarith [hzpos, hdiag]
  rcases eq_or_lt_of_le htnn with h0 | hpos'
  · -- ‖M‖ = 0 forces M = 0, so both sides vanish
    have hM0 : M = 0 := norm_eq_zero.mp (ht.symm.trans h0.symm)
    simp [hM0]
  · exact le_of_mul_le_mul_left hmain hpos'

/-- **THE BRIDGE.** Let `A` be a bounded operator with a self-adjoint, positive semidefinite
bounded left inverse `M` (`M (A v) = v` for all `v`), and suppose `‖M‖ ≤ B` with `0 < B`.
Then `A` is coercive with constant `1 / B`:
`(1/B) * ‖v‖² ≤ ⟪v, A v⟫` for every `v`.

Read against CMP99b: `A := C*Δ_kC`, `M := (C*Δ_kC)⁻¹ = C^(k)(Λ)↾_Λ̃` by (3.158), and `B` is
the operator-norm bound on the covariance.  The conclusion is exactly the shape of p.428's
"`positive definite operator C*Δ_kC with a lower bound γ₀ > 0`", with `γ₀ = 1/B`.  Hence
`γ₀`'s independence of `k` and `U` is inherited from `B`'s — it is not an extra demand. -/
theorem coercive_of_inverse_opNorm_le
    (A M : H →L[ℝ] H)
    (hleft : ∀ v : H, M (A v) = v)
    (hsa : ∀ x y : H, ⟪M x, y⟫_ℝ = ⟪x, M y⟫_ℝ)
    (hpos : ∀ x : H, 0 ≤ ⟪x, M x⟫_ℝ)
    (B : ℝ) (hB : 0 < B) (hMB : ‖M‖ ≤ B)
    (v : H) :
    (1 / B) * ‖v‖ ^ 2 ≤ ⟪v, A v⟫_ℝ := by
  have hv : M (A v) = v := hleft v
  have hkey : ‖M (A v)‖ ^ 2 ≤ ‖M‖ * ⟪A v, M (A v)⟫_ℝ :=
    normSq_apply_le_norm_mul_inner M hsa hpos (A v)
  rw [hv] at hkey
  -- ⟪A v, v⟫ = ⟪v, A v⟫
  have hsymm : ⟪A v, v⟫_ℝ = ⟪v, A v⟫_ℝ := real_inner_comm _ _
  rw [hsymm] at hkey
  -- ‖v‖² ≤ ‖M‖ ⟪v, A v⟫ ≤ B ⟪v, A v⟫
  have hnn : (0:ℝ) ≤ ‖M‖ := norm_nonneg M
  by_cases hq : (0:ℝ) ≤ ⟪v, A v⟫_ℝ
  · have hBq : ‖v‖ ^ 2 ≤ B * ⟪v, A v⟫_ℝ := by nlinarith [hkey, hq, hMB]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hB]
    linarith [hBq]
  · -- a negative form value would force ‖v‖ = 0, hence the value is 0: contradiction
    exfalso
    push_neg at hq
    have hle0 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [hkey, hq, hnn]
    have hn0 : ‖v‖ = 0 := by nlinarith [norm_nonneg v, hle0]
    have hv0 : v = 0 := norm_eq_zero.mp hn0
    rw [hv0] at hq
    simp at hq

/-- **Must-not-fire control (S82 garbage substitution).** The bridge is NOT algebraically
forced: with `M := 0` (which is self-adjoint and PSD, `‖M‖ = 0 ≤ B`) the left-inverse
hypothesis `∀ v, M (A v) = v` FAILS on any nonzero `v`.  So the hypothesis set is not
satisfiable by the degenerate witness, i.e. `hleft` carries content. -/
theorem zero_is_not_a_left_inverse (A : H →L[ℝ] H) (v : H) (hv : v ≠ 0) :
    ¬ ((0 : H →L[ℝ] H) (A v) = v) := by
  simpa using hv.symm

/-- **Sharpness / non-vacuity witness.** At `A = M = id` and `B = 1` the bridge's conclusion is
`‖v‖² ≤ ⟪v, v⟫`, an equality — so the constant `1/B` cannot be improved in general. -/
theorem bridge_sharp_at_identity (v : H) :
    (1 / (1:ℝ)) * ‖v‖ ^ 2 = ⟪v, (ContinuousLinearMap.id ℝ H) v⟫_ℝ := by
  simp

end P429Pivot
