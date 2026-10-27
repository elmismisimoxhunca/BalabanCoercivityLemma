/-
# `RenderStep` — THE RENDERING STEP, DERIVED, UNDER THE SOURCE'S NORMALIZED TRACE.

LANE `compute/rendering_step_v2/`.  Write scope: that directory only.  Never `lake build`.

**THIS MODULE SUPERSEDES `compute/rendering_step/stage/RenderStep.lean`, WHICH IS CONVICTED** on
its §1.6: it read CMP99b's `|X|² = tr X*X` with the UNNORMALIZED trace, obtained
`A² = (|A|²/2)·1` and `‖A‖ = |A|/√2`, and therefore consumed a premise `√2`-STRICTER than the
printed (3.35).  Under the source's own normalized trace (`tr 1 = 1`, p.392 line 1) the constants
are all `1`:

    |A|² = tr(A*A),  A·A = |A|²·1,  ‖A‖_op = |A|   EXACTLY.

See `stage/TwoByTwo.lean` §0 for both conventions side by side, with the two verbatim page
sentences and the theorem `TwoByTwo.trace_one_ne_one` that separates them.

## What this module proves

`compute/sigma_threading/SCOPE.md` §8 item 3 names the chain's most exposed joint, VERBATIM:

> **The link-level smallness `‖rep(U^u e) − 1‖ ≤ ε` is this lane's rendering of (3.35).**  The
> printed condition bounds `|A|` with `U^u = e^{iηA}`; the step from `|ηA| ≤ ε` to
> `‖rep(e^{iηA}) − 1‖ ≤ ε` is NOT proved here — it is assumed in the hypothesis's shape.

**This module proves that step, from the printed premise and nothing stronger.**

## The printed source

CMP99b printed p.396, my own 400-dpi render (`probe/img/c_p396_b.png`), VERBATIM:

> for an arbitrary cube `□` of the described above class, and for a configuration `U` there exists
> a gauge transformation `u` on `□` such that `U^u = e^{iηA}`. and if the index of `□` is `j`, then
>
>     |A| < O(1) M α₀ (L^j η)^{-1},   |∇^η A| < O(1) M α₀ (L^j η)^{-2}   on □,
>     where O(1)M is a size of □ in T_{L^{-j}};                                            (3.35)
>
>     |∂^{η*} ∂^η A| < O(1) M α₀ (L^j η)^{-3}   on □.                                      (3.36)

Only the FIRST inequality of (3.35) is consumed.  The printed relation is STRICT (`<`); the
hypotheses below use `≤`, which is the weaker requirement, so every configuration the page admits
satisfies them.

**The per-cube quantifier structure of (3.35) is handled in `stage/RenderChain.lean`, NOT here.**
Everything in this module is a statement about ONE link's potential.

## The chain, and where every constant comes from

Write `Y := iηA`, `a := |A|` (the PRINTED size).

1. `A` Hermitian ⟹ `Y = η(iA)` skew-adjoint (`star_eta_smul_mul`), and `‖Y‖ = η‖A‖`
   (`norm_eta_smul_mul`) — constant `1`, from `i` unitary.
2. Skew-adjoint exponent ⟹ `exp(tY)` unitary ⟹ `‖exp(tY)‖ = 1`
   (`norm_exp_smul_of_skewAdjoint`) — DERIVED, not assumed.
3. Mean value theorem along `t ↦ exp(tY)` ⟹ `‖exp Y − 1‖ ≤ ‖Y‖` (`norm_exp_sub_one_le_of_skewAdjoint`)
   — constant `1`, no exponential loss.
4. **`‖A‖ = a` EXACTLY** (`norm_eq_printed`), from Cayley–Hamilton `A·A = a²·1` and the C*-identity
   `‖A‖² = ‖A*A‖`.  **No `√2`, in either direction** (`sqrt_two_reading_false`).
5. `η·a ≤ η·O(1)Mα₀(L^jη)^{-1} = O(1)Mα₀/L^j` (`eta_cancellation`) — the mesh `η` cancels.
6. Adjoint rep: `‖Ad(g) − 1‖ ≤ 2‖g − 1‖` (`norm_adOp_sub_one_le`) — constant `2` = the number of
   terms in `gYg⁻¹ − Y = (g−1)Yg⁻¹ + Y(g⁻¹−1)`.

Constants `1`, `1`, `1`, `2`: each counted or derived, none guessed.

Nothing here is graded by this lane (BUILD DISCIPLINE 8); it reports facts.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.longLine false

namespace RenderStep

open NormedSpace

/-! ## §1 — THE EXPONENTIAL STEP -/

section ExpCore

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-! ### §1.1 — the mean value step -/

/-- **THE CORE ESTIMATE.**  `‖exp X − 1‖ ≤ C‖X‖` whenever the one-parameter path `exp(tX)`,
`t ∈ [0,1]`, is bounded by `C` in norm.  Proof: the mean value inequality along that path. -/
theorem norm_exp_sub_one_le_of_path_bound (X : 𝔸) (C : ℝ)
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖exp (t • X)‖ ≤ C) :
    ‖exp X - 1‖ ≤ C * ‖X‖ := by
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun u : ℝ => exp (u • X)) (exp (t • X) * X) (Set.Icc (0 : ℝ) 1) t :=
    fun t _ => (hasDerivAt_exp_smul_const X t).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖exp (t • X) * X‖ ≤ C * ‖X‖ := by
    intro t ht
    calc ‖exp (t • X) * X‖ ≤ ‖exp (t • X)‖ * ‖X‖ := norm_mul_le _ _
      _ ≤ C * ‖X‖ := mul_le_mul_of_nonneg_right (hC t ht) (norm_nonneg _)
  have hmvt : ‖exp ((1 : ℝ) • X) - exp ((0 : ℝ) • X)‖ ≤ (C * ‖X‖) * ‖(1 : ℝ) - 0‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Icc 0 1)
      (by simp) (by simp)
  rw [one_smul, zero_smul, exp_zero] at hmvt
  simpa using hmvt

end ExpCore

/-! ### §1.2 — the estimate degenerates exactly where it should -/

section ExpControls

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **CONTROL.**  At `X = 0` the estimate is an equality `0 ≤ 0` — no spurious additive constant. -/
theorem exp_sub_one_at_zero : ‖exp (0 : 𝔸) - 1‖ = 0 := by
  rw [exp_zero, sub_self, norm_zero]

end ExpControls

section ExpUnitary

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable [StarRing 𝔸] [CStarRing 𝔸] [ContinuousStar 𝔸] [StarModule ℝ 𝔸] [Nontrivial 𝔸]

/-! ### §1.3 — the path is unitary, so `C = 1` -/

/-- A real multiple of a skew-adjoint element is skew-adjoint. -/
theorem smul_mem_skewAdjoint {X : 𝔸} (hX : star X = -X) (t : ℝ) :
    t • X ∈ skewAdjoint 𝔸 := by
  rw [skewAdjoint.mem_iff, star_smul, star_trivial, hX, smul_neg]

/-- **`exp` of a skew-adjoint element is unitary, hence of norm one.**  `[Nontrivial 𝔸]` excludes
the zero algebra, where every norm is `0`. -/
theorem norm_exp_smul_of_skewAdjoint {X : 𝔸} (hX : star X = -X) (t : ℝ) :
    ‖exp (t • X)‖ = 1 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exact CStarRing.norm_of_mem_unitary
    (exp_mem_unitary_of_mem_skewAdjoint (smul_mem_skewAdjoint hX t))

/-- **THE SHARP EXPONENTIAL BOUND.**  `‖exp Y − 1‖ ≤ ‖Y‖` for skew-adjoint `Y`.  No exponential
loss, no smallness hypothesis on `Y`. -/
theorem norm_exp_sub_one_le_of_skewAdjoint {Y : 𝔸} (hY : star Y = -Y) :
    ‖exp Y - 1‖ ≤ ‖Y‖ := by
  have h := norm_exp_sub_one_le_of_path_bound Y 1
    (fun t _ => le_of_eq (norm_exp_smul_of_skewAdjoint hY t))
  simpa using h

end ExpUnitary

/-! ### §1.4 — the unitarity hypothesis is LOAD-BEARING -/

/-- `e > 2`, from Mathlib's decimal bound. -/
theorem two_lt_expOne : (2 : ℝ) < Real.exp 1 :=
  lt_trans (by norm_num) Real.exp_one_gt_d9

/-- **CONTROL (must-fail).**  Drop skew-adjointness and the sharp bound is FALSE. -/
theorem exp_sub_one_bound_fails_without_unitarity :
    ¬ (‖exp (1 : ℝ) - 1‖ ≤ ‖(1 : ℝ)‖) := by
  have hexp : exp (1 : ℝ) = Real.exp 1 := by rw [← Real.exp_eq_exp_ℝ]
  have hgt := two_lt_expOne
  intro hcon
  rw [hexp, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith), abs_one] at hcon
  linarith

/-- **CONTROL (must-fail, the other side).**  The non-unitary exponent really does violate the
path bound at `C = 1`. -/
theorem path_bound_fails_without_unitarity :
    ¬ (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖exp (t • (1 : ℝ))‖ ≤ 1) := by
  intro h
  have h1 := h 1 (by norm_num)
  rw [smul_eq_mul, mul_one] at h1
  have hexp : exp (1 : ℝ) = Real.exp 1 := by rw [← Real.exp_eq_exp_ℝ]
  have hgt := two_lt_expOne
  rw [hexp, Real.norm_eq_abs, abs_of_pos (by linarith)] at h1
  linarith

/-! ### §1.5 — the printed `i`, as an ELEMENT of the algebra -/

section ImaginaryUnit

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
variable [StarRing 𝔸] [CStarRing 𝔸] [StarModule ℝ 𝔸] [Nontrivial 𝔸]

/-- The printed `i` of `e^{iηA}`, as an element of the algebra. -/
structure IsImaginaryUnit (J : 𝔸) : Prop where
  /-- `i* = −i`. -/
  star_eq : star J = -J
  /-- `i² = −1`. -/
  sq_eq : J * J = -1
  /-- `i` is central — this is what makes `(iA)* = −iA` for Hermitian `A`. -/
  central : ∀ x : 𝔸, J * x = x * J

/-- `i` is unitary: `i*i = −i·i = 1`. -/
theorem IsImaginaryUnit.mem_unitary {J : 𝔸} (hJ : IsImaginaryUnit J) : J ∈ unitary 𝔸 := by
  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩
  · rw [hJ.star_eq, neg_mul, hJ.sq_eq, neg_neg]
  · rw [hJ.star_eq, mul_neg, hJ.sq_eq, neg_neg]

/-- **`iA` is skew-adjoint when `A` is Hermitian.**  `(iA)* = A*i* = A(−i) = −(Ai) = −(iA)`. -/
theorem IsImaginaryUnit.star_mul_of_selfAdjoint {J A : 𝔸} (hJ : IsImaginaryUnit J)
    (hA : star A = A) : star (J * A) = -(J * A) := by
  rw [star_mul, hA, hJ.star_eq, mul_neg, ← hJ.central A]

/-- `‖iA‖ = ‖A‖`: multiplication by a unitary is isometric in a C*-algebra. -/
theorem IsImaginaryUnit.norm_mul {J : 𝔸} (hJ : IsImaginaryUnit J) (A : 𝔸) :
    ‖J * A‖ = ‖A‖ :=
  CStarRing.norm_coe_unitary_mul (⟨J, hJ.mem_unitary⟩ : unitary 𝔸) A

/-- **`‖η·(iA)‖ = η‖A‖`** for `η ≥ 0` — the mesh factor comes out of the exponent linearly, with
constant `1`. -/
theorem norm_eta_smul_mul (J A : 𝔸) (hJ : IsImaginaryUnit J) (η : ℝ) (hη : 0 ≤ η) :
    ‖(η • (J * A) : 𝔸)‖ = η * ‖A‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη, hJ.norm_mul A]

/-- **`Y = η·(iA)` is skew-adjoint** — the hypothesis §1.3 needs, from `A` Hermitian alone. -/
theorem star_eta_smul_mul (J A : 𝔸) (hJ : IsImaginaryUnit J) (hA : star A = A) (η : ℝ) :
    star ((η • (J * A) : 𝔸)) = -(η • (J * A)) := by
  rw [star_smul, star_trivial, hJ.star_mul_of_selfAdjoint hA, smul_neg]

end ImaginaryUnit

/-- **NON-VACUITY WITNESS (L7).**  `IsImaginaryUnit` is inhabited: `Complex.I` in the C*-algebra
`ℂ`.  DISCLOSED: `ℂ` is commutative, so on this witness `adOp` is the identity and §2 says nothing.
A NONCOMMUTATIVE witness is `Carrier.isImaginaryUnit_imagUnit`. -/
theorem isImaginaryUnit_complexI : IsImaginaryUnit (Complex.I : ℂ) where
  star_eq := by simp
  sq_eq := by simp [Complex.I_mul_I]
  central := fun x => by ring

/-! ### §1.6 — `|A|` VERSUS THE ALGEBRA NORM: THEY ARE EQUAL

**THIS IS THE SECTION THAT WAS CONVICTED, AND THIS IS THE REPAIR.**

CMP99b's `|A|` is the Hilbert–Schmidt norm `|X|² = tr X*X` (p.390) with `tr` the paper's
NORMALIZED trace, `tr 1 = 1` (p.392 line 1).  For a traceless Hermitian `2×2` `A` this gives
Cayley–Hamilton in the form

    A·A = |A|²·1                       (`TwoByTwo.herm2_sq`)

and hence, by the C*-identity `‖A‖² = ‖A*A‖`,

    ‖A‖ = |A|      EXACTLY,  constant 1.

The convicted module had `A·A = (|A|²/2)·1` and `‖A‖ = |A|/√2`, which are the SAME two facts
written in the unnormalized convention — i.e. with `|A|` denoting `√2` times the printed size.
Consuming (3.35) in that convention tightens the premise by `√2`. -/

section CStarNorm

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
variable [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]

/-- For a self-adjoint `A` with `A·A = κ·1`, `κ ≥ 0`, the C*-norm is EXACTLY `√κ`. -/
theorem norm_of_sq_eq_smul_one (A : 𝔸) (hA : star A = A) (κ : ℝ) (hκ : 0 ≤ κ)
    (hsq : A * A = κ • (1 : 𝔸)) : ‖A‖ = Real.sqrt κ := by
  have hnorm : ‖A‖ * ‖A‖ = κ := by
    have h := CStarRing.norm_star_mul_self (x := A)
    rw [hA, hsq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hκ, norm_one, mul_one] at h
    exact h.symm
  have hsqn : ‖A‖ ^ 2 = κ := by rw [sq]; exact hnorm
  rw [← hsqn, Real.sqrt_sq (norm_nonneg A)]

/-- **THE ALGEBRA NORM IS THE PRINTED NORM.**  `‖A‖ = |A|` for a traceless `2×2` Hermitian `A`
with printed size `a = |A|` (so `A·A = a²·1`).  Constant `1`; no comparison constant is left. -/
theorem norm_eq_printed (A : 𝔸) (hA : star A = A) (a : ℝ) (ha : 0 ≤ a)
    (hsq : A * A = (a ^ 2) • (1 : 𝔸)) : ‖A‖ = a := by
  have hκ : (0 : ℝ) ≤ a ^ 2 := by positivity
  rw [norm_of_sq_eq_smul_one A hA (a ^ 2) hκ hsq, Real.sqrt_sq ha]

/-- The inequality form, for use where only domination is needed. -/
theorem norm_le_printed (A : 𝔸) (hA : star A = A) (a : ℝ) (ha : 0 ≤ a)
    (hsq : A * A = (a ^ 2) • (1 : 𝔸)) : ‖A‖ ≤ a :=
  le_of_eq (norm_eq_printed A hA a ha hsq)

/-- **THE CONVICTED `√2` IS FALSE UNDER THE PRINTED CONVENTION.**  The superseded module proved
`‖A‖·√2 = |A|`.  With `|A|` the PRINTED size that equation forces `a = 0`: since `‖A‖ = a`, it
says `a√2 = a`.  So for every nonzero potential the old identity is FALSE. -/
theorem sqrt_two_reading_false (A : 𝔸) (hA : star A = A) (a : ℝ) (ha : 0 < a)
    (hsq : A * A = (a ^ 2) • (1 : 𝔸)) : ‖A‖ * Real.sqrt 2 ≠ a := by
  rw [norm_eq_printed A hA a (le_of_lt ha) hsq]
  intro h
  have hlt : (1 : ℝ) < Real.sqrt 2 := by
    have hs : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa [Real.sqrt_one] using hs
  nlinarith [h, hlt, ha]

end CStarNorm

/-! ## §2 — THE REPRESENTATION STEP -/

section Adjoint

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- **THE ADJOINT DISPLACEMENT BOUND, pointwise.**  `gYg⁻¹ − Y = (g−1)Yg⁻¹ + Y(g⁻¹−1)`, two terms,
each bounded by `‖g−1‖‖Y‖` when `‖g⁻¹‖ ≤ 1`.  The constant `2` is the number of terms. -/
theorem norm_conj_sub_self_le (g ginv Y : 𝔸) (hinv : ginv * g = 1) (hginv : ‖ginv‖ ≤ 1) :
    ‖g * Y * ginv - Y‖ ≤ 2 * ‖g - 1‖ * ‖Y‖ := by
  have hsplit : g * Y * ginv - Y = (g - 1) * Y * ginv + Y * (ginv - 1) := by
    noncomm_ring
  have hinvclose : ‖ginv - 1‖ ≤ ‖g - 1‖ := by
    have hfac : ginv - 1 = ginv * (1 - g) := by
      rw [mul_sub, mul_one, hinv]
    calc ‖ginv - 1‖ = ‖ginv * (1 - g)‖ := by rw [hfac]
      _ ≤ ‖ginv‖ * ‖1 - g‖ := norm_mul_le _ _
      _ ≤ 1 * ‖1 - g‖ := mul_le_mul_of_nonneg_right hginv (norm_nonneg _)
      _ = ‖g - 1‖ := by rw [one_mul, norm_sub_rev]
  have hA : ‖(g - 1) * Y * ginv‖ ≤ ‖g - 1‖ * ‖Y‖ := by
    calc ‖(g - 1) * Y * ginv‖ ≤ ‖(g - 1) * Y‖ * ‖ginv‖ := norm_mul_le _ _
      _ ≤ (‖g - 1‖ * ‖Y‖) * ‖ginv‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (‖g - 1‖ * ‖Y‖) * 1 :=
          mul_le_mul_of_nonneg_left hginv (by positivity)
      _ = ‖g - 1‖ * ‖Y‖ := mul_one _
  have hB : ‖Y * (ginv - 1)‖ ≤ ‖g - 1‖ * ‖Y‖ := by
    calc ‖Y * (ginv - 1)‖ ≤ ‖Y‖ * ‖ginv - 1‖ := norm_mul_le _ _
      _ ≤ ‖Y‖ * ‖g - 1‖ := mul_le_mul_of_nonneg_left hinvclose (norm_nonneg _)
      _ = ‖g - 1‖ * ‖Y‖ := mul_comm _ _
  calc ‖g * Y * ginv - Y‖ = ‖(g - 1) * Y * ginv + Y * (ginv - 1)‖ := by rw [hsplit]
    _ ≤ ‖(g - 1) * Y * ginv‖ + ‖Y * (ginv - 1)‖ := norm_add_le _ _
    _ ≤ ‖g - 1‖ * ‖Y‖ + ‖g - 1‖ * ‖Y‖ := add_le_add hA hB
    _ = 2 * ‖g - 1‖ * ‖Y‖ := by ring

/-- The adjoint action as a continuous linear operator on the algebra: `Y ↦ g·Y·ginv`. -/
noncomputable def adOp (g ginv : 𝔸) : 𝔸 →L[ℝ] 𝔸 :=
  ContinuousLinearMap.mulLeftRight ℝ 𝔸 g ginv

@[simp] theorem adOp_apply (g ginv Y : 𝔸) : adOp g ginv Y = g * Y * ginv := rfl

/-- **THE REPRESENTATION STEP.**  `‖Ad(g) − 1‖ ≤ 2‖g − 1‖`, in the operator norm on the fibre. -/
theorem norm_adOp_sub_one_le (g ginv : 𝔸) (hinv : ginv * g = 1) (hginv : ‖ginv‖ ≤ 1) :
    ‖adOp g ginv - 1‖ ≤ 2 * ‖g - 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun Y => ?_)
  have hval : (adOp g ginv - 1) Y = g * Y * ginv - Y := by
    simp
  rw [hval]
  exact norm_conj_sub_self_le g ginv Y hinv hginv

/-- `Ad(g)` is a contraction when `g` and `g⁻¹` are — the hypothesis `HolonomyGap` calls `hcontr`. -/
theorem norm_adOp_le_one (g ginv : 𝔸) (hg : ‖g‖ ≤ 1) (hginv : ‖ginv‖ ≤ 1) :
    ‖adOp g ginv‖ ≤ 1 := by
  have h : ‖adOp g ginv‖ ≤ ‖g‖ * ‖ginv‖ :=
    ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ 𝔸 g ginv
  calc ‖adOp g ginv‖ ≤ ‖g‖ * ‖ginv‖ := h
    _ ≤ 1 * 1 := mul_le_mul hg hginv (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num

/-- **CONTROL.**  `adOp` is the identity exactly on the commutant — it is not silently `id`. -/
theorem adOp_id_iff_commutes (g ginv Y : 𝔸) (hL : ginv * g = 1) (hR : g * ginv = 1) :
    adOp g ginv Y = Y ↔ g * Y = Y * g := by
  rw [adOp_apply]
  constructor
  · intro h
    calc g * Y = g * Y * (ginv * g) := by rw [hL, mul_one]
      _ = (g * Y * ginv) * g := by noncomm_ring
      _ = Y * g := by rw [h]
  · intro h
    calc g * Y * ginv = Y * g * ginv := by rw [h]
      _ = Y * (g * ginv) := by rw [mul_assoc]
      _ = Y := by rw [hR, mul_one]

/-- **CONTROL.**  At `g = 1` the adjoint displacement is exactly `0` — no spurious constant. -/
theorem adOp_one : adOp (1 : 𝔸) 1 = 1 := by
  ext Y <;> simp

end Adjoint

/-! ## §3 — THE PRINTED BOUND, AND THE COMPOSITION -/

/-- (3.35)'s right-hand side for `|A|`: `O(1) M α₀ (L^j η)^{-1}`.  **`c` is the printed `O(1)`, NOT
`O(1)M`** — `M` is carried as its own argument and multiplies `c` in the body, so reading `c` as
`O(1)M` would double-count `M`.  `Lj` is `L^j` for the index `j` OF THE CUBE the bound is stated
on — see `RenderChain`. -/
noncomputable def printedABound (c M α₀ Lj η : ℝ) : ℝ := c * M * α₀ / (Lj * η)

/-- The per-link operator smallness consumed by `SigmaThread.pairwise_gap_scale_uniform`. -/
noncomputable def linkEps (c M α₀ Lj : ℝ) : ℝ := c * M * α₀ / Lj

/-- **THE MESH CANCELLATION.**  `η · O(1)Mα₀(L^jη)^{-1} = O(1)Mα₀/L^j`. -/
theorem eta_cancellation (c M α₀ Lj η : ℝ) (hLj : Lj ≠ 0) (hη : η ≠ 0) :
    η * printedABound c M α₀ Lj η = linkEps c M α₀ Lj := by
  unfold printedABound linkEps
  field_simp

/-- `linkEps` is nonnegative at nonnegative printed data. -/
theorem linkEps_nonneg (c M α₀ Lj : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀) (hLj : 0 < Lj) :
    0 ≤ linkEps c M α₀ Lj := by
  unfold linkEps
  positivity

section Rendering

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable [StarRing 𝔸] [CStarRing 𝔸] [ContinuousStar 𝔸] [StarModule ℝ 𝔸] [Nontrivial 𝔸]

/-- **THE RENDERING STEP AT THE GROUP LEVEL.**  Constant `1`. -/
theorem rendering_step_group (g Y : 𝔸) (hg : g = exp Y) (hY : star Y = -Y)
    (η Aprint c M α₀ Lj : ℝ) (hη : 0 ≤ η) (hLj : 0 < Lj) (hηne : η ≠ 0)
    (hYnorm : ‖Y‖ ≤ η * Aprint)
    (hA : Aprint ≤ printedABound c M α₀ Lj η) :
    ‖g - 1‖ ≤ linkEps c M α₀ Lj := by
  have hstep : ‖g - 1‖ ≤ ‖Y‖ := by
    rw [hg]; exact norm_exp_sub_one_le_of_skewAdjoint hY
  have hmul : η * Aprint ≤ η * printedABound c M α₀ Lj η :=
    mul_le_mul_of_nonneg_left hA hη
  have hcancel : η * printedABound c M α₀ Lj η = linkEps c M α₀ Lj :=
    eta_cancellation c M α₀ Lj η (ne_of_gt hLj) hηne
  calc ‖g - 1‖ ≤ ‖Y‖ := hstep
    _ ≤ η * Aprint := hYnorm
    _ ≤ η * printedABound c M α₀ Lj η := hmul
    _ = linkEps c M α₀ Lj := hcancel

/-- **THE RENDERING STEP AT THE REPRESENTATION LEVEL**, adjoint fibre: constant `2`. -/
theorem rendering_step_adjoint (g ginv Y : 𝔸) (hg : g = exp Y) (hY : star Y = -Y)
    (hinv : ginv * g = 1) (hginv : ‖ginv‖ ≤ 1)
    (η Aprint c M α₀ Lj : ℝ) (hη : 0 ≤ η) (hLj : 0 < Lj) (hηne : η ≠ 0)
    (hYnorm : ‖Y‖ ≤ η * Aprint)
    (hA : Aprint ≤ printedABound c M α₀ Lj η) :
    ‖adOp g ginv - 1‖ ≤ 2 * linkEps c M α₀ Lj := by
  have h1 := norm_adOp_sub_one_le g ginv hinv hginv
  have h2 := rendering_step_group g Y hg hY η Aprint c M α₀ Lj hη hLj hηne hYnorm hA
  calc ‖adOp g ginv - 1‖ ≤ 2 * ‖g - 1‖ := h1
    _ ≤ 2 * linkEps c M α₀ Lj := by linarith

/-- **THE INVERSE LINK IS AUTOMATIC.**  `exp(−Y)` is the two-sided inverse of `exp Y` and is itself
unitary, so `hinv`/`hginv` are DISCHARGED whenever the link is the printed exponential. -/
theorem exp_neg_inv_and_contraction (Y : 𝔸) (hY : star Y = -Y) :
    exp (-Y) * exp Y = 1 ∧ ‖exp (-Y)‖ ≤ 1 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hmem : Y ∈ skewAdjoint 𝔸 := by rw [skewAdjoint.mem_iff]; exact hY
  have hu : exp Y ∈ unitary 𝔸 := exp_mem_unitary_of_mem_skewAdjoint hmem
  have hstar : star (exp Y) = exp (-Y) := by rw [star_exp, hY]
  have hneg : star (-Y) = -(-Y) := by rw [star_neg, hY, neg_neg]
  refine ⟨?_, ?_⟩
  · have h1 := (Unitary.mem_iff.mp hu).1
    rw [hstar] at h1
    exact h1
  · have h2 := norm_exp_smul_of_skewAdjoint hneg 1
    rw [one_smul] at h2
    exact le_of_eq h2

/-- **THE RENDERING STEP, HYPOTHESIS-MINIMAL FORM.** -/
theorem rendering_step_from_printed (Y : 𝔸) (hY : star Y = -Y)
    (η Aprint c M α₀ Lj : ℝ) (hη : 0 ≤ η) (hLj : 0 < Lj) (hηne : η ≠ 0)
    (hYnorm : ‖Y‖ ≤ η * Aprint)
    (hA : Aprint ≤ printedABound c M α₀ Lj η) :
    ‖adOp (exp Y) (exp (-Y)) - 1‖ ≤ 2 * linkEps c M α₀ Lj := by
  obtain ⟨hinv, hcontr⟩ := exp_neg_inv_and_contraction Y hY
  exact rendering_step_adjoint (exp Y) (exp (-Y)) Y rfl hY hinv hcontr
    η Aprint c M α₀ Lj hη hLj hηne hYnorm hA

end Rendering

/-! ### §3.1 — THE RENDERING STEP FROM SOURCE DATA ONLY, WITH THE PRINTED PREMISE -/

section FromSource

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable [StarRing 𝔸] [CStarRing 𝔸] [ContinuousStar 𝔸] [StarModule ℝ 𝔸] [Nontrivial 𝔸]

/-- **THE EXPONENT'S NORM IS EXACTLY `η|A|`.**  This is the statement that shows the derivation
adds NO strictness to (3.35): the printed size `a` enters the estimate through an EQUALITY, not
through a lossy comparison.  (The convicted module had `‖Y‖ = η‖A‖ = η·a/√2` with `a` its own
unnormalized size — the `√2` that tightened its premise.) -/
theorem norm_exponent_eq_eta_printed (J A : 𝔸) (hJ : IsImaginaryUnit J) (hA : star A = A)
    (η a : ℝ) (hη : 0 ≤ η) (ha : 0 ≤ a) (hsq : A * A = (a ^ 2) • (1 : 𝔸)) :
    ‖(η • (J * A) : 𝔸)‖ = η * a := by
  rw [norm_eta_smul_mul J A hJ η hη, norm_eq_printed A hA a ha hsq]

/-- **THE RENDERING STEP, SOURCE-DATA FORM, PRINTED PREMISE.**

* `hJ`     — `J` is the printed `i`: skew-adjoint, square `−1`, central;
* `hA`     — `A` Hermitian (CMP99b's convention for the potential in `U^u = e^{iηA}`);
* `hsq`    — Cayley–Hamilton with the PRINTED size: `A² = |A|²·1`, `a = |A|`
             (`TwoByTwo.herm2_sq`);
* `hprint` — **(3.35)**: `|A| ≤ O(1)Mα₀(L^jη)^{-1}`, at the PRINTED normalization, on the cube
             whose index gives `Lj`.

Conclusion: `2·O(1)Mα₀/L^j`, `η`-free.  The only constant above the printed one is the adjoint
`2`; there is no `√2`. -/
theorem rendering_step_from_source (J A : 𝔸) (hJ : IsImaginaryUnit J) (hA : star A = A)
    (η a c M α₀ Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (ha : 0 ≤ a) (hLj : 0 < Lj)
    (hsq : A * A = (a ^ 2) • (1 : 𝔸))
    (hprint : a ≤ printedABound c M α₀ Lj η) :
    ‖adOp (exp (η • (J * A))) (exp (-(η • (J * A)))) - 1‖ ≤ 2 * linkEps c M α₀ Lj := by
  have hYnorm : ‖(η • (J * A) : 𝔸)‖ ≤ η * a :=
    le_of_eq (norm_exponent_eq_eta_printed J A hJ hA η a hη ha hsq)
  exact rendering_step_from_printed (η • (J * A)) (star_eta_smul_mul J A hJ hA η)
    η a c M α₀ Lj hη hLj hηne hYnorm hprint

/-- **THE GROUP-LEVEL STEP AT THE PRINTED PREMISE**, constant `1` — for a consumer whose fibre is
the DEFINING representation rather than the adjoint. -/
theorem rendering_step_group_from_source (J A : 𝔸) (hJ : IsImaginaryUnit J) (hA : star A = A)
    (η a c M α₀ Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (ha : 0 ≤ a) (hLj : 0 < Lj)
    (hsq : A * A = (a ^ 2) • (1 : 𝔸))
    (hprint : a ≤ printedABound c M α₀ Lj η) :
    ‖exp (η • (J * A)) - 1‖ ≤ linkEps c M α₀ Lj :=
  rendering_step_group _ (η • (J * A)) rfl (star_eta_smul_mul J A hJ hA η)
    η a c M α₀ Lj hη hLj hηne
    (le_of_eq (norm_exponent_eq_eta_printed J A hJ hA η a hη ha hsq)) hprint

end FromSource

/-! ## §4 — WHAT THE CORRECTION CHANGED, AS ARITHMETIC

The convicted premise, restated in PRINTED units, is `√2·|A| ≤ O(1)Mα₀(L^jη)^{-1}`, i.e. the
printed condition with `α₀` replaced by `α₀/√2`.  It therefore EXCLUDES configurations the page
admits.  A concrete such point: `|A| = 1` with the printed bound `= 1`. -/

/-- **THE CONVICTED PREMISE EXCLUDES A PRINTED-ADMISSIBLE POINT.**  At `a = 1` and printed bound
`1`, the printed condition `a ≤ 1` HOLDS while the convicted condition `√2·a ≤ 1` FAILS. -/
theorem convicted_premise_excludes_printed_point :
    (1 : ℝ) ≤ 1 ∧ ¬ ((1 : ℝ) * Real.sqrt 2 ≤ 1) := by
  refine ⟨le_refl 1, ?_⟩
  intro h
  have hlt : (1 : ℝ) < Real.sqrt 2 := by
    have : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa [Real.sqrt_one] using this
  rw [one_mul] at h
  linarith

/-- **THE PRINTED RELATION IS STRICT; THE HYPOTHESES USE `≤`.**  So every configuration the page
admits satisfies the hypotheses — the `<`→`≤` move WEAKENS the requirement, it does not tighten
it. -/
theorem strict_implies_le (a B : ℝ) (h : a < B) : a ≤ B := le_of_lt h

/-! ## §5 — THE `L^j` CANCELLATION AT THE DERIVED CONSTANT -/

/-- **THE CANCELLATION AT THE DERIVED CONSTANT.**  `(cube length in T_η) × (derived per-link ε)`
is `L^j`-free and `η`-free. -/
theorem derived_length_times_epsilon (c c' M α₀ Lj : ℝ) (hLj : 0 < Lj) :
    (c' * M * Lj) * (2 * linkEps c M α₀ Lj) = 2 * (c * c') * M ^ 2 * α₀ := by
  have hne : Lj ≠ 0 := ne_of_gt hLj
  unfold linkEps
  field_simp

/-- **CONTROL.**  The derived constant is exactly twice the assumed one. -/
theorem derived_eps_is_twice_linkEps (c M α₀ Lj : ℝ) :
    2 * linkEps c M α₀ Lj = linkEps (2 * c) M α₀ Lj := by
  unfold linkEps
  ring

/-! ### Numeric pins — a mutation of either formula moves one of these -/

theorem printedABound_pin_one : printedABound 1 1 1 1 1 = 1 := by
  unfold printedABound; norm_num

theorem printedABound_pin_eta_two : printedABound 1 1 1 1 2 = 1 / 2 := by
  unfold printedABound; norm_num

theorem printedABound_pin_Lj_two : printedABound 1 1 1 2 1 = 1 / 2 := by
  unfold printedABound; norm_num

theorem linkEps_pin_one : linkEps 1 1 1 1 = 1 := by
  unfold linkEps; norm_num

theorem linkEps_pin_Lj_two : linkEps 1 1 1 2 = 1 / 2 := by
  unfold linkEps; norm_num

/-- **CONTROL.**  The mesh really has cancelled: `printedABound` at TWO different meshes feeds the
SAME `linkEps`. -/
theorem eta_cancellation_two_meshes (c M α₀ Lj η η' : ℝ) (hLj : Lj ≠ 0) (hη : η ≠ 0)
    (hη' : η' ≠ 0) :
    η * printedABound c M α₀ Lj η = η' * printedABound c M α₀ Lj η' := by
  rw [eta_cancellation c M α₀ Lj η hLj hη, eta_cancellation c M α₀ Lj η' hLj hη']

end RenderStep
