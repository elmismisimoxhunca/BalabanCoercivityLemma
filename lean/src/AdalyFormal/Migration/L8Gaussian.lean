/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic
import AdalyFormal.Migration.L8Theorem

/-!
# The finite-dimensional Gaussian moment identity (R4 / Theorem L8 clause (i))

Standalone, mathlib-only development of

  `∫ y, exp (-(1/2) ⟨y, A y⟩ + ⟨b, y⟩) = Z_A * exp ((1/2) ⟨b, A⁻¹ b⟩)`,  `Z_A > 0`,

for a symmetric `A : Matrix (Fin n) (Fin n) ℝ` that is positive definite, with
`Z_A := ∫ y, exp (-(1/2) ⟨y, A y⟩)` — the `J`-free normalization.  Note the value of `Z_A`
is deliberately NOT computed: the hoisted statement only asks for SOME positive `Z'` chosen
before `J`, and taking the `J = 0` integral itself is that constant.  This removes the need
for the `(2π)^{n/2} (det A)^{-1/2}` change-of-variables computation entirely.
-/

namespace AdalyFormal.Migration.L8Gaussian

open MeasureTheory Matrix Real

variable {n : ℕ}

/-! ## §1 Elementary facts about the quadratic form `x ↦ x ⬝ᵥ A *ᵥ x` -/

lemma qform_continuous (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun x : Fin n → ℝ => x ⬝ᵥ A *ᵥ x) := by
  have h : (fun x : Fin n → ℝ => x ⬝ᵥ A *ᵥ x)
      = fun x : Fin n → ℝ => ∑ i, ∑ j, x i * (A i j * x j) := by
    funext x; simp [dotProduct, mulVec, Finset.mul_sum]
  rw [h]; fun_prop

lemma qform_smul (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x : Fin n → ℝ) :
    (t • x) ⬝ᵥ A *ᵥ (t • x) = t ^ 2 * (x ⬝ᵥ A *ᵥ x) := by
  simp [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

lemma qform_zero (A : Matrix (Fin n) (Fin n) ℝ) :
    (0 : Fin n → ℝ) ⬝ᵥ A *ᵥ (0 : Fin n → ℝ) = 0 := by
  simp

/-! ## §2 Coercivity: a positive definite form dominates a multiple of `∑ xᵢ²` -/

/-- **Coercivity.**  If `x ⬝ᵥ A *ᵥ x > 0` for every `x ≠ 0`, then there is `c > 0` with
`c * ∑ xᵢ² ≤ x ⬝ᵥ A *ᵥ x` for every `x`.  Proved by minimising the (continuous) form on the
compact unit sphere `{x | ∑ xᵢ² = 1}` and using degree-2 homogeneity. -/
theorem exists_coercive_bound (A : Matrix (Fin n) (Fin n) ℝ)
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ, c * (∑ i, (x i) ^ 2) ≤ x ⬝ᵥ A *ᵥ x := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨1, one_pos, fun x => by simp⟩
  · set S : Set (Fin n → ℝ) := {x | ∑ i, (x i) ^ 2 = 1} with hSdef
    have hcont : Continuous (fun x : Fin n → ℝ => ∑ i, (x i) ^ 2) := by fun_prop
    have hSclosed : IsClosed S := isClosed_eq hcont continuous_const
    have hSbdd : Bornology.IsBounded S := by
      refine Bornology.IsBounded.subset
        (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)) ?_
      intro x hx
      have hx' : ∑ i, (x i) ^ 2 = 1 := hx
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
        Finset.single_le_sum (f := fun j => (x j) ^ 2) (fun j _ => sq_nonneg (x j))
          (Finset.mem_univ i)
      rw [hx'] at h1
      simpa [Real.norm_eq_abs] using (sq_le_one_iff_abs_le_one (x i)).mp h1
    have hScpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSclosed hSbdd
    have hSne : S.Nonempty := by
      refine ⟨(fun i => if i = (⟨0, hn⟩ : Fin n) then (1 : ℝ) else 0), ?_⟩
      change ∑ i, (if i = (⟨0, hn⟩ : Fin n) then (1 : ℝ) else 0) ^ 2 = 1
      rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
      · simp
      · intro b _ hb; simp [hb]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    obtain ⟨x₀, hx₀S, hmin⟩ :=
      hScpt.exists_isMinOn hSne (qform_continuous A).continuousOn
    have hx₀ne : x₀ ≠ 0 := by
      intro h
      have : ∑ i, (x₀ i) ^ 2 = 1 := hx₀S
      rw [h] at this
      simp at this
    refine ⟨x₀ ⬝ᵥ A *ᵥ x₀, hpos x₀ hx₀ne, ?_⟩
    intro x
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · have hs : 0 < ∑ i, (x i) ^ 2 := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
        have hi' : x i ≠ 0 := hi
        have hpos_i : 0 < (x i) ^ 2 := by
          rcases lt_trichotomy (x i) 0 with h | h | h
          · nlinarith
          · exact absurd h hi'
          · nlinarith
        exact lt_of_lt_of_le hpos_i
          (Finset.single_le_sum (f := fun j => (x j) ^ 2) (fun j _ => sq_nonneg (x j))
            (Finset.mem_univ i))
      have hr : 0 < Real.sqrt (∑ i, (x i) ^ 2) := Real.sqrt_pos.mpr hs
      have hr2 : (Real.sqrt (∑ i, (x i) ^ 2)) ^ 2 = ∑ i, (x i) ^ 2 := Real.sq_sqrt hs.le
      set r := Real.sqrt (∑ i, (x i) ^ 2) with hrdef
      have hmem : (r⁻¹ • x) ∈ S := by
        change ∑ i, ((r⁻¹ • x) i) ^ 2 = 1
        simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
        rw [← hr2]
        field_simp
      have hle : (x₀ ⬝ᵥ A *ᵥ x₀) ≤ (r⁻¹ • x) ⬝ᵥ A *ᵥ (r⁻¹ • x) := hmin hmem
      rw [qform_smul] at hle
      have hkey : (x₀ ⬝ᵥ A *ᵥ x₀) ≤ (r⁻¹) ^ 2 * (x ⬝ᵥ A *ᵥ x) := hle
      have hrne : r ≠ 0 := ne_of_gt hr
      have : (x₀ ⬝ᵥ A *ᵥ x₀) * r ^ 2 ≤ (x ⬝ᵥ A *ᵥ x) := by
        have h2 : (r⁻¹) ^ 2 * (x ⬝ᵥ A *ᵥ x) * r ^ 2 = (x ⬝ᵥ A *ᵥ x) := by
          field_simp
        calc (x₀ ⬝ᵥ A *ᵥ x₀) * r ^ 2
            ≤ ((r⁻¹) ^ 2 * (x ⬝ᵥ A *ᵥ x)) * r ^ 2 := by
              exact mul_le_mul_of_nonneg_right hkey (sq_nonneg r)
          _ = (x ⬝ᵥ A *ᵥ x) := h2
      rw [hr2] at this
      linarith [this]

/-! ## §3 Integrability of `exp (-(1/2) ⟨y, A y⟩)` -/

/-- **Integrability.**  For positive definite `A`, `y ↦ exp (-(1/2) ⟨y, A y⟩)` is integrable
for the Lebesgue measure on `Fin n → ℝ`.  Dominated by the product Gaussian
`∏ i, exp (-(c/2) yᵢ²)` supplied by `exists_coercive_bound`. -/
theorem integrable_gaussian_qform (A : Matrix (Fin n) (Fin n) ℝ)
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x) :
    Integrable (fun y : Fin n → ℝ => Real.exp (-(1 / 2 : ℝ) * (y ⬝ᵥ A *ᵥ y)))
      (volume : Measure (Fin n → ℝ)) := by
  obtain ⟨c, hc, hcb⟩ := exists_coercive_bound A hpos
  have hdom : Integrable (fun y : Fin n → ℝ => ∏ i, Real.exp (-(c / 2) * (y i) ^ 2))
      (volume : Measure (Fin n → ℝ)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun _ : Fin n => fun t : ℝ => Real.exp (-(c / 2) * t ^ 2))
      (fun _ => integrable_exp_neg_mul_sq (by positivity))
  refine Integrable.mono' hdom ?_ ?_
  · have hc2 : Continuous fun y : Fin n → ℝ => -(1 / 2 : ℝ) * (y ⬝ᵥ A *ᵥ y) :=
      continuous_const.mul (qform_continuous A)
    exact (Real.continuous_exp.comp hc2).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hprod : ∏ i, Real.exp (-(c / 2) * (y i) ^ 2)
        = Real.exp (∑ i, -(c / 2) * (y i) ^ 2) := (Real.exp_sum _ _).symm
    rw [hprod]
    apply Real.exp_le_exp.mpr
    have h1 : ∑ i, -(c / 2) * (y i) ^ 2 = -(c / 2) * ∑ i, (y i) ^ 2 := by
      rw [Finset.mul_sum]
    rw [h1]
    have := hcb y
    linarith

/-! ## §4 The normalization constant is strictly positive -/

theorem gaussian_norm_pos (A : Matrix (Fin n) (Fin n) ℝ)
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x) :
    0 < ∫ y : Fin n → ℝ, Real.exp (-(1 / 2 : ℝ) * (y ⬝ᵥ A *ᵥ y)) := by
  have hint := integrable_gaussian_qform A hpos
  rw [integral_pos_iff_support_of_nonneg (fun y => (Real.exp_pos _).le) hint]
  have hsupp : (Function.support
      fun y : Fin n → ℝ => Real.exp (-(1 / 2 : ℝ) * (y ⬝ᵥ A *ᵥ y))) = Set.univ := by
    ext y
    simp [Function.mem_support, Real.exp_ne_zero]
  rw [hsupp]
  exact MeasureTheory.Measure.measure_univ_pos.mpr (NeZero.ne _)

/-! ## §5 Completing the square, and the moment identity -/

/-- **Completing the square**, purely algebraic. -/
lemma complete_the_square (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (hdet : IsUnit A.det) (b y : Fin n → ℝ) :
    -(1 / 2 : ℝ) * (y ⬝ᵥ A *ᵥ y) + b ⬝ᵥ y
      = -(1 / 2 : ℝ) * ((y - A⁻¹ *ᵥ b) ⬝ᵥ A *ᵥ (y - A⁻¹ *ᵥ b))
          + (1 / 2 : ℝ) * (b ⬝ᵥ A⁻¹ *ᵥ b) := by
  set μ : Fin n → ℝ := A⁻¹ *ᵥ b with hμ
  have hAμ : A *ᵥ μ = b := by
    rw [hμ, mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, one_mulVec]
  have hexp : (y - μ) ⬝ᵥ A *ᵥ (y - μ)
      = y ⬝ᵥ A *ᵥ y - y ⬝ᵥ A *ᵥ μ - μ ⬝ᵥ A *ᵥ y + μ ⬝ᵥ A *ᵥ μ := by
    rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct]
    ring
  have h1 : y ⬝ᵥ A *ᵥ μ = b ⬝ᵥ y := by rw [hAμ, dotProduct_comm]
  have h2 : μ ⬝ᵥ A *ᵥ y = b ⬝ᵥ y := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq, hAμ]
  have h3 : μ ⬝ᵥ A *ᵥ μ = b ⬝ᵥ μ := by rw [hAμ, dotProduct_comm]
  rw [hexp, h1, h2, h3]
  ring

/-- **The Gaussian moment identity, hoisted form.**  `Z` is `J`-free.

NOTE the hypotheses: positive definiteness is NOT needed here.  The identity is a pointwise
algebraic rewrite (completing the square) followed by translation invariance of Lebesgue
measure, both of which hold for the Bochner integral whether or not the integrand is
integrable.  Positive definiteness enters ONLY through `gaussian_norm_pos`, i.e. only to
know the constant is `> 0` rather than `0`. -/
theorem gaussian_moment_identity (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (hdet : IsUnit A.det) (b : Fin n → ℝ) :
    (∫ y : Fin n → ℝ, Real.exp (-(1 / 2 : ℝ) * (y ⬝ᵥ A *ᵥ y) + b ⬝ᵥ y))
      = (∫ y : Fin n → ℝ, Real.exp (-(1 / 2 : ℝ) * (y ⬝ᵥ A *ᵥ y)))
          * Real.exp ((1 / 2 : ℝ) * (b ⬝ᵥ A⁻¹ *ᵥ b)) := by
  have hcongr : ∀ y : Fin n → ℝ,
      Real.exp (-(1 / 2 : ℝ) * (y ⬝ᵥ A *ᵥ y) + b ⬝ᵥ y)
        = Real.exp (-(1 / 2 : ℝ) * ((y - A⁻¹ *ᵥ b) ⬝ᵥ A *ᵥ (y - A⁻¹ *ᵥ b)))
            * Real.exp ((1 / 2 : ℝ) * (b ⬝ᵥ A⁻¹ *ᵥ b)) := by
    intro y
    rw [← Real.exp_add, complete_the_square A hA hdet b y]
  simp_rw [hcongr]
  rw [integral_mul_const]
  congr 1
  exact integral_sub_right_eq_self
    (fun y : Fin n → ℝ => Real.exp (-(1 / 2 : ℝ) * (y ⬝ᵥ A *ᵥ y))) (A⁻¹ *ᵥ b)

/-! ## §6 Invertibility of a positive definite symmetric matrix -/

theorem isUnit_det_of_pos (A : Matrix (Fin n) (Fin n) ℝ)
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x) : IsUnit A.det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := A)).mpr hdet
  have := hpos v hv0
  rw [hv] at this
  simp at this

/-! ## §7 The bridge: Theorem L8 clause (i) in the hoisted form -/

/-- **Theorem L8 clause (i)**, hoisted form: `∃ Z' > 0` chosen BEFORE `J`.
`Z'` is the `J = 0` integral itself. -/
theorem l8_clauseI :
    ∀ (m n : ℕ) (C : Matrix (Fin m) (Fin n) ℝ) (Δ : Matrix (Fin m) (Fin m) ℝ),
      Δ.IsSymm → Function.Injective C.mulVec →
      (∀ y : Fin m → ℝ, y ∈ Set.range C.mulVec → y ≠ 0 → 0 < y ⬝ᵥ Δ.mulVec y) →
      ∃ Z' : ℝ, 0 < Z' ∧ ∀ J : Fin m → ℝ,
        (∫ (y : Fin n → ℝ),
            Real.exp (-(1 / 2 : ℝ) * (C.mulVec y ⬝ᵥ Δ.mulVec (C.mulVec y)) + (J ⬝ᵥ C.mulVec y)))
          = Z' * Real.exp ((1 / 2 : ℝ) * (J ⬝ᵥ (Migration.L8Theorem.schurCov C Δ).mulVec J)) := by
  intro m n C Δ hsymm hinj hpd
  -- the reduced form `A = CᵀΔC` on the `C`-coordinates
  set A : Matrix (Fin n) (Fin n) ℝ := Cᵀ * Δ * C with hAdef
  -- `A` is symmetric
  have hAsymm : A.IsSymm := by
    unfold Matrix.IsSymm
    rw [hAdef, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsymm.eq]
    rw [Matrix.mul_assoc]
  -- the quadratic form pulls back
  have hpull : ∀ y : Fin n → ℝ, y ⬝ᵥ A *ᵥ y = (C *ᵥ y) ⬝ᵥ Δ *ᵥ (C *ᵥ y) := by
    intro y
    rw [hAdef, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  -- `A` is positive definite
  have hApos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x := by
    intro x hx
    rw [hpull]
    refine hpd (C *ᵥ x) ⟨x, rfl⟩ ?_
    intro hCx
    exact hx (hinj (by rw [hCx, Matrix.mulVec_zero]))
  have hdet : IsUnit A.det := isUnit_det_of_pos A hApos
  refine ⟨∫ y : Fin n → ℝ, Real.exp (-(1 / 2 : ℝ) * (y ⬝ᵥ A *ᵥ y)),
    gaussian_norm_pos A hApos, ?_⟩
  intro J
  -- the linear term pulls back
  have hlin : ∀ y : Fin n → ℝ, J ⬝ᵥ (C *ᵥ y) = (Cᵀ *ᵥ J) ⬝ᵥ y := by
    intro y
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have hLHS : (∫ (y : Fin n → ℝ),
      Real.exp (-(1 / 2 : ℝ) * (C.mulVec y ⬝ᵥ Δ.mulVec (C.mulVec y)) + (J ⬝ᵥ C.mulVec y)))
      = ∫ (y : Fin n → ℝ),
          Real.exp (-(1 / 2 : ℝ) * (y ⬝ᵥ A *ᵥ y) + ((Cᵀ *ᵥ J) ⬝ᵥ y)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only [hpull, hlin]
  -- the covariance pulls back: `J ⬝ᵥ (C A⁻¹ Cᵀ) J = (CᵀJ) ⬝ᵥ A⁻¹ (CᵀJ)`
  have hcov : J ⬝ᵥ (Migration.L8Theorem.schurCov C Δ) *ᵥ J
      = (Cᵀ *ᵥ J) ⬝ᵥ A⁻¹ *ᵥ (Cᵀ *ᵥ J) := by
    rw [Migration.L8Theorem.schurCov, ← hAdef, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hlin]
  rw [hLHS, gaussian_moment_identity A hAsymm hdet (Cᵀ *ᵥ J), hcov]

#print axioms exists_coercive_bound
#print axioms integrable_gaussian_qform
#print axioms gaussian_norm_pos
#print axioms gaussian_moment_identity
#print axioms l8_clauseI

end AdalyFormal.Migration.L8Gaussian
