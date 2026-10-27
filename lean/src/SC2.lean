import Mathlib

/-!
# SC2 -- pure real-number lemmas of the scaled-coercivity proof (no repo types).
 * `elem_combine`: from `F = N - T`, `N ≥ λN X`, `F ≥ μ0 T`  to  `(1+μ0) F ≥ μ0 λN X`.
 * `margin_quad`  : from `q ≥ α s - β r`, `0 ≤ q`:  `(1+β²)(r²+q²) ≥ α² s²`.
 * `Ncomp`        : per-component lower bound of `E + κ q²` from a gap `G y² ≤ E` and `q ≥ q0 x - A y`.
 * `S2comp`       : per-component upper bound of `q²` from `q ≤ A (x+y)` and `λ0 x² + G y² ≤ E`.
Standard axioms only.
-/
set_option autoImplicit false
namespace AdalyFormal.ScaledCoercivity

theorem elem_combine {F N T X lN μ0 : ℝ} (hF : F = N - T) (hN : lN * X ≤ N) (hμ : μ0 * T ≤ F)
    (hμ0 : 0 ≤ μ0) : μ0 * lN * X ≤ (1 + μ0) * F := by
  have h1 : lN * X ≤ F + T := by linarith
  have h2 : μ0 * (lN * X) ≤ μ0 * (F + T) := mul_le_mul_of_nonneg_left h1 hμ0
  nlinarith [h2, hμ]

theorem margin_quad {α β r s q : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hβ : 0 ≤ β) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (h : α * s - β * r ≤ q) : α ^ 2 * s ^ 2 ≤ (1 + β ^ 2) * (r ^ 2 + q ^ 2) := by
  have h1 : α * s ≤ β * r + q := by linarith
  have h2 : 0 ≤ α * s := mul_nonneg hα hs
  have h3 : (α * s) ^ 2 ≤ (β * r + q) ^ 2 := by
    apply sq_le_sq'
    · linarith
    · exact h1
  nlinarith [sq_nonneg (r - β * q), h3]

theorem Ncomp {E x y q G K A q0 : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hq : 0 ≤ q) (hG : 0 < G) (hK : 0 ≤ K)
    (hA : 0 < A) (hq0 : 0 ≤ q0) (hE : G * y ^ 2 ≤ E) (hqq : q0 * x - A * y ≤ q) :
    min (K * q0 ^ 2 / 4) (G * q0 ^ 2 / (4 * A ^ 2 + q0 ^ 2)) * (x ^ 2 + y ^ 2) ≤ E + K * q ^ 2 := by
  have hD : 0 < 4 * A ^ 2 + q0 ^ 2 := by positivity
  set m := min (K * q0 ^ 2 / 4) (G * q0 ^ 2 / (4 * A ^ 2 + q0 ^ 2)) with hm
  have hm1 : m ≤ K * q0 ^ 2 / 4 := min_le_left _ _
  have hm2 : m ≤ G * q0 ^ 2 / (4 * A ^ 2 + q0 ^ 2) := min_le_right _ _
  have hm3 : 0 ≤ m := le_min (by positivity) (by positivity)
  by_cases hc : q0 * x ≤ 2 * A * y
  · -- y large:  G y² ≥ G q0²/(4A²+q0²) (x²+y²)
    have h1 : q0 ^ 2 * x ^ 2 ≤ 4 * A ^ 2 * y ^ 2 := by
      have h0 : 0 ≤ q0 * x := mul_nonneg hq0 hx
      nlinarith [hc, h0]
    have h2 : G * q0 ^ 2 / (4 * A ^ 2 + q0 ^ 2) * (x ^ 2 + y ^ 2) ≤ G * y ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hD]
      have : G * q0 ^ 2 * (x ^ 2 + y ^ 2) ≤ G * y ^ 2 * (4 * A ^ 2 + q0 ^ 2) := by
        have := mul_le_mul_of_nonneg_left h1 hG.le
        nlinarith [this]
      exact this
    have h3 : m * (x ^ 2 + y ^ 2) ≤ G * q0 ^ 2 / (4 * A ^ 2 + q0 ^ 2) * (x ^ 2 + y ^ 2) :=
      mul_le_mul_of_nonneg_right hm2 (by positivity)
    have h4 : 0 ≤ K * q ^ 2 := by positivity
    linarith
  · push_neg at hc
    have h1 : q0 * x / 2 ≤ q := by nlinarith [hqq]
    have h2 : (q0 * x / 2) ^ 2 ≤ q ^ 2 := by
      apply sq_le_sq'
      · have : 0 ≤ q0 * x / 2 := by positivity
        linarith
      · exact h1
    have h3 : K * q0 ^ 2 / 4 * x ^ 2 ≤ K * q ^ 2 := by
      have := mul_le_mul_of_nonneg_left h2 hK
      nlinarith [this]
    have h5 : m * x ^ 2 ≤ K * q0 ^ 2 / 4 * x ^ 2 := mul_le_mul_of_nonneg_right hm1 (by positivity)
    have h6 : m * y ^ 2 ≤ G * y ^ 2 := by
      have : m ≤ G := by
        have hq2 : q0 ^ 2 / (4 * A ^ 2 + q0 ^ 2) ≤ 1 := by
          rw [div_le_one hD]; nlinarith [sq_nonneg A]
        calc m ≤ G * q0 ^ 2 / (4 * A ^ 2 + q0 ^ 2) := hm2
          _ = G * (q0 ^ 2 / (4 * A ^ 2 + q0 ^ 2)) := by ring
          _ ≤ G * 1 := mul_le_mul_of_nonneg_left hq2 hG.le
          _ = G := mul_one G
      exact mul_le_mul_of_nonneg_right this (by positivity)
    nlinarith [h3, h5, h6, hE]

theorem S2comp {E x y q G l0 A : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hq : 0 ≤ q) (hG : 0 < G) (hl0 : 0 < l0)
    (hA : 0 ≤ A) (hE : l0 * x ^ 2 + G * y ^ 2 ≤ E) (hqq : q ≤ A * (x + y)) :
    q ^ 2 ≤ A ^ 2 * (1 / l0 + 1 / G) * E := by
  have h1 : q ^ 2 ≤ (A * (x + y)) ^ 2 := by
    apply sq_le_sq'
    · have : 0 ≤ A * (x + y) := by positivity
      linarith
    · exact hqq
  have h2 : (x + y) ^ 2 ≤ (1 / l0 + 1 / G) * (l0 * x ^ 2 + G * y ^ 2) := by
    have hlG : 0 < l0 * G := mul_pos hl0 hG
    have key : (x + y) ^ 2 * (l0 * G) ≤ (G + l0) * (l0 * x ^ 2 + G * y ^ 2) := by
      nlinarith [sq_nonneg (l0 * x - G * y)]
    have e : (1 / l0 + 1 / G) = (G + l0) / (l0 * G) := by field_simp
    rw [e, div_mul_eq_mul_div, le_div_iff₀ hlG]
    exact key
  have h3 : (1 / l0 + 1 / G) * (l0 * x ^ 2 + G * y ^ 2) ≤ (1 / l0 + 1 / G) * E :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  calc q ^ 2 ≤ (A * (x + y)) ^ 2 := h1
    _ = A ^ 2 * (x + y) ^ 2 := by ring
    _ ≤ A ^ 2 * ((1 / l0 + 1 / G) * E) := mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
    _ = A ^ 2 * (1 / l0 + 1 / G) * E := by ring

#print axioms elem_combine
#print axioms margin_quad
#print axioms Ncomp
#print axioms S2comp

end AdalyFormal.ScaledCoercivity
