import AdalyFormal.Balaban.Bch2

/-!
# GG1 -- group-level gluing algebra for SU(2) charts (m2_glue2, 2026-10-15)

Pure matrix algebra on `M2 = Matrix (Fin 2) (Fin 2) ℂ` with the Frobenius norm `frobNorm`.
* unitary invariance and submultiplicativity of `frobNorm`;
* `gauge_step_one`, `gauge_step_two`: a gauge transformation `G ↦ k₀ G k₁⁻¹` moves `|G − 1|` and the
  bond-to-bond difference `|G' − G|` by first and SECOND differences of `k` only (no BCH expansion);
* `resolvent_second_diff`: second differences of `X ↦ F(X)` for any family with the resolvent identity
  `F i − F j = F i (X j − X i) F j`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2Glue2

open Matrix
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log coe_mul coe_inv coe_one)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq frobSq_nonneg frobSq_mul_le
  frobSq_mul_right_isometry)
open AdalyFormal.Balaban.Bch2 (frobNorm_add_le frobNorm_nonneg)
open AdalyFormal.Balaban.RegularityGap (frobNorm_neg)
open scoped Matrix

/-! ## §1 Frobenius norm facts -/

theorem frobSq_conjTranspose (A : M2) : frobSq Aᴴ = frobSq A := by
  unfold frobSq
  have hs : ∀ z : ℂ, Complex.normSq (star z) = Complex.normSq z := fun z => Complex.normSq_conj z
  simp only [Matrix.conjTranspose_apply, hs]
  ring

theorem frobNorm_conjTranspose (A : M2) : frobNorm Aᴴ = frobNorm A := by
  unfold frobNorm; rw [frobSq_conjTranspose]

theorem frobNorm_mul_le (A B : M2) : frobNorm (A * B) ≤ frobNorm A * frobNorm B := by
  unfold frobNorm
  rw [← Real.sqrt_mul (frobSq_nonneg A)]
  exact Real.sqrt_le_sqrt (frobSq_mul_le A B)

theorem su2_mul_star (g : SU2) : (g : M2) * (g : M2)ᴴ = 1 :=
  AdalyFormal.Balaban.SuTwoLogExp.mul_star_self g

theorem su2_star_mul (g : SU2) : (g : M2)ᴴ * (g : M2) = 1 :=
  AdalyFormal.Balaban.SuTwoLogExp.star_mul_self g

theorem frobNorm_mul_su2 (A : M2) (g : SU2) : frobNorm (A * (g : M2)) = frobNorm A := by
  unfold frobNorm; rw [frobSq_mul_right_isometry A g (su2_mul_star g)]

theorem frobNorm_mul_su2_star (A : M2) (g : SU2) : frobNorm (A * (g : M2)ᴴ) = frobNorm A := by
  unfold frobNorm
  have h : (g : M2)ᴴ * ((g : M2)ᴴ)ᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact su2_star_mul g
  rw [frobSq_mul_right_isometry A _ h]

theorem frobNorm_su2_mul (g : SU2) (A : M2) : frobNorm ((g : M2) * A) = frobNorm A := by
  rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, frobNorm_mul_su2_star, frobNorm_conjTranspose]

theorem frobNorm_su2_mul_star (g : SU2) (A : M2) : frobNorm ((g : M2)ᴴ * A) = frobNorm A := by
  rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    frobNorm_mul_su2, frobNorm_conjTranspose]

theorem frobNorm_sub_comm (A B : M2) : frobNorm (A - B) = frobNorm (B - A) := by
  rw [← neg_sub, frobNorm_neg]

theorem frobNorm_sub_le' (A B C : M2) : frobNorm (A - C) ≤ frobNorm (A - B) + frobNorm (B - C) := by
  have := frobNorm_add_le (A - B) (B - C)
  rwa [show A - B + (B - C) = A - C by abel] at this

theorem frobNorm_add3_le (A B C : M2) : frobNorm (A + B + C) ≤ frobNorm A + frobNorm B + frobNorm C :=
  (frobNorm_add_le _ _).trans (by linarith [frobNorm_add_le A B])

theorem frobNorm_add4_le (A B C D : M2) :
    frobNorm (A + B + C + D) ≤ frobNorm A + frobNorm B + frobNorm C + frobNorm D :=
  (frobNorm_add_le _ _).trans (by linarith [frobNorm_add3_le A B C])

theorem frobNorm_add5_le (A B C D E : M2) :
    frobNorm (A + B + C + D + E) ≤ frobNorm A + frobNorm B + frobNorm C + frobNorm D + frobNorm E :=
  (frobNorm_add_le _ _).trans (by linarith [frobNorm_add4_le A B C D])

theorem frobNorm_mul3_le (A B C : M2) : frobNorm (A * B * C) ≤ frobNorm A * frobNorm B * frobNorm C := by
  calc frobNorm (A * B * C) ≤ frobNorm (A * B) * frobNorm C := frobNorm_mul_le _ _
    _ ≤ frobNorm A * frobNorm B * frobNorm C :=
        mul_le_mul_of_nonneg_right (frobNorm_mul_le _ _) (frobNorm_nonneg _)

/-! ## §2 The gauge step (group level) -/

/-- `|k₀ G k₁⁻¹ − 1| ≤ |G − 1| + |k₁ − k₀|`. -/
theorem gauge_step_one (k0 k1 G : SU2) :
    frobNorm (((k0 * G * k1⁻¹ : SU2) : M2) - 1)
      ≤ frobNorm ((G : M2) - 1) + frobNorm ((k1 : M2) - (k0 : M2)) := by
  rw [coe_mul, coe_mul, coe_inv]
  have h1 := su2_mul_star k1
  have hid : (k0 : M2) * (G : M2) * (k1 : M2)ᴴ - 1
      = (k0 : M2) * ((G : M2) - 1) * (k1 : M2)ᴴ + ((k0 : M2) - (k1 : M2)) * (k1 : M2)ᴴ := by
    have e : (k0 : M2) * ((G : M2) - 1) * (k1 : M2)ᴴ + ((k0 : M2) - (k1 : M2)) * (k1 : M2)ᴴ
        = (k0 : M2) * (G : M2) * (k1 : M2)ᴴ - (k1 : M2) * (k1 : M2)ᴴ := by noncomm_ring
    rw [e, h1]
  rw [hid]
  refine (frobNorm_add_le _ _).trans ?_
  rw [frobNorm_mul_su2_star, frobNorm_su2_mul, frobNorm_mul_su2_star, frobNorm_sub_comm (k0 : M2) (k1 : M2)]

/-- **second-order gauge step.** `T = k₀ G k₁⁻¹` (bond `(x,ν)`), `T' = k₂ G' k₃⁻¹` (bond `(x+μ,ν)`). -/
theorem gauge_step_two (k0 k1 k2 k3 G G' : SU2) :
    frobNorm (((k2 * G' * k3⁻¹ : SU2) : M2) - ((k0 * G * k1⁻¹ : SU2) : M2))
      ≤ frobNorm ((G' : M2) - (G : M2))
        + frobNorm ((G : M2) - 1) * (frobNorm ((k2 : M2) - k0) + frobNorm ((k3 : M2) - k1))
        + frobNorm ((k2 : M2) - k0) * frobNorm ((k3 : M2) - k2)
        + frobNorm ((k3 : M2) - k2 - ((k1 : M2) - k0)) := by
  simp only [coe_mul, coe_inv]
  have h0 := su2_mul_star k0
  have h2 := su2_mul_star k2
  set K0 : M2 := (k0 : M2) with hK0
  set K1 : M2 := (k1 : M2) with hK1
  set K2 : M2 := (k2 : M2) with hK2
  set K3 : M2 := (k3 : M2) with hK3
  set g : M2 := (G : M2) with hg
  set g' : M2 := (G' : M2) with hg'
  have hid : K2 * g' * K3ᴴ - K0 * g * K1ᴴ
      = (K2 - K0) * (K3 - K2)ᴴ + K0 * (K3 - K2 - (K1 - K0))ᴴ + K2 * (g' - g) * K3ᴴ
        + (K2 - K0) * (g - 1) * K3ᴴ + K0 * ((g - 1) * (K3 - K1)ᴴ) := by
    have e : (K2 - K0) * (K3 - K2)ᴴ + K0 * (K3 - K2 - (K1 - K0))ᴴ + K2 * (g' - g) * K3ᴴ
        + (K2 - K0) * (g - 1) * K3ᴴ + K0 * ((g - 1) * (K3 - K1)ᴴ)
        = K2 * g' * K3ᴴ - K0 * g * K1ᴴ - K2 * K2ᴴ + K0 * K0ᴴ := by
      simp only [Matrix.conjTranspose_sub]
      noncomm_ring
    rw [e, h0, h2]; abel
  rw [hid]
  refine (frobNorm_add5_le _ _ _ _ _).trans ?_
  have t1 : frobNorm ((K2 - K0) * (K3 - K2)ᴴ) ≤ frobNorm (K2 - K0) * frobNorm (K3 - K2) := by
    have := frobNorm_mul_le (K2 - K0) (K3 - K2)ᴴ; rwa [frobNorm_conjTranspose] at this
  have t2 : frobNorm (K0 * (K3 - K2 - (K1 - K0))ᴴ) = frobNorm (K3 - K2 - (K1 - K0)) := by
    rw [hK0, frobNorm_su2_mul, frobNorm_conjTranspose]
  have t3 : frobNorm (K2 * (g' - g) * K3ᴴ) = frobNorm (g' - g) := by
    rw [hK3, hK2, frobNorm_mul_su2_star, frobNorm_su2_mul]
  have t4 : frobNorm ((K2 - K0) * (g - 1) * K3ᴴ) ≤ frobNorm (g - 1) * frobNorm (K2 - K0) := by
    rw [hK3, frobNorm_mul_su2_star]
    have := frobNorm_mul_le (K2 - K0) (g - 1); linarith
  have t5 : frobNorm (K0 * ((g - 1) * (K3 - K1)ᴴ)) ≤ frobNorm (g - 1) * frobNorm (K3 - K1) := by
    rw [hK0, frobNorm_su2_mul]
    have := frobNorm_mul_le (g - 1) (K3 - K1)ᴴ; rwa [frobNorm_conjTranspose] at this
  nlinarith [t1, t2, t3, t4, t5]

/-! ## §3 Resolvent-type second differences -/

/-- If `F i − F j = F i (X j − X i) F j` for the four indices used, and `|F i| ≤ B`, then second differences of
`F` are controlled by second differences of `X` plus products of first differences. -/
theorem resolvent_second_diff (F X : Fin 4 → M2)
    (hF : ∀ i j : Fin 4, F i - F j = F i * (X j - X i) * F j) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i, frobNorm (F i) ≤ B) :
    frobNorm (F 3 - F 2 - (F 1 - F 0))
      ≤ B ^ 2 * frobNorm (X 3 - X 2 - (X 1 - X 0))
        + B ^ 3 * (frobNorm (X 3 - X 1) + frobNorm (X 2 - X 0)) * frobNorm (X 1 - X 0) := by
  have hid : F 3 - F 2 - (F 1 - F 0)
      = F 3 * (-(X 3 - X 2 - (X 1 - X 0))) * F 2 + (F 3 - F 1) * (X 0 - X 1) * F 2
        + F 1 * (X 0 - X 1) * (F 2 - F 0) := by
    rw [hF 3 2, hF 1 0]
    noncomm_ring
  rw [hid]
  refine (frobNorm_add3_le _ _ _).trans ?_
  have n1 : frobNorm (F 3 * (-(X 3 - X 2 - (X 1 - X 0))) * F 2)
      ≤ B ^ 2 * frobNorm (X 3 - X 2 - (X 1 - X 0)) := by
    refine (frobNorm_mul3_le _ _ _).trans ?_
    have : frobNorm (-(X 3 - X 2 - (X 1 - X 0))) = frobNorm (X 3 - X 2 - (X 1 - X 0)) :=
      frobNorm_neg _
    rw [this]
    have a := hB 3; have b := hB 2
    have c := frobNorm_nonneg (X 3 - X 2 - (X 1 - X 0))
    have := frobNorm_nonneg (F 3); have := frobNorm_nonneg (F 2)
    nlinarith [mul_le_mul a b (frobNorm_nonneg _) hB0]
  have d31 : frobNorm (F 3 - F 1) ≤ B ^ 2 * frobNorm (X 3 - X 1) := by
    rw [hF 3 1]
    refine (frobNorm_mul3_le _ _ _).trans ?_
    rw [frobNorm_sub_comm (X 1) (X 3)]
    have a := hB 3; have b := hB 1
    have := frobNorm_nonneg (F 3); have := frobNorm_nonneg (F 1)
    have c := frobNorm_nonneg (X 3 - X 1)
    nlinarith [mul_le_mul a b (frobNorm_nonneg _) hB0]
  have d20 : frobNorm (F 2 - F 0) ≤ B ^ 2 * frobNorm (X 2 - X 0) := by
    rw [hF 2 0]
    refine (frobNorm_mul3_le _ _ _).trans ?_
    rw [frobNorm_sub_comm (X 0) (X 2)]
    have a := hB 2; have b := hB 0
    have := frobNorm_nonneg (F 2); have := frobNorm_nonneg (F 0)
    have c := frobNorm_nonneg (X 2 - X 0)
    nlinarith [mul_le_mul a b (frobNorm_nonneg _) hB0]
  have x01 : frobNorm (X 0 - X 1) = frobNorm (X 1 - X 0) := frobNorm_sub_comm _ _
  have n2 : frobNorm ((F 3 - F 1) * (X 0 - X 1) * F 2)
      ≤ B ^ 3 * frobNorm (X 3 - X 1) * frobNorm (X 1 - X 0) := by
    refine (frobNorm_mul3_le _ _ _).trans ?_
    rw [x01]
    have b := hB 2
    have := frobNorm_nonneg (F 2); have := frobNorm_nonneg (X 1 - X 0)
    have := frobNorm_nonneg (F 3 - F 1); have := frobNorm_nonneg (X 3 - X 1)
    calc frobNorm (F 3 - F 1) * frobNorm (X 1 - X 0) * frobNorm (F 2)
        ≤ (B ^ 2 * frobNorm (X 3 - X 1)) * frobNorm (X 1 - X 0) * B := by gcongr
      _ = B ^ 3 * frobNorm (X 3 - X 1) * frobNorm (X 1 - X 0) := by ring
  have n3 : frobNorm (F 1 * (X 0 - X 1) * (F 2 - F 0))
      ≤ B ^ 3 * frobNorm (X 2 - X 0) * frobNorm (X 1 - X 0) := by
    refine (frobNorm_mul3_le _ _ _).trans ?_
    rw [x01]
    have b := hB 1
    have := frobNorm_nonneg (F 1); have := frobNorm_nonneg (X 1 - X 0)
    have := frobNorm_nonneg (F 2 - F 0); have := frobNorm_nonneg (X 2 - X 0)
    calc frobNorm (F 1) * frobNorm (X 1 - X 0) * frobNorm (F 2 - F 0)
        ≤ B * frobNorm (X 1 - X 0) * (B ^ 2 * frobNorm (X 2 - X 0)) := by gcongr
      _ = B ^ 3 * frobNorm (X 2 - X 0) * frobNorm (X 1 - X 0) := by ring
  nlinarith [n1, n2, n3]

end AdalyFormal.M2Glue2
