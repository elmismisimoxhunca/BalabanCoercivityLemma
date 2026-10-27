import AdalyFormal.Balaban.ClassPropagationUbar
import AdalyFormal.Balaban.LemmaAssembly
import AdalyFormal.Balaban.BlockingLinkEstimate
import AdalyFormal.Balaban.RegularUQChain

/-!
# DL54 -- the exponential of `𝔰𝔲(2)` to second order, with an explicit cubic remainder (Frobenius norm)

For `H` anti-Hermitian traceless (`AHT H`), `F = frobNorm H ≤ 1`:
* **`exp_expand`** : `frobNorm (exp H − 1 − H − ½H²) ≤ F³/4`  (closed form `exp H = cos r·1 + (sin r/r)H`, `r = F/√2`, and
  Mathlib's `Real.cos_bound`, `Real.sin_bound`);
* `exp_sub_one_le` : `frobNorm (exp H − 1) ≤ 2F`;  `exp_conjT` : `(exp H)ᴴ = exp(−H)`;  `exp_unitary` : `exp H (exp H)ᴴ = 1`.
Small Frobenius toolkit: `fN_add`, `fN_sub`, `fN_neg`, `fN_csmul`, `fN_rsmul`, `fN_conjT`, `fN_one`, `fN_mul_unitary`, `fN_trace`,
`fN_piProj` (`‖π X‖ ≤ 2‖X‖`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

/-! ## Frobenius toolkit -/

theorem fN_mul (A B : Mt) : frobNorm (A * B) ≤ frobNorm A * frobNorm B :=
  AdalyFormal.Balaban.LemmaAssembly.frobNorm_mul_le A B

theorem fN_add (A B : Mt) : frobNorm (A + B) ≤ frobNorm A + frobNorm B :=
  AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_add_le A B

theorem frobSq_csmul (z : ℂ) (A : Mt) : frobSq (z • A) = Complex.normSq z * frobSq A := by
  unfold frobSq
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul]
  ring

theorem fN_csmul (z : ℂ) (A : Mt) : frobNorm (z • A) = ‖z‖ * frobNorm A := by
  unfold frobNorm
  rw [frobSq_csmul, Real.sqrt_mul (Complex.normSq_nonneg z), Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem fN_rsmul (r : ℝ) (A : Mt) : frobNorm (r • A) = |r| * frobNorm A := by
  have : r • A = (r : ℂ) • A := by ext i j; simp
  rw [this, fN_csmul, Complex.norm_real, Real.norm_eq_abs]

theorem fN_neg (A : Mt) : frobNorm (-A) = frobNorm A := by
  have : -A = (-1 : ℂ) • A := by simp
  rw [this, fN_csmul]; simp

theorem fN_sub (A B : Mt) : frobNorm (A - B) ≤ frobNorm A + frobNorm B := by
  rw [sub_eq_add_neg]; exact (fN_add _ _).trans (by rw [fN_neg])

theorem fN_conjT (A : Mt) : frobNorm Aᴴ = frobNorm A :=
  AdalyFormal.Balaban.RegularUQChain.frobNorm_conjTranspose A

theorem fN_one : frobNorm (1 : Mt) = Real.sqrt 2 := by
  unfold frobNorm frobSq
  congr 1
  simp [Matrix.one_apply]
  norm_num

theorem fN_mul_unitary (M W : Mt) (hW : W * Wᴴ = 1) : frobNorm (M * W) = frobNorm M := by
  unfold frobNorm
  rw [AdalyFormal.Balaban.RMapLipschitz.frobSq_mul_right_isometry M W hW]

theorem fN_zero : frobNorm (0 : Mt) = 0 := by unfold frobNorm frobSq; simp

theorem fN_trace (A : Mt) : ‖Matrix.trace A‖ ≤ Real.sqrt 2 * frobNorm A := by
  have h2 : ‖Matrix.trace A‖ ^ 2 ≤ (Real.sqrt 2 * frobNorm A) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), frobNorm_sq, Matrix.trace_fin_two]
    unfold frobSq
    have h := norm_add_le (A 0 0) (A 1 1)
    have ha := Complex.normSq_eq_norm_sq (A 0 0)
    have hb := Complex.normSq_eq_norm_sq (A 1 1)
    have h3 := Complex.normSq_nonneg (A 0 1)
    have h4 := Complex.normSq_nonneg (A 1 0)
    have h5 : ‖A 0 0 + A 1 1‖ ^ 2 ≤ (‖A 0 0‖ + ‖A 1 1‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [sq_nonneg (‖A 0 0‖ - ‖A 1 1‖)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (frobNorm_nonneg _))
    two_ne_zero).mp h2

theorem fN_piProj (A : Mt) : frobNorm (AdalyFormal.Balaban.SourceJ.piProj A) ≤ 2 * frobNorm A := by
  unfold AdalyFormal.Balaban.SourceJ.piProj
  refine (fN_sub _ _).trans ?_
  rw [fN_csmul, fN_one, norm_div]
  have h1 := fN_trace A
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have : ‖Matrix.trace A‖ / 2 * Real.sqrt 2 ≤ frobNorm A := by
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    calc ‖Matrix.trace A‖ / 2 * Real.sqrt 2 ≤ (Real.sqrt 2 * frobNorm A) / 2 * Real.sqrt 2 := by
          gcongr
      _ = frobNorm A := by rw [show Real.sqrt 2 * frobNorm A / 2 * Real.sqrt 2
            = (Real.sqrt 2 * Real.sqrt 2) * frobNorm A / 2 by ring, hs]; ring
  linarith

/-! ## the exponential -/

/-- anti-Hermitian traceless -/
structure AHT (H : Mt) : Prop where
  ah : Hᴴ = -H
  tr : Matrix.trace H = 0

theorem AHT.neg {H : Mt} (h : AHT H) : AHT (-H) :=
  ⟨by rw [Matrix.conjTranspose_neg, h.ah], by rw [Matrix.trace_neg, h.tr, neg_zero]⟩

theorem fN_eq_r (H : Mt) : frobNorm H = Real.sqrt 2 * Real.sqrt (frobSq H / 2) := by
  unfold frobNorm
  rw [← Real.sqrt_mul (by norm_num)]
  congr 1; ring

/-- the closed form, total (also at `H = 0`) -/
theorem exp_form (H : Mt) (hH : AHT H) :
    NormedSpace.exp H = (Real.cos (Real.sqrt (frobSq H / 2))) • (1 : Mt)
      + (Real.sin (Real.sqrt (frobSq H / 2)) * (Real.sqrt (frobSq H / 2))⁻¹) • H := by
  rcases eq_or_lt_of_le (frobSq_nonneg H) with h0 | hpos
  · have hH0 : H = 0 := AdalyFormal.Balaban.AlphaAnalyticity.matrix_eq_zero_of_frobSq_zero h0.symm
    subst hH0
    rw [NormedSpace.exp_zero]
    simp [frobSq]
  · have hr : 0 < Real.sqrt (frobSq H / 2) := Real.sqrt_pos.mpr (by linarith)
    exact AdalyFormal.Balaban.ClassPropagationUbar.exp_closed hH.ah hH.tr hr
      (Real.sq_sqrt (by linarith))

theorem sq_AHT (H : Mt) (hH : AHT H) : H * H = (-(frobSq H / 2) : ℝ) • (1 : Mt) := by
  have h := AdalyFormal.Balaban.ClassPropagationUbar.alg_sq hH.ah hH.tr
  rw [h]; ext i j; simp

/-- **the second-order expansion with cubic remainder** -/
theorem exp_expand (H : Mt) (hH : AHT H) (h1 : frobNorm H ≤ 1) :
    frobNorm (NormedSpace.exp H - 1 - H - (1 / 2 : ℝ) • (H * H)) ≤ frobNorm H ^ 3 / 4 := by
  set r := Real.sqrt (frobSq H / 2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hF : frobNorm H = Real.sqrt 2 * r := fN_eq_r H
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr1 : r ≤ 1 := by
    have : Real.sqrt 2 * r ≤ 1 := by rw [← hF]; exact h1
    have h1s : 1 ≤ Real.sqrt 2 := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith
  have hr2 : r ^ 2 = frobSq H / 2 := Real.sq_sqrt (by have := frobSq_nonneg H; linarith)
  have hHH : H * H = (-(r ^ 2)) • (1 : Mt) := by rw [sq_AHT H hH, hr2]
  rw [exp_form H hH, ← hr, hHH]
  rcases eq_or_lt_of_le hr0 with h0 | hrpos
  · -- r = 0 ⇒ H = 0
    have hHz : frobSq H = 0 := by rw [← h0] at hr2; nlinarith
    have hH0 : H = 0 := AdalyFormal.Balaban.AlphaAnalyticity.matrix_eq_zero_of_frobSq_zero hHz
    rw [hH0, ← h0]
    simp [fN_zero]
  · have e1 : Real.cos r • (1 : Mt) + (Real.sin r * r⁻¹) • H - 1 - H - (1 / 2 : ℝ) • ((-(r ^ 2)) • (1 : Mt))
        = (Real.cos r - 1 + r ^ 2 / 2) • (1 : Mt) + (Real.sin r * r⁻¹ - 1) • H := by
      simp only [smul_smul, sub_smul, add_smul, one_smul]
      module
    rw [e1]
    refine (fN_add _ _).trans ?_
    rw [fN_rsmul, fN_rsmul, fN_one, hF]
    have hc := Real.cos_bound (x := r) (by rw [abs_of_nonneg hr0]; exact hr1)
    have hsn := Real.sin_bound (x := r) (by rw [abs_of_nonneg hr0]; exact hr1)
    rw [abs_of_nonneg hr0] at hc hsn
    have hc' : |Real.cos r - 1 + r ^ 2 / 2| ≤ r ^ 4 * (5 / 96) := by
      rw [show Real.cos r - 1 + r ^ 2 / 2 = Real.cos r - (1 - r ^ 2 / 2) by ring]; exact hc
    have hs' : |Real.sin r * r⁻¹ - 1| ≤ r ^ 2 / 6 + r ^ 3 * (5 / 96) := by
      have e2 : Real.sin r * r⁻¹ - 1 = (Real.sin r - (r - r ^ 3 / 6)) / r - r ^ 2 / 6 := by
        field_simp; ring
      rw [e2]
      refine (abs_sub _ _).trans ?_
      rw [abs_div, abs_of_pos hrpos, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 2 / 6)]
      have : |Real.sin r - (r - r ^ 3 / 6)| / r ≤ r ^ 3 * (5 / 96) := by
        rw [div_le_iff₀ hrpos]; nlinarith
      linarith
    have hgoal : |Real.cos r - 1 + r ^ 2 / 2| * Real.sqrt 2 + |Real.sin r * r⁻¹ - 1| * (Real.sqrt 2 * r)
        ≤ (Real.sqrt 2 * r) ^ 3 / 4 := by
      have hA : |Real.cos r - 1 + r ^ 2 / 2| * Real.sqrt 2 ≤ r ^ 4 * (5 / 96) * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_right hc' hs2.le
      have hB : |Real.sin r * r⁻¹ - 1| * (Real.sqrt 2 * r) ≤ (r ^ 2 / 6 + r ^ 3 * (5 / 96)) * (Real.sqrt 2 * r) :=
        mul_le_mul_of_nonneg_right hs' (by positivity)
      have hC : r ^ 4 * (5 / 96) * Real.sqrt 2 + (r ^ 2 / 6 + r ^ 3 * (5 / 96)) * (Real.sqrt 2 * r)
          ≤ (Real.sqrt 2 * r) ^ 3 / 4 := by
        have e3 : (Real.sqrt 2 * r) ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 * r ^ 3 := by ring
        rw [e3, hs2sq]
        have : r ^ 4 ≤ r ^ 3 := by nlinarith [pow_nonneg hr0 3]
        nlinarith [mul_nonneg hs2.le (pow_nonneg hr0 3), mul_nonneg hs2.le (pow_nonneg hr0 4)]
      linarith
    exact hgoal

theorem exp_sub_one_le (H : Mt) (hH : AHT H) (h1 : frobNorm H ≤ 1) :
    frobNorm (NormedSpace.exp H - 1) ≤ 2 * frobNorm H := by
  have he := exp_expand H hH h1
  have e : NormedSpace.exp H - 1 = H + (1 / 2 : ℝ) • (H * H) + (NormedSpace.exp H - 1 - H - (1 / 2 : ℝ) • (H * H)) := by
    abel
  rw [e]
  refine (fN_add _ _).trans ?_
  refine (add_le_add (fN_add _ _) he).trans ?_
  rw [fN_rsmul]
  have hm := fN_mul H H
  have hF0 := frobNorm_nonneg H
  have h3 : frobNorm H ^ 3 ≤ frobNorm H := by nlinarith
  have h2 : frobNorm H * frobNorm H ≤ frobNorm H := by nlinarith
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith

theorem exp_conjT (H : Mt) (hH : AHT H) : (NormedSpace.exp H)ᴴ = NormedSpace.exp (-H) := by
  rw [exp_form H hH, exp_form (-H) hH.neg]
  have hf : frobSq (-H) = frobSq H := by unfold frobSq; simp [Complex.normSq_neg]
  rw [hf, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    hH.ah]
  simp

theorem exp_unitary (H : Mt) (hH : AHT H) : NormedSpace.exp H * (NormedSpace.exp H)ᴴ = 1 := by
  rw [exp_conjT H hH, exp_form H hH, exp_form (-H) hH.neg]
  have hf : frobSq (-H) = frobSq H := by unfold frobSq; simp [Complex.normSq_neg]
  rw [hf]
  set r := Real.sqrt (frobSq H / 2) with hr
  set s := Real.sin r * r⁻¹ with hs
  have hHH := sq_AHT H hH
  have e : (Real.cos r • (1 : Mt) + s • H) * (Real.cos r • (1 : Mt) + s • -H)
      = (Real.cos r ^ 2) • (1 : Mt) - (s ^ 2) • (H * H) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      smul_neg, Matrix.mul_neg, smul_smul]
    module
  rw [e, hHH, smul_smul, ← sub_smul]
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (frobSq H / 2)) with h0 | hpos
  · rw [← hr] at h0
    have hz : frobSq H = 0 := by
      have h2 : r ^ 2 = frobSq H / 2 := Real.sq_sqrt (by have := frobSq_nonneg H; linarith)
      rw [← h0] at h2; nlinarith
    rw [← h0]; simp [hz]
  · rw [← hr] at hpos
    have h2 : r ^ 2 = frobSq H / 2 := Real.sq_sqrt (by have := frobSq_nonneg H; linarith)
    have : Real.cos r ^ 2 - s ^ 2 * -(frobSq H / 2) = 1 := by
      rw [hs, ← h2]
      field_simp
      nlinarith [Real.sin_sq_add_cos_sq r]
    rw [this, one_smul]

#print axioms fN_csmul
#print axioms fN_piProj
#print axioms fN_trace
#print axioms exp_form
#print axioms exp_expand
#print axioms exp_sub_one_le
#print axioms exp_conjT
#print axioms exp_unitary

end AdalyFormal.DLayer
