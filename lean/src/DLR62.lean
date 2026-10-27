import DLR61
import DLR54

/-!
# DL62 -- second-order ("even part") rules for `exp` and its inverse, in the Frobenius norm `frobNorm`

`ℓ^∞`-operator norm ↔ Frobenius: `‖X‖_∞ ≤ √2 frobNorm X`, `frobNorm X ≤ √2 ‖X‖_∞` (`linfty_le_frob`, `frob_le_linfty`).
For `X0` and nearby `X, Y` (`frobNorm (X−X0), frobNorm (Y−X0) ≤ 1/2`), with `x0 = frobNorm X0`, `E = e^{√2 x0}`:
* **`even_exp`** : `‖e^X + e^Y − 2e^{X0}‖ ≤ 2E ‖X + Y − 2X0‖ + 2√2 E (‖X−X0‖² + ‖Y−X0‖²)`;
* **`even_exp_inv`** (`2(E − 1) ≤ 1/2`) : `‖X + Y − 2X0‖ ≤ 2 (‖e^X + e^Y − 2e^{X0}‖ + 2√2 E (‖X−X0‖² + ‖Y−X0‖²))`
  — the second-order bound for the LOGARITHM at a non-identity point, obtained by inverting `exp` (no derivative of `log`);
* `lip_exp` : `‖e^X − e^{X0}‖ ≤ 2E‖X−X0‖ + 2√2E‖X−X0‖²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq)
open AdalyFormal.DLayer.ExpC11 (expL expL_add expL_smul exp_second_order expL_le expL_sub_le)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem row_le_linfty (X : Mt) (i : Fin 2) : ‖X i 0‖ + ‖X i 1‖ ≤ ‖X‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h : (∑ j, ‖X i j‖₊) ≤ Finset.univ.sup (fun i => ∑ j, ‖X i j‖₊) :=
    Finset.le_sup (f := fun i => ∑ j, ‖X i j‖₊) (Finset.mem_univ i)
  have h2 : ((∑ j, ‖X i j‖₊ : NNReal) : ℝ) = ‖X i 0‖ + ‖X i 1‖ := by
    rw [NNReal.coe_sum, Fin.sum_univ_two]; rfl
  rw [← h2]; exact_mod_cast h

theorem linfty_le_of_rows (X : Mt) (c : ℝ) (hc : 0 ≤ c) (h : ∀ i, ‖X i 0‖ + ‖X i 1‖ ≤ c) : ‖X‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  have : Finset.univ.sup (fun i => ∑ j, ‖X i j‖₊) ≤ ⟨c, hc⟩ := by
    refine Finset.sup_le (fun i _ => ?_)
    show (∑ j, ‖X i j‖₊ : NNReal) ≤ ⟨c, hc⟩
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, Fin.sum_univ_two]
    exact h i
  exact_mod_cast this

theorem nsq (z : ℂ) : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z

theorem linfty_le_frob (X : Mt) : ‖X‖ ≤ Real.sqrt 2 * frobNorm X := by
  refine linfty_le_of_rows X _ (mul_nonneg (Real.sqrt_nonneg _) (frobNorm_nonneg _)) (fun i => ?_)
  have hF : frobNorm X ^ 2 = ‖X 0 0‖ ^ 2 + ‖X 0 1‖ ^ 2 + ‖X 1 0‖ ^ 2 + ‖X 1 1‖ ^ 2 := by
    rw [frobNorm_sq]; unfold frobSq; simp only [nsq]
  have hrow : ‖X i 0‖ ^ 2 + ‖X i 1‖ ^ 2 ≤ frobNorm X ^ 2 := by
    rw [hF]; fin_cases i <;> simp <;> nlinarith [sq_nonneg ‖X 1 0‖, sq_nonneg ‖X 1 1‖, sq_nonneg ‖X 0 0‖, sq_nonneg ‖X 0 1‖]
  have h2 : (‖X i 0‖ + ‖X i 1‖) ^ 2 ≤ (Real.sqrt 2 * frobNorm X) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith [sq_nonneg (‖X i 0‖ - ‖X i 1‖)]
  exact (pow_le_pow_iff_left₀ (by positivity) (mul_nonneg (Real.sqrt_nonneg _) (frobNorm_nonneg _))
    two_ne_zero).mp h2

theorem frob_le_linfty (X : Mt) : frobNorm X ≤ Real.sqrt 2 * ‖X‖ := by
  have hF : frobNorm X ^ 2 = ‖X 0 0‖ ^ 2 + ‖X 0 1‖ ^ 2 + ‖X 1 0‖ ^ 2 + ‖X 1 1‖ ^ 2 := by
    rw [frobNorm_sq]; unfold frobSq; simp only [nsq]
  have r0 := row_le_linfty X 0
  have r1 := row_le_linfty X 1
  have h2 : frobNorm X ^ 2 ≤ (Real.sqrt 2 * ‖X‖) ^ 2 := by
    rw [hF, mul_pow, Real.sq_sqrt (by norm_num)]
    have n00 := norm_nonneg (X 0 0); have n01 := norm_nonneg (X 0 1)
    have n10 := norm_nonneg (X 1 0); have n11 := norm_nonneg (X 1 1)
    nlinarith [mul_nonneg n00 n01, mul_nonneg n10 n11]
  exact (pow_le_pow_iff_left₀ (frobNorm_nonneg _) (by positivity) two_ne_zero).mp h2

/-! ## the exp rules in `frobNorm` -/

theorem exp_second_order_F (A B : Mt) (hB : frobNorm B ≤ 1 / 2) :
    frobNorm (NormedSpace.exp (A + B) - NormedSpace.exp A - expL A B)
      ≤ 2 * Real.sqrt 2 * frobNorm B ^ 2 * Real.exp (Real.sqrt 2 * frobNorm A) := by
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 / 2 : ℝ) = Real.sqrt (9 / 4) by rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hB' : ‖B‖ ≤ 1 := by
    have := linfty_le_frob B
    have := frobNorm_nonneg B
    nlinarith
  have h := exp_second_order A B hB'
  have hA := linfty_le_frob A
  have hBB := linfty_le_frob B
  refine (frob_le_linfty _).trans ?_
  have hexp : Real.exp ‖A‖ ≤ Real.exp (Real.sqrt 2 * frobNorm A) := Real.exp_le_exp.mpr hA
  have hb2 : ‖B‖ ^ 2 ≤ 2 * frobNorm B ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hBB 2
    rw [mul_pow, Real.sq_sqrt (by norm_num)] at this; exact this
  have he0 := Real.exp_pos ‖A‖
  calc Real.sqrt 2 * ‖NormedSpace.exp (A + B) - NormedSpace.exp A - expL A B‖
      ≤ Real.sqrt 2 * (‖B‖ ^ 2 * Real.exp ‖A‖) := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt 2 * ((2 * frobNorm B ^ 2) * Real.exp (Real.sqrt 2 * frobNorm A)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact mul_le_mul hb2 hexp he0.le (by positivity)
    _ = 2 * Real.sqrt 2 * frobNorm B ^ 2 * Real.exp (Real.sqrt 2 * frobNorm A) := by ring

theorem expL_sub_le_F (A B : Mt) :
    frobNorm (expL A B - B) ≤ 2 * (Real.exp (Real.sqrt 2 * frobNorm A) - 1) * frobNorm B := by
  have h := expL_sub_le A B
  have hA := linfty_le_frob A
  have hB := linfty_le_frob B
  refine (frob_le_linfty _).trans ?_
  have hexp : Real.exp ‖A‖ - 1 ≤ Real.exp (Real.sqrt 2 * frobNorm A) - 1 := by
    linarith [Real.exp_le_exp.mpr hA]
  have he : 0 ≤ Real.exp ‖A‖ - 1 := by linarith [Real.add_one_le_exp ‖A‖, norm_nonneg A]
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc Real.sqrt 2 * ‖expL A B - B‖ ≤ Real.sqrt 2 * ((Real.exp ‖A‖ - 1) * ‖B‖) :=
        mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt 2 * ((Real.exp (Real.sqrt 2 * frobNorm A) - 1) * (Real.sqrt 2 * frobNorm B)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact mul_le_mul hexp hB (norm_nonneg _) (le_trans he hexp)
    _ = 2 * (Real.exp (Real.sqrt 2 * frobNorm A) - 1) * frobNorm B := by
        rw [show Real.sqrt 2 * ((Real.exp (Real.sqrt 2 * frobNorm A) - 1) * (Real.sqrt 2 * frobNorm B))
          = (Real.sqrt 2 * Real.sqrt 2) * (Real.exp (Real.sqrt 2 * frobNorm A) - 1) * frobNorm B by ring, hs]

theorem expL_le_F (A B : Mt) : frobNorm (expL A B) ≤ 2 * Real.exp (Real.sqrt 2 * frobNorm A) * frobNorm B := by
  have h := expL_le A B
  have hA := linfty_le_frob A
  have hB := linfty_le_frob B
  refine (frob_le_linfty _).trans ?_
  have hexp : Real.exp ‖A‖ ≤ Real.exp (Real.sqrt 2 * frobNorm A) := Real.exp_le_exp.mpr hA
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc Real.sqrt 2 * ‖expL A B‖ ≤ Real.sqrt 2 * (Real.exp ‖A‖ * ‖B‖) := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt 2 * (Real.exp (Real.sqrt 2 * frobNorm A) * (Real.sqrt 2 * frobNorm B)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact mul_le_mul hexp hB (norm_nonneg _) (Real.exp_pos _).le
    _ = 2 * Real.exp (Real.sqrt 2 * frobNorm A) * frobNorm B := by
        rw [show Real.sqrt 2 * (Real.exp (Real.sqrt 2 * frobNorm A) * (Real.sqrt 2 * frobNorm B))
          = (Real.sqrt 2 * Real.sqrt 2) * Real.exp (Real.sqrt 2 * frobNorm A) * frobNorm B by ring, hs]

theorem expL_sub (A B C : Mt) : expL A (B - C) = expL A B - expL A C := by
  rw [sub_eq_add_neg, expL_add, show -C = (-1 : ℝ) • C by simp, expL_smul]; simp [sub_eq_add_neg]

end Linfty

/-! ## the even-part rules -/

/-- **even part of `exp` around an arbitrary base point** -/
theorem even_exp (X Y X0 : Mt) (hX : frobNorm (X - X0) ≤ 1 / 2) (hY : frobNorm (Y - X0) ≤ 1 / 2) :
    frobNorm (NormedSpace.exp X + NormedSpace.exp Y - 2 • NormedSpace.exp X0)
      ≤ 2 * Real.exp (Real.sqrt 2 * frobNorm X0) * frobNorm (X + Y - 2 • X0)
        + 2 * Real.sqrt 2 * Real.exp (Real.sqrt 2 * frobNorm X0) * (frobNorm (X - X0) ^ 2 + frobNorm (Y - X0) ^ 2) := by
  have hRX := exp_second_order_F X0 (X - X0) hX
  have hRY := exp_second_order_F X0 (Y - X0) hY
  rw [add_sub_cancel] at hRX hRY
  have e : NormedSpace.exp X + NormedSpace.exp Y - 2 • NormedSpace.exp X0
      = expL X0 (X + Y - 2 • X0) + (NormedSpace.exp X - NormedSpace.exp X0 - expL X0 (X - X0))
        + (NormedSpace.exp Y - NormedSpace.exp X0 - expL X0 (Y - X0)) := by
    have hl : expL X0 (X + Y - 2 • X0) = expL X0 (X - X0) + expL X0 (Y - X0) := by
      rw [← expL_add]; congr 1; rw [two_nsmul]; abel
    rw [hl, two_nsmul]; abel
  rw [e]
  refine (fN_add _ _).trans ?_
  refine (add_le_add (fN_add _ _) hRY).trans ?_
  have := expL_le_F X0 (X + Y - 2 • X0)
  nlinarith [hRX]

/-- **even part of the INVERSE of `exp`** (the logarithm at a non-identity point, via `exp`) -/
theorem even_exp_inv (X Y X0 : Mt) (hX : frobNorm (X - X0) ≤ 1 / 2) (hY : frobNorm (Y - X0) ≤ 1 / 2)
    (hE : 2 * (Real.exp (Real.sqrt 2 * frobNorm X0) - 1) ≤ 1 / 2) :
    frobNorm (X + Y - 2 • X0)
      ≤ 2 * (frobNorm (NormedSpace.exp X + NormedSpace.exp Y - 2 • NormedSpace.exp X0)
        + 2 * Real.sqrt 2 * Real.exp (Real.sqrt 2 * frobNorm X0) * (frobNorm (X - X0) ^ 2 + frobNorm (Y - X0) ^ 2)) := by
  have hRX := exp_second_order_F X0 (X - X0) hX
  have hRY := exp_second_order_F X0 (Y - X0) hY
  rw [add_sub_cancel] at hRX hRY
  set δ := X + Y - 2 • X0 with hδ
  have hl : expL X0 δ = (NormedSpace.exp X + NormedSpace.exp Y - 2 • NormedSpace.exp X0)
      - (NormedSpace.exp X - NormedSpace.exp X0 - expL X0 (X - X0))
      - (NormedSpace.exp Y - NormedSpace.exp X0 - expL X0 (Y - X0)) := by
    have h1 : expL X0 δ = expL X0 (X - X0) + expL X0 (Y - X0) := by
      rw [← expL_add]; congr 1; rw [hδ, two_nsmul]; abel
    rw [h1, two_nsmul]; abel
  have hd := expL_sub_le_F X0 δ
  have hδ1 : frobNorm δ ≤ frobNorm (expL X0 δ) + frobNorm (expL X0 δ - δ) := by
    have e : δ = expL X0 δ - (expL X0 δ - δ) := by abel
    calc frobNorm δ = frobNorm (expL X0 δ - (expL X0 δ - δ)) := by rw [← e]
      _ ≤ frobNorm (expL X0 δ) + frobNorm (expL X0 δ - δ) := fN_sub _ _
  have hlb : frobNorm (expL X0 δ) ≤ frobNorm (NormedSpace.exp X + NormedSpace.exp Y - 2 • NormedSpace.exp X0)
      + frobNorm (NormedSpace.exp X - NormedSpace.exp X0 - expL X0 (X - X0))
      + frobNorm (NormedSpace.exp Y - NormedSpace.exp X0 - expL X0 (Y - X0)) := by
    rw [hl]; exact (fN_sub _ _).trans (add_le_add (fN_sub _ _) le_rfl)
  have hδ0 := frobNorm_nonneg δ
  nlinarith [mul_le_mul_of_nonneg_right hE hδ0]

theorem lip_exp (X X0 : Mt) (hX : frobNorm (X - X0) ≤ 1 / 2) :
    frobNorm (NormedSpace.exp X - NormedSpace.exp X0)
      ≤ 2 * Real.exp (Real.sqrt 2 * frobNorm X0) * frobNorm (X - X0)
        + 2 * Real.sqrt 2 * Real.exp (Real.sqrt 2 * frobNorm X0) * frobNorm (X - X0) ^ 2 := by
  have hR := exp_second_order_F X0 (X - X0) hX
  rw [add_sub_cancel] at hR
  have e : NormedSpace.exp X - NormedSpace.exp X0 = expL X0 (X - X0) + (NormedSpace.exp X - NormedSpace.exp X0 - expL X0 (X - X0)) := by abel
  rw [e]
  refine (fN_add _ _).trans ?_
  have := expL_le_F X0 (X - X0)
  linarith

#print axioms linfty_le_frob
#print axioms frob_le_linfty
#print axioms exp_second_order_F
#print axioms even_exp
#print axioms even_exp_inv
#print axioms lip_exp

end AdalyFormal.DLayer
