import Mathlib

/-!
# MI1 -- abstract first-order IMS and the W4 assembly (M1 lane E, 2026-10-13)

Hilbert-space level, no lattice.  `m i` are the localisation maps (multiplication by `h_i` on the domain), `P i` the
localisation maps on the codomain of a "square" `Y` (multiplication by `h_i` there), with `Σ_i ‖P i y‖² = ‖y‖²`.
The commutator sum `e_Y(A) = Σ_i ‖Y(m_i A) − P_i(Y A)‖²` is the only input:

* `sum_inner_le` : Cauchy–Schwarz for the cross term;
* `ims_sq_two_sided` : `|Σ_i ‖Y m_i A‖² − ‖YA‖²| ≤ 2‖YA‖√e_Y + e_Y`  (FIRST order: no double commutator, no kernel);
* `ims_sq_upper`     : `Σ_i ‖Y m_i A‖² ≤ (1+ε)‖YA‖² + (1 + 1/ε) e_Y`  (`ε > 0`);  `ims_sq_lower` : the lower companion;
* `ims_assembly`     : (W4, abstract) `Σ_i N(m_i A) = N(A)`, `Σ_i K(m_i A) ≤ (1+ε)K(A) + e N(A)`, `c_P N(m_i A) ≤ K(m_i A)`
                       `⇒ (c_P − e) N(A) ≤ (1+ε) K(A)`;
* `ims_assembly_div` : the same with the constant `(c_P − e)/(1+ε)` in front of `N`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open Finset

section
variable {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Cauchy–Schwarz for a finite family of inner products. -/
theorem sum_inner_le (u c : ι → F) :
    |∑ i, ⟪u i, c i⟫| ≤ Real.sqrt (∑ i, ‖u i‖ ^ 2) * Real.sqrt (∑ i, ‖c i‖ ^ 2) := by
  have h1 : |∑ i, ⟪u i, c i⟫| ≤ ∑ i, ‖u i‖ * ‖c i‖ :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => abs_real_inner_le_norm _ _)
  have h2 : (∑ i, ‖u i‖ * ‖c i‖) ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * (∑ i, ‖c i‖ ^ 2) :=
    sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : 0 ≤ ∑ i, ‖u i‖ * ‖c i‖ := sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine h1.trans ?_
  rw [← Real.sqrt_mul (sum_nonneg fun i _ => sq_nonneg _)]
  exact Real.le_sqrt_of_sq_le h2

/-- **first-order IMS for one square** (two-sided). -/
theorem ims_sq_two_sided (Y : E → F) (m : ι → E → E) (P : ι → F → F)
    (hP : ∀ y, ∑ i, ‖P i y‖ ^ 2 = ‖y‖ ^ 2) (A : E) :
    |∑ i, ‖Y (m i A)‖ ^ 2 - ‖Y A‖ ^ 2|
      ≤ 2 * ‖Y A‖ * Real.sqrt (∑ i, ‖Y (m i A) - P i (Y A)‖ ^ 2) + ∑ i, ‖Y (m i A) - P i (Y A)‖ ^ 2 := by
  set u : ι → F := fun i => P i (Y A)
  set c : ι → F := fun i => Y (m i A) - P i (Y A)
  have hsplit : ∀ i, ‖Y (m i A)‖ ^ 2 = ‖u i‖ ^ 2 + 2 * ⟪u i, c i⟫ + ‖c i‖ ^ 2 := by
    intro i
    have : Y (m i A) = u i + c i := by simp [u, c]
    rw [this, norm_add_sq_real]
  have hsum : ∑ i, ‖Y (m i A)‖ ^ 2 - ‖Y A‖ ^ 2 = 2 * ∑ i, ⟪u i, c i⟫ + ∑ i, ‖c i‖ ^ 2 := by
    simp only [hsplit, sum_add_distrib, ← mul_sum]
    rw [show ∑ i, ‖u i‖ ^ 2 = ‖Y A‖ ^ 2 from hP (Y A)]
    ring
  rw [hsum]
  have hcs := sum_inner_le u c
  rw [show ∑ i, ‖u i‖ ^ 2 = ‖Y A‖ ^ 2 from hP (Y A), Real.sqrt_sq (norm_nonneg _)] at hcs
  have hc0 : 0 ≤ ∑ i, ‖c i‖ ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  calc |2 * ∑ i, ⟪u i, c i⟫ + ∑ i, ‖c i‖ ^ 2| ≤ |2 * ∑ i, ⟪u i, c i⟫| + |∑ i, ‖c i‖ ^ 2| := abs_add_le _ _
    _ = 2 * |∑ i, ⟪u i, c i⟫| + ∑ i, ‖c i‖ ^ 2 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hc0]
    _ ≤ 2 * (‖Y A‖ * Real.sqrt (∑ i, ‖c i‖ ^ 2)) + ∑ i, ‖c i‖ ^ 2 := by linarith
    _ = _ := by ring

/-- **first-order IMS, upper form**: `Σ_i ‖Y m_i A‖² ≤ (1+ε)‖YA‖² + (1+1/ε) e_Y`. -/
theorem ims_sq_upper (Y : E → F) (m : ι → E → E) (P : ι → F → F)
    (hP : ∀ y, ∑ i, ‖P i y‖ ^ 2 = ‖y‖ ^ 2) (A : E) (ε : ℝ) (hε : 0 < ε) :
    ∑ i, ‖Y (m i A)‖ ^ 2 ≤ (1 + ε) * ‖Y A‖ ^ 2 + (1 + 1 / ε) * ∑ i, ‖Y (m i A) - P i (Y A)‖ ^ 2 := by
  have h := ims_sq_two_sided Y m P hP A
  set e := ∑ i, ‖Y (m i A) - P i (Y A)‖ ^ 2
  have he : 0 ≤ e := sum_nonneg fun i _ => sq_nonneg _
  set s := Real.sqrt e
  have hs : s ^ 2 = e := Real.sq_sqrt he
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  -- 2 a s ≤ ε a² + s²/ε
  have hamgm : 2 * ‖Y A‖ * s ≤ ε * ‖Y A‖ ^ 2 + (1 / ε) * s ^ 2 := by
    have : 0 ≤ (ε * ‖Y A‖ - s) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
    have e1 : (ε * ‖Y A‖ - s) ^ 2 / ε = ε * ‖Y A‖ ^ 2 - 2 * ‖Y A‖ * s + (1 / ε) * s ^ 2 := by
      field_simp; ring
    linarith
  have h' := (abs_le.mp h).2
  rw [hs] at hamgm
  nlinarith

/-- **first-order IMS, lower form**: `(1−ε)‖YA‖² − (1 + 1/ε) e_Y ≤ Σ_i ‖Y m_i A‖²` for `0 < ε`. -/
theorem ims_sq_lower (Y : E → F) (m : ι → E → E) (P : ι → F → F)
    (hP : ∀ y, ∑ i, ‖P i y‖ ^ 2 = ‖y‖ ^ 2) (A : E) (ε : ℝ) (hε : 0 < ε) :
    (1 - ε) * ‖Y A‖ ^ 2 - (1 + 1 / ε) * ∑ i, ‖Y (m i A) - P i (Y A)‖ ^ 2 ≤ ∑ i, ‖Y (m i A)‖ ^ 2 := by
  have h := ims_sq_two_sided Y m P hP A
  set e := ∑ i, ‖Y (m i A) - P i (Y A)‖ ^ 2
  have he : 0 ≤ e := sum_nonneg fun i _ => sq_nonneg _
  set s := Real.sqrt e
  have hs : s ^ 2 = e := Real.sq_sqrt he
  have hamgm : 2 * ‖Y A‖ * s ≤ ε * ‖Y A‖ ^ 2 + (1 / ε) * s ^ 2 := by
    have : 0 ≤ (ε * ‖Y A‖ - s) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
    have e1 : (ε * ‖Y A‖ - s) ^ 2 / ε = ε * ‖Y A‖ ^ 2 - 2 * ‖Y A‖ * s + (1 / ε) * s ^ 2 := by
      field_simp; ring
    linarith
  have h' := (abs_le.mp h).1
  rw [hs] at hamgm
  nlinarith

end

section
variable {ι E : Type*} [Fintype ι]

/-- **W4, abstract IMS assembly.** -/
theorem ims_assembly (K N : E → ℝ) (m : ι → E → E) (hN : ∀ A, ∑ i, N (m i A) = N A) (cP ε e : ℝ)
    (hims : ∀ A, ∑ i, K (m i A) ≤ (1 + ε) * K A + e * N A)
    (hpatch : ∀ i A, cP * N (m i A) ≤ K (m i A)) (A : E) :
    (cP - e) * N A ≤ (1 + ε) * K A := by
  have h1 : cP * N A = ∑ i, cP * N (m i A) := by rw [← mul_sum, hN A]
  have h2 : ∑ i, cP * N (m i A) ≤ ∑ i, K (m i A) := sum_le_sum fun i _ => hpatch i A
  have := hims A
  linarith

/-- **W4, abstract, normalised constant**: `((c_P − e)/(1+ε)) N(A) ≤ K(A)`. -/
theorem ims_assembly_div (K N : E → ℝ) (m : ι → E → E) (hN : ∀ A, ∑ i, N (m i A) = N A) (cP ε e : ℝ)
    (hε : 0 ≤ ε)
    (hims : ∀ A, ∑ i, K (m i A) ≤ (1 + ε) * K A + e * N A)
    (hpatch : ∀ i A, cP * N (m i A) ≤ K (m i A)) (A : E) :
    ((cP - e) / (1 + ε)) * N A ≤ K A := by
  have h := ims_assembly K N m hN cP ε e hims hpatch A
  have hpos : 0 < 1 + ε := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  linarith

end

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.sum_inner_le
#print axioms AdalyFormal.M1IMS.ims_sq_two_sided
#print axioms AdalyFormal.M1IMS.ims_sq_upper
#print axioms AdalyFormal.M1IMS.ims_sq_lower
#print axioms AdalyFormal.M1IMS.ims_assembly
#print axioms AdalyFormal.M1IMS.ims_assembly_div
