import Mathlib

/-!
# SG — pin of the remaining pencil (UNCOMPILED DRAFT)

This file is not a Lake root and was not compiled. Nothing here is a theorem of the
project tree. It imports only Mathlib. It does not import `D2Cons`, `DrEquiv`,
`DrRed1`, `DrPath1`, `DrMargin`, or any frozen module.

`P428Target8SG selAll selAll` is not decided here. The frozen equivalence with
`GuardPencilT` is not re-proved. What is proved, as linear algebra only:

* `IsUnit A → IsUnit (A - D)` is false for real scalars (`not_generic_unit_transfer`).
* A scalar path `carrier t = (2 - t) • 1`, correction `1`, has `carrier 1` a unit and
  `carrier 1 - corr` not a unit. Both are units for every `t < 1`. `carrier` itself
  dies only at `t = 2` (`scalar_path_crosses_earlier`).
* On any finite-dimensional real inner product space, if `A` is `c`-coercive and
  `c > ‖D‖`, then `A - D` is a unit. A failure forces `c ≤ ‖D‖`
  (`coercivity_le_opNorm_of_pencil_fail`). This is the abstract shape of
  `G1inv_lit_isUnit_of_margin` and `coercivity_le_Delta2_of_gap`. It is not those
  theorems.
* A zero correction never moves the root (`unit_of_zero_correction`).

The scalar path is not a link configuration, not `ClassCoupled`, and not a
counterexample to `P428Target8SG`.
-/

set_option autoImplicit false

namespace AdalyFormal.AHP.SGGuarded

open scoped RealInnerProductSpace

noncomputable def carrier (t : ℝ) : ℝ →L[ℝ] ℝ := (2 - t) • (1 : ℝ →L[ℝ] ℝ)

noncomputable def corr : ℝ →L[ℝ] ℝ := (1 : ℝ →L[ℝ] ℝ)

noncomputable def pencil (t : ℝ) : ℝ →L[ℝ] ℝ := (1 - t) • (1 : ℝ →L[ℝ] ℝ)

theorem carrier_apply (t x : ℝ) : carrier t x = (2 - t) * x := by
  simp [carrier]

theorem pencil_apply (t x : ℝ) : pencil t x = (1 - t) * x := by
  simp [pencil]

theorem pencil_eq (t : ℝ) : carrier t - corr = pencil t := by
  ext x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, carrier, corr, pencil]
  ring

theorem isUnit_smul_one {c : ℝ} (hc : c ≠ 0) : IsUnit (c • (1 : ℝ →L[ℝ] ℝ)) := by
  refine ⟨{
    val := c • (1 : ℝ →L[ℝ] ℝ)
    inv := c⁻¹ • (1 : ℝ →L[ℝ] ℝ)
    val_inv := ?_
    inv_val := ?_
  }, rfl⟩
  · ext x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    calc
      c * (c⁻¹ * x) = (c * c⁻¹) * x := by ring
      _ = 1 * x := by rw [mul_inv_cancel₀ hc]
      _ = x := by ring
  · ext x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    calc
      c⁻¹ * (c * x) = (c⁻¹ * c) * x := by ring
      _ = 1 * x := by rw [inv_mul_cancel₀ hc]
      _ = x := by ring

theorem not_isUnit_zero_smul_one : ¬ IsUnit ((0 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) := by
  simp [zero_smul, not_isUnit_zero]

theorem carrier_unit_of (t : ℝ) (ht : t ≠ 2) : IsUnit (carrier t) := by
  have hc : 2 - t ≠ 0 := by
    intro h
    apply ht
    linarith
  simpa [carrier] using isUnit_smul_one hc

theorem pencil_unit_of (t : ℝ) (ht : t ≠ 1) : IsUnit (pencil t) := by
  have hc : 1 - t ≠ 0 := by
    intro h
    apply ht
    linarith
  simpa [pencil] using isUnit_smul_one hc

theorem carrier_not_unit_at_two : ¬ IsUnit (carrier 2) := by
  simpa [carrier, sub_self] using not_isUnit_zero_smul_one

theorem pencil_not_unit_at_one : ¬ IsUnit (pencil 1) := by
  simpa [pencil, sub_self] using not_isUnit_zero_smul_one

/-- The bare transfer is not an algebraic fact. A nonzero scalar correction moves the root. -/
theorem not_generic_unit_transfer :
    ¬ ∀ (A D : ℝ →L[ℝ] ℝ), IsUnit A → IsUnit (A - D) := by
  intro h
  have hU : IsUnit (carrier 1) := carrier_unit_of 1 (by norm_num)
  have hbad : IsUnit (carrier 1 - corr) := h _ _ hU
  rw [pencil_eq] at hbad
  exact pencil_not_unit_at_one hbad

theorem form_pencil (t x : ℝ) : ⟪x, pencil t x⟫ = (1 - t) * ‖x‖ ^ 2 := by
  rw [pencil_apply]
  have hsm : (1 - t) * x = (1 - t) • x := (smul_eq_mul (1 - t) x).symm
  rw [hsm, real_inner_smul_right, real_inner_self_eq_norm_sq]

theorem pencil_nonneg_at_zero (x : ℝ) : 0 ≤ ⟪x, (carrier 0 - corr) x⟫ := by
  rw [pencil_eq, form_pencil]
  have : (1 - 0) * ‖x‖ ^ 2 = ‖x‖ ^ 2 := by ring
  rw [this]
  exact sq_nonneg _

theorem pencil_neg_at_three : ⟪(1 : ℝ), (carrier 3 - corr) (1 : ℝ)⟫ < 0 := by
  rw [pencil_eq, form_pencil]
  simp [norm_one]
  norm_num

/-- Both operators are units on `(−∞, 1)`, the pencil dies at `1`, the carrier dies at `2`. -/
theorem scalar_path_crosses_earlier :
    IsUnit (carrier 1) ∧ ¬ IsUnit (carrier 1 - corr) ∧
      (∀ t : ℝ, t < 1 → IsUnit (carrier t) ∧ IsUnit (carrier t - corr)) ∧
      ¬ IsUnit (carrier 2) := by
  refine ⟨carrier_unit_of 1 (by norm_num), ?_, ?_, carrier_not_unit_at_two⟩
  · rw [pencil_eq]
    exact pencil_not_unit_at_one
  · intro t ht
    refine ⟨carrier_unit_of t ?_, ?_⟩
    · intro h
      linarith
    · rw [pencil_eq]
      exact pencil_unit_of t (by linarith)

theorem unit_of_zero_correction (A : ℝ →L[ℝ] ℝ) (h : IsUnit A) : IsUnit (A - 0) := by
  simpa using h

theorem isUnit_of_coercive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (F : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hco : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, F x⟫) : IsUnit F := by
  have hinj : Function.Injective (⇑F) := by
    intro x y hxy
    have h0 : F (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h1 := hco (x - y)
    rw [h0, inner_zero_right] at h1
    have h2 : c * ‖x - y‖ ^ 2 = 0 := le_antisymm h1 (mul_nonneg hc.le (sq_nonneg _))
    have h3 : ‖x - y‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hc.ne'
      · exact h
    exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3))
  have hsurj : Function.Surjective (⇑F) :=
    LinearMap.surjective_of_injective (f := (F : E →ₗ[ℝ] E)) hinj
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩

theorem pencil_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A D : E →L[ℝ] E) {c ε : ℝ} (hco : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, A x⟫) (hε : ‖D‖ ≤ ε) (x : E) :
    (c - ε) * ‖x‖ ^ 2 ≤ ⟪x, (A - D) x⟫ := by
  have hop : ‖D x‖ ≤ ‖D‖ * ‖x‖ := ContinuousLinearMap.le_opNorm D x
  have h1 : ‖x‖ * ‖D x‖ ≤ ‖x‖ * (‖D‖ * ‖x‖) :=
    mul_le_mul_of_nonneg_left hop (norm_nonneg _)
  have h2 : ‖x‖ * (‖D‖ * ‖x‖) ≤ ‖x‖ * (ε * ‖x‖) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hε (norm_nonneg _)) (norm_nonneg _)
  have hD : ⟪x, D x⟫ ≤ ε * ‖x‖ ^ 2 := by
    calc
      ⟪x, D x⟫ ≤ ‖x‖ * ‖D x‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖D‖ * ‖x‖) := h1
      _ ≤ ‖x‖ * (ε * ‖x‖) := h2
      _ = ε * ‖x‖ ^ 2 := by ring
  simp only [ContinuousLinearMap.sub_apply, inner_sub_right]
  linarith [hco x]

/-- Outside the margin the pencil is a unit. A failure forces `c ≤ ‖D‖`. -/
theorem coercivity_le_opNorm_of_pencil_fail {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (A D : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hco : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, A x⟫) (hn : ¬ IsUnit (A - D)) : c ≤ ‖D‖ := by
  by_contra hlt
  push_neg at hlt
  exact hn (isUnit_of_coercive (A - D) (sub_pos.mpr hlt) (pencil_lower A D hco le_rfl))

end AdalyFormal.AHP.SGGuarded
