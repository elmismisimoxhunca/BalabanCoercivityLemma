import Mathlib

/-!
# DL1 -- abstract lemmas for the D-layer (Mathlib only)

* `opNorm_le_of_symm_form` : a symmetric operator whose quadratic form is bounded by `ε‖x‖²` has operator norm `≤ ε` (polarization).
* `coercive_isUnit`, `coercive_inv_bound` : `c‖x‖² ≤ ⟪x, M x⟫` (`c > 0`, `M` NOT assumed symmetric) gives `IsUnit M` and
  `c ‖M⁻¹ y‖ ≤ ‖y‖` (the Combes–Thomas step: a conjugated operator that stays coercive has a bounded inverse).
* `pair_lower` : `⟪u₋, u₊⟫ ≥ ‖u‖² − ‖u‖(d₊+d₋) − d₊d₋` when `‖u± − u‖ ≤ d±` (the `X*X` term under weight conjugation).
* `sum_le_weighted` : `Σ fᵢ ≤ √(Σ wᵢ⁻²) · √(Σ wᵢ² fᵢ²)` (ℓ¹ from weighted ℓ², Cauchy–Schwarz).
* `cyc_geom_sum` : `Σ_{t : Fin N} exp(−a · min(t, N−t)) ≤ 2 / (1 − exp(−a))` for `a > 0`.
-/
set_option autoImplicit false

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem form_polar (T : E →L[ℝ] E) (hs : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (x y : E) :
    ⟪x + y, T (x + y)⟫ - ⟪x - y, T (x - y)⟫ = 4 * ⟪T x, y⟫ := by
  have h1 : ⟪x, T y⟫ = ⟪T x, y⟫ := (hs x y).symm
  have h2 : ⟪y, T x⟫ = ⟪T x, y⟫ := real_inner_comm _ _
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [h1, h2]
  ring

/-- polarization: symmetric `T` with `|⟪x,Tx⟫| ≤ ε‖x‖²` has `‖T‖ ≤ ε`. -/
theorem opNorm_le_of_symm_form (T : E →L[ℝ] E) (hs : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ x, |⟪x, T x⟫| ≤ ε * ‖x‖ ^ 2) : ‖T‖ ≤ ε := by
  have key : ∀ x y : E, 4 * ⟪T x, y⟫ ≤ 2 * ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    intro x y
    rw [← form_polar T hs x y]
    have h1 := hf (x + y)
    have h2 := hf (x - y)
    have hp : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      rw [norm_add_sq_real, norm_sub_sq_real]; ring
    have a1 := le_abs_self ⟪x + y, T (x + y)⟫
    have a2 := neg_abs_le ⟪x - y, T (x - y)⟫
    nlinarith
  refine ContinuousLinearMap.opNorm_le_bound _ hε (fun x => ?_)
  by_cases hT : T x = 0
  · rw [hT, norm_zero]; positivity
  have hTpos : 0 < ‖T x‖ := norm_pos_iff.mpr hT
  by_cases hx : x = 0
  · rw [hx, map_zero, norm_zero]; simp
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set t : ℝ := ‖x‖ / ‖T x‖ with ht
  have htpos : 0 < t := div_pos hxpos hTpos
  have hTne : ‖T x‖ ≠ 0 := hTpos.ne'
  have h := key x (t • T x)
  have i1 : ⟪T x, t • T x⟫ = ‖x‖ * ‖T x‖ := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, ht]; field_simp
  have i2 : ‖t • T x‖ = ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht]; field_simp
  rw [i1, i2] at h
  have h' : ‖x‖ * ‖T x‖ ≤ ‖x‖ * (ε * ‖x‖) := by nlinarith
  exact le_of_mul_le_mul_left h' hxpos

variable [FiniteDimensional ℝ E]

/-- coercive ⟹ unit (no symmetry assumed). -/
theorem coercive_isUnit (M : E →L[ℝ] E) {c : ℝ} (hc : 0 < c) (h : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, M x⟫) :
    IsUnit M := by
  have hinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 := h x
    rw [hx, inner_zero_right] at h1
    have : ‖x‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (M : E →ₗ[ℝ] E))).mp hinj⟩

theorem coercive_apply_inverse (M : E →L[ℝ] E) {c : ℝ} (hc : 0 < c) (h : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, M x⟫)
    (y : E) : M (Ring.inverse M y) = y := by
  obtain ⟨u, hu⟩ := coercive_isUnit M hc h
  rw [← hu, Ring.inverse_unit]
  exact ContinuousLinearMap.ext_iff.mp u.mul_inv y

/-- the Combes–Thomas output: `c ‖M⁻¹ y‖ ≤ ‖y‖`. -/
theorem coercive_inv_bound (M : E →L[ℝ] E) {c : ℝ} (hc : 0 < c) (h : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, M x⟫) (y : E) :
    c * ‖Ring.inverse M y‖ ≤ ‖y‖ := by
  set x := Ring.inverse M y with hx
  have hMx : M x = y := coercive_apply_inverse M hc h y
  have h1 := h x
  rw [hMx] at h1
  have h2 : ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  by_cases h0 : ‖x‖ = 0
  · rw [h0]; simp
  have hpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm h0)
  have : c * ‖x‖ * ‖x‖ ≤ ‖y‖ * ‖x‖ := by nlinarith
  exact le_of_mul_le_mul_right this hpos

end

section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- `⟪u₋,u₊⟫ ≥ ‖u‖² − ‖u‖(‖u₊−u‖+‖u₋−u‖) − ‖u₊−u‖‖u₋−u‖`. -/
theorem pair_lower (u up um : F) :
    ‖u‖ ^ 2 - ‖u‖ * (‖up - u‖ + ‖um - u‖) - ‖up - u‖ * ‖um - u‖ ≤ ⟪um, up⟫ := by
  have e : ⟪um, up⟫ = ‖u‖ ^ 2 + ⟪u, up - u⟫ + ⟪um - u, u⟫ + ⟪um - u, up - u⟫ := by
    have h1 : um = u + (um - u) := by abel
    have h2 : up = u + (up - u) := by abel
    conv_lhs => rw [h1, h2]
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq]
    ring
  rw [e]
  have t1 := neg_abs_le ⟪u, up - u⟫
  have t2 := neg_abs_le ⟪um - u, u⟫
  have t3 := neg_abs_le ⟪um - u, up - u⟫
  have s1 := abs_real_inner_le_norm u (up - u)
  have s2 := abs_real_inner_le_norm (um - u) u
  have s3 := abs_real_inner_le_norm (um - u) (up - u)
  nlinarith [norm_nonneg u, norm_nonneg (up - u), norm_nonneg (um - u)]

end

/-- ℓ¹ from weighted ℓ² (Cauchy–Schwarz). -/
theorem sum_le_weighted {ι : Type*} (s : Finset ι) (f w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) :
    ∑ i ∈ s, f i ≤ Real.sqrt (∑ i ∈ s, (w i)⁻¹ ^ 2) * Real.sqrt (∑ i ∈ s, (w i * f i) ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => (w i)⁻¹) (fun i => w i * f i)
  have e : ∑ i ∈ s, (w i)⁻¹ * (w i * f i) = ∑ i ∈ s, f i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have := (hw i hi).ne'
    field_simp
  rw [e] at hcs
  have hA : 0 ≤ ∑ i ∈ s, (w i)⁻¹ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h1 : Real.sqrt ((∑ i ∈ s, f i) ^ 2) ≤ Real.sqrt ((∑ i ∈ s, (w i)⁻¹ ^ 2) * ∑ i ∈ s, (w i * f i) ^ 2) :=
    Real.sqrt_le_sqrt hcs
  rw [Real.sqrt_mul hA, Real.sqrt_sq_eq_abs] at h1
  exact (le_abs_self _).trans h1

/-- cyclic distance on `Fin N` to `0`. -/
def cycd {N : ℕ} (t : Fin N) : ℕ := min t.val (N - t.val)

theorem exp_neg_cycd_le {N : ℕ} (a : ℝ) (ha : 0 ≤ a) (t : Fin N) :
    Real.exp (-(a * (cycd t : ℝ))) ≤ Real.exp (-(a * (t.val : ℝ))) + Real.exp (-(a * ((N - t.val : ℕ) : ℝ))) := by
  unfold cycd
  rcases le_total t.val (N - t.val) with h | h
  · rw [min_eq_left h]
    have := Real.exp_pos (-(a * ((N - t.val : ℕ) : ℝ)))
    linarith
  · rw [min_eq_right h]
    have := Real.exp_pos (-(a * (t.val : ℝ)))
    linarith

theorem geom_exp_sum (a : ℝ) (ha : 0 < a) (M : ℕ) :
    ∑ j ∈ Finset.range M, Real.exp (-(a * (j : ℝ))) ≤ 1 / (1 - Real.exp (-a)) := by
  have hq0 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hq1 : Real.exp (-a) < 1 := by
    have := Real.exp_lt_exp.mpr (show -a < 0 by linarith)
    rwa [Real.exp_zero] at this
  have e : ∀ j : ℕ, Real.exp (-(a * (j : ℝ))) = Real.exp (-a) ^ j := by
    intro j
    rw [← Real.exp_nat_mul]; ring_nf
  simp only [e]
  have hs := summable_geometric_of_lt_one hq0 hq1
  have h1 := hs.sum_le_tsum (Finset.range M) (fun j _ => pow_nonneg hq0 j)
  rw [tsum_geometric_of_lt_one hq0 hq1] at h1
  rw [one_div]
  exact h1

/-- `Σ_{t:Fin N} exp(−a·cycd t) ≤ 2/(1−e^{−a})`. -/
theorem cyc_geom_sum (N : ℕ) (a : ℝ) (ha : 0 < a) :
    ∑ t : Fin N, Real.exp (-(a * (cycd t : ℝ))) ≤ 2 / (1 - Real.exp (-a)) := by
  have h1 : ∑ t : Fin N, Real.exp (-(a * (cycd t : ℝ)))
      ≤ ∑ t : Fin N, (Real.exp (-(a * (t.val : ℝ))) + Real.exp (-(a * ((N - t.val : ℕ) : ℝ)))) :=
    Finset.sum_le_sum (fun t _ => exp_neg_cycd_le a ha.le t)
  rw [Finset.sum_add_distrib] at h1
  have h2 : ∑ t : Fin N, Real.exp (-(a * (t.val : ℝ))) = ∑ j ∈ Finset.range N, Real.exp (-(a * (j : ℝ))) :=
    Fin.sum_univ_eq_sum_range (fun j => Real.exp (-(a * (j : ℝ)))) N
  have h3 : ∑ t : Fin N, Real.exp (-(a * ((N - t.val : ℕ) : ℝ)))
      ≤ ∑ j ∈ Finset.range N, Real.exp (-(a * (j : ℝ))) := by
    -- reflect t ↦ N - 1 - t : the terms are exp(-a (j+1)) ≤ exp(-a j)
    have hr : ∑ t : Fin N, Real.exp (-(a * ((N - t.val : ℕ) : ℝ)))
        = ∑ j ∈ Finset.range N, Real.exp (-(a * (((N - j : ℕ)) : ℝ))) :=
      Fin.sum_univ_eq_sum_range (fun j => Real.exp (-(a * (((N - j : ℕ)) : ℝ)))) N
    rw [hr]
    have hrefl := Finset.sum_range_reflect (fun j => Real.exp (-(a * (((N - j : ℕ)) : ℝ)))) N
    rw [← hrefl]
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hjN : j < N := Finset.mem_range.mp hj
    have e : N - (N - 1 - j) = j + 1 := by omega
    rw [e]
    apply Real.exp_le_exp.mpr
    have : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ j
    nlinarith
  have hg := geom_exp_sum a ha N
  rw [h2] at h1
  calc _ ≤ _ := h1
    _ ≤ 1 / (1 - Real.exp (-a)) + 1 / (1 - Real.exp (-a)) := by linarith
    _ = 2 / (1 - Real.exp (-a)) := by ring

#print axioms form_polar
#print axioms opNorm_le_of_symm_form
#print axioms coercive_isUnit
#print axioms coercive_apply_inverse
#print axioms coercive_inv_bound
#print axioms pair_lower
#print axioms sum_le_weighted
#print axioms exp_neg_cycd_le
#print axioms geom_exp_sum
#print axioms cyc_geom_sum

end AdalyFormal.DLayer
