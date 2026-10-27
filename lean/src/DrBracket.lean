import D1IVT

/-!
# DrBracket -- an abstract pencil-bracketing lemma (finite-dimensional real inner product space, no lattice objects).

If `M t` is a continuous family of symmetric COERCIVE operators on `[0,T]`, `Δ` is symmetric, `M 0 - Δ` is positive semidefinite and
`M T - Δ` has a strictly negative direction, then there is `t ∈ [0,T)` with `M t` a unit and `M t - Δ` not a unit.
This is a sufficiency statement about linear algebra; it says nothing about when its hypotheses hold for the lattice operators.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.D1Residual

open scoped RealInnerProductSpace
open Set
open AdalyFormal.D1Literal (PSD exists_nonunit_path)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- a coercive operator on a finite-dimensional space is a unit. -/
theorem isUnit_of_coercive (F : E →L[ℝ] E) {c : ℝ} (hc : 0 < c) (hco : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, F x⟫) : IsUnit F := by
  have hinj : Function.Injective F := by
    intro x y hxy
    have h0 : F (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h1 := hco (x - y)
    rw [h0, inner_zero_right] at h1
    have h2 : c * ‖x - y‖ ^ 2 = 0 := le_antisymm h1 (by positivity)
    have h3 : ‖x - y‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hc.ne'
      · exact h
    exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3))
  have hbij : Function.Bijective F := ⟨hinj, LinearMap.surjective_of_injective (f := (F : E →ₗ[ℝ] E)) hinj⟩
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr hbij

/-- **bracketing**: along a continuous path of symmetric coercive `M t`, the shifted family `M t - Δ`, positive semidefinite at `0` and with a
negative direction at `T`, has a non-unit at some `t < T` where `M t` is a unit. -/
theorem pencil_bracket (M : ℝ → (E →L[ℝ] E)) (Δ : E →L[ℝ] E) (hc : Continuous M)
    (hs : ∀ t x y, ⟪M t x, y⟫ = ⟪x, M t y⟫) (hΔ : ∀ x y, ⟪Δ x, y⟫ = ⟪x, Δ y⟫)
    (T : ℝ) (hT : 0 < T) (hco : ∀ t ∈ Icc (0 : ℝ) T, ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, M t x⟫)
    (h0 : PSD (M 0 - Δ)) (v : E) (hv : ⟪v, (M T - Δ) v⟫ < 0) :
    ∃ t : ℝ, 0 ≤ t ∧ t < T ∧ IsUnit (M t) ∧ ¬ IsUnit (M t - Δ) := by
  obtain ⟨t, ht0, htT, hnu⟩ := exists_nonunit_path (fun s => M s - Δ) (by fun_prop)
    (fun s x y => by
      simp only [sub_apply, inner_sub_left, inner_sub_right, hs s x y, hΔ x y]) h0 T hT v hv
  obtain ⟨c, hc0, hcc⟩ := hco t ⟨ht0, htT.le⟩
  exact ⟨t, ht0, htT, isUnit_of_coercive (M t) hc0 hcc, hnu⟩

/-- CONTROL: with `Δ = 0` the hypotheses of the bracketing lemma contradict each other (coercivity at `T` against a negative direction of `M T - Δ`);
the criterion can only fire when `Δ` is nonzero on the relevant mode. -/
theorem bracket_hyps_inconsistent_of_zero (M : E →L[ℝ] E) {c : ℝ} (hc : 0 < c) (hco : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, M x⟫)
    (v : E) : ¬ ⟪v, (M - 0) v⟫ < 0 := by
  intro h
  have h1 := hco v
  simp only [sub_zero] at h
  have : 0 ≤ c * ‖v‖ ^ 2 := by positivity
  linarith

#print axioms isUnit_of_coercive
#print axioms bracket_hyps_inconsistent_of_zero
#print axioms pencil_bracket

end AdalyFormal.D1Residual
