import DrBracket

/-!
# DrBracket2 -- the sign-free bracketing lemma: it needs `M t` to be a UNIT on `[ta, tb]` (not coercive from `0`), so it covers both signs of the coupling.

`M t` continuous and symmetric, `Δ` symmetric, `M t` a unit for every `t ∈ [ta, tb]`, `M ta - Δ` positive semidefinite and `M tb - Δ` with a negative direction
give `t ∈ [ta, tb)` with `M t` a unit and `M t - Δ` not a unit.  (`pencil_bracket` is the case `ta = 0` with `M` coercive.)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.D1Residual

open scoped RealInnerProductSpace
open Set
open AdalyFormal.D1Literal (PSD exists_nonunit_path)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem pencil_bracket_unit (M : ℝ → (E →L[ℝ] E)) (Δ : E →L[ℝ] E) (hc : Continuous M)
    (hs : ∀ t x y, ⟪M t x, y⟫ = ⟪x, M t y⟫) (hΔ : ∀ x y, ⟪Δ x, y⟫ = ⟪x, Δ y⟫)
    (ta tb : ℝ) (hab : ta < tb) (hu : ∀ t ∈ Icc ta tb, IsUnit (M t))
    (h0 : PSD (M ta - Δ)) (v : E) (hv : ⟪v, (M tb - Δ) v⟫ < 0) :
    ∃ t : ℝ, ta ≤ t ∧ t < tb ∧ IsUnit (M t) ∧ ¬ IsUnit (M t - Δ) := by
  obtain ⟨s, hs0, hsT, hnu⟩ := exists_nonunit_path (fun s => M (ta + s) - Δ) (by fun_prop)
    (fun s x y => by
      simp only [sub_apply, inner_sub_left, inner_sub_right, hs (ta + s) x y, hΔ x y])
    (by simpa using h0) (tb - ta) (by linarith) v (by simpa using hv)
  refine ⟨ta + s, by linarith, by linarith, hu _ ⟨by linarith, by linarith⟩, hnu⟩

/-- the coercive-from-zero lemma is the special case. -/
theorem pencil_bracket_unit_of_coercive (M : ℝ → (E →L[ℝ] E)) (Δ : E →L[ℝ] E) (hc : Continuous M)
    (hs : ∀ t x y, ⟪M t x, y⟫ = ⟪x, M t y⟫) (hΔ : ∀ x y, ⟪Δ x, y⟫ = ⟪x, Δ y⟫)
    (T : ℝ) (hT : 0 < T) (hco : ∀ t ∈ Icc (0 : ℝ) T, ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, M t x⟫)
    (h0 : PSD (M 0 - Δ)) (v : E) (hv : ⟪v, (M T - Δ) v⟫ < 0) :
    ∃ t : ℝ, 0 ≤ t ∧ t < T ∧ IsUnit (M t) ∧ ¬ IsUnit (M t - Δ) :=
  pencil_bracket_unit M Δ hc hs hΔ 0 T hT
    (fun t ht => by obtain ⟨c, hc0, hcc⟩ := hco t ht; exact isUnit_of_coercive (M t) hc0 hcc) h0 v hv

#print axioms pencil_bracket_unit
#print axioms pencil_bracket_unit_of_coercive

end AdalyFormal.D1Residual
