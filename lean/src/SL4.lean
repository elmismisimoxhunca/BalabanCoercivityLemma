import SL3

/-!
# SL4 -- harmonic energy bound and SliceDivSmall from ONE right inverse (abstract)

`harmonic_energy_of_ext`: if every `w` has a preimage `f` under `QU` with `‖DU f‖ ≤ b‖w‖`, `‖QU s‖ ≤ q‖s‖`,
and `ker QU ⊆ N`, then every `DU`-harmonic `s` (rel. `N`) has `‖DU s‖ ≤ b q ‖s‖`.  (Energy minimality, `energy_min`.)
`slice_div_small_of_harm`: harmonic energy `κ` ⇒ `‖DU* x‖ ≤ κ‖x‖` on the slice (the duality of `slice_div_small`).
So SL2's two inputs `hS1`, `hS2` both come from one right inverse with `κ = b q`.
Scaling (flat full tower, numerics explore/p3): `b² ≈ 49.6 n`, `q = n^{-3/2}` ⇒ `κ² ≈ 49.6 n⁻²` (true harmonic value 32.3 n⁻²).
-/
set_option autoImplicit false
namespace AdalyFormal.SliceCoerc

open scoped RealInnerProductSpace

variable {E F C : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup C] [InnerProductSpace ℝ C]

theorem harmonic_energy_of_ext (DU : E →L[ℝ] F) (QU : E →L[ℝ] C) (N : Submodule ℝ E)
    (hN : ∀ f, QU f = 0 → f ∈ N) (b q : ℝ) (hb : 0 ≤ b)
    (hext : ∀ w : C, ∃ f : E, QU f = w ∧ ‖DU f‖ ≤ b * ‖w‖) (hQq : ∀ f, ‖QU f‖ ≤ q * ‖f‖)
    (s : E) (hs : ∀ ν ∈ N, ⟪DU s, DU ν⟫ = 0) : ‖DU s‖ ≤ b * q * ‖s‖ := by
  obtain ⟨f, hf, hfb⟩ := hext (QU s)
  have hmin := energy_min DU N s f hs (hN _ (by rw [map_sub, hf, sub_self]))
  have h1 : ‖DU s‖ ≤ ‖DU f‖ := by
    by_contra h
    have h' := lt_of_not_ge h
    nlinarith [norm_nonneg (DU f), norm_nonneg (DU s)]
  calc ‖DU s‖ ≤ ‖DU f‖ := h1
    _ ≤ b * ‖QU s‖ := hfb
    _ ≤ b * (q * ‖s‖) := mul_le_mul_of_nonneg_left (hQq s) hb
    _ = b * q * ‖s‖ := by ring

theorem slice_div_small_of_harm (DU : E →L[ℝ] F) (DUs : F →L[ℝ] E) (N : Submodule ℝ E)
    (hadj : ∀ (x : F) (s : E), ⟪x, DU s⟫ = ⟪DUs x, s⟫) (κ : ℝ) (hκ : 0 ≤ κ)
    (hharm : ∀ s : E, (∀ ν ∈ N, ⟪DU s, DU ν⟫ = 0) → ‖DU s‖ ≤ κ * ‖s‖)
    (x : F) (hx : ∀ ν ∈ N, ⟪DU (DUs x), DU ν⟫ = 0) : ‖DUs x‖ ≤ κ * ‖x‖ := by
  set s := DUs x with hsdef
  have hDs := hharm s hx
  have hss : ‖s‖ ^ 2 = ⟪x, DU s⟫ := by
    rw [hadj, ← hsdef, real_inner_self_eq_norm_sq]
  have hcs : ⟪x, DU s⟫ ≤ ‖x‖ * ‖DU s‖ := real_inner_le_norm _ _
  have hkey : ‖s‖ ^ 2 ≤ ‖x‖ * (κ * ‖s‖) := by
    have := mul_le_mul_of_nonneg_left hDs (norm_nonneg x)
    linarith
  rcases eq_or_lt_of_le (norm_nonneg s) with h | h
  · rw [← h]; exact mul_nonneg hκ (norm_nonneg x)
  · nlinarith

#print axioms harmonic_energy_of_ext
#print axioms slice_div_small_of_harm

end AdalyFormal.SliceCoerc
