import Mathlib

/-!
# SL1 -- SliceDivSmall from a smooth right inverse (abstract Hilbert-space lemmas)

Setting: `E` (site fields), `F` (bond fields), `C` (coarse site fields) real inner product spaces,
`D : E → F` (covariant gradient), `Ds : F → E` its adjoint (`hadj`), `N ⊆ E` a submodule (`N(Q')`).

* `energy_min`: if `⟪D s, D ν⟫ = 0` for all `ν ∈ N` ("`s` is `D`-harmonic relative to `N`") and
  `f - s ∈ N`, then `‖D s‖² ≤ ‖D f‖²` (Pythagoras).
* `slice_div_small`: if `x` lies in the slice `⟪D (Ds x), D ν⟫ = 0 ∀ ν ∈ N` (this is `R D* x = 0` when
  `R` is the orthogonal projection onto `D*D N`), and every `s` has an `N`-equivalent `f` with
  `‖D f‖ ≤ κ ‖s‖`, then `‖Ds x‖ ≤ κ ‖x‖`.   Proof: `‖s‖² = ⟪x, D s⟫ ≤ ‖x‖ ‖D s‖ ≤ ‖x‖ κ ‖s‖`, `s = Ds x`.
* `ext_of_rightInverse`: a right inverse `E1` of `Q1` with `‖E1 w‖ ≤ a‖w‖`, `‖DU (E1 w)‖ ≤ b‖w‖` and a
  drift `‖(QU - Q1) f‖ ≤ ε‖f‖`, `ε a < 1`, gives a right inverse of `QU` with constants divided by
  `1 - ε a` (finite-dimensional `C`: injective ⇒ surjective; no Neumann series).
No smallness, no geometry: the content of the geometric primitive is the hypothesis on `E1`.
-/
set_option autoImplicit false
namespace AdalyFormal.SliceCoerc

open scoped RealInnerProductSpace

variable {E F C : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup C] [InnerProductSpace ℝ C]

theorem energy_min (D : E →L[ℝ] F) (N : Submodule ℝ E) (s f : E)
    (hs : ∀ ν ∈ N, ⟪D s, D ν⟫ = 0) (hf : f - s ∈ N) : ‖D s‖ ^ 2 ≤ ‖D f‖ ^ 2 := by
  have hdec : D f = D s + D (f - s) := by rw [map_sub]; abel
  have h0 : ⟪D s, D (f - s)⟫ = 0 := hs _ hf
  rw [hdec, norm_add_sq_real, h0]
  nlinarith [sq_nonneg ‖D (f - s)‖]

theorem slice_div_small (D : E →L[ℝ] F) (Ds : F →L[ℝ] E) (N : Submodule ℝ E)
    (hadj : ∀ (x : F) (s : E), ⟪x, D s⟫ = ⟪Ds x, s⟫) (κ : ℝ) (hκ : 0 ≤ κ)
    (hext : ∀ s : E, ∃ f : E, f - s ∈ N ∧ ‖D f‖ ≤ κ * ‖s‖)
    (x : F) (hx : ∀ ν ∈ N, ⟪D (Ds x), D ν⟫ = 0) : ‖Ds x‖ ≤ κ * ‖x‖ := by
  set s := Ds x with hsdef
  obtain ⟨f, hf, hfb⟩ := hext s
  have hmin := energy_min D N s f hx hf
  have hDs : ‖D s‖ ≤ κ * ‖s‖ := by
    have h1 : ‖D s‖ ≤ ‖D f‖ := by
      by_contra h
      have h' := lt_of_not_ge h
      nlinarith [norm_nonneg (D f), norm_nonneg (D s)]
    linarith
  have hss : ‖s‖ ^ 2 = ⟪x, D s⟫ := by
    rw [hadj, ← hsdef, real_inner_self_eq_norm_sq]
  have hcs : ⟪x, D s⟫ ≤ ‖x‖ * ‖D s‖ := real_inner_le_norm _ _
  have hkey : ‖s‖ ^ 2 ≤ ‖x‖ * (κ * ‖s‖) := by
    have := mul_le_mul_of_nonneg_left hDs (norm_nonneg x)
    linarith
  rcases eq_or_lt_of_le (norm_nonneg s) with h | h
  · rw [← h]; exact mul_nonneg hκ (norm_nonneg x)
  · nlinarith

/-- A right inverse of `Q1`, transported to `QU` through the drift `QU - Q1` (finite-dimensional `C`). -/
theorem ext_of_rightInverse [FiniteDimensional ℝ C] (Q1 QU : E →L[ℝ] C) (E1 : C →L[ℝ] E)
    (DU : E →L[ℝ] F) (a b ε : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 ≤ ε) (hεa : ε * a < 1)
    (hQE : ∀ w, Q1 (E1 w) = w) (hEa : ∀ w, ‖E1 w‖ ≤ a * ‖w‖) (hEb : ∀ w, ‖DU (E1 w)‖ ≤ b * ‖w‖)
    (hdrift : ∀ f, ‖QU f - Q1 f‖ ≤ ε * ‖f‖) (w : C) :
    ∃ f : E, QU f = w ∧ ‖DU f‖ ≤ b / (1 - ε * a) * ‖w‖ ∧ ‖f‖ ≤ a / (1 - ε * a) * ‖w‖ := by
  set K : C →L[ℝ] C := QU.comp E1 with hK
  have hpos : 0 < 1 - ε * a := by linarith
  have hlow : ∀ v, (1 - ε * a) * ‖v‖ ≤ ‖K v‖ := by
    intro v
    have h1 : ‖K v - v‖ ≤ ε * a * ‖v‖ := by
      have := hdrift (E1 v)
      rw [hQE] at this
      calc ‖K v - v‖ = ‖QU (E1 v) - v‖ := rfl
        _ ≤ ε * ‖E1 v‖ := this
        _ ≤ ε * (a * ‖v‖) := mul_le_mul_of_nonneg_left (hEa v) hε
        _ = ε * a * ‖v‖ := by ring
    have h2 : ‖v‖ ≤ ‖K v‖ + ‖K v - v‖ := by
      have := norm_sub_le (K v) (K v - v)
      simpa using this
    nlinarith
  have hinj : Function.Injective K := by
    intro v1 v2 h
    have h0 : K (v1 - v2) = 0 := by rw [map_sub, h, sub_self]
    have := hlow (v1 - v2)
    rw [h0, norm_zero] at this
    have hn : ‖v1 - v2‖ = 0 := by
      have := mul_nonneg hpos.le (norm_nonneg (v1 - v2))
      nlinarith [norm_nonneg (v1 - v2)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hsurj : Function.Surjective K :=
    (LinearMap.injective_iff_surjective (f := (K : C →ₗ[ℝ] C))).mp hinj
  obtain ⟨v, hv⟩ := hsurj w
  have hvb : ‖v‖ ≤ ‖w‖ / (1 - ε * a) := by
    rw [le_div_iff₀ hpos]
    have := hlow v
    rw [hv] at this
    linarith
  refine ⟨E1 v, hv, ?_, ?_⟩
  · calc ‖DU (E1 v)‖ ≤ b * ‖v‖ := hEb v
      _ ≤ b * (‖w‖ / (1 - ε * a)) := mul_le_mul_of_nonneg_left hvb hb
      _ = b / (1 - ε * a) * ‖w‖ := by ring
  · calc ‖E1 v‖ ≤ a * ‖v‖ := hEa v
      _ ≤ a * (‖w‖ / (1 - ε * a)) := mul_le_mul_of_nonneg_left hvb ha
      _ = a / (1 - ε * a) * ‖w‖ := by ring

/-- SliceDivSmall at `U` from a right inverse of the FLAT `Q1`, the drift `QU - Q1`, and `‖QU s‖ ≤ q‖s‖`.
`N` must contain `ker QU`. -/
theorem sliceDivSmall_of_rightInverse [FiniteDimensional ℝ C] (Q1 QU : E →L[ℝ] C) (E1 : C →L[ℝ] E)
    (DU : E →L[ℝ] F) (DUs : F →L[ℝ] E) (N : Submodule ℝ E)
    (hadj : ∀ (x : F) (s : E), ⟪x, DU s⟫ = ⟪DUs x, s⟫) (hN : ∀ f, QU f = 0 → f ∈ N)
    (a b ε q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 ≤ ε) (hq : 0 ≤ q) (hεa : ε * a < 1)
    (hQE : ∀ w, Q1 (E1 w) = w) (hEa : ∀ w, ‖E1 w‖ ≤ a * ‖w‖) (hEb : ∀ w, ‖DU (E1 w)‖ ≤ b * ‖w‖)
    (hdrift : ∀ f, ‖QU f - Q1 f‖ ≤ ε * ‖f‖) (hQq : ∀ f, ‖QU f‖ ≤ q * ‖f‖)
    (x : F) (hx : ∀ ν ∈ N, ⟪DU (DUs x), DU ν⟫ = 0) :
    ‖DUs x‖ ≤ b / (1 - ε * a) * q * ‖x‖ := by
  have hpos : 0 < 1 - ε * a := by linarith
  have hκ : 0 ≤ b / (1 - ε * a) * q := mul_nonneg (div_nonneg hb hpos.le) hq
  refine slice_div_small DU DUs N hadj _ hκ (fun s => ?_) x hx
  obtain ⟨f, hf, hfD, -⟩ := ext_of_rightInverse Q1 QU E1 DU a b ε ha hb hε hεa hQE hEa hEb hdrift (QU s)
  refine ⟨f, hN _ (by rw [map_sub, hf, sub_self]), ?_⟩
  calc ‖DU f‖ ≤ b / (1 - ε * a) * ‖QU s‖ := hfD
    _ ≤ b / (1 - ε * a) * (q * ‖s‖) := mul_le_mul_of_nonneg_left (hQq s) (div_nonneg hb hpos.le)
    _ = b / (1 - ε * a) * q * ‖s‖ := by ring

#print axioms energy_min
#print axioms slice_div_small
#print axioms ext_of_rightInverse
#print axioms sliceDivSmall_of_rightInverse

end AdalyFormal.SliceCoerc
