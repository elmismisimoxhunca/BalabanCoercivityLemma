import SL1

/-!
# SL2 -- the flat gauge-fixing term on the NON-flat slice (abstract)

For `x` in the `U`-slice (`⟪DU (DU* x), DU ν⟫ = 0` for `ν ∈ NU`), the flat term `R1 D1* x` is small:
`‖R1 D1* x‖ ≤ γ ‖x‖`,  `γ = κ (δ P + κ P² (δ + b ε)) + δ`, where
* `κ`: SliceDivSmall at `U` (`‖DU* x‖ ≤ κ‖x‖`) and the harmonic energy bound `‖DU s‖ ≤ κ‖s‖` for `s = DU* x`;
* `δ`: gradient drift `‖D1 f - DU f‖ ≤ δ‖f‖`;
* `P`: Poincare on `N1` (`‖ν‖ ≤ P‖D1 ν‖`);
* `b`: right inverse of `QU` with `‖DU f‖ ≤ b‖w‖`; `ε`: `‖QU ν‖ ≤ ε‖ν‖` on `N1` (drift of `Q'`).
`R1` is any operator with `‖R1 s‖² = ⟪s, R1 s⟫` and `R1 s ∈ D1*D1 N1` (the orthogonal projection onto
`Δ_1 N(Q'_1)`, R2Ops1 `Rproj` at `Ω₀ = univ`).
Scaling in the intended use: `κ ~ K/n`, `δ ~ d ρ/n`, `P ~ C n`, `b ~ K' n^{1/2}`, `ε ~ e ρ n^{-3/2}`: then
`n γ = O(ρ)`, i.e. `n² ‖R1 D1* x‖² = O(ρ²)‖x‖²` -- volume free, k uniform.
-/
set_option autoImplicit false
namespace AdalyFormal.SliceCoerc

open scoped RealInnerProductSpace

variable {E F C : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup C] [InnerProductSpace ℝ C]

/-- adjoint drift from drift. -/
theorem adj_drift (D1 DU : E →L[ℝ] F) (D1s DUs : F →L[ℝ] E)
    (h1 : ∀ (x : F) (s : E), ⟪x, D1 s⟫ = ⟪D1s x, s⟫) (hU : ∀ (x : F) (s : E), ⟪x, DU s⟫ = ⟪DUs x, s⟫)
    (δ : ℝ) (hδ : 0 ≤ δ) (hd : ∀ f, ‖D1 f - DU f‖ ≤ δ * ‖f‖) (x : F) :
    ‖D1s x - DUs x‖ ≤ δ * ‖x‖ := by
  set y := D1s x - DUs x
  have hy : ‖y‖ ^ 2 = ⟪x, D1 y - DU y⟫ := by
    rw [inner_sub_right, h1, hU, ← inner_sub_left, real_inner_self_eq_norm_sq]
  have hb : ⟪x, D1 y - DU y⟫ ≤ ‖x‖ * (δ * ‖y‖) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hd y) (norm_nonneg x))
  rcases eq_or_lt_of_le (norm_nonneg y) with h | h
  · rw [← h]; exact mul_nonneg hδ (norm_nonneg x)
  · nlinarith

/-- the key bound: `‖R1 s‖ ≤ δ P ‖s‖ + (δ + b ε) P² ‖DU s‖` for every `DU`-harmonic `s`. -/
theorem R1_harmonic_le (D1 DU : E →L[ℝ] F) (D1s : F →L[ℝ] E) (R1 : E →L[ℝ] E) (QU : E →L[ℝ] C)
    (N1 NU : Submodule ℝ E)
    (h1 : ∀ (x : F) (s : E), ⟪x, D1 s⟫ = ⟪D1s x, s⟫)
    (hRn : ∀ s, ‖R1 s‖ ^ 2 = ⟪s, R1 s⟫) (hRim : ∀ s, ∃ ν ∈ N1, R1 s = D1s (D1 ν))
    (P δ b ε : ℝ) (hP : 0 ≤ P) (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (hPoinc : ∀ ν ∈ N1, ‖ν‖ ≤ P * ‖D1 ν‖) (hd : ∀ f, ‖D1 f - DU f‖ ≤ δ * ‖f‖)
    (hext : ∀ w : C, ∃ f : E, QU f = w ∧ ‖DU f‖ ≤ b * ‖w‖) (hNU : ∀ f, QU f = 0 → f ∈ NU)
    (hQN1 : ∀ ν ∈ N1, ‖QU ν‖ ≤ ε * ‖ν‖)
    (s : E) (hs : ∀ ν ∈ NU, ⟪DU s, DU ν⟫ = 0) :
    ‖R1 s‖ ≤ δ * P * ‖s‖ + (δ + b * ε) * P ^ 2 * ‖DU s‖ := by
  obtain ⟨ν, hν, hRν⟩ := hRim s
  set r := ‖R1 s‖ with hr
  -- r^2 = ⟪D1 s, D1 ν⟫
  have hr2 : r ^ 2 = ⟪D1 s, D1 ν⟫ := by
    rw [hr, hRn, hRν, real_inner_comm, ← h1, real_inner_comm]
  -- ‖D1 ν‖ ≤ P r and ‖ν‖ ≤ P^2 r
  have hDν2 : ‖D1 ν‖ ^ 2 ≤ ‖ν‖ * r := by
    have : ‖D1 ν‖ ^ 2 = ⟪ν, R1 s⟫ := by
      rw [hRν, real_inner_comm, ← h1, real_inner_self_eq_norm_sq]
    rw [this]; exact real_inner_le_norm _ _
  have hDν : ‖D1 ν‖ ≤ P * r := by
    have hp := hPoinc ν hν
    have : ‖D1 ν‖ ^ 2 ≤ P * ‖D1 ν‖ * r := by
      have := mul_le_mul_of_nonneg_right hp (norm_nonneg (R1 s))
      nlinarith
    rcases eq_or_lt_of_le (norm_nonneg (D1 ν)) with h | h
    · rw [← h]; exact mul_nonneg hP (norm_nonneg _)
    · nlinarith
  have hνr : ‖ν‖ ≤ P ^ 2 * r := by
    have := hPoinc ν hν
    have := mul_le_mul_of_nonneg_left hDν hP
    nlinarith
  -- correction into NU
  obtain ⟨f, hf, hfb⟩ := hext (QU ν)
  have hνt : ν - f ∈ NU := hNU _ (by rw [map_sub, hf, sub_self])
  have h0 : ⟪DU s, DU ν⟫ = ⟪DU s, DU f⟫ := by
    have := hs _ hνt
    rw [map_sub, inner_sub_right] at this
    linarith
  have hfν : ‖DU f‖ ≤ b * ε * ‖ν‖ := by
    calc ‖DU f‖ ≤ b * ‖QU ν‖ := hfb
      _ ≤ b * (ε * ‖ν‖) := mul_le_mul_of_nonneg_left (hQN1 ν hν) hb
      _ = b * ε * ‖ν‖ := by ring
  -- split ⟪D1 s, D1 ν⟫
  have hsplit : ⟪D1 s, D1 ν⟫ = ⟪D1 s - DU s, D1 ν⟫ + ⟪DU s, D1 ν - DU ν⟫ + ⟪DU s, DU f⟫ := by
    rw [← h0, inner_sub_left, inner_sub_right]; ring
  have t1 : ⟪D1 s - DU s, D1 ν⟫ ≤ δ * ‖s‖ * (P * r) :=
    (real_inner_le_norm _ _).trans (mul_le_mul (hd s) hDν (norm_nonneg _)
      (mul_nonneg hδ (norm_nonneg _)))
  have t2 : ⟪DU s, D1 ν - DU ν⟫ ≤ ‖DU s‖ * (δ * (P ^ 2 * r)) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      ((hd ν).trans (mul_le_mul_of_nonneg_left hνr hδ)) (norm_nonneg _))
  have t3 : ⟪DU s, DU f⟫ ≤ ‖DU s‖ * (b * ε * (P ^ 2 * r)) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (hfν.trans (mul_le_mul_of_nonneg_left hνr (mul_nonneg hb hε))) (norm_nonneg _))
  have hmain : r ^ 2 ≤ r * (δ * P * ‖s‖ + (δ + b * ε) * P ^ 2 * ‖DU s‖) := by
    rw [hr2, hsplit]; nlinarith
  have hr0 : 0 ≤ r := norm_nonneg _
  have hRHS : 0 ≤ δ * P * ‖s‖ + (δ + b * ε) * P ^ 2 * ‖DU s‖ := by
    have := mul_nonneg hb hε
    have := norm_nonneg s; have := norm_nonneg (DU s)
    positivity
  rcases eq_or_lt_of_le hr0 with h | h
  · rw [← h]; exact hRHS
  · nlinarith

/-- `‖R1 D1* x‖ ≤ γ ‖x‖` on the `U`-slice, `γ = κ (δP + κP²(δ + bε)) + δ`. -/
theorem R1_on_slice_le (D1 DU : E →L[ℝ] F) (D1s DUs : F →L[ℝ] E) (R1 : E →L[ℝ] E) (QU : E →L[ℝ] C)
    (N1 NU : Submodule ℝ E)
    (h1 : ∀ (x : F) (s : E), ⟪x, D1 s⟫ = ⟪D1s x, s⟫) (hU : ∀ (x : F) (s : E), ⟪x, DU s⟫ = ⟪DUs x, s⟫)
    (hRn : ∀ s, ‖R1 s‖ ^ 2 = ⟪s, R1 s⟫) (hRim : ∀ s, ∃ ν ∈ N1, R1 s = D1s (D1 ν))
    (P δ b ε κ : ℝ) (hP : 0 ≤ P) (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hε : 0 ≤ ε) (hκ : 0 ≤ κ)
    (hPoinc : ∀ ν ∈ N1, ‖ν‖ ≤ P * ‖D1 ν‖) (hd : ∀ f, ‖D1 f - DU f‖ ≤ δ * ‖f‖)
    (hext : ∀ w : C, ∃ f : E, QU f = w ∧ ‖DU f‖ ≤ b * ‖w‖) (hNU : ∀ f, QU f = 0 → f ∈ NU)
    (hQN1 : ∀ ν ∈ N1, ‖QU ν‖ ≤ ε * ‖ν‖)
    (x : F) (hx : ∀ ν ∈ NU, ⟪DU (DUs x), DU ν⟫ = 0)
    (hS1 : ‖DUs x‖ ≤ κ * ‖x‖) (hS2 : ‖DU (DUs x)‖ ≤ κ * ‖DUs x‖) :
    ‖R1 (D1s x)‖ ≤ (κ * (δ * P + κ * P ^ 2 * (δ + b * ε)) + δ) * ‖x‖ := by
  have hRs := R1_harmonic_le D1 DU D1s R1 QU N1 NU h1 hRn hRim P δ b ε hP hδ hb hε hPoinc hd hext hNU
    hQN1 (DUs x) hx
  have hcontr : ∀ s, ‖R1 s‖ ≤ ‖s‖ := by
    intro s
    have h := hRn s
    have hcs : ⟪s, R1 s⟫ ≤ ‖s‖ * ‖R1 s‖ := real_inner_le_norm _ _
    rcases eq_or_lt_of_le (norm_nonneg (R1 s)) with h0 | h0
    · rw [← h0]; exact norm_nonneg s
    · nlinarith
  have hsplit : R1 (D1s x) = R1 (DUs x) + R1 (D1s x - DUs x) := by
    rw [map_sub]; abel
  have hdr := adj_drift D1 DU D1s DUs h1 hU δ hδ hd x
  have hA : ‖R1 (D1s x - DUs x)‖ ≤ δ * ‖x‖ := (hcontr _).trans hdr
  have hB : ‖R1 (DUs x)‖ ≤ κ * (δ * P + κ * P ^ 2 * (δ + b * ε)) * ‖x‖ := by
    have e1 : δ * P * ‖DUs x‖ ≤ δ * P * (κ * ‖x‖) :=
      mul_le_mul_of_nonneg_left hS1 (mul_nonneg hδ hP)
    have e2 : (δ + b * ε) * P ^ 2 * ‖DU (DUs x)‖ ≤ (δ + b * ε) * P ^ 2 * (κ * (κ * ‖x‖)) := by
      refine mul_le_mul_of_nonneg_left (hS2.trans (mul_le_mul_of_nonneg_left hS1 hκ)) ?_
      have := mul_nonneg hb hε
      positivity
    nlinarith
  calc ‖R1 (D1s x)‖ ≤ ‖R1 (DUs x)‖ + ‖R1 (D1s x - DUs x)‖ := by rw [hsplit]; exact norm_add_le _ _
    _ ≤ _ := by nlinarith

#print axioms adj_drift
#print axioms R1_harmonic_le
#print axioms R1_on_slice_le

end AdalyFormal.SliceCoerc
