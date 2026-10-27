import SC4c

/-!
# SC4d -- trigonometric lower bound for the non-zero modes, spectral gap `4/n²`, and the `ModeData` of the cell.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped ComplexInnerProductSpace BigOperators ComplexConjugate
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

section Gap
variable {n : ℕ}

/-- the zero mode index -/
def k0 (hn : 0 < n) : Cell n := fun _ => ⟨0, hn⟩

theorem sin_lower (n : ℕ) (hn : 0 < n) (θ : ℝ) (hθ1 : -Real.pi < θ) (hθ2 : θ ≤ Real.pi) (m : ℕ)
    (hm1 : 1 ≤ m) (hm2 : m < n) : 1 / (n : ℝ) ≤ Real.sin ((θ + 2 * Real.pi * (m : ℝ)) / (2 * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hm2R : (m : ℝ) + 1 ≤ n := by exact_mod_cast hm2
  set y : ℝ := (θ + 2 * Real.pi * (m : ℝ)) / (2 * n) with hy
  have hpi := Real.pi_pos
  have h2n : 0 < 2 * (n : ℝ) := by positivity
  have hy1 : Real.pi / (2 * n) ≤ y := by
    rw [hy]; apply div_le_div_of_nonneg_right _ h2n.le
    nlinarith
  have hy2 : y ≤ Real.pi - Real.pi / (2 * n) := by
    rw [hy, le_sub_iff_add_le, ← add_div, div_le_iff₀ h2n]
    have : Real.pi / (2 * n) * (2 * n) = Real.pi := by field_simp
    nlinarith
  have hpn : 0 < Real.pi / (2 * n) := by positivity
  set u : ℝ := min y (Real.pi - y) with hu
  have hu1 : Real.pi / (2 * n) ≤ u := le_min hy1 (by linarith)
  have hu2 : u ≤ Real.pi / 2 := by
    rcases le_total y (Real.pi - y) with h | h
    · rw [hu, min_eq_left h]; linarith
    · rw [hu, min_eq_right h]; linarith
  have hsin : Real.sin y = Real.sin u := by
    rcases le_total y (Real.pi - y) with h | h
    · rw [hu, min_eq_left h]
    · rw [hu, min_eq_right h, Real.sin_pi_sub]
  have h3 := Real.mul_le_sin (by linarith : 0 ≤ u) hu2
  rw [hsin]
  calc 1 / (n : ℝ) = 2 / Real.pi * (Real.pi / (2 * n)) := by field_simp
    _ ≤ 2 / Real.pi * u := mul_le_mul_of_nonneg_left hu1 (by positivity)
    _ ≤ Real.sin u := h3

theorem sg_sub_one_ge (hn : 0 < n) (z : Fin 3 → Circle) (k : Cell n) (μ : Fin 3) (hk : k μ ≠ ⟨0, hn⟩) :
    4 / (n : ℝ) ^ 2 ≤ ‖sg n z k μ - 1‖ ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold sg
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have hm1 : 1 ≤ (k μ : ℕ) := by
    by_contra h
    apply hk
    apply Fin.ext
    simp only [not_le] at h
    simpa using (by omega : (k μ : ℕ) = 0)
  have hm2 := (k μ).isLt
  have hθ := th_mem z μ
  have hs := sin_lower n hn (th z μ) hθ.1 hθ.2 (k μ : ℕ) hm1 hm2
  have e : ((th z μ + 2 * Real.pi * ((k μ : ℕ) : ℝ)) / (n : ℝ)) / 2
      = (th z μ + 2 * Real.pi * ((k μ : ℕ) : ℝ)) / (2 * n) := by field_simp
  rw [e]
  have hpos : 0 < Real.sin ((th z μ + 2 * Real.pi * ((k μ : ℕ) : ℝ)) / (2 * n)) :=
    lt_of_lt_of_le (by positivity) hs
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos]
  simp only [abs_two]
  have : 2 / (n : ℝ) ≤ 2 * Real.sin ((th z μ + 2 * Real.pi * ((k μ : ℕ) : ℝ)) / (2 * n)) := by
    have := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 / (n : ℝ) = 2 * (1 / n) := by ring
      _ ≤ _ := this
  have h2 : (2 / (n : ℝ)) ^ 2 ≤ (2 * Real.sin ((th z μ + 2 * Real.pi * ((k μ : ℕ) : ℝ)) / (2 * n))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) this 2
  calc 4 / (n : ℝ) ^ 2 = (2 / (n : ℝ)) ^ 2 := by ring
    _ ≤ _ := h2

theorem lam_ge (hn : 0 < n) (z : Fin 3 → Circle) (k : Cell n) (hk : k ≠ k0 hn) :
    4 / (n : ℝ) ^ 2 ≤ lam n z k := by
  have : ∃ μ, k μ ≠ ⟨0, hn⟩ := by
    by_contra h; push_neg at h; exact hk (funext h)
  obtain ⟨μ, hμ⟩ := this
  unfold lam
  calc 4 / (n : ℝ) ^ 2 ≤ ‖sg n z k μ - 1‖ ^ 2 := sg_sub_one_ge hn z k μ hμ
    _ ≤ ∑ ν, ‖sg n z k ν - 1‖ ^ 2 :=
      Finset.single_le_sum (f := fun ν => ‖sg n z k ν - 1‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ μ)

theorem gap_cell (hn : 0 < n) (z : Fin 3 → Circle) (f : CV n) (hf : ⟪pk n z (k0 hn), f⟫ = 0) :
    4 / (n : ℝ) ^ 2 * ‖f‖ ^ 2 ≤ Ef (cellSym hn z) f := by
  rw [Ef_parseval hn z f, ← parseval_pk hn z f, Finset.mul_sum]
  refine Finset.sum_le_sum (fun k _ => ?_)
  by_cases hk : k = k0 hn
  · subst hk; rw [hf]; simp
  · exact mul_le_mul_of_nonneg_right (lam_ge hn z k hk) (by positivity)

theorem norm_pk (hn : 0 < n) (z : Fin 3 → Circle) (k : Cell n) : ‖pk n z k‖ = 1 := by
  have h := inner_pk hn z k k
  rw [if_pos rfl, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖pk n z k‖ ^ 2 = 1 := by
    have : ((‖pk n z k‖ : ℝ) : ℂ) ^ 2 = ((1 : ℝ) : ℂ) := by simpa using h
    exact_mod_cast this
  have h3 : 0 ≤ ‖pk n z k‖ := norm_nonneg _
  nlinarith

/-- the `ModeData` of the twisted cell: lowest plane wave and the gap `4/n²` -/
noncomputable def cellMode (hn : 0 < n) (z : Fin 3 → Circle) : ModeData (cellSym hn z) where
  e0 := pk n z (k0 hn)
  norm_e0 := norm_pk hn z (k0 hn)
  l0 := lam n z (k0 hn)
  l0_nonneg := lam_nonneg z _
  lap_e0 := Lap_pk hn z (k0 hn)
  G := 4 / (n : ℝ) ^ 2
  G_pos := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  gap := fun f hf => gap_cell hn z f hf

end Gap

#print axioms gap_cell
#print axioms cellMode

end AdalyFormal.ScaledCoercivity
