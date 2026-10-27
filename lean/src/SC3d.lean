import SC3c

/-!
# SC3d -- the one-dimensional "K-structure": lower bounds for the projected-divergence slack `S`.
 * trivial twist: `S ≥ ‖D*w‖²`;
 * non-trivial twist: with `g = Lap⁻¹ ε`, `S ≥ ‖D*w‖² - |⟨g, D*w⟩|²/‖g‖²`.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped ComplexInnerProductSpace
open AdalyFormal.FlatCoercivity
open Finset

namespace AdalyFormal.ScaledCoercivity

section K
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable (sd : SymData V)

theorem Lap_zero : sd.Lap (0 : V) = 0 := by
  have := sd.Lap_smul (0 : ℂ) (0 : V)
  simpa using this

theorem Lap_eps_trivial (hall : ∀ μ, sd.ph μ = 1) : sd.Lap sd.eps = 0 := by
  unfold SymData.Lap
  refine Finset.sum_eq_zero (fun μ _ => ?_)
  have : sd.D μ sd.eps = 0 := (sd.D_eq_zero_iff μ _).mpr (sd.eps_fixed hall μ)
  rw [this]; unfold SymData.Ds; simp

/-- at trivial twist `Lap` maps onto `ε^⊥` -/
theorem Lap_range_trivial (hall : ∀ μ, sd.ph μ = 1) (f : V) (hf : ⟪sd.eps, f⟫ = 0) :
    ∃ u, ⟪sd.eps, u⟫ = 0 ∧ sd.Lap u = f := by
  have hsym : sd.LapL.IsSymmetric := fun x y => sd.Lap_selfadj x y
  have horth := hsym.orthogonal_range
  have hf2 : f ∈ (LinearMap.ker sd.LapL)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    have hx2 : sd.Lap x = 0 := hx
    have h3 := sd.Lap_eq_zero x hx2
    obtain ⟨c, hc⟩ := sd.fixed_span hall x h3
    rw [hc, inner_smul_left, hf]; simp
  have hrange : f ∈ LinearMap.range sd.LapL := by
    rw [← horth] at hf2
    rwa [Submodule.orthogonal_orthogonal] at hf2
  obtain ⟨u0, hu0⟩ := hrange
  have hu0' : sd.Lap u0 = f := hu0
  have hne := sd.eps_inner_ne
  refine ⟨u0 - (⟪sd.eps, u0⟫ / ⟪sd.eps, sd.eps⟫) • sd.eps, ?_, ?_⟩
  · rw [inner_sub_right, inner_smul_right]; field_simp; ring
  · rw [sd.Lap_sub, sd.Lap_smul, Lap_eps_trivial sd hall, hu0']; simp

theorem S_ge_trivial (hall : ∀ μ, sd.ph μ = 1) (w : Fin 3 → V) (S : ℝ) (hS0 : 0 ≤ S)
    (hS : ∀ u, ⟪sd.eps, u⟫ = 0 → ‖⟪sd.Dstar w, sd.Lap u⟫‖ ^ 2 ≤ S * ‖sd.Lap u‖ ^ 2) :
    ‖sd.Dstar w‖ ^ 2 ≤ S := by
  obtain ⟨u, hu, hLu⟩ := Lap_range_trivial sd hall (sd.Dstar w) (inner_eps_Dstar sd hall w)
  have h := hS u hu
  rw [hLu] at h
  have h1 : ⟪sd.Dstar w, sd.Dstar w⟫ = ((‖sd.Dstar w‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [h1] at h
  have h2 : ‖((‖sd.Dstar w‖ ^ 2 : ℝ) : ℂ)‖ = ‖sd.Dstar w‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [h2] at h
  by_cases h0 : ‖sd.Dstar w‖ = 0
  · rw [h0]; simpa using hS0
  · have hp : 0 < ‖sd.Dstar w‖ ^ 2 := by positivity
    have : (‖sd.Dstar w‖ ^ 2) * (‖sd.Dstar w‖ ^ 2) ≤ S * ‖sd.Dstar w‖ ^ 2 := by nlinarith [h]
    exact le_of_mul_le_mul_right this hp

/-- non-trivial twist -/
theorem S_ge_nontrivial (g : V) (hg : sd.Lap g = sd.eps) (hg0 : g ≠ 0) (μ0 : Fin 3) (hμ0 : sd.ph μ0 ≠ 1)
    (w : Fin 3 → V) (S : ℝ) (hS0 : 0 ≤ S)
    (hS : ∀ u, ⟪sd.eps, u⟫ = 0 → ‖⟪sd.Dstar w, sd.Lap u⟫‖ ^ 2 ≤ S * ‖sd.Lap u‖ ^ 2) :
    ‖sd.Dstar w‖ ^ 2 - ‖⟪g, sd.Dstar w⟫‖ ^ 2 / ‖g‖ ^ 2 ≤ S := by
  set f := sd.Dstar w with hf
  have hgg : ⟪g, g⟫ = ((‖g‖ ^ 2 : ℝ) : ℂ) := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hgn : (‖g‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hgn' : ⟪g, g⟫ ≠ 0 := by rw [hgg]; exact_mod_cast hgn
  set c : ℂ := ⟪g, f⟫ / ⟪g, g⟫ with hc
  set fp : V := f - c • g with hfp
  have hgfp : ⟪g, fp⟫ = 0 := by
    rw [hfp, inner_sub_right, inner_smul_right, hc]; field_simp; ring
  obtain ⟨u, hu⟩ := sd.Lap_surj μ0 hμ0 fp
  have hεu : ⟪sd.eps, u⟫ = 0 := by
    rw [← hg, sd.Lap_selfadj, hu, hgfp]
  have h := hS u hεu
  rw [hu] at h
  have hffp : ⟪f, fp⟫ = ((‖fp‖ ^ 2 : ℝ) : ℂ) := by
    have : f = fp + c • g := by rw [hfp]; abel
    rw [this, inner_add_left, inner_smul_left, hgfp]
    rw [inner_self_eq_norm_sq_to_K]; simp
  rw [hffp] at h
  have h2 : ‖((‖fp‖ ^ 2 : ℝ) : ℂ)‖ = ‖fp‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [h2] at h
  have hfp2 : ‖fp‖ ^ 2 ≤ S := by
    by_cases h0 : ‖fp‖ = 0
    · rw [h0]; simpa using hS0
    · have hp : 0 < ‖fp‖ ^ 2 := by positivity
      have : (‖fp‖ ^ 2) * (‖fp‖ ^ 2) ≤ S * ‖fp‖ ^ 2 := by nlinarith [h]
      exact le_of_mul_le_mul_right this hp
  have hpyth : ‖f‖ ^ 2 = ‖fp‖ ^ 2 + ‖c • g‖ ^ 2 := by
    have h1 : ⟪fp, c • g⟫ = 0 := by
      rw [inner_smul_right, ← inner_conj_symm, hgfp]; simp
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) fp (c • g) h1
    have h3 : ‖fp + c • g‖ ^ 2 = ‖fp‖ ^ 2 + ‖c • g‖ ^ 2 := by simpa [sq] using this
    have e : f = fp + c • g := by rw [hfp]; abel
    rw [← e] at h3; exact h3
  have hcg : ‖c • g‖ ^ 2 = ‖⟪g, f⟫‖ ^ 2 / ‖g‖ ^ 2 := by
    rw [norm_smul, mul_pow, hc, norm_div, hgg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), div_pow]
    field_simp
  rw [hcg] at hpyth
  linarith

end K

#print axioms S_ge_trivial
#print axioms S_ge_nontrivial

end AdalyFormal.ScaledCoercivity
