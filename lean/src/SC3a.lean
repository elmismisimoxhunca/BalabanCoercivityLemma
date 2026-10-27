import GFC5
import SC2

/-!
# SC3a -- abstract (SymData) basics for the explicit cell theorem: energy forms, linearity of `Qm`,
`Qm` operator bound, commutation `Lap ∘ D = D ∘ Lap`, range of `Lap` at trivial twist.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped ComplexInnerProductSpace
open AdalyFormal.FlatCoercivity
open Finset

namespace AdalyFormal.ScaledCoercivity

section Abs
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (sd : SymData V)

/-- `E1(f) = Σ_ν ‖D_ν f‖²` -/
noncomputable def Ef (f : V) : ℝ := ∑ ν, ‖sd.D ν f‖ ^ 2
noncomputable def Eb (w : Fin 3 → V) : ℝ := ∑ μ, Ef sd (w μ)
noncomputable def g1b (w : Fin 3 → V) : ℝ :=
  (1 / 2 : ℝ) * ∑ μ, ∑ ν, ‖sd.D μ (w ν) - sd.D ν (w μ)‖ ^ 2
noncomputable def g2b (w : Fin 3 → V) : ℝ := ∑ μ, ‖sd.Qm μ (w μ)‖ ^ 2

theorem Ef_nonneg (f : V) : 0 ≤ Ef sd f := Finset.sum_nonneg (fun _ _ => by positivity)
theorem Eb_nonneg (w : Fin 3 → V) : 0 ≤ Eb sd w := Finset.sum_nonneg (fun μ _ => Ef_nonneg sd _)
theorem g2b_nonneg (w : Fin 3 → V) : 0 ≤ g2b sd w := Finset.sum_nonneg (fun _ _ => by positivity)

theorem weitz_b (w : Fin 3 → V) : g1b sd w + ‖sd.Dstar w‖ ^ 2 = Eb sd w := by
  have h := sd.weitzenbock w
  unfold g1b Eb Ef SymData.Dstar
  exact h

theorem Ef_eq (f : V) : ((Ef sd f : ℝ) : ℂ) = ⟪f, sd.Lap f⟫ := by
  rw [sd.inner_Lap]
  unfold Ef
  push_cast
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem D_sum {ι : Type*} (s : Finset ι) (μ : Fin 3) (f : ι → V) :
    sd.D μ (∑ i ∈ s, f i) = ∑ i ∈ s, sd.D μ (f i) := by
  unfold SymData.D
  rw [map_sum, Finset.sum_sub_distrib]

theorem Lap_D (μ : Fin 3) (x : V) : sd.Lap (sd.D μ x) = sd.D μ (sd.Lap x) := by
  unfold SymData.Lap
  rw [D_sum]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [sd.D_D ν μ, sd.Ds_D ν μ]

theorem Qm_add (μ : Fin 3) (x y : V) : sd.Qm μ (x + y) = sd.Qm μ x + sd.Qm μ y := by
  unfold SymData.Qm
  have : ∀ i : ℕ, (sd.S μ)^[i] (x + y) = (sd.S μ)^[i] x + (sd.S μ)^[i] y := by
    intro i
    rw [← sd.Sl_pow_apply, ← sd.Sl_pow_apply, ← sd.Sl_pow_apply, map_add]
  simp only [this, Finset.sum_add_distrib, inner_add_right]

theorem Qm_smul (μ : Fin 3) (c : ℂ) (x : V) : sd.Qm μ (c • x) = c * sd.Qm μ x := by
  unfold SymData.Qm
  have : ∀ i : ℕ, (sd.S μ)^[i] (c • x) = c • (sd.S μ)^[i] x := by
    intro i
    rw [← sd.Sl_pow_apply, ← sd.Sl_pow_apply, map_smul]
  simp only [this, ← Finset.smul_sum, inner_smul_right]

theorem Qm_sub (μ : Fin 3) (x y : V) : sd.Qm μ (x - y) = sd.Qm μ x - sd.Qm μ y := by
  have : x - y = x + (-1 : ℂ) • y := by rw [neg_smul, one_smul, sub_eq_add_neg]
  rw [this, Qm_add, Qm_smul]; ring

theorem norm_iter (μ : Fin 3) (i : ℕ) (x : V) : ‖(sd.S μ)^[i] x‖ = ‖x‖ := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', LinearIsometryEquiv.norm_map, ih]

theorem Qm_norm_le (μ : Fin 3) (x : V) : ‖sd.Qm μ x‖ ≤ (sd.n : ℝ) * ‖sd.eps‖ * ‖x‖ := by
  unfold SymData.Qm
  calc ‖⟪sd.eps, ∑ i ∈ Finset.range sd.n, (sd.S μ)^[i] x⟫‖
      ≤ ‖sd.eps‖ * ‖∑ i ∈ Finset.range sd.n, (sd.S μ)^[i] x‖ := norm_inner_le_norm _ _
    _ ≤ ‖sd.eps‖ * (∑ i ∈ Finset.range sd.n, ‖(sd.S μ)^[i] x‖) :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖sd.eps‖ * ((sd.n : ℝ) * ‖x‖) := by
        simp only [norm_iter, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (sd.n : ℝ) * ‖sd.eps‖ * ‖x‖ := by ring

/-- `Dstar` is orthogonal to `eps` at trivial twist -/
theorem inner_eps_Ds (hall : ∀ μ, sd.ph μ = 1) (μ : Fin 3) (y : V) : ⟪sd.eps, sd.Ds μ y⟫ = 0 := by
  have h1 : sd.D μ sd.eps = 0 := (sd.D_eq_zero_iff μ _).mpr (sd.eps_fixed hall μ)
  rw [← inner_conj_symm, sd.inner_Ds, h1]
  simp

theorem inner_eps_Dstar (hall : ∀ μ, sd.ph μ = 1) (w : Fin 3 → V) : ⟪sd.eps, sd.Dstar w⟫ = 0 := by
  unfold SymData.Dstar
  rw [inner_sum]
  exact Finset.sum_eq_zero (fun μ _ => inner_eps_Ds sd hall μ _)

end Abs

#print axioms Qm_norm_le
#print axioms Lap_D
#print axioms weitz_b

end AdalyFormal.ScaledCoercivity
