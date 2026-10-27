import SC3b

/-!
# SC3c -- per-component and per-field bounds from the low mode `e0` and the gap.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped ComplexInnerProductSpace
open AdalyFormal.FlatCoercivity
open Finset

namespace AdalyFormal.ScaledCoercivity

section Comp
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {sd : SymData V} (md : ModeData sd)

theorem Ef_ge_gap (f : V) (c : ℂ) (h : V) (hf : f = c • md.e0 + h) (hh : ⟪md.e0, h⟫ = 0) :
    md.G * ‖h‖ ^ 2 ≤ Ef sd f := by
  rw [hf, decomp_Ef md c h hh]
  have := md.gap h hh
  have h0 : 0 ≤ md.l0 * ‖c‖ ^ 2 := mul_nonneg md.l0_nonneg (by positivity)
  linarith

theorem comp_N (κ A q0 : ℝ) (hκ : 0 ≤ κ) (hA : 0 < A) (hq0 : 0 ≤ q0)
    (hq : ∀ μ, q0 ≤ ‖sd.Qm μ md.e0‖) (hAq : ∀ μ x, ‖sd.Qm μ x‖ ≤ A * ‖x‖) (μ : Fin 3) (f : V) :
    min (κ * q0 ^ 2 / 4) (md.G * q0 ^ 2 / (4 * A ^ 2 + q0 ^ 2)) * ‖f‖ ^ 2
      ≤ Ef sd f + κ * ‖sd.Qm μ f‖ ^ 2 := by
  obtain ⟨c, h, hf, hh⟩ := decomp_exists md f
  have hn := decomp_norm md c h hh
  rw [← hf] at hn
  have hQ : sd.Qm μ f = c * sd.Qm μ md.e0 + sd.Qm μ h := by
    rw [hf, Qm_add, Qm_smul]
  have h1 : q0 * ‖c‖ - A * ‖h‖ ≤ ‖sd.Qm μ f‖ := by
    have e : c * sd.Qm μ md.e0 = sd.Qm μ f - sd.Qm μ h := by rw [hQ]; ring
    have h2 : ‖c * sd.Qm μ md.e0‖ ≤ ‖sd.Qm μ f‖ + ‖sd.Qm μ h‖ := by
      rw [e]; exact norm_sub_le _ _
    have h3 : q0 * ‖c‖ ≤ ‖c * sd.Qm μ md.e0‖ := by
      rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_left (hq μ) (norm_nonneg _)
    have h4 := hAq μ h
    linarith
  have := Ncomp (E := Ef sd f) (x := ‖c‖) (y := ‖h‖) (q := ‖sd.Qm μ f‖) (G := md.G) (K := κ)
    (A := A) (q0 := q0) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) md.G_pos hκ hA hq0
    (Ef_ge_gap md f c h hf hh) h1
  rw [hn]
  exact this

theorem comp_S2 (hl0 : 0 < md.l0) (A : ℝ) (hA : 0 ≤ A) (hAq : ∀ μ x, ‖sd.Qm μ x‖ ≤ A * ‖x‖)
    (μ : Fin 3) (f : V) :
    ‖sd.Qm μ f‖ ^ 2 ≤ A ^ 2 * (1 / md.l0 + 1 / md.G) * Ef sd f := by
  obtain ⟨c, h, hf, hh⟩ := decomp_exists md f
  have hQ : sd.Qm μ f = c * sd.Qm μ md.e0 + sd.Qm μ h := by
    rw [hf, Qm_add, Qm_smul]
  have h1 : ‖sd.Qm μ f‖ ≤ A * (‖c‖ + ‖h‖) := by
    have h2 : ‖sd.Qm μ f‖ ≤ ‖c * sd.Qm μ md.e0‖ + ‖sd.Qm μ h‖ := by rw [hQ]; exact norm_add_le _ _
    have h3 : ‖c * sd.Qm μ md.e0‖ ≤ ‖c‖ * A := by
      rw [norm_mul]
      have := hAq μ md.e0
      rw [md.norm_e0, mul_one] at this
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
    have h4 := hAq μ h
    nlinarith
  have hE : md.l0 * ‖c‖ ^ 2 + md.G * ‖h‖ ^ 2 ≤ Ef sd f := by
    rw [hf, decomp_Ef md c h hh]
    have := md.gap h hh
    linarith
  exact S2comp (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) md.G_pos hl0 hA hE h1

theorem N_coercive (κ A q0 : ℝ) (hκ : 0 ≤ κ) (hA : 0 < A) (hq0 : 0 ≤ q0)
    (hq : ∀ μ, q0 ≤ ‖sd.Qm μ md.e0‖) (hAq : ∀ μ x, ‖sd.Qm μ x‖ ≤ A * ‖x‖) (w : Fin 3 → V) :
    min (κ * q0 ^ 2 / 4) (md.G * q0 ^ 2 / (4 * A ^ 2 + q0 ^ 2)) * ∑ μ, ‖w μ‖ ^ 2
      ≤ Eb sd w + κ * g2b sd w := by
  unfold Eb g2b
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun μ _ => ?_)
  exact comp_N md κ A q0 hκ hA hq0 hq hAq μ (w μ)

theorem S2_bound (hl0 : 0 < md.l0) (A : ℝ) (hA : 0 ≤ A) (hAq : ∀ μ x, ‖sd.Qm μ x‖ ≤ A * ‖x‖)
    (w : Fin 3 → V) : g2b sd w ≤ A ^ 2 * (1 / md.l0 + 1 / md.G) * Eb sd w := by
  unfold Eb g2b
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun μ _ => ?_)
  exact comp_S2 md hl0 A hA hAq μ (w μ)

end Comp

#print axioms N_coercive
#print axioms S2_bound

end AdalyFormal.ScaledCoercivity
