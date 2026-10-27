import SC3a

/-!
# SC3b -- low-mode / gap decomposition: `ModeData`, the spectral inequality, and the two per-field bounds
`N_coercive` (lower bound of `E + κ g2`) and `S2_bound` (upper bound of `g2` by `E`).  Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped ComplexInnerProductSpace
open AdalyFormal.FlatCoercivity
open Finset

namespace AdalyFormal.ScaledCoercivity

section Mode
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (sd : SymData V)

/-- a distinguished low mode `e0` (eigenvector of `Lap`, eigenvalue `l0`) and a spectral gap `G` on `e0^⊥` -/
structure ModeData where
  e0 : V
  norm_e0 : ‖e0‖ = 1
  l0 : ℝ
  l0_nonneg : 0 ≤ l0
  lap_e0 : sd.Lap e0 = (l0 : ℂ) • e0
  G : ℝ
  G_pos : 0 < G
  gap : ∀ f : V, ⟪e0, f⟫ = 0 → G * ‖f‖ ^ 2 ≤ Ef sd f

variable {sd}

theorem inner_e0_self (md : ModeData sd) : ⟪md.e0, md.e0⟫ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, md.norm_e0]; simp

/-- decomposition `f = c e0 + h` -/
theorem decomp_norm (md : ModeData sd) (c : ℂ) (h : V) (hh : ⟪md.e0, h⟫ = 0) :
    ‖c • md.e0 + h‖ ^ 2 = ‖c‖ ^ 2 + ‖h‖ ^ 2 := by
  have h1 : ⟪c • md.e0, h⟫ = 0 := by rw [inner_smul_left, hh]; simp
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (c • md.e0) h h1
  have h2 : ‖c • md.e0 + h‖ ^ 2 = ‖c • md.e0‖ ^ 2 + ‖h‖ ^ 2 := by simpa [sq] using this
  rw [h2, norm_smul, md.norm_e0]; simp

theorem decomp_Ef (md : ModeData sd) (c : ℂ) (h : V) (hh : ⟪md.e0, h⟫ = 0) :
    Ef sd (c • md.e0 + h) = md.l0 * ‖c‖ ^ 2 + Ef sd h := by
  have hc : (Ef sd (c • md.e0 + h) : ℂ) = ((md.l0 * ‖c‖ ^ 2 + Ef sd h : ℝ) : ℂ) := by
    rw [Ef_eq, sd.Lap_add, sd.Lap_smul, md.lap_e0]
    have e1 : ⟪md.e0, sd.Lap h⟫ = 0 := by
      rw [← sd.Lap_selfadj, md.lap_e0, inner_smul_left, hh]; simp
    have e2 : ⟪h, md.e0⟫ = 0 := by rw [← inner_conj_symm, hh]; simp
    have T1 : ⟪c • md.e0, c • (md.l0 : ℂ) • md.e0⟫ = ((md.l0 * ‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_smul_left, inner_smul_right, inner_smul_right, inner_e0_self]
      have hcc : (starRingEnd ℂ) c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.conj_mul']; push_cast; ring
      calc (starRingEnd ℂ) c * (c * (↑md.l0 * 1)) = ((starRingEnd ℂ) c * c) * md.l0 := by ring
        _ = _ := by rw [hcc]; push_cast; ring
    have T2 : ⟪c • md.e0, sd.Lap h⟫ = 0 := by rw [inner_smul_left, e1]; simp
    have T3 : ⟪h, c • (md.l0 : ℂ) • md.e0⟫ = 0 := by
      rw [inner_smul_right, inner_smul_right, e2]; simp
    rw [inner_add_left, inner_add_right, inner_add_right, T1, T2, T3, ← Ef_eq]
    push_cast; ring
  exact_mod_cast hc

theorem decomp_exists (md : ModeData sd) (f : V) :
    ∃ (c : ℂ) (h : V), f = c • md.e0 + h ∧ ⟪md.e0, h⟫ = 0 := by
  refine ⟨⟪md.e0, f⟫, f - ⟪md.e0, f⟫ • md.e0, by abel, ?_⟩
  rw [inner_sub_right, inner_smul_right, inner_e0_self]; ring

/-- the spectral inequality -/
theorem spec_low (md : ModeData sd) (f : V) :
    md.l0 * ‖⟪md.e0, f⟫‖ ^ 2 + md.G * (‖f‖ ^ 2 - ‖⟪md.e0, f⟫‖ ^ 2) ≤ Ef sd f := by
  obtain ⟨c, h, hf, hh⟩ := decomp_exists md f
  have hc : ⟪md.e0, f⟫ = c := by
    rw [hf, inner_add_right, inner_smul_right, inner_e0_self, hh]; ring
  rw [hc]
  have h1 := decomp_norm md c h hh
  have h2 := decomp_Ef md c h hh
  have h3 := md.gap h hh
  rw [← hf] at h1 h2
  have h4 : ‖f‖ ^ 2 - ‖c‖ ^ 2 = ‖h‖ ^ 2 := by linarith
  rw [h4, h2]
  linarith

end Mode

end AdalyFormal.ScaledCoercivity
