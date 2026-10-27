import CG6d

/-!
# CG6e -- wrapper for the cyclic cell boxes, and the elementary bounds used by `CoverGeomBoxU`
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

namespace AdalyFormal.CoverGeom

open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.StatementLane2

variable {L : PeriodicLatticeExtent}

theorem cellbox_wrap {ell M R c k : ℕ} {S : Tower L} (s : ℕ) (hs : 2 ≤ s)
    (hadm : Admissible ell M R k S) (hcov : CoversOm0p ell M c k S)
    (n u : Fin 3 → ℕ) (hn : ∀ τ, L τ + 1 = s * n τ) (hu : ∀ τ, u τ < n τ)
    (two : Fin 3 → Prop) [DecidablePred two] (hfree : ∃ ρ, ¬ two ρ)
    {Om : Set (PeriodicLatticeSite L)} (hOm0 : Om ⊆ S.Om 0)
    (hΩ : ∀ x ∈ CellReg s n u two, x ∈ Om)
    (hWidx : ∀ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M c k S sites i →
      (∃ y ∈ sites, y ∈ CellReg s n u two) → s ∣ bigSide M ell i) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M c k S sites i ∧
      CellReg s n u two ⊆ sites := by
  obtain ⟨ρ, hρ⟩ := hfree
  fin_cases ρ
  · exact cellbox_core s hs hadm hcov n u hn hu two 1 2 0 (by decide) (by decide) (by decide)
      (by intro τ; fin_cases τ <;> simp) hρ hOm0 hΩ hWidx
  · exact cellbox_core s hs hadm hcov n u hn hu two 0 2 1 (by decide) (by decide) (by decide)
      (by intro τ; fin_cases τ <;> simp) hρ hOm0 hΩ hWidx
  · exact cellbox_core s hs hadm hcov n u hn hu two 0 1 2 (by decide) (by decide) (by decide)
      (by intro τ; fin_cases τ <;> simp) hρ hOm0 hΩ hWidx

theorem t_bounds {X Ui U1 : ℝ} (hX0 : 0 ≤ X) (hXh : X ≤ 1 / 2) (hUi0 : 0 ≤ Ui) (hle : Ui ≤ U1) (hU1' : U1 ≤ 1) :
    X * Ui ≤ X * U1 ∧ (1 + 4 * (X * Ui)) * (X * Ui ^ 2) ≤ 3 * (X * U1 ^ 2) ∧
      2 * ((1 + 4 * (X * Ui)) * (X * Ui ^ 2)) + 2 * (X * Ui) ^ 2 ≤ 7 * (X * U1 ^ 2) := by
  have hU1 : 0 ≤ U1 := hUi0.trans hle
  have h1 : X * Ui ≤ X * U1 := mul_le_mul_of_nonneg_left hle hX0
  have hsq : Ui ^ 2 ≤ U1 ^ 2 := pow_le_pow_left₀ hUi0 hle 2
  have h2 : X * Ui ^ 2 ≤ X * U1 ^ 2 := mul_le_mul_of_nonneg_left hsq hX0
  have ht1 : X * Ui ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_left (hle.trans hU1') hX0]
  have ht1' : 0 ≤ X * Ui := mul_nonneg hX0 hUi0
  have h3 : (1 + 4 * (X * Ui)) ≤ 3 := by linarith
  have hX2 : 0 ≤ X * Ui ^ 2 := mul_nonneg hX0 (sq_nonneg _)
  have h4 : (1 + 4 * (X * Ui)) * (X * Ui ^ 2) ≤ 3 * (X * U1 ^ 2) := by
    calc (1 + 4 * (X * Ui)) * (X * Ui ^ 2) ≤ 3 * (X * Ui ^ 2) := mul_le_mul_of_nonneg_right h3 hX2
      _ ≤ 3 * (X * U1 ^ 2) := by linarith
  refine ⟨h1, h4, ?_⟩
  have h5 : (X * Ui) ^ 2 ≤ (X * U1) ^ 2 := pow_le_pow_left₀ ht1' h1 2
  have h6 : (X * U1) ^ 2 ≤ (1 / 2) * (X * U1 ^ 2) := by
    have : (X * U1) ^ 2 = X * (X * U1 ^ 2) := by ring
    rw [this]
    have hh : 0 ≤ X * U1 ^ 2 := mul_nonneg hX0 (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right hXh hh
  linarith

end AdalyFormal.CoverGeom
