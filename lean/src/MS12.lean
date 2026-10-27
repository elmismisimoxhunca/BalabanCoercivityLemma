import MS11

/-!
# MS12 -- non-vacuity controls for the site layer

* `wNormSq_pos` : `x ∈ Ω₀`, `f x ≠ 0` ⇒ `0 < wNormSq G f` (the S1 left side is not identically zero).
* `form_pos_M1` : under the MS9 regime with `216ρ_T² < 1`, `⟪f, Δ'_a f⟫ > 0` for every `f` not vanishing on `Ω₀` — the conclusion of
  `site_coercive_M1` has content on every admissible tower with `Ω₀ ≠ ∅`.
* `regime_flat` : the flat configuration satisfies the MS9 link and plaquette clauses for every `ρ ≥ 0` (the hypothesis set is
  inhabited for every admissible tower).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1Site

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.CurvBlock (dv pw)

variable {Lf : PeriodicLatticeExtent}

theorem wNormSq_pos (G : TowerGeom Lf) (hell : 0 < G.ell) (f : SiteL2 Lf) (x : PeriodicLatticeSite Lf)
    (hx : x ∈ G.Om0) (hfx : f x ≠ 0) : 0 < wNormSq G f := by
  unfold wNormSq
  have hterm : 0 < ‖siteMask G.Om0 f x‖ ^ 2 / ((G.ell : ℝ) ^ stratG G x) ^ 2 := by
    rw [siteMask_on _ _ _ hx]
    have h1 : 0 < ‖f x‖ := norm_pos_iff.mpr hfx
    have h2 : (0 : ℝ) < (G.ell : ℝ) ^ stratG G x := pow_pos (by exact_mod_cast hell) _
    positivity
  exact lt_of_lt_of_le hterm (Finset.single_le_sum (f := fun y => ‖siteMask G.Om0 f y‖ ^ 2 / ((G.ell : ℝ) ^ stratG G y) ^ 2)
    (fun y _ => div_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_univ x))

theorem form_pos_M1 (ell M R k : ℕ) (hell : 2 ≤ ell) {S : Tower Lf} (hS : Admissible ell M R k S)
    (hRM : 18 ≤ R * M) (hbig : ∀ σ, 4 * ell ^ k < Lf σ + 1)
    (U : Cfg Lf) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ) (hsmall : 4000000 * (ell : ℝ) ^ 2 * ρ ≤ 1)
    (hlink : ∀ j0, j0 ≤ k → ∀ b : Bond Lf, b.1 ∈ S.Om j0 → periodicLatticeShift b.1 b.2 ∈ S.Om j0 →
      dv (U b) ≤ ρ / (ell : ℝ) ^ j0)
    (hplaq : ∀ j0, j0 ≤ k → ∀ (y : PeriodicLatticeSite Lf) (ν μ : Fin 3),
      y ∈ S.Om j0 → coarseShift y 1 ν ∈ S.Om j0 → coarseShift y 1 μ ∈ S.Om j0 →
      coarseShift (coarseShift y 1 ν) 1 μ ∈ S.Om j0 → dv (pw 1 U y ν μ) ≤ ρ / (ell : ℝ) ^ (2 * j0))
    (h216 : 216 * (((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ) ^ 2 < 1)
    (f : SiteL2 Lf) (x : PeriodicLatticeSite Lf) (hx : x ∈ S.Om 0) (hfx : f x ≠ 0) :
    0 < ⟪f, DelpA (geomOf ell k S) U a f⟫ := by
  have hS1 := site_coercive_M1 ell M R k hell hS hRM hbig U a ha ρ hρ hsmall hlink hplaq f
  have hw := wNormSq_pos (geomOf ell k S) (show 0 < ell by omega) f x hx hfx
  have hm : 0 < max 6 (16 / (3 * a)) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have h1 : 0 < (1 - 216 * (((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ) ^ 2) * wNormSq (geomOf ell k S) f :=
    mul_pos (by linarith) hw
  by_contra hneg
  push Not at hneg
  have := mul_le_mul_of_nonneg_left hneg hm.le
  linarith

theorem dv_one' : dv (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = 0 := AdalyFormal.CurvBlock.dv_one

theorem regime_flat (ell M R k : ℕ) {S : Tower Lf} (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∀ j0, j0 ≤ k → ∀ b : Bond Lf, b.1 ∈ S.Om j0 → periodicLatticeShift b.1 b.2 ∈ S.Om j0 →
      dv (trivialU Lf b) ≤ ρ / (ell : ℝ) ^ j0) ∧
    (∀ j0, j0 ≤ k → ∀ (y : PeriodicLatticeSite Lf) (ν μ : Fin 3),
      y ∈ S.Om j0 → coarseShift y 1 ν ∈ S.Om j0 → coarseShift y 1 μ ∈ S.Om j0 →
      coarseShift (coarseShift y 1 ν) 1 μ ∈ S.Om j0 → dv (pw 1 (trivialU Lf) y ν μ) ≤ ρ / (ell : ℝ) ^ (2 * j0)) := by
  refine ⟨fun j0 _ b _ _ => ?_, fun j0 _ y ν μ _ _ _ _ => ?_⟩
  · show dv 1 ≤ _
    rw [dv_one']; exact div_nonneg hρ (by positivity)
  · show dv (1 * 1 * (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)⁻¹ * (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)⁻¹) ≤ _
    simp only [mul_one, inv_one]
    rw [dv_one']; exact div_nonneg hρ (by positivity)

#print axioms wNormSq_pos
#print axioms form_pos_M1
#print axioms regime_flat

#print axioms dv_one'

end AdalyFormal.M1Site
