import UD11
import M2B10

/-!
# UD12 -- non-vacuity witnesses (lane m2_unitcharts_20261014)

1. `zc_witness_*`: exhaustive `decide` over all pairs `(a, b)` on `Z/24` of the bounds of `off_bounds` (blocks `B = 1`, `B = 2`, radius `r = 3`) -- an independent
   check of the arithmetic of UD1 (the proofs there are by `omega`).
2. `chart_of_class_nonvac`: the hypotheses of `chart_of_class` hold simultaneously at `ell = 2`, `M = 32`, `R = 23`, `k = 1`, the full tower, `Λ = univ`, a non-flat
   configuration `Ufield η χ` of the printed class, centre `q = 0`, radius `r = 32`; the conclusion (a gauge `g` and an `M1Regular` `V` agreeing with `U^g` on the ball) is delivered.
   (`R = 23` is what `D + 21 M ≤ R M` needs at `M = 32`; M2B10's `R = 18` does not satisfy it.)
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2UnitCharts

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt)
open AdalyFormal.M1 (M1Regular ufield_M1Regular perCube_of_M1)

example : offN 24 (zc 24 1 7) 7 = 5 := by decide
example : ∀ a < 24, ∀ b < 24, pcd 24 a b ≤ 3 →
    5 ≤ offN 24 (zc 24 1 a) b + 3 ∧ offN 24 (zc 24 1 a) b + 1 ≤ 6 * 1 + 3 := by decide
example : ∀ a < 24, ∀ b < 24, pcd 24 a b ≤ 7 →
    5 * 2 ≤ offN 24 (zc 24 2 a) b + 7 ∧ offN 24 (zc 24 2 a) b + 1 ≤ 6 * 2 + 7 := by decide
example : ∀ a < 24, ∀ b < 24, offN 24 (zc 24 2 a) b < 12 * 2 → pcd 24 a b ≤ 7 * 2 := by decide

theorem chart_of_class_nonvac {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 384) {α₀ : ℝ} (hα : 0 < α₀)
    (χ : Bond (scaleUp 2 1 Lu) → ℝ) (hχ : ∀ e, |χ e| ≤ α₀ * ((((2 : ℕ) : ℝ) ^ 1)⁻¹) ^ 2 / 10) :
    ∃ (U : LinkCfg (scaleUp 2 1 Lu)) (g : GaugeFn (scaleUp 2 1 Lu)) (V : LinkCfg (scaleUp 2 1 Lu)),
      PerCubeRegular2 2 32 12 1 (AdalyFormal.IngredientFamilyR2.fullTower 2 1 Lu) α₀ ((((2 : ℕ) : ℝ) ^ 1)⁻¹) U ∧
      M1Regular 2 32 12 1 (AdalyFormal.IngredientFamilyR2.fullTower 2 1 Lu) (((2 : ℕ) : ℝ) ^ 3 * (2 * α₀)) ((((2 : ℕ) : ℝ) ^ 1)⁻¹) V ∧
      AgreeAt (Ball (embY 2 1 Lu (by norm_num) (fun _ => 0)) 32) (periodicGaugeTransform g U) V := by
  have hA : Admissible 2 32 23 1 (AdalyFormal.IngredientFamilyR2.fullTower 2 1 Lu) :=
    AdalyFormal.M0Corollary.fullTower_admissible 2 32 23 1 (by norm_num) le_rfl Lu (fun μ => by rw [hLu μ]; norm_num)
  have hU := ufield_M1Regular (ell := 2) (M := 32) (f := 12) (k := 1) (by norm_num) (by norm_num) (by norm_num)
    (AdalyFormal.IngredientFamilyR2.fullTower 2 1 Lu) hα χ hχ
  have hP := perCube_of_M1 hA hU
  have hN : ∀ μ, scaleUp 2 1 Lu μ + 1 = 768 := fun μ => by
    rw [scaleUp_succ 2 1 Lu (by norm_num) μ, hLu μ]
    norm_num
  have hLuF : ∀ σ, 1 ≤ scaleUp 2 1 Lu σ := fun σ => by have := hN σ; omega
  have hL : AdalyFormal.StatementLane.LambdaOK 2 32 23 1 (AdalyFormal.IngredientFamilyR2.fullTower 2 1 Lu) (Set.univ : Set (PeriodicLatticeSite Lu)) := by
    refine ⟨fun x _ y _ => Set.mem_univ y, embY 2 1 Lu (by norm_num), fun y μ => embY_val 2 1 Lu (by norm_num) y μ, ?_, ?_⟩
    · intro y _; simp [AdalyFormal.IngredientFamilyR2.fullTower]
    · intro y _ y' h; exact absurd (by simp [AdalyFormal.IngredientFamilyR2.fullTower]) h
  obtain ⟨g, V, h1, h2⟩ := chart_of_class (ell := 2) (M := 32) (R := 23) (k := 1) (Lu := Lu) (by norm_num) (by norm_num) hA hL
    (y0 := fun _ => 0) (Set.mem_univ _) (fun _ => 0) (by rw [AdalyFormal.StatementLane.pdist_self]; norm_num) 32 (by norm_num) hLuF hα hP
  exact ⟨_, g, V, hP, h1, h2⟩

end AdalyFormal.M2UnitCharts

#print axioms AdalyFormal.M2UnitCharts.chart_of_class_nonvac
