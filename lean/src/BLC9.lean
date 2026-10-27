import BLC8
import OG16

/-!
# BLC9 -- `BallChartsG` proved; the headline reduces to the three-field `Residual` (m2_ballcharts, 2026-10-15)

`ballChartsG : AdalyFormal.OneGap.BallChartsG` (statement of compute/m2_onegap_20261015/src/BallCharts.lean, unchanged).
Choices (all before `k`): `m₁ = 5` (so `M = ℓ^m ≥ 32`), `R₁ = 45ℓ + 30`, `C = CC ℓ M + 56 M`, threshold `min (Xthr ℓ M) (1/2)`.
`j ≥ 1`: `ball_chart_pos` (BLC6: vertex charts → rows → slabs → ball).  `j = 0`: `ball_chart_zero` (BLC8: axial gauge).
`target8_of_residual : Residual → P428Target8` via OG16 `target8_of_ballChartsG`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2BallCharts

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2 AdalyFormal.M2GlueGeo
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

theorem ballChartsG : AdalyFormal.OneGap.BallChartsG := by
  intro ell hell
  refine ⟨5, fun m hm => ⟨45 * ell + 30, fun R hR => ?_⟩⟩
  have hM32 : 32 ≤ ell ^ m := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      _ ≤ ell ^ m := Nat.pow_le_pow_left hell m
  have hM0 : 0 < ell ^ m := by omega
  have hMr : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by exact_mod_cast hM0
  obtain ⟨-, -, -, -, -, -, c7, c8⟩ := consts_nonneg ell (ell ^ m)
  refine ⟨CC ell (ell ^ m) + 56 * ((ell ^ m : ℕ) : ℝ), ?_, min (Xthr ell (ell ^ m)) (1 / 2),
    lt_min (Xthr_pos ell (ell ^ m) hM0) (by norm_num), ?_⟩
  · show (1 : ℝ) ≤ CC ell (ell ^ m) + 56 * ((ell ^ m : ℕ) : ℝ)
    unfold CC; linarith
  intro k hk Lu α₀ hα hsα hT S hS Lam hLam U hcc hU1 hne j hjk w hw r hr7 hnw hin hout hsm
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    positivity
  set X : ℝ := (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hCC : 1 ≤ CC ell (ell ^ m) := by unfold CC; linarith
  have hcast : (((12 : ℕ) : ℝ)) = (12 : ℝ) := by norm_num
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · -- j = 0
    subst hj0
    have hr7' : r ≤ 7 * ell ^ m := by simpa using hr7
    have hin' : ∀ x ∈ Ball w r, x ∈ S.Om 0 := hin
    obtain ⟨g, hg⟩ := ball_chart_zero (R := R) hcc.1 (by omega) hr7' hnw hin' hη hα.le hcc.2
      (hsα.trans (min_le_right _ _))
    refine ⟨g, hg.mono subset_rfl ?_ ?_⟩
    · simp only [Nat.zero_sub, pow_zero, inv_one, mul_one, hcast]
      rw [← hXdef]; nlinarith
    · simp only [Nat.zero_sub, pow_zero, inv_one, one_pow, mul_one, hcast]
      rw [← hXdef]; nlinarith
  · -- j ≥ 1
    obtain ⟨x0, hx0, hwx⟩ := hw
    obtain ⟨g, hg⟩ := ball_chart_pos hS hcc.1 hell (by omega) hj1 hjk hx0 hwx hr7 hnw hR hη hα.le hcc.2
      (hsα.trans (min_le_left _ _))
    refine ⟨g, hg.mono subset_rfl ?_ ?_⟩
    · rw [hcast, ← hXdef]
      have : 0 ≤ X * ((ell : ℝ) ^ (j - 1))⁻¹ := by positivity
      have h56 : 0 ≤ 56 * ((ell ^ m : ℕ) : ℝ) := by positivity
      have e : X * ((ell : ℝ) ^ (j - 1))⁻¹ = (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * ((ell : ℝ) ^ (j - 1))⁻¹ := by
        rw [hXdef]
      rw [← e]; nlinarith
    · rw [hcast, ← hXdef]
      have : 0 ≤ X * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 := by positivity
      have h56 : 0 ≤ 56 * ((ell ^ m : ℕ) : ℝ) := by positivity
      have e : X * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2
          = (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 := by
        rw [hXdef]
      rw [← e]; nlinarith

/-- **the headline reduces to the three-field `Residual`** (opLayer, qsInjExit, thin). -/
theorem target8_of_residual (R2 : AdalyFormal.OneGap.Residual) : AdalyFormal.StatementLaneG.P428Target8 :=
  AdalyFormal.OneGap.target8_of_ballChartsG ballChartsG R2

end AdalyFormal.M2BallCharts
