import UD3

/-!
# UD4 -- `chart_of_class`: one M1Regular chart agreeing with `U^g` on a ball, from the PRINTED per-cube class (lane m2_unitcharts_20261014)

Given `PerCubeRegular2 ell M 12 k S α₀ ℓ^{-k} U` (no global gauge), a unit site `q` within `R M - 21 M` of a point of `Λ`, and a fine radius `r`
with `r + 128 n + 5 ≤ 5 M n`: there are a gauge `g` and a torus-wide `M1Regular` configuration `V` (at `ℓ³·2α₀`) with `U^g = V` at every bond based
in `Ball (embY q) r`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2UnitCharts

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (PerCubeRegular2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt pdist_shift_le)
open AdalyFormal.IngredientFamilyR2 (embY embY_val)
open AdalyFormal.M2Bridge (offc)

theorem chart_of_class {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (hM : 0 < M)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) {Lam : Set (PeriodicLatticeSite Lu)}
    (hL : AdalyFormal.StatementLane.LambdaOK ell M R k S Lam)
    {y0 : PeriodicLatticeSite Lu} (hy0 : y0 ∈ Lam) (q : PeriodicLatticeSite Lu)
    (hD : pdist y0 q + 21 * M ≤ R * M) (r : ℕ) (hr : r + 128 * ell ^ k + 5 ≤ 5 * (M * ell ^ k))
    (hLu : ∀ σ : Fin 3, 1 ≤ scaleUp ell k Lu σ) {α₀ : ℝ} (hα : 0 < α₀) {U : LinkCfg (scaleUp ell k Lu)}
    (hP : PerCubeRegular2 ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U) :
    ∃ (g : GaugeFn (scaleUp ell k Lu)) (V : LinkCfg (scaleUp ell k Lu)),
      AdalyFormal.M1.M1Regular ell M 12 k S ((ell : ℝ) ^ 3 * (2 * α₀)) ((ell : ℝ) ^ k)⁻¹ V ∧
      AgreeAt (Ball (embY ell k Lu hell q) r) (periodicGaugeTransform g U) V := by
  obtain ⟨z, hcube, hcore⟩ := class_cube_at hell hM hS hL hy0 q hD r hr
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hs7 : 7 ≤ 12 * bigSide M ell k := by
    have : 1 ≤ bigSide M ell k := Nat.mul_pos hM (pow_pos hell k)
    omega
  obtain ⟨g, χ, V, hreg, -, hsupp, hχ1, hV⟩ :=
    AdalyFormal.M2Bridge.regime_of_class hS hell (by norm_num) hM hα hη hP hcube (z := z) rfl hLu
      (w := 64 * ell ^ k) le_rfl hs7
  refine ⟨g, V, hreg, ?_⟩
  intro x' hx' μ
  have hχ : χ x' = 1 := hχ1 x' (hcore x' hx')
  have hmem : ∀ y, pdist x' y ≤ 6 → y ∈ siteBox z (12 * bigSide M ell k) := hsupp x' (by rw [hχ]; norm_num)
  have hcb : CubeBond (siteBox z (12 * bigSide M ell k)) (x', μ) :=
    ⟨hmem x' (by rw [AdalyFormal.StatementLane.pdist_self]; norm_num),
     hmem _ (le_trans (pdist_shift_le x' μ) (by norm_num))⟩
  exact (hV (x', μ) hcb hχ).symm

end AdalyFormal.M2UnitCharts

#print axioms AdalyFormal.M2UnitCharts.chart_of_class
