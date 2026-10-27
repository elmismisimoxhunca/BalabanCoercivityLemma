import UD4
import AC_UD3
import AC_Base

/-! AC copy of UD4: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2UnitCharts

open AdalyFormal.AllC
variable {fc : ℕ} [CubeFactor fc]

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (PerCubeRegular2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt pdist_shift_le)
open AdalyFormal.IngredientFamilyR2 (embY embY_val)
open AdalyFormal.M2Bridge (offc)

theorem chart_of_classAC {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (hM : 0 < M)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) {Lam : Set (PeriodicLatticeSite Lu)}
    (hL : AdalyFormal.StatementLane.LambdaOK ell M R k S Lam)
    (hthick : ∀ σ : Fin 3, 12 * (M * ell ^ k) ≤ scaleUp ell k Lu σ + 1)
    {y0 : PeriodicLatticeSite Lu} (hy0 : y0 ∈ Lam) (q : PeriodicLatticeSite Lu)
    (hD : pdist y0 q + 3 * (fc * M) ≤ R * M) (r : ℕ) (hr : r + 128 * ell ^ k + 5 ≤ 4 * (M * ell ^ k))
    (hLu : ∀ σ : Fin 3, 1 ≤ scaleUp ell k Lu σ) {α₀ : ℝ} (hα : 0 < α₀) {U : LinkCfg (scaleUp ell k Lu)}
    (hP : PerCubeRegular2H ell M fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U) :
    ∃ (g : GaugeFn (scaleUp ell k Lu)) (V : LinkCfg (scaleUp ell k Lu)),
      AdalyFormal.M1.M1Regular ell M 12 k S ((ell : ℝ) ^ 3 * (2 * α₀)) ((ell : ℝ) ^ k)⁻¹ V ∧
      AgreeAt (Ball (embY ell k Lu hell q) r) (periodicGaugeTransform g U) V := by
  have hfc := CubeFactor.pos (fc := fc)
  have hfc10 : 10 ≤ fc := CubeFactor.ge
  obtain ⟨z, hcube, hcore⟩ := class_cube_atAC hell hM hS hL hthick hy0 q hD r hr
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hs7 : 7 ≤ fc * bigSide M ell k := by
    have : 1 ≤ bigSide M ell k := Nat.mul_pos hM (pow_pos hell k)
    have h10 : 10 * bigSide M ell k ≤ fc * bigSide M ell k := Nat.mul_le_mul_right _ hfc10
    omega
  have hα'' : 0 < ((12 : ℕ) : ℝ) * α₀ / fc := by positivity
  obtain ⟨g, χ, V, hreg, -, hsupp, hχ1, hV⟩ :=
    AdalyFormal.M2Bridge.regime_of_class hS hell hfc hM hα'' hη (hP.toOrig hfc) hcube (z := z) rfl hLu
      (w := 64 * ell ^ k) le_rfl hs7
  have hreg' : AdalyFormal.M1.M1Regular ell M 12 k S ((ell : ℝ) ^ 3 * (2 * α₀)) ((ell : ℝ) ^ k)⁻¹ V :=
    (m1Regular_congr_bound (f := fc) (f' := 12) (M := M) (by
      have e := bound_eq (M := M) (b := 12) hfc α₀
      push_cast at e ⊢
      calc (fc : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * ((12 : ℝ) * α₀ / fc))) = (ell : ℝ) ^ 3 * 2 * ((fc : ℝ) * M * ((12 : ℝ) * α₀ / fc)) := by ring
        _ = (ell : ℝ) ^ 3 * 2 * (12 * M * α₀) := by rw [e]
        _ = _ := by ring)).1 hreg
  refine ⟨g, V, hreg', ?_⟩
  intro x' hx' μ
  have hχ : χ x' = 1 := hχ1 x' (hcore x' hx')
  have hmem : ∀ y, pdist x' y ≤ 6 → y ∈ siteBox z (fc * bigSide M ell k) := hsupp x' (by rw [hχ]; norm_num)
  have hcb : CubeBond (siteBox z (fc * bigSide M ell k)) (x', μ) :=
    ⟨hmem x' (by rw [AdalyFormal.StatementLane.pdist_self]; norm_num),
     hmem _ (le_trans (pdist_shift_le x' μ) (by norm_num))⟩
  exact (hV (x', μ) hcb hχ).symm

end AdalyFormal.M2UnitCharts

