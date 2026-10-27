import SG1

/-!
# SG2 -- `chart_gen`: one `M1Regular` chart agreeing with `U^g` on a ball, at ANY level `i` (lane m2_fields123_20261015)

Generalisation of `M2UnitCharts.chart_of_class` (index `k`, via `LambdaOK2`) to a general index `i ≤ k` with the geometric inputs of `class_cube_gen`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2F123

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (PerCubeRegular2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt pdist_shift_le)
open AdalyFormal.M2Bridge (offc)

/-- a ball `Ball x r` sits in the core (margin `128 n + 4`, `n = ℓ^i`) of a class cube of some index `i` -/
def PlacedAt {L : PeriodicLatticeExtent} (ell M k : ℕ) (S : Tower L) (x : PeriodicLatticeSite L) (r : ℕ) : Prop :=
  ∃ (z : PeriodicLatticeSite L) (i : ℕ),
    IsClassCube ell M 12 k S (siteBox z (12 * bigSide M ell i)) i ∧
    ∀ x' ∈ Ball x r, ∀ σ : Fin 3, 12 * bigSide M ell i ≤ L σ + 1 →
      2 * (64 * ell ^ i) + 4 ≤ offc z x' σ ∧ offc z x' σ + 2 * (64 * ell ^ i) + 5 ≤ 12 * bigSide M ell i

theorem chart_of_placed {ell M R k : ℕ} {L : PeriodicLatticeExtent} (hell : 0 < ell) (hM : 0 < M)
    {S : Tower L} (hS : Admissible ell M R k S) (x : PeriodicLatticeSite L) (r : ℕ)
    (hpl : PlacedAt ell M k S x r)
    (hL : ∀ σ : Fin 3, 1 ≤ L σ) {α₀ η : ℝ} (hα : 0 < α₀) (hη : 0 < η) {U : LinkCfg L}
    (hP : PerCubeRegular2 ell M 12 k S α₀ η U) :
    ∃ (g : GaugeFn L) (V : LinkCfg L),
      AdalyFormal.M1.M1Regular ell M 12 k S ((ell : ℝ) ^ 3 * (2 * α₀)) η V ∧
      AgreeAt (Ball x r) (periodicGaugeTransform g U) V := by
  obtain ⟨z, i, hcube, hcore⟩ := hpl
  have hs7 : 7 ≤ 12 * bigSide M ell i := by
    have : 1 ≤ bigSide M ell i := Nat.mul_pos hM (pow_pos hell i)
    omega
  obtain ⟨g, χ, V, hreg, -, hsupp, hχ1, hV⟩ :=
    AdalyFormal.M2Bridge.regime_of_class hS hell (by norm_num) hM hα hη hP hcube (z := z) rfl hL
      (w := 64 * ell ^ i) le_rfl hs7
  refine ⟨g, V, hreg, ?_⟩
  intro x' hx' μ
  have hχ : χ x' = 1 := hχ1 x' (hcore x' hx')
  have hmem : ∀ y, pdist x' y ≤ 6 → y ∈ siteBox z (12 * bigSide M ell i) := hsupp x' (by rw [hχ]; norm_num)
  have hcb : CubeBond (siteBox z (12 * bigSide M ell i)) (x', μ) :=
    ⟨hmem x' (by rw [AdalyFormal.StatementLane.pdist_self]; norm_num),
     hmem _ (le_trans (pdist_shift_le x' μ) (by norm_num))⟩
  exact (hV (x', μ) hcb hχ).symm

theorem placed_gen {ell M R k : ℕ} {L : PeriodicLatticeExtent} (hell : 0 < ell) (hM : 0 < M)
    {S : Tower L} (hS : Admissible ell M R k S) {i : ℕ} (hi : i ≤ k) (x : PeriodicLatticeSite L)
    (hbox : ∀ x'' : PeriodicLatticeSite L,
      (∀ σ : Fin 3, pcd (L σ + 1) (x σ).val (x'' σ).val ≤ 7 * (M * ell ^ i)) → x'' ∈ S.Om i)
    (hout : ∀ x'' : PeriodicLatticeSite L,
      (∀ σ : Fin 3, pcd (L σ + 1) (x σ).val (x'' σ).val ≤ 7 * (M * ell ^ i)) → x'' ∉ S.Om (i + 2))
    (w : PeriodicLatticeSite L) (hw : pdist x w ≤ 5 * (M * ell ^ i)) (hwO : w ∉ S.Om (i + 1))
    (r : ℕ) (hr : r + 128 * ell ^ i + 5 ≤ 5 * (M * ell ^ i)) : PlacedAt ell M k S x r := by
  obtain ⟨z, hc, hcore⟩ := class_cube_gen hell hM hS hi x hbox hout w hw hwO r hr
  exact ⟨z, i, hc, hcore⟩

theorem chart_gen {ell M R k : ℕ} {L : PeriodicLatticeExtent} (hell : 0 < ell) (hM : 0 < M)
    {S : Tower L} (hS : Admissible ell M R k S) {i : ℕ} (hi : i ≤ k) (x : PeriodicLatticeSite L)
    (hbox : ∀ x'' : PeriodicLatticeSite L,
      (∀ σ : Fin 3, pcd (L σ + 1) (x σ).val (x'' σ).val ≤ 7 * (M * ell ^ i)) → x'' ∈ S.Om i)
    (hout : ∀ x'' : PeriodicLatticeSite L,
      (∀ σ : Fin 3, pcd (L σ + 1) (x σ).val (x'' σ).val ≤ 7 * (M * ell ^ i)) → x'' ∉ S.Om (i + 2))
    (w : PeriodicLatticeSite L) (hw : pdist x w ≤ 5 * (M * ell ^ i)) (hwO : w ∉ S.Om (i + 1))
    (r : ℕ) (hr : r + 128 * ell ^ i + 5 ≤ 5 * (M * ell ^ i))
    (hL : ∀ σ : Fin 3, 1 ≤ L σ) {α₀ η : ℝ} (hα : 0 < α₀) (hη : 0 < η) {U : LinkCfg L}
    (hP : PerCubeRegular2 ell M 12 k S α₀ η U) :
    ∃ (g : GaugeFn L) (V : LinkCfg L),
      AdalyFormal.M1.M1Regular ell M 12 k S ((ell : ℝ) ^ 3 * (2 * α₀)) η V ∧
      AgreeAt (Ball x r) (periodicGaugeTransform g U) V :=
  chart_of_placed hell hM hS x r (placed_gen hell hM hS hi x hbox hout w hw hwO r hr) hL hα hη hP

end AdalyFormal.M2F123

#print axioms AdalyFormal.M2F123.chart_of_placed
#print axioms AdalyFormal.M2F123.placed_gen
#print axioms AdalyFormal.M2F123.chart_gen
