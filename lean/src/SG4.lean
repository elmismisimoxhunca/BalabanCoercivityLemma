import SG3
import MS11

/-!
# SG4 -- block-local gauge (`hU`, `hT`) from ONE anchor chart (lane m2_fields123_20261015)

`blockGauge_of_chart` : if `AnchorChart` holds at the base point `y` of a constraint block `(j, y)` with radius `7 ℓ^j`, there is a gauge `γ`
with the two block-local bounds that `M1Site.site_coercive_weighted_perblock` / `M1IMS.gamma_sharp` consume, with the M1 constant
`ρ_T = (ℓ + 3πℓ²)·ρ₁(12, M, ℓ³·2α₀)`.  `γ = g'·g`: `g` = the cube gauge (chart), `g'` = the gauge of `M1Regular V`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2F123

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.SiteCoercivity (inBlockBonds mem_inBlockBonds)
open AdalyFormal.IngredientFamilyR2 (geomOf bgTower)

theorem pdist_block_le {L : PeriodicLatticeExtent} {n : ℕ} {y z : PeriodicLatticeSite L}
    (hz : z ∈ blockOf y n) : pdist y z ≤ 3 * n := by
  rw [mem_blockOf] at hz
  unfold pdist
  calc ∑ μ : Fin 3, pcd (L μ + 1) (y μ).val (z μ).val ≤ ∑ _μ : Fin 3, n := by
        refine Finset.sum_le_sum (fun μ _ => ?_)
        have h := hz μ
        have := AdalyFormal.StatementLaneR8.pcd_le_diff (L μ + 1) (y μ).val (z μ).val h.1
        omega
    _ = 3 * n := by simp

theorem rhoT_le_eight (ell : ℕ) (hell : 2 ≤ ell) (i : ℕ) : AdalyFormal.StatementLaneR8.rhoT ell i + 8 ≤ 8 * ell ^ i := by
  induction i with
  | zero => simp [AdalyFormal.StatementLaneR8.rhoT]
  | succ i ih =>
    rw [AdalyFormal.StatementLaneR8.rhoT_succ]
    have h1 : ell ^ i * ell = ell ^ (i + 1) := (pow_succ ell i).symm
    have h2 : 2 * ell ^ i ≤ ell ^ i * ell := by nlinarith [Nat.zero_le (ell ^ i)]
    rw [h1] at h2 ⊢
    have : 8 * ell ^ (i + 1) = 8 * ell ^ (i + 1) := rfl
    nlinarith

theorem gauge_comp {L : PeriodicLatticeExtent} (g' g : GaugeFn L) (U : LinkCfg L) :
    periodicGaugeTransform (fun z => g' z * g z) U = periodicGaugeTransform g' (periodicGaugeTransform g U) := by
  funext e
  apply Subtype.ext
  simp [periodicGaugeTransform, mul_assoc, mul_inv_rev]

theorem blockGauge_of_chart {ell M R k : ℕ} {L : PeriodicLatticeExtent} (hell : 2 ≤ ell)
    {S : Tower L} (hS : Admissible ell M R k S) (hRM : 18 ≤ R * M) (hbig : ∀ σ : Fin 3, 4 * ell ^ k < L σ + 1)
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀)
    (ha1 : (12 : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * AdalyFormal.TowerLoc.rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1)
    (U : LinkCfg L) {j : ℕ} (hj : j ≤ k) {y : PeriodicLatticeSite L} (hy : y ∈ (geomOf ell k S).Lam j)
    (hch : AnchorChart ell M k S U α₀ η y (7 * ell ^ j)) :
    ∃ γ : GaugeFn L,
      (∀ b ∈ inBlockBonds y (ell ^ j),
        frobNorm ((((periodicGaugeTransform γ U b : Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
          ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * AdalyFormal.TowerLoc.rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) / (ell : ℝ) ^ j) ∧
      (∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
        coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
        frobNorm ((bgTower (geomOf ell k S) (periodicGaugeTransform γ U) i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
          ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * AdalyFormal.TowerLoc.rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) * (ell : ℝ) ^ i / (ell : ℝ) ^ j) := by
  obtain ⟨g, V, ⟨g', A, hVg, hB⟩, hag⟩ := hch
  have hell0 : 0 < ell := by omega
  have hα' : 0 ≤ (ell : ℝ) ^ 3 * (2 * α₀) := by positivity
  have hag' : AgreeAt (Ball y (7 * ell ^ j)) (periodicGaugeTransform (fun z => g' z * g z) U) (periodicGaugeTransform g' V) := by
    rw [gauge_comp]
    exact AdalyFormal.M2Unit.agree_gauge hag g'
  refine ⟨fun z => g' z * g z, ?_, ?_⟩
  · intro b hb
    rw [mem_inBlockBonds] at hb
    have hmem : b.1 ∈ Ball y (7 * ell ^ j) := by
      have := pdist_block_le hb.1
      have h3 : 3 * ell ^ j ≤ 7 * ell ^ j := by omega
      exact le_trans this h3
    have e : periodicGaugeTransform (fun z => g' z * g z) U b = periodicGaugeTransform g' V b := by
      have := hag' b.1 hmem b.2
      exact this
    rw [e]
    exact AdalyFormal.M1GaugeW4.site_hU_M1 hell hS V g' A hVg hB hη hα' j hj y hy b (mem_inBlockBonds.mpr hb)
  · intro i hi z hz hzal μ hzs
    have hT := AdalyFormal.M1GaugeW4.site_hT_M1 hell hS hRM hbig V g' A hVg hB hη hα' ha1 hsm4 j hj y hy i hi z hz hzal μ hzs
    have hsub : Ball z (AdalyFormal.StatementLaneR8.rhoT ell i) ⊆ Ball y (7 * ell ^ j) := by
      intro w hw
      have h1 : pdist z w ≤ AdalyFormal.StatementLaneR8.rhoT ell i := hw
      have h2 := pdist_block_le hz
      have h3 := AdalyFormal.StatementLaneR8.pdist_triangle y z w
      have h4 := rhoT_le_eight ell hell i
      have h5 : ell ^ i * ell ≤ ell ^ j := by
        rw [← pow_succ]; exact Nat.pow_le_pow_right hell0 hi
      have h6 : 2 * ell ^ i ≤ ell ^ i * ell := by nlinarith [Nat.zero_le (ell ^ i)]
      show pdist y w ≤ 7 * ell ^ j
      omega
    have hc := AdalyFormal.StatementLaneR8.bgTower_congr (geomOf ell k S) (by exact hell0) (l := i) z
      (hag'.mono hsub) μ
    rw [hc]
    exact hT

end AdalyFormal.M2F123

#print axioms AdalyFormal.M2F123.blockGauge_of_chart
