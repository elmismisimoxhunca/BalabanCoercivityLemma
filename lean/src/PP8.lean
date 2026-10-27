import SG6
import PP7
import OGP0

/-!
# SG7 -- F2 (`RowBound`) from per-block anchor charts (lane m2_fields123_20261015)

* `glue_gauges12` : per-block gauges `γ_q` (with the block-local `hU`, `hT`) glue to ONE gauge `Γ` for which `U^Γ` satisfies the global-form `hU`, `hT` consumed by
  `M1IMS.hatPack_of` and `M1IMS.gamma_sharp` (the blocks are disjoint; `hU`/`hT` read only in-block data) -- the same gluing as in `site_coercive_weighted_perblock`.
* `rowBound_of_charts12` : `RowBound ell k S U a (gamC ell a ρ_T (epsXnum ell W a ρ_T))`, `W = R M ℓ`, `ρ_T = rhoT ell 12 M (alpha1 ell α₀)`: `gamma_sharp` at `U^Γ`
  and the gauge transfer `rowBound_of_gauge`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.OneGap12

open AdalyFormal.M2F123
open AdalyFormal.OneGap12

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.SiteCoercivity (inBlockBonds mem_inBlockBonds)
open AdalyFormal.IngredientFamilyR2 (geomOf bgTower Cfg TowerGeom)
open AdalyFormal.M1Site
open AdalyFormal.M1IMS

variable {L : PeriodicLatticeExtent}

theorem glue_gauges12 {ell k : ℕ} (hell : 2 ≤ ell) {G : TowerGeom L} (hP : AdalyFormal.SiteCoercivity.ProperTower G ell k)
    (U : Cfg L) (γB : QIdx G → GaugeFn L) (ρ : ℝ)
    (hU : ∀ q : QIdx G, ∀ b ∈ inBlockBonds (yq q) (ell ^ jq q),
      frobNorm ((((periodicGaugeTransform (γB q) U b : Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ jq q)
    (hT : ∀ q : QIdx G, ∀ i, i < jq q → ∀ z ∈ blockOf (yq q) (ell ^ jq q), z ∈ CoarseLattice L (ell ^ i) →
      ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf (yq q) (ell ^ jq q) →
      frobNorm ((bgTower G (periodicGaugeTransform (γB q) U) i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ jq q) :
    ∃ Γ : GaugeFn L,
      (∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
        frobNorm ((((periodicGaugeTransform Γ U b : Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
          ≤ ρ / (ell : ℝ) ^ j) ∧
      (∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
        coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
        frobNorm ((bgTower G (periodicGaugeTransform Γ U) i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
          ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j) := by
  classical
  set γ : GaugeFn L := fun x =>
    if h : ∃ q : QIdx G, x ∈ blockOf (yq q) (ell ^ jq q) then γB (Classical.choose h) x else 1 with hγdef
  have hγ : ∀ q : QIdx G, ∀ x ∈ blockOf (yq q) (ell ^ jq q), γ x = γB q x := by
    intro q x hx
    have h : ∃ q : QIdx G, x ∈ blockOf (yq q) (ell ^ jq q) := ⟨q, hx⟩
    simp only [hγdef, dif_pos h]
    have hq' := Classical.choose_spec h
    by_cases hqq : Classical.choose h = q
    · rw [hqq]
    · exact absurd hx (Finset.disjoint_left.mp (disj_q hP hqq) hq')
  have mkq : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∃ q : QIdx G, jq q = j ∧ yq q = y := by
    intro j hj y hy
    exact ⟨⟨(⟨j, by rw [hP.k_eq]; omega⟩, y), hy⟩, rfl, rfl⟩
  refine ⟨γ, ?_, ?_⟩
  · intro j hj y hy b hb
    obtain ⟨q, hqj, hqy⟩ := mkq j hj y hy
    subst hqj; subst hqy
    rw [mem_inBlockBonds] at hb
    have e : periodicGaugeTransform γ U b = periodicGaugeTransform (γB q) U b := by
      show γ b.1 * U b * (γ (periodicLatticeShift b.1 b.2))⁻¹
        = γB q b.1 * U b * (γB q (periodicLatticeShift b.1 b.2))⁻¹
      rw [hγ q b.1 hb.1, hγ q _ hb.2]
    rw [e]
    exact hU q b (mem_inBlockBonds.mpr hb)
  · intro j hj y hy i hi z hz hzal μ hzs
    obtain ⟨q, hqj, hqy⟩ := mkq j hj y hy
    subst hqj; subst hqy
    have e : bgTower G (periodicGaugeTransform γ U) i (z, μ)
        = bgTower G (periodicGaugeTransform (γB q) U) i (z, μ) := by
      rw [AdalyFormal.GaugeCov.bgTower_gauge, AdalyFormal.GaugeCov.bgTower_gauge]
      show γ z * bgTower G U i (z, μ) * (γ (coarseShift z (G.ell ^ i) μ))⁻¹
        = γB q z * bgTower G U i (z, μ) * (γB q (coarseShift z (G.ell ^ i) μ))⁻¹
      rw [hP.ell_eq, hγ q z hz, hγ q _ hzs]
    rw [e]
    exact hT q i hi z hz hzal μ hzs

/-- **F2 from per-block charts.**  The SK1 field `RowBound` with the SK1 constant (`gamC`/`epsXnum`, `W = R M ℓ`). -/
theorem rowBound_of_charts12 {ell M R k : ℕ} (hell : 2 ≤ ell)
    {S : Tower L} (hS : Admissible ell M R k S) (hRM : 18 ≤ R * M) (hbig : ∀ σ : Fin 3, 4 * ell ^ k < L σ + 1)
    (hL : ∀ σ : Fin 3, 1 ≤ L σ) (hR1 : 1 ≤ R) (hM1 : 1 ≤ M) {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀)
    (ha1 : (12 : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * AdalyFormal.TowerLoc.rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1)
    (a : ℝ) (ha : 0 < a) (ε1 : ℝ)
    (hN : AdalyFormal.M1GaugeW4.W4Num ell M 12 (R * M * ell) a (AdalyFormal.M2Skel.alpha1 ell α₀) ε1)
    (U : LinkCfg L)
    (hch : ∀ q : QIdx (geomOf ell k S), 1 ≤ jq q → AnchorChart12 ell M k S U α₀ η (yq q) (7 * ell ^ jq q)) :
    AdalyFormal.M2Skel.RowBound ell k S U a
      (gamC ell a (AdalyFormal.M1GaugeW4.rhoT ell 12 M (AdalyFormal.M2Skel.alpha1 ell α₀))
        (AdalyFormal.M1GaugeW4.epsXnum ell (R * M * ell) a (AdalyFormal.M1GaugeW4.rhoT ell 12 M (AdalyFormal.M2Skel.alpha1 ell α₀)))) := by
  have hell0 : 0 < ell := by omega
  have hα' : 0 ≤ (ell : ℝ) ^ 3 * (2 * α₀) := by positivity
  have hρ : 0 ≤ AdalyFormal.M1GaugeW4.rhoT ell 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) :=
    AdalyFormal.M1GaugeW4.rhoT_nonneg ell 12 M _ hα'
  obtain ⟨h216, h12⟩ := AdalyFormal.M1GaugeW4.rhoT_smalls ell 12 M _ hα' (by omega) hsm4
  obtain ⟨γB, hU, hT⟩ := exists_blockGauges12 hell hS hRM hbig hL hη hα ha1 hsm4 U hch
  obtain ⟨Γ, hU', hT'⟩ := glue_gauges12 (k := k) hell (AdalyFormal.M1Site.properTower_geomOf hell0 hS) U γB
    (AdalyFormal.M1GaugeW4.rhoT ell 12 M ((ell : ℝ) ^ 3 * (2 * α₀))) hU hT
  have hW : 1 ≤ R * M * ell := by
    have : 1 ≤ R * M := by omega
    nlinarith
  have hp := hatPack_of (W := R * M * ell) hS hell (periodicGaugeTransform Γ U) a ha _ hρ h216 hU' hT' hN.hsm hN.hsmD
  have hγ := gamma_sharp hS hW hell hR1 hM1 le_rfl (periodicGaugeTransform Γ U) a _ hp _ hρ h12 hU' hT' hN.hgs
  exact rowBound_of_gauge (geomOf ell k S) Γ U a _ hp.hu hγ

end AdalyFormal.OneGap12
#print axioms AdalyFormal.OneGap12.glue_gauges12
#print axioms AdalyFormal.OneGap12.rowBound_of_charts12
