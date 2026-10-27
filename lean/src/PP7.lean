import PP6
import OGP0

/-!
# SG5 -- F1 (`SiteS1`) from per-block anchor charts (lane m2_fields123_20261015)

`exists_blockGauges12` : an `AnchorChart12` (radius `7 ℓ^j`) at the base point of every constraint block of level `j ≥ 1` gives a family of gauges
`γ_q` satisfying the hypotheses of `site_coercive_weighted_perblock`; level-`0` blocks need no chart (`inBlockBonds y 1 = ∅` when every `L_σ ≥ 1`).
`siteS1_of_charts12` : the S1 bound of SK1 (`SiteS1`) with the SK1 constant `csOf a (rhoT ell 12 M (alpha1 ell α₀))`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.OneGap12

open AdalyFormal.M2F123
open AdalyFormal.OneGap12

open scoped RealInnerProductSpace
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
open AdalyFormal.M1Site (QIdx yq jq yq_mem jq_le)

theorem inBlockBonds_one_empty12 {L : PeriodicLatticeExtent} (hL : ∀ σ : Fin 3, 1 ≤ L σ) (y : PeriodicLatticeSite L) :
    inBlockBonds y 1 = ∅ := by
  ext b
  simp only [Finset.notMem_empty, iff_false]
  intro hb
  rw [mem_inBlockBonds] at hb
  obtain ⟨h1, h2⟩ := hb
  rw [mem_blockOf] at h1 h2
  have e1 : b.1 = y := by
    funext μ; apply Fin.ext; have := h1 μ; omega
  have h2' := h2 b.2
  have h1' := h1 b.2
  -- the shifted site moves coordinate `b.2` by one (mod `L+1`), `L ≥ 1`
  have hl := hL b.2
  have hv : (periodicLatticeShift b.1 b.2 b.2).val = if (b.1 b.2).val = L b.2 then 0 else (b.1 b.2).val + 1 := by
    unfold periodicLatticeShift
    rw [Function.update_self, Fin.val_add_one]
    by_cases h : b.1 b.2 = Fin.last (L b.2)
    · rw [if_pos h]; rw [h]; simp
    · rw [if_neg h]
      have : (b.1 b.2).val ≠ L b.2 := fun hh => h (Fin.ext (by simpa using hh))
      rw [if_neg this]
  rw [hv] at h2'
  have := (b.1 b.2).isLt
  split_ifs at h2' <;> omega

theorem exists_blockGauges12 {ell M R k : ℕ} {L : PeriodicLatticeExtent} (hell : 2 ≤ ell)
    {S : Tower L} (hS : Admissible ell M R k S) (hRM : 18 ≤ R * M) (hbig : ∀ σ : Fin 3, 4 * ell ^ k < L σ + 1)
    (hL : ∀ σ : Fin 3, 1 ≤ L σ) {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀)
    (ha1 : (12 : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * AdalyFormal.TowerLoc.rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1)
    (U : LinkCfg L)
    (hch : ∀ q : QIdx (geomOf ell k S), 1 ≤ jq q → AnchorChart12 ell M k S U α₀ η (yq q) (7 * ell ^ jq q)) :
    ∃ γB : QIdx (geomOf ell k S) → GaugeFn L,
      (∀ q : QIdx (geomOf ell k S), ∀ b ∈ inBlockBonds (yq q) (ell ^ jq q),
        frobNorm ((((periodicGaugeTransform (γB q) U b : Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
          ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * AdalyFormal.TowerLoc.rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) / (ell : ℝ) ^ jq q) ∧
      (∀ q : QIdx (geomOf ell k S), ∀ i, i < jq q → ∀ z ∈ blockOf (yq q) (ell ^ jq q), z ∈ CoarseLattice L (ell ^ i) →
        ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf (yq q) (ell ^ jq q) →
        frobNorm ((bgTower (geomOf ell k S) (periodicGaugeTransform (γB q) U) i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
          ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * AdalyFormal.TowerLoc.rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) * (ell : ℝ) ^ i / (ell : ℝ) ^ jq q) := by
  classical
  have key : ∀ q : QIdx (geomOf ell k S), ∃ γ : GaugeFn L,
      (∀ b ∈ inBlockBonds (yq q) (ell ^ jq q),
        frobNorm ((((periodicGaugeTransform γ U b : Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
          ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * AdalyFormal.TowerLoc.rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) / (ell : ℝ) ^ jq q) ∧
      (∀ i, i < jq q → ∀ z ∈ blockOf (yq q) (ell ^ jq q), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
        coarseShift z (ell ^ i) μ ∈ blockOf (yq q) (ell ^ jq q) →
        frobNorm ((bgTower (geomOf ell k S) (periodicGaugeTransform γ U) i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
          ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * AdalyFormal.TowerLoc.rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) * (ell : ℝ) ^ i / (ell : ℝ) ^ jq q) := by
    intro q
    by_cases h1 : 1 ≤ jq q
    · exact blockGauge_of_chart12 hell hS hRM hbig hη hα ha1 hsm4 U (jq_le q) (yq_mem q) (hch q h1)
    · have h0 : jq q = 0 := by omega
      refine ⟨fun _ => 1, ?_, ?_⟩
      · intro b hb
        rw [h0, pow_zero, inBlockBonds_one_empty12 hL] at hb
        exact absurd hb (Finset.notMem_empty _)
      · intro i hi
        omega
  exact ⟨fun q => (key q).choose, fun q => (key q).choose_spec.1, fun q => (key q).choose_spec.2⟩

/-- **F1 from per-block charts.**  The SK1 field `SiteS1` with the SK1 constant `csOf a (rhoT ell 12 M (alpha1 ell α₀))`. -/
theorem siteS1_of_charts12 {ell M R k : ℕ} {L : PeriodicLatticeExtent} (hell : 2 ≤ ell)
    {S : Tower L} (hS : Admissible ell M R k S) (hRM : 18 ≤ R * M) (hbig : ∀ σ : Fin 3, 4 * ell ^ k < L σ + 1)
    (hL : ∀ σ : Fin 3, 1 ≤ L σ) {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀)
    (ha1 : (12 : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * AdalyFormal.TowerLoc.rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1)
    (U : LinkCfg L)
    (hch : ∀ q : QIdx (geomOf ell k S), 1 ≤ jq q → AnchorChart12 ell M k S U α₀ η (yq q) (7 * ell ^ jq q))
    (a : ℝ) (ha : 0 < a) :
    AdalyFormal.M2Skel.SiteS1 ell k S U a
      (AdalyFormal.M1IMS.csOf a (AdalyFormal.M1GaugeW4.rhoT ell 12 M (AdalyFormal.M2Skel.alpha1 ell α₀))) := by
  have hell0 : 0 < ell := by omega
  obtain ⟨γB, hU, hT⟩ := exists_blockGauges12 hell hS hRM hbig hL hη hα ha1 hsm4 U hch
  have hρ : 0 ≤ AdalyFormal.M1GaugeW4.rhoT ell 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) :=
    AdalyFormal.M1GaugeW4.rhoT_nonneg ell 12 M _ (by positivity)
  have hM0 : 0 < max 6 (16 / (3 * a)) := lt_max_of_lt_left (by norm_num)
  intro f
  have h := AdalyFormal.M1Site.site_coercive_weighted_perblock ell k hell (AdalyFormal.M1Site.hdvd_of_admissible hS)
    (AdalyFormal.M1Site.properTower_geomOf hell0 hS) U γB a ha _ hρ hU hT f
  unfold AdalyFormal.M1IMS.csOf AdalyFormal.M2Skel.alpha1
  rw [div_mul_eq_mul_div, div_le_iff₀ hM0]
  exact h.trans_eq (mul_comm _ _)

end AdalyFormal.OneGap12
#print axioms AdalyFormal.OneGap12.siteS1_of_charts12
#print axioms AdalyFormal.OneGap12.inBlockBonds_one_empty12
#print axioms AdalyFormal.OneGap12.exists_blockGauges12
