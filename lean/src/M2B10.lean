import M2B8
import MC1

/-!
# M2B10 -- NON-VACUITY of `regime_of_class` (m2_bridge_20261014, Layer B1/B5)

`ell = 2`, `M = 32 = 2^5`, `f = 12`, `k = 1`, `R = 18`, the full tower on a fine torus of side `768 = 12·M·ell` per direction (one class cube = the whole torus,
`i = 1`), `w = 128 = 64·ell^i`, and the non-flat configurations `Ufield η χ` (any `|χ| ≤ α₀ η²/10`): every hypothesis of `regime_of_class` holds
(class cube from `cube_isClass`, `PerCubeRegular2` from `perCube_of_M1 (ufield_M1Regular ..)`), the core `{x | ∀σ, 260 ≤ offc ≤ 507}` is non-empty and the
conclusion is delivered (`regime_of_class_nonvac`).  `regime_of_class_nonvac_wide`: the same on a torus of side `384 < 768` (the cube WRAPS in every direction; the cutoff is `≡ 1` and `V = U^g` on every bond).  (This is the full tower: it shows the hypothesis set of the bridge is consistent at `M ≥ 23`; it is NOT a configuration without a
small global gauge.)
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2Bridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1 (M1Regular ufield_M1Regular perCube_of_M1)

theorem regime_of_class_nonvac {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 384) {α₀ : ℝ} (hα : 0 < α₀)
    (χ : Bond (scaleUp 2 1 Lu) → ℝ) (hχ : ∀ e, |χ e| ≤ α₀ * ((((2 : ℕ) : ℝ) ^ 1)⁻¹) ^ 2 / 10) :
    ∃ (g : PeriodicLatticeSite (scaleUp 2 1 Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (χc : PeriodicLatticeSite (scaleUp 2 1 Lu) → ℝ) (V : LinkCfg (scaleUp 2 1 Lu)),
      M1Regular 2 32 12 1 (fullTower 2 1 Lu) (((2 : ℕ) : ℝ) ^ 3 * (2 * α₀)) (((2 : ℕ) : ℝ) ^ 1)⁻¹ V ∧ (∃ x, χc x = 1) := by
  have hN : ∀ μ, scaleUp 2 1 Lu μ + 1 = 768 := fun μ => by
    rw [scaleUp_succ 2 1 Lu (by norm_num) μ, hLu μ]
    norm_num
  have hA : Admissible 2 32 18 1 (fullTower 2 1 Lu) :=
    AdalyFormal.M0Corollary.fullTower_admissible 2 32 18 1 (by norm_num) le_rfl Lu (fun μ => by rw [hLu μ]; norm_num)
  have hU := ufield_M1Regular (ell := 2) (M := 32) (f := 12) (k := 1) (by norm_num) (by norm_num) (by norm_num)
    (fullTower 2 1 Lu) hα χ hχ
  have hP := perCube_of_M1 hA hU
  set z : PeriodicLatticeSite (scaleUp 2 1 Lu) := fun μ => ⟨0, by have := hN μ; omega⟩ with hz
  have hgrid : GridCorner (bigSide 32 2 1) z := fun μ => by simp [hz]
  have hbs : bigSide 32 2 1 = 64 := by simp [bigSide]
  have hsub : siteBox z (12 * bigSide 32 2 1) ⊆ (fullTower 2 1 Lu).Om 1 := fun q _ => by simp [fullTower]
  have hyQ : z ∈ siteBox z (12 * bigSide 32 2 1) := by
    rw [mem_siteBox_offc]
    intro σ
    unfold offc
    simp [hz, hbs, hN σ]
  have hy : z ∈ towerBj (fullTower 2 1 Lu) 1 := by
    refine ⟨by simp [fullTower], ?_⟩
    simp [fullTower]
  have hq := cube_isClass hA (j := 1) le_rfl hgrid hsub hyQ hy (by norm_num : 3 * 12 ≤ 18 * 2)
  have hL : ∀ σ, 1 ≤ scaleUp 2 1 Lu σ := fun σ => by have := hN σ; omega
  obtain ⟨g, χc, V, hreg, -, -, hcore, -⟩ :=
    regime_of_class (w := 128) hA (by norm_num) (by norm_num) (by norm_num) hα (by norm_num : (0 : ℝ) < (((2 : ℕ) : ℝ) ^ 1)⁻¹) hP hq
      (z := z) rfl hL (by norm_num) (by rw [hbs]; norm_num)
  refine ⟨g, χc, V, hreg, ?_⟩
  set x : PeriodicLatticeSite (scaleUp 2 1 Lu) := fun μ => ⟨384, by have := hN μ; omega⟩ with hx
  refine ⟨x, hcore x (fun σ _ => ?_)⟩
  unfold offc
  simp [hx, hz, hbs, hN σ]

/-- **the WIDE branch is non-vacuous too**: the same data on a torus of side `384 = 12·M·ell/2 < 768` per direction (the class cube WRAPS in every direction):
the cutoff is `≡ 1`, and `regime_of_class` returns a `V` that equals `U^g` on EVERY bond -- i.e. the one-global-gauge case is recovered. -/
theorem regime_of_class_nonvac_wide {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 192) {α₀ : ℝ} (hα : 0 < α₀)
    (χ : Bond (scaleUp 2 1 Lu) → ℝ) (hχ : ∀ e, |χ e| ≤ α₀ * ((((2 : ℕ) : ℝ) ^ 1)⁻¹) ^ 2 / 10) :
    ∃ (g : PeriodicLatticeSite (scaleUp 2 1 Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (V : LinkCfg (scaleUp 2 1 Lu)),
      M1Regular 2 32 12 1 (fullTower 2 1 Lu) (((2 : ℕ) : ℝ) ^ 3 * (2 * α₀)) (((2 : ℕ) : ℝ) ^ 1)⁻¹ V ∧
      ∀ e : Bond (scaleUp 2 1 Lu), V e = periodicGaugeTransform g (Ufield (((2 : ℕ) : ℝ) ^ 1)⁻¹ χ) e := by
  have hN : ∀ μ, scaleUp 2 1 Lu μ + 1 = 384 := fun μ => by
    rw [scaleUp_succ 2 1 Lu (by norm_num) μ, hLu μ]
    norm_num
  have hA : Admissible 2 32 18 1 (fullTower 2 1 Lu) :=
    AdalyFormal.M0Corollary.fullTower_admissible 2 32 18 1 (by norm_num) le_rfl Lu (fun μ => by rw [hLu μ]; norm_num)
  have hU := ufield_M1Regular (ell := 2) (M := 32) (f := 12) (k := 1) (by norm_num) (by norm_num) (by norm_num)
    (fullTower 2 1 Lu) hα χ hχ
  have hP := perCube_of_M1 hA hU
  set z : PeriodicLatticeSite (scaleUp 2 1 Lu) := fun μ => ⟨0, by have := hN μ; omega⟩ with hz
  have hgrid : GridCorner (bigSide 32 2 1) z := fun μ => by simp [hz]
  have hbs : bigSide 32 2 1 = 64 := by simp [bigSide]
  have hsub : siteBox z (12 * bigSide 32 2 1) ⊆ (fullTower 2 1 Lu).Om 1 := fun q _ => by simp [fullTower]
  have hall : ∀ q : PeriodicLatticeSite (scaleUp 2 1 Lu), q ∈ siteBox z (12 * bigSide 32 2 1) := fun q => by
    rw [mem_siteBox_offc]
    intro σ
    have := offc_lt z q σ
    rw [hbs]; have := hN σ; omega
  have hy : z ∈ towerBj (fullTower 2 1 Lu) 1 := by
    refine ⟨by simp [fullTower], ?_⟩
    simp [fullTower]
  have hq := cube_isClass hA (j := 1) le_rfl hgrid hsub (hall z) hy (by norm_num : 3 * 12 ≤ 18 * 2)
  have hL : ∀ σ, 1 ≤ scaleUp 2 1 Lu σ := fun σ => by have := hN σ; omega
  obtain ⟨g, χc, V, hreg, -, -, hcore, hagree⟩ :=
    regime_of_class (w := 128) hA (by norm_num) (by norm_num) (by norm_num) hα (by norm_num : (0 : ℝ) < (((2 : ℕ) : ℝ) ^ 1)⁻¹) hP hq
      (z := z) rfl hL (by norm_num) (by rw [hbs]; norm_num)
  refine ⟨g, V, hreg, fun e => hagree e ⟨hall _, hall _⟩ (hcore e.1 (fun σ h => ?_))⟩
  exfalso
  rw [hbs, hN σ] at h
  omega

end AdalyFormal.M2Bridge
