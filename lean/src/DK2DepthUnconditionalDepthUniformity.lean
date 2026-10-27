import DK2DepthPropositionOne
import DepthComposition

set_option autoImplicit false
noncomputable section
namespace DepthUniformityFinal.Assemble

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.BlockedBackground (ubarTowerSU2)
open DepthUniformity.Strided (orientedPlaqHolS)
open DepthUniformity.RawTower (etaSq geomS)
open DepthUniformity.Fitted (SublatticePlaqBound)
open Prop1.ScaleFittedRepair (scale_fitted_propagation)
open Prop1.ScaleFittedTest.Composition (depth_uniformity)

variable {L : PeriodicLatticeExtent}

/-- The two analytic side-conditions inherited unchanged from `tower_recurrence`
(`hcontract` and `hc`) are jointly satisfiable for every `alpha0 > 0` bounded by
`min` of their two individual thresholds, for every `ell ≥ 2`, once `C0` is
fixed at Proposition 1's concrete constant `44465`. This is not vacuous: an
explicit witness is exhibited, not merely asserted. -/
theorem alpha0_witness_exists (ell : ℕ) (hell : 2 ≤ ell) :
    ∃ alpha0 : ℝ, 0 < alpha0 ∧
      4 * (44465 : ℝ) * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1 ∧
      2 * alpha0 ≤ (400 * (ell : ℝ)^2)⁻¹ := by
  have hell' : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hsq : (0 : ℝ) < (ell : ℝ)^2 := by nlinarith
  set A : ℝ := ((ell : ℝ)^2 - 1) / (4 * 44465 * (ell : ℝ)^2) with hAdef
  set B : ℝ := 1 / (800 * (ell : ℝ)^2) with hBdef
  have hApos : 0 < A := by
    rw [hAdef]
    apply div_pos (by nlinarith) (by positivity)
  have hBpos : 0 < B := by rw [hBdef]; positivity
  refine ⟨min A B, lt_min hApos hBpos, ?_, ?_⟩
  · have hle : min A B ≤ A := min_le_left A B
    have key : 4 * 44465 * A * (ell : ℝ)^2 = (ell : ℝ)^2 - 1 := by
      rw [hAdef]; field_simp
    nlinarith [mul_le_mul_of_nonneg_right hle (le_of_lt hsq)]
  · have hle : min A B ≤ B := min_le_right A B
    have key : 2 * B = (400 * (ell : ℝ)^2)⁻¹ := by
      rw [hBdef]; field_simp; ring
    linarith

/-- Fully unconditional depth-`k` uniform plaquette-smallness propagation
across the raw tower `ubarTowerSU2`. This is `depth_uniformity` specialized by
literally supplying `scale_fitted_propagation` (with `C0 = 44465`,
`c2' = (400 * ell^2)⁻¹`, Proposition 1's concrete unconditional constants) in
place of the `hProp1` hypothesis. No `ScaleFittedPropagation` hypothesis
remains. `hcontract` and `hc` are retained exactly as in `tower_recurrence`:
they are genuine, already-proved-satisfiable (see `alpha0_witness_exists`)
analytic side-conditions on the constants `alpha0`, not unpaid hypotheses
about the field `U`. -/
theorem unconditional_depth_uniformity (ell k : ℕ) (hell : 2 ≤ ell) (alpha0 : ℝ)
    (ha : 0 < alpha0)
    (hcontract : 4 * 44465 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1)
    (hc : 2 * alpha0 ≤ (400 * (ell : ℝ)^2)⁻¹)
    (hdepth : ∀ μ : Fin 3, ell^k ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration SU2 L)
    (hfine : ∀ y μ ν,
      frobNorm (((orientedPlaqHolS 1 U y μ ν : SU2) : M2) - 1) ≤ alpha0 * etaSq ell k)
    (j : ℕ) (hjk : j ≤ k) :
    SublatticePlaqBound (ell^j) (ubarTowerSU2 ell U j) (2 * alpha0) ∧
    SublatticePlaqBound (ell^j) (ubarTowerSU2 ell U j)
      (2 * (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k)) ∧
    SublatticePlaqBound (ell^j) (ubarTowerSU2 ell U j)
      ((alpha0 * ((ell : ℝ)^2)^j * etaSq ell k) *
        (1 + 4 * 44465 * alpha0 * etaSq ell k * geomS ell j)) ∧
    (j < k → ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L (ell^j) →
      ∀ μ ν : Fin 3,
        frobNorm (((orientedPlaqHolS (ell^j) (ubarTowerSU2 ell U j) y μ ν : SU2) : M2) - 1)
          < alpha0) :=
  depth_uniformity ell k hell 44465 alpha0 (400 * (ell : ℝ)^2)⁻¹ (by norm_num) ha
    hcontract hc hdepth U (scale_fitted_propagation ell (by omega)) hfine j hjk

end DepthUniformityFinal.Assemble

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`DepthUniformityFinal.Assemble.alpha0_witness_exists,
      `DepthUniformityFinal.Assemble.unconditional_depth_uniformity] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"UNCONDITIONAL_DEPTH_UNIFORMITY_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
  Lean.logInfo "UNCONDITIONAL_DEPTH_UNIFORMITY_COMPLETE"
