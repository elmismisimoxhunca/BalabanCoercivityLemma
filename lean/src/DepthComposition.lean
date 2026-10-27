import PureGaugeTest
import ExcludedCorner

set_option autoImplicit false
noncomputable section
namespace Prop1.ScaleFittedTest.Composition

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.BlockedBackground
  (ubarSU2 ubarTowerSU2 ubarTowerSU2_zero ubarTowerSU2_succ)
open DepthUniformity.Strided (orientedPlaqHolS)
open DepthUniformity.RawTower
  (betaRec etaSq geomS betaRec_zero betaRec_succ betaRec_nonneg betaRec_le
   betaRec_le_two_alpha0 betaRec_le_two_a betaRec_lt_alpha0_of_lt)
open DepthUniformity.Fitted
  (ScaleFittedPropagation SublatticePlaqBound sublatticePlaqBound_one_iff
   level_dvd_of_depth_dvd coarseLattice_antitone)

variable {L : PeriodicLatticeExtent}

/-- Coordinate nesting uses the certified antitone theorem, not an invented
coarse lattice or any assumption about extent divisibility. -/
theorem level_corner_nested (ell i j : ℕ) (hij : i ≤ j)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (ell^j)) :
    y ∈ CoarseLattice L (ell^i) := by
  have hdiv : ell^i ∣ ell^j := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hij
    rw [pow_add]
    exact dvd_mul_right _ _
  exact coarseLattice_antitone hdiv hy

/-- Fresh induction on the actual raw tower, conditional ONLY on the corrected
scale-fitted analytic proposition. Each output is literally the next input:
SublatticePlaqBound (ell^j * ell) is the level-(j+1) bound. The one-scale extent
condition is obtained from the full depth condition with the imported lemma. -/
theorem tower_recurrence (ell k : ℕ) (hell : 2 ≤ ell) (C0 alpha0 c2' : ℝ)
    (hC0 : 0 ≤ C0) (ha : 0 < alpha0)
    (hcontract : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1)
    (hc : 2 * alpha0 ≤ c2')
    (hdepth : ∀ μ : Fin 3, ell^k ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration SU2 L)
    (hProp1 : ScaleFittedPropagation (L := L) ell C0 c2')
    (hfine : SublatticePlaqBound 1 U (alpha0 * etaSq ell k)) :
    ∀ j : ℕ, j ≤ k →
      SublatticePlaqBound (ell^j) (ubarTowerSU2 ell U j)
        (betaRec ell C0 alpha0 k j) := by
  intro j
  induction j with
  | zero =>
      intro _
      simpa only [pow_zero, ubarTowerSU2_zero, betaRec_zero] using hfine
  | succ j ih =>
      intro hjk
      have hj : j ≤ k := Nat.le_of_succ_le hjk
      have hnonneg := betaRec_nonneg ell C0 alpha0 hC0 ha k j
      have hsmall := betaRec_le_two_alpha0 ell C0 alpha0 hell hC0 ha hcontract hj
      have hdiv : ∀ μ : Fin 3, ell^j * ell ∣ (L μ + 1) := by
        rw [← pow_succ]
        exact level_dvd_of_depth_dvd ell k hdepth hjk
      have hstep := hProp1 (ell^j) (Nat.pow_pos (by omega)) hdiv
        (ubarTowerSU2 ell U j) (betaRec ell C0 alpha0 k j)
        hnonneg (hsmall.trans hc) (ih hj)
      simpa only [ubarTowerSU2_succ, pow_succ, betaRec_succ] using hstep

/-- The established scalar telescoping/geometric-series contraction is reused,
not replaced by an unproved depth-dependent constant. It yields the uniform
ceiling, per-level damping, the explicit geometric bound, and strict smallness
at intermediate levels. This does NOT discharge hProp1. -/
theorem depth_uniformity (ell k : ℕ) (hell : 2 ≤ ell) (C0 alpha0 c2' : ℝ)
    (hC0 : 0 ≤ C0) (ha : 0 < alpha0)
    (hcontract : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1)
    (hc : 2 * alpha0 ≤ c2')
    (hdepth : ∀ μ : Fin 3, ell^k ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration SU2 L)
    (hProp1 : ScaleFittedPropagation (L := L) ell C0 c2')
    (hfine : ∀ y μ ν,
      frobNorm (((orientedPlaqHolS 1 U y μ ν : SU2) : M2) - 1) ≤ alpha0 * etaSq ell k)
    (j : ℕ) (hjk : j ≤ k) :
    SublatticePlaqBound (ell^j) (ubarTowerSU2 ell U j) (2 * alpha0) ∧
    SublatticePlaqBound (ell^j) (ubarTowerSU2 ell U j)
      (2 * (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k)) ∧
    SublatticePlaqBound (ell^j) (ubarTowerSU2 ell U j)
      ((alpha0 * ((ell : ℝ)^2)^j * etaSq ell k) *
        (1 + 4 * C0 * alpha0 * etaSq ell k * geomS ell j)) ∧
    (j < k → ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L (ell^j) →
      ∀ μ ν : Fin 3,
        frobNorm (((orientedPlaqHolS (ell^j) (ubarTowerSU2 ell U j) y μ ν : SU2) : M2) - 1)
          < alpha0) := by
  have hb := tower_recurrence ell k hell C0 alpha0 c2' hC0 ha hcontract hc hdepth U
    hProp1 ((sublatticePlaqBound_one_iff U _).mpr hfine) j hjk
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy μ ν
    exact (hb y hy μ ν).trans
      (betaRec_le_two_alpha0 ell C0 alpha0 hell hC0 ha hcontract hjk)
  · intro y hy μ ν
    exact (hb y hy μ ν).trans
      (betaRec_le_two_a ell C0 alpha0 hell hC0 ha hcontract hjk)
  · intro y hy μ ν
    exact (hb y hy μ ν).trans
      (betaRec_le ell C0 alpha0 hell hC0 ha hcontract j hjk)
  · intro hjlt y hy μ ν
    exact (hb y hy μ ν).trans_lt
      (betaRec_lt_alpha0_of_lt ell C0 alpha0 hell hC0 ha hcontract hjlt).2

/-- All intermediate levels may also be evaluated at a final-level corner,
by nesting. No unrestricted/all-sites conclusion is inferred. -/
theorem uniform_at_final_corners (ell k : ℕ) (hell : 2 ≤ ell) (C0 alpha0 c2' : ℝ)
    (hC0 : 0 ≤ C0) (ha : 0 < alpha0)
    (hcontract : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1)
    (hc : 2 * alpha0 ≤ c2')
    (hdepth : ∀ μ : Fin 3, ell^k ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration SU2 L)
    (hProp1 : ScaleFittedPropagation (L := L) ell C0 c2')
    (hfine : SublatticePlaqBound 1 U (alpha0 * etaSq ell k))
    (j : ℕ) (hjk : j ≤ k) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L (ell^k)) (μ ν : Fin 3) :
    frobNorm (((orientedPlaqHolS (ell^j) (ubarTowerSU2 ell U j) y μ ν : SU2) : M2) - 1)
      ≤ 2 * alpha0 := by
  have hb := tower_recurrence ell k hell C0 alpha0 c2' hC0 ha hcontract hc hdepth U
    hProp1 hfine j hjk
  exact (hb y (level_corner_nested ell j k hjk y hy) μ ν).trans
    (betaRec_le_two_alpha0 ell C0 alpha0 hell hC0 ha hcontract hjk)

end Prop1.ScaleFittedTest.Composition

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`Prop1.ScaleFittedTest.Composition.level_corner_nested,
      `Prop1.ScaleFittedTest.Composition.tower_recurrence,
      `Prop1.ScaleFittedTest.Composition.depth_uniformity,
      `Prop1.ScaleFittedTest.Composition.uniform_at_final_corners] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"COMPOSITION_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
