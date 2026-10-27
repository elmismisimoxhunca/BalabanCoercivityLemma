import FittedTarget

set_option autoImplicit false

/-!
A separate, composable interface on the ACTUAL physical-coordinate raw tower.
This is NOT asserted to follow from `OneStepPropagationFitted`: restricting only
that proposition's output cannot furnish its next global input.

At stride s, genuine input sites lie in CoarseLattice L s and genuine output
sites in CoarseLattice L (s*ell). At s=1 this is exactly the requested output
restriction CoarseLattice L ell. Full tileability to depth k is ell^k | (L μ+1).
-/
noncomputable section
namespace DepthUniformity.Fitted

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.BlockedBackground
  (ubarSU2 ubarTowerSU2 ubarTowerSU2_succ)
open DepthUniformity.Strided (orientedPlaqHolS)
open DepthUniformity.RawTower
  (betaRec etaSq betaRec_succ betaRec_nonneg betaRec_le_two_alpha0
   betaRec_le_two_a betaRec_lt_alpha0_of_lt)

variable {L : PeriodicLatticeExtent}

/-- Plaquette bound on the genuine stride-s sublattice. -/
def SublatticePlaqBound (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (β : ℝ) : Prop :=
  ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L s → ∀ μ ν : Fin 3,
    frobNorm (((orientedPlaqHolS s V y μ ν : SU2) : M2) - 1) ≤ β

/-- Scale-aware analytic obligation. Input and output domains both change with
stride. Divisibility guarantees complete blocks and shift-closed output corners.
This is a hypothesis, NOT a proof of Proposition 1. -/
def ScaleFittedPropagation (ell : ℕ) (C0 c2' : ℝ) : Prop :=
  ∀ s : ℕ, 0 < s → (∀ μ : Fin 3, s * ell ∣ (L μ + 1)) →
    ∀ (V : PeriodicLinkConfiguration SU2 L) (β : ℝ),
      0 ≤ β → β ≤ c2' → SublatticePlaqBound s V β →
      SublatticePlaqBound (s * ell) (ubarSU2 s ell V)
        ((ell : ℝ)^2 * β + C0 * ((ell : ℝ)^2 * β)^2)

/-- Literal all-sites input at unit stride: every site is in CoarseLattice L 1. -/
theorem sublatticePlaqBound_one_iff (V : PeriodicLinkConfiguration SU2 L) (β : ℝ) :
    SublatticePlaqBound 1 V β ↔ ∀ y μ ν,
      frobNorm (((orientedPlaqHolS 1 V y μ ν : SU2) : M2) - 1) ≤ β := by
  constructor
  · intro h y μ ν
    exact h y (mem_CoarseLattice.mpr (fun _ => Nat.mod_one _)) μ ν
  · intro h y _ μ ν
    exact h y μ ν

/-- Extent divisibility propagates DOWN to all levels, not UP from level one. -/
theorem level_dvd_of_depth_dvd (ell k : ℕ)
    (hdepth : ∀ μ : Fin 3, ell ^ k ∣ (L μ + 1)) {j : ℕ} (hjk : j ≤ k) :
    ∀ μ : Fin 3, ell ^ j ∣ (L μ + 1) := by
  intro μ
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hjk
  exact dvd_trans (by rw [pow_add]; exact dvd_mul_right _ _) (hdepth μ)

/-- Genuine coarse sites nest under divisibility of scales; no extent hypothesis
is required for this purely coordinatewise inclusion. -/
theorem coarseLattice_antitone {s t : ℕ} (hst : s ∣ t)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L t) :
    y ∈ CoarseLattice L s := by
  apply mem_CoarseLattice.mpr
  intro μ
  exact Nat.mod_eq_zero_of_dvd (dvd_trans hst
    (Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy μ)))

/-- The imported raw-tower induction, with its input/output domains repaired.
The only new analytic assumption is explicitly `ScaleFittedPropagation`, not the
weaker literal output-only interface. All contraction arithmetic is reused. -/
theorem sublatticePlaqBound_tower
    (ell : ℕ) (hell : 2 ≤ ell) (C0 alpha0 c2' : ℝ)
    (hC0 : 0 ≤ C0) (hα0 : 0 < alpha0)
    (hC0α0 : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1)
    (hc2 : 2 * alpha0 ≤ c2') (k : ℕ)
    (hdepth : ∀ μ : Fin 3, ell ^ k ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration SU2 L)
    (hProp1 : ScaleFittedPropagation (L := L) ell C0 c2')
    (hFine : SublatticePlaqBound 1 U (alpha0 * etaSq ell k)) :
    ∀ j : ℕ, j ≤ k →
      SublatticePlaqBound (ell ^ j) (ubarTowerSU2 ell U j)
        (betaRec ell C0 alpha0 k j) := by
  intro j
  induction j with
  | zero => intro _; exact hFine
  | succ j ih =>
      intro hjk
      have hjk' : j ≤ k := Nat.le_of_succ_le hjk
      have hβj2 := betaRec_le_two_alpha0 ell C0 alpha0 hell hC0 hα0 hC0α0 hjk'
      have hβj0 := betaRec_nonneg ell C0 alpha0 hC0 hα0 k j
      have hpow : ell ^ (j + 1) = ell ^ j * ell := pow_succ ell j
      have hdvd : ∀ μ : Fin 3, ell ^ j * ell ∣ (L μ + 1) := by
        rw [← hpow]
        exact level_dvd_of_depth_dvd ell k hdepth hjk
      rw [ubarTowerSU2_succ, hpow, betaRec_succ]
      exact hProp1 (ell ^ j) (Nat.pow_pos (by omega)) hdvd
        (ubarTowerSU2 ell U j) (betaRec ell C0 alpha0 k j)
        hβj0 (hβj2.trans hc2) (ih hjk')

/-- Depth-uniform plaquette bound on genuine level-j plaquettes, with an
additional per-level damping bound and strict intermediate-level smallness. -/
theorem sublatticePlaqBound_tower_uniform
    (ell k : ℕ) (hell : 2 ≤ ell) (C0 alpha0 c2' : ℝ)
    (hC0 : 0 ≤ C0) (hα0 : 0 < alpha0)
    (hC0α0 : 4 * C0 * alpha0 * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1)
    (hc2 : 2 * alpha0 ≤ c2')
    (hdepth : ∀ μ : Fin 3, ell ^ k ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration SU2 L)
    (hProp1 : ScaleFittedPropagation (L := L) ell C0 c2')
    (hFine : ∀ y μ ν,
      frobNorm (((orientedPlaqHolS 1 U y μ ν : SU2) : M2) - 1) ≤ alpha0 * etaSq ell k)
    (j : ℕ) (hjk : j ≤ k) :
    SublatticePlaqBound (ell ^ j) (ubarTowerSU2 ell U j) (2 * alpha0) ∧
    SublatticePlaqBound (ell ^ j) (ubarTowerSU2 ell U j)
      (2 * (alpha0 * ((ell : ℝ)^2)^j * etaSq ell k)) ∧
    (j < k → ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L (ell ^ j) →
      ∀ μ ν : Fin 3,
        frobNorm (((orientedPlaqHolS (ell ^ j) (ubarTowerSU2 ell U j) y μ ν : SU2) : M2) - 1)
          < alpha0) := by
  have hb := sublatticePlaqBound_tower ell hell C0 alpha0 c2' hC0 hα0 hC0α0 hc2 k
    hdepth U hProp1 ((sublatticePlaqBound_one_iff _ _).mpr hFine) j hjk
  refine ⟨?_, ?_, ?_⟩
  · intro y hy μ ν
    exact (hb y hy μ ν).trans
      (betaRec_le_two_alpha0 ell C0 alpha0 hell hC0 hα0 hC0α0 hjk)
  · intro y hy μ ν
    exact (hb y hy μ ν).trans
      (betaRec_le_two_a ell C0 alpha0 hell hC0 hα0 hC0α0 hjk)
  · intro hjlt y hy μ ν
    exact (hb y hy μ ν).trans_lt
      (betaRec_lt_alpha0_of_lt ell C0 alpha0 hell hC0 hα0 hC0α0 hjlt).2

end DepthUniformity.Fitted

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`DepthUniformity.Fitted.ScaleFittedPropagation,
      `DepthUniformity.Fitted.sublatticePlaqBound_one_iff,
      `DepthUniformity.Fitted.level_dvd_of_depth_dvd,
      `DepthUniformity.Fitted.coarseLattice_antitone,
      `DepthUniformity.Fitted.sublatticePlaqBound_tower,
      `DepthUniformity.Fitted.sublatticePlaqBound_tower_uniform] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"SCALE_FITTED_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
