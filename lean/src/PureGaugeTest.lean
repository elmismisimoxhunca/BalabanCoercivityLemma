import ScaleFittedTower

set_option autoImplicit false
noncomputable section
namespace Prop1.ScaleFittedTest

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarSU2_gauge ubarSU2_trivialU)
open DepthUniformity.RawTower
  (pureGauge orientedPlaqHolS_pureGauge frobNorm_one_sub_one prop1_poly_nonneg)
open DepthUniformity.Strided (orientedPlaqHolS)
open DepthUniformity.Fitted (SublatticePlaqBound)

variable {L : PeriodicLatticeExtent}

/-- Direct covariance calculation with the exact imported raw operator. No
assumption of any propagation proposition, nor use of modified averaging. -/
theorem raw_pureGauge_stride_scaled (s ell : ℕ)
    (g : PeriodicLatticeSite L → SU2) :
    ubarSU2 s ell (pureGauge s g) = pureGauge (s * ell) g := by
  funext c
  unfold pureGauge
  rw [ubarSU2_gauge, ubarSU2_trivialU]

/-- Flatness is global, hence in particular true on the exact output sublattice. -/
theorem raw_pureGauge_flat (s ell : ℕ) (g : PeriodicLatticeSite L → SU2)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    orientedPlaqHolS (s * ell) (ubarSU2 s ell (pureGauge s g)) y μ ν = 1 := by
  rw [raw_pureGauge_stride_scaled]
  exact orientedPlaqHolS_pureGauge (s * ell) g y μ ν

/-- The input and output of ScaleFittedPropagation, instantiated at ANY pure
 gauge, are both satisfied. This rules out the entire pure-gauge witness class,
 including beta=0 and arbitrary noncommuting site gauges, at every stride. -/
theorem pureGauge_passes_scaleFitted (ell : ℕ) (C0 c2' : ℝ) (hC0 : 0 ≤ C0)
    (s : ℕ) (_hs : 0 < s) (_hdvd : ∀ μ : Fin 3, s * ell ∣ (L μ + 1))
    (g : PeriodicLatticeSite L → SU2) (β : ℝ) (hβ : 0 ≤ β) (_hc : β ≤ c2') :
    SublatticePlaqBound s (pureGauge s g) β ∧
    SublatticePlaqBound (s * ell) (ubarSU2 s ell (pureGauge s g))
      ((ell : ℝ)^2 * β + C0 * ((ell : ℝ)^2 * β)^2) := by
  constructor
  · intro y _ μ ν
    rw [orientedPlaqHolS_pureGauge, frobNorm_one_sub_one]
    exact hβ
  · intro y _ μ ν
    rw [raw_pureGauge_flat, frobNorm_one_sub_one]
    exact prop1_poly_nonneg ell C0 β hC0 hβ

end Prop1.ScaleFittedTest

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`Prop1.ScaleFittedTest.raw_pureGauge_stride_scaled,
      `Prop1.ScaleFittedTest.raw_pureGauge_flat,
      `Prop1.ScaleFittedTest.pureGauge_passes_scaleFitted] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"PURE_GAUGE_TEST_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
