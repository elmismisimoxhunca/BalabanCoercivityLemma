import DepthComposition

set_option autoImplicit false
noncomputable section
namespace Prop1.ScaleFittedProof

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite
  (coarseGaugeTransform stepBlockOf mem_stepBlockOf card_stepBlockOf)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarSU2_gauge)
open DepthUniformity.Strided (orientedPlaqHolS)
open DepthUniformity.Fitted (SublatticePlaqBound ScaleFittedPropagation coarseLattice_antitone)

variable {L : PeriodicLatticeExtent}

/-- The exact admitted output corner has a complete block, including at the
last tile. This derives the old cardinality theorem's fitting hypothesis from
the NEW target's divisibility and scale-alignment hypotheses. -/
theorem output_block_fits (s ell : ℕ)
    (hdvd : ∀ μ : Fin 3, s * ell ∣ (L μ + 1))
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (s * ell)) :
    ∀ μ : Fin 3, (y μ).val + s * ell ≤ L μ + 1 := by
  intro μ
  have hydiv := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy μ)
  have hdiff : s * ell ∣ L μ + 1 - (y μ).val := Nat.dvd_sub (hdvd μ) hydiv
  have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt (y μ).isLt) hdiff
  omega

theorem output_block_card (s ell : ℕ) (hs : 0 < s)
    (hdvd : ∀ μ : Fin 3, s * ell ∣ (L μ + 1))
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (s * ell)) :
    (stepBlockOf y s ell).card = ell ^ 3 :=
  card_stepBlockOf y s ell hs (output_block_fits s ell hdvd y hy)

/-- All actual summation sites lie in the input domain of the residual. -/
theorem block_sites_input_aligned (s ell : ℕ)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (s * ell))
    (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y s ell) :
    x ∈ CoarseLattice L s := by
  have hys : y ∈ CoarseLattice L s := coarseLattice_antitone (dvd_mul_right s ell) hy
  apply mem_CoarseLattice.mpr
  intro μ
  have hb := mem_stepBlockOf.mp hx μ
  have hydiv := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hys μ)
  apply Nat.mod_eq_zero_of_dvd
  have h := dvd_add hydiv hb.2.2
  simpa only [Nat.add_sub_of_le hb.1] using h

/-- Paper (45), with exactly the sublattice input predicate used here. -/
theorem input_gauge_iff (s : ℕ) (g : PeriodicLatticeSite L → SU2)
    (V : PeriodicLinkConfiguration SU2 L) (β : ℝ) :
    SublatticePlaqBound s (coarseGaugeTransform s g V) β ↔
      SublatticePlaqBound s V β := by
  unfold SublatticePlaqBound
  simp only [DepthUniformity.RawTower.plaq_gauge_norm]

/-- Paper (45) for the raw averaged output, NOT the modified relative average. -/
theorem output_gauge_norm (s ell : ℕ) (g : PeriodicLatticeSite L → SU2)
    (V : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    frobNorm (((orientedPlaqHolS (s * ell)
      (ubarSU2 s ell (coarseGaugeTransform s g V)) y μ ν : SU2) : M2) - 1) =
    frobNorm (((orientedPlaqHolS (s * ell) (ubarSU2 s ell V) y μ ν : SU2) : M2) - 1) := by
  have hcov : ubarSU2 s ell (coarseGaugeTransform s g V) =
      coarseGaugeTransform (s * ell) g (ubarSU2 s ell V) := by
    funext c
    exact ubarSU2_gauge s ell g V c
  rw [hcov]
  exact DepthUniformity.RawTower.plaq_gauge_norm _ _ _ _ _ _

end Prop1.ScaleFittedProof

/- Freshly audit both prerequisite witness classes and conditional composition
before using them as the gate for the analytic work. -/
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`Prop1.ScaleFittedTest.raw_pureGauge_stride_scaled,
      `Prop1.ScaleFittedTest.raw_pureGauge_flat,
      `Prop1.ScaleFittedTest.pureGauge_passes_scaleFitted,
      `Prop1.ScaleFittedTest.Stride.concrete_stride_test,
      `Prop1.ScaleFittedTest.Stride.excluded_holonomy,
      `Prop1.ScaleFittedTest.Composition.tower_recurrence,
      `Prop1.ScaleFittedTest.Composition.depth_uniformity,
      `Prop1.ScaleFittedProof.output_block_fits,
      `Prop1.ScaleFittedProof.output_block_card,
      `Prop1.ScaleFittedProof.block_sites_input_aligned,
      `Prop1.ScaleFittedProof.input_gauge_iff,
      `Prop1.ScaleFittedProof.output_gauge_norm] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"GEOMETRY_GATE_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
