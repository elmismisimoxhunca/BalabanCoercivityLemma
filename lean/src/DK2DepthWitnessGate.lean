import ExcludedCorner
import PureGaugeTest

set_option autoImplicit false
noncomputable section
namespace Prop1.ScaleFittedRepair

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.BlockedBackground
  (ubarSU2 ubarSU2_gauge ubarSU2_trivialU ubarTowerSU2 ubarTowerSU2_zero ubarTowerSU2_succ)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open DepthUniformity.Strided (orientedPlaqHolS)
open DepthUniformity.RawTower
  (pureGauge orientedPlaqHolS_pureGauge frobNorm_one_sub_one prop1_poly_nonneg
   betaRec etaSq betaRec_zero betaRec_succ betaRec_nonneg betaRec_le_two_alpha0)
open DepthUniformity.Fitted
  (ScaleFittedPropagation SublatticePlaqBound level_dvd_of_depth_dvd coarseLattice_antitone)

variable {L : PeriodicLatticeExtent}

/-- Fresh exact-operator calculation, including the stride multiplication. -/
theorem pure_raw (s ell : ℕ) (g : PeriodicLatticeSite L → SU2) :
    ubarSU2 s ell (pureGauge s g) = pureGauge (s * ell) g := by
  funext c
  unfold pureGauge
  rw [ubarSU2_gauge, ubarSU2_trivialU]

/-- Both sides of the actual residual pass for the whole pure-gauge family. -/
theorem pure_test (s ell : ℕ) (C0 β : ℝ) (hC : 0 ≤ C0) (hβ : 0 ≤ β)
    (g : PeriodicLatticeSite L → SU2) :
    SublatticePlaqBound s (pureGauge s g) β ∧
    SublatticePlaqBound (s * ell) (ubarSU2 s ell (pureGauge s g))
      ((ell : ℝ)^2 * β + C0 * ((ell : ℝ)^2 * β)^2) := by
  constructor
  · intro y _ μ ν
    rw [orientedPlaqHolS_pureGauge, frobNorm_one_sub_one]
    exact hβ
  · rw [pure_raw]
    intro y _ μ ν
    rw [orientedPlaqHolS_pureGauge, frobNorm_one_sub_one]
    exact prop1_poly_nonneg ell C0 β hC hβ

open Prop1.ScaleFittedTest.Stride

/-- Kernel-computed numeric corner test, not an assertion that the old
unrestricted witness transfers. Extent 8; s=ell=2; corner=(2,6,0). -/
theorem excluded_corner_rechecked :
    corner ∈ CoarseLattice witL 2 ∧ corner ∉ CoarseLattice witL (2 * 2) := by
  simp only [mem_CoarseLattice]
  decide +kernel

/-- Exact SU2 numerical field t=1/100, with all output corners quantified.
Reuse the verified coefficient-to-SU2 evaluations of the concrete field.
The polynomial is precisely that in ScaleFittedPropagation, for every input
radius, not only one convenient choice. -/
theorem numeric_test (C0 c2' β : ℝ) (hC : 0 ≤ C0) (hβ : 0 ≤ β)
    (_hc : β ≤ c2') (hin : SublatticePlaqBound 2 (field (1/100)) β) :
    (∀ μ : Fin 3, 2 * 2 ∣ (witL μ + 1)) ∧
    SublatticePlaqBound (2 * 2) (ubarSU2 2 2 (field (1/100)))
      ((2 : ℝ)^2 * β + C0 * ((2 : ℝ)^2 * β)^2) := by
  refine ⟨by decide +kernel, ?_⟩
  intro y hy μ ν
  have hout := output_bound (1/100) (by norm_num) y hy μ ν
  have hr := radius_le_of_input (1/100) β hin
  have hq := mul_nonneg hC (sq_nonneg ((2 : ℝ)^2 * β))
  nlinarith

/-- The concrete test is nonvacuous: its input radius is attained at origin. -/
theorem numeric_input : SublatticePlaqBound 2 (field (1/100)) (radius (1/100)) :=
  input_bound _

/-- Fresh induction, retaining the analytic residual as a visible hypothesis. -/
theorem repaired_depth (ell k : ℕ) (hell : 2 ≤ ell) (C0 a c : ℝ)
    (hC : 0 ≤ C0) (ha : 0 < a)
    (hcontract : 4 * C0 * a * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1)
    (hc : 2 * a ≤ c) (hd : ∀ μ : Fin 3, ell^k ∣ (L μ + 1))
    (V : PeriodicLinkConfiguration SU2 L)
    (hp : ScaleFittedPropagation (L := L) ell C0 c)
    (hin : SublatticePlaqBound 1 V (a * etaSq ell k)) :
    ∀ j, j ≤ k → SublatticePlaqBound (ell^j) (ubarTowerSU2 ell V j)
      (betaRec ell C0 a k j) := by
  intro j
  induction j with
  | zero =>
      intro _
      simpa only [pow_zero, ubarTowerSU2_zero, betaRec_zero] using hin
  | succ j ih =>
      intro hjk
      have hj := Nat.le_of_succ_le hjk
      have hdiv : ∀ μ : Fin 3, ell^j * ell ∣ (L μ + 1) := by
        rw [← pow_succ]
        exact level_dvd_of_depth_dvd ell k hd hjk
      have hb := betaRec_le_two_alpha0 ell C0 a hell hC ha hcontract hj
      have hout := hp (ell^j) (Nat.pow_pos (by omega)) hdiv
        (ubarTowerSU2 ell V j) (betaRec ell C0 a k j)
        (betaRec_nonneg ell C0 a hC ha k j) (hb.trans hc) (ih hj)
      simpa only [ubarTowerSU2_succ, pow_succ, betaRec_succ] using hout

/-- Reuse the scalar telescoping/contraction estimate and the certified
coarse-lattice nesting, giving a depth-independent bound at final corners. -/
theorem repaired_uniform (ell k : ℕ) (hell : 2 ≤ ell) (C0 a c : ℝ)
    (hC : 0 ≤ C0) (ha : 0 < a)
    (hcontract : 4 * C0 * a * (ell : ℝ)^2 ≤ (ell : ℝ)^2 - 1)
    (hc : 2 * a ≤ c) (hd : ∀ μ : Fin 3, ell^k ∣ (L μ + 1))
    (V : PeriodicLinkConfiguration SU2 L)
    (hp : ScaleFittedPropagation (L := L) ell C0 c)
    (hin : SublatticePlaqBound 1 V (a * etaSq ell k))
    (j : ℕ) (hj : j ≤ k) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L (ell^k)) (μ ν : Fin 3) :
    frobNorm (((orientedPlaqHolS (ell^j) (ubarTowerSU2 ell V j) y μ ν : SU2) : M2) - 1)
      ≤ 2 * a := by
  have hdiv : ell^j ∣ ell^k := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [pow_add]
    exact dvd_mul_right _ _
  have hb := repaired_depth ell k hell C0 a c hC ha hcontract hc hd V hp hin j hj
  exact (hb y (coarseLattice_antitone hdiv hy) μ ν).trans
    (betaRec_le_two_alpha0 ell C0 a hell hC ha hcontract hj)

end Prop1.ScaleFittedRepair

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`Prop1.ScaleFittedRepair.pure_raw, `Prop1.ScaleFittedRepair.pure_test,
      `Prop1.ScaleFittedRepair.excluded_corner_rechecked, `Prop1.ScaleFittedRepair.numeric_test,
      `Prop1.ScaleFittedRepair.numeric_input, `Prop1.ScaleFittedRepair.repaired_depth,
      `Prop1.ScaleFittedRepair.repaired_uniform] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"REPAIR_GATE_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
  Lean.logInfo "REPAIR_WITNESS_GATE_COMPLETE"
