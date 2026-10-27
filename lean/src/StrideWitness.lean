import SparseBlocks

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

noncomputable section
namespace Prop1.ScaleFittedTest.Stride

open AdalyFormal.Target.ClayStatement (PeriodicLinkConfiguration)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open DepthUniformity.Strided (orientedPlaqHolS)
open Prop1.RawBoundary (qRaw)

/-- The attempted bad corner has linear curvature coefficient -9/2, greater in
absolute value than ell^2=4, but fails the exact output membership condition. -/
theorem excluded_output_coefficient :
    Multiplicative.toAdd (orientedPlaqHolS 4
      (fun e => Multiplicative.ofAdd (qRaw 2 2 qField e)) corner 0 1) = -(9/2 : ℚ) := by
  simp only [qRaw, stepBlock_sparse]
  decide +kernel

/-- Explicit finite table for the genuine 4-aligned output bonds. -/
def qOutput : PeriodicLinkConfiguration (Multiplicative ℚ) witL :=
  fun e => Multiplicative.ofAdd
    (if e.2 = 1 then (if (e.1 0).val < 4 then 1 else -1) else 0)

theorem fitted_raw_coefficients : ∀ (y : Site), y ∈ CoarseLattice witL 4 →
    ∀ μ : Fin 3, qRaw 2 2 qField (y, μ) = Multiplicative.toAdd (qOutput (y, μ)) := by
  simp only [mem_CoarseLattice, qRaw, stepBlock_sparse]
  decide +kernel

theorem fitted_offset_loop_values : ∀ (y : Site), y ∈ CoarseLattice witL 4 →
    ∀ (μ : Fin 3) (o : Fin 3 → Fin 2),
      let q := Multiplicative.toAdd (loopVar 2 2 qField (y, μ) (offsetSite y o))
      q = 0 ∨ q = 2 ∨ q = -2 := by
  simp only [mem_CoarseLattice]
  decide +kernel

theorem fitted_loop_values (y : Site) (hy : y ∈ CoarseLattice witL 4)
    (μ : Fin 3) (x : Site) (hx : x ∈ stepBlockOf y 2 2) :
      let q := Multiplicative.toAdd (loopVar 2 2 qField (y, μ) x)
      q = 0 ∨ q = 2 ∨ q = -2 := by
  rw [stepBlock_sparse] at hx
  obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hx).1
  exact fitted_offset_loop_values y hy μ o

theorem fitted_loop_coefficients (y : Site) (hy : y ∈ CoarseLattice witL 4)
    (μ : Fin 3) (x : Site) (hx : x ∈ stepBlockOf y 2 2) :
      |Multiplicative.toAdd (loopVar 2 2 qField (y, μ) x)| ≤ 2 := by
  rcases fitted_loop_values y hy μ x hx with h | h | h <;> rw [h] <;> norm_num

theorem fitted_output_coefficients : ∀ (y : Site), y ∈ CoarseLattice witL 4 →
    ∀ μ ν : Fin 3,
      let q := Multiplicative.toAdd (orientedPlaqHolS 4 qOutput y μ ν)
      q = 0 ∨ q = 2 ∨ q = -2 := by
  simp only [mem_CoarseLattice]
  decide +kernel

theorem fitted_shift_closed : ∀ (y : Site), y ∈ CoarseLattice witL 4 →
    ∀ μ : Fin 3, coarseShift y 4 μ ∈ CoarseLattice witL 4 := by
  intro y hy μ
  exact AdalyFormal.Balaban.CoarseCurl.coarseShift_mem_coarseLattice extent_dvd hy μ

theorem fitted_blocks_complete : ∀ (y : Site), y ∈ CoarseLattice witL 4 →
    (stepBlockOf y 2 2).card = 8 := by
  simp only [mem_CoarseLattice, stepBlock_sparse]
  decide +kernel

end Prop1.ScaleFittedTest.Stride

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`Prop1.ScaleFittedTest.Stride.extent_dvd,
      `Prop1.ScaleFittedTest.Stride.corner_only_ell_aligned,
      `Prop1.ScaleFittedTest.Stride.input_coefficients,
      `Prop1.ScaleFittedTest.Stride.excluded_output_coefficient,
      `Prop1.ScaleFittedTest.Stride.fitted_raw_coefficients,
      `Prop1.ScaleFittedTest.Stride.fitted_loop_coefficients,
      `Prop1.ScaleFittedTest.Stride.fitted_output_coefficients,
      `Prop1.ScaleFittedTest.Stride.fitted_shift_closed,
      `Prop1.ScaleFittedTest.Stride.fitted_blocks_complete] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"STRIDE_COEFFICIENT_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
