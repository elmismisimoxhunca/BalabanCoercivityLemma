import StrideSU2

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
noncomputable section
namespace Prop1.ScaleFittedTest.Stride

open AdalyFormal.Balaban.SuTwoLogExp (SU2 torus)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open DepthUniformity.Strided (orientedPlaqHolS)
open Prop1.RawBoundary (torusScale qRaw raw_torus plaq_map)

/-- The four edges of the EXCLUDED plaquette. -/
def excludedEdge (i : Fin 4) : Edge :=
  ![(corner, 0), (coarseShift corner 4 0, 1),
    (coarseShift corner 4 1, 0), (corner, 1)] i

theorem excluded_loop_values : ∀ (i : Fin 4) (o : Fin 3 → Fin 2),
    let c := excludedEdge i
    let q := Multiplicative.toAdd (loopVar 2 2 qField c (offsetSite c.1 o))
    q = 0 ∨ q = 2 ∨ q = -2 := by decide +kernel

theorem excluded_bond (t : ℝ) (ht : |t| ≤ 1/10) (i : Fin 4) :
    ubarSU2 2 2 (field t) (excludedEdge i) =
      torusScale t (Multiplicative.ofAdd (qRaw 2 2 qField (excludedEdge i))) := by
  apply raw_torus
  intro x hx
  rw [stepBlock_sparse] at hx
  obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hx).1
  have hq : |((Multiplicative.toAdd
      (loopVar 2 2 qField (excludedEdge i) (offsetSite (excludedEdge i).1 o)) : ℚ) : ℝ)| ≤ 2 := by
    rcases excluded_loop_values i o with h | h | h <;> rw [h] <;> norm_num
  calc
    |_ * t| = |_| * |t| := abs_mul _ _
    _ ≤ 2 * (1/10 : ℝ) := mul_le_mul hq ht (abs_nonneg _) (by norm_num)
    _ < Real.pi := by linarith [Real.pi_gt_three]

/-- Exact nonlinear raw output at the bad corner: this demonstrates the failed
attack on the genuine operator, while corner_only_ell_aligned explains why the
attack is not a counterexample to ScaleFittedPropagation. -/
theorem excluded_holonomy (t : ℝ) (ht : |t| ≤ 1/10) :
    orientedPlaqHolS 4 (ubarSU2 2 2 (field t)) corner 0 1 =
      torus (-(9/2 : ℝ) * t) := by
  have h0 := excluded_bond t ht 0
  have h1 := excluded_bond t ht 1
  have h2 := excluded_bond t ht 2
  have h3 := excluded_bond t ht 3
  change ubarSU2 2 2 (field t) (corner, 0) =
    torusScale t (Multiplicative.ofAdd (qRaw 2 2 qField (corner, 0))) at h0
  change ubarSU2 2 2 (field t) (coarseShift corner 4 0, 1) =
    torusScale t (Multiplicative.ofAdd (qRaw 2 2 qField (coarseShift corner 4 0, 1))) at h1
  change ubarSU2 2 2 (field t) (coarseShift corner 4 1, 0) =
    torusScale t (Multiplicative.ofAdd (qRaw 2 2 qField (coarseShift corner 4 1, 0))) at h2
  change ubarSU2 2 2 (field t) (corner, 1) =
    torusScale t (Multiplicative.ofAdd (qRaw 2 2 qField (corner, 1))) at h3
  have hp : orientedPlaqHolS 4 (ubarSU2 2 2 (field t)) corner 0 1 =
      orientedPlaqHolS 4
        (fun e => torusScale t (Multiplicative.ofAdd (qRaw 2 2 qField e))) corner 0 1 := by
    unfold orientedPlaqHolS
    rw [h0, h1, h2, h3]
  rw [hp, plaq_map]
  change torus (((Multiplicative.toAdd _ : ℚ) : ℝ) * t) = _
  rw [excluded_output_coefficient]
  norm_num

end Prop1.ScaleFittedTest.Stride

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let n := `Prop1.ScaleFittedTest.Stride.excluded_holonomy
  let axioms ← Lean.collectAxioms n
  Lean.logInfo m!"EXCLUDED_CORNER_AXIOMS {n}: {axioms}"
  for ax in axioms do
    unless allowed.contains ax do
      throwError "Nonstandard axiom in {n}: {ax}"
