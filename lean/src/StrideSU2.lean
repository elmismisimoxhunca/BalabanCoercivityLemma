import StrideWitness

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
noncomputable section
namespace Prop1.ScaleFittedTest.Stride

open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 torus torus_zero torus_add)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open DepthUniformity.Strided (orientedPlaqHolS frobNorm_inv_sub_one)
open DepthUniformity.RawTower (frobNorm_one_sub_one)
open DepthUniformity.Fitted (SublatticePlaqBound)
open Prop1.RawBoundary (torusScale qRaw raw_torus plaq_map torus_inv)

/-- The numerical family is genuinely mapped through the principal logarithm,
with a uniform verified branch margin, not merely a linearized substitute. -/
theorem fitted_bond (t : ℝ) (ht : |t| ≤ 1/10)
    (y : Site) (hy : y ∈ CoarseLattice witL 4) (μ : Fin 3) :
    ubarSU2 2 2 (field t) (y, μ) = torusScale t (qOutput (y, μ)) := by
  have hraw := raw_torus 2 2 qField t (y, μ) (by
    intro x hx
    have hq : |((Multiplicative.toAdd (loopVar 2 2 qField (y, μ) x) : ℚ) : ℝ)| ≤ 2 := by
      exact_mod_cast fitted_loop_coefficients y hy μ x hx
    calc
      |_ * t| = |_| * |t| := abs_mul _ _
      _ ≤ 2 * (1/10 : ℝ) := mul_le_mul hq ht (abs_nonneg _) (by norm_num)
      _ < Real.pi := by linarith [Real.pi_gt_three])
  rw [fitted_raw_coefficients y hy μ] at hraw
  exact hraw

theorem fitted_holonomy (t : ℝ) (ht : |t| ≤ 1/10)
    (y : Site) (hy : y ∈ CoarseLattice witL 4) (μ ν : Fin 3) :
    orientedPlaqHolS 4 (ubarSU2 2 2 (field t)) y μ ν =
      torus (((Multiplicative.toAdd (orientedPlaqHolS 4 qOutput y μ ν) : ℚ) : ℝ) * t) := by
  calc
    _ = orientedPlaqHolS 4 (fun e => torusScale t (qOutput e)) y μ ν := by
      unfold orientedPlaqHolS
      rw [fitted_bond t ht y hy μ,
        fitted_bond t ht (coarseShift y 4 μ) (fitted_shift_closed y hy μ) ν,
        fitted_bond t ht (coarseShift y 4 ν) (fitted_shift_closed y hy ν) μ,
        fitted_bond t ht y hy ν]
    _ = _ := plaq_map (torusScale t) 4 qOutput y μ ν

def radius (t : ℝ) : ℝ := frobNorm (((torus t : SU2) : M2) - 1)

theorem radius_nonneg (t : ℝ) : 0 ≤ radius t := frobNorm_nonneg _

theorem input_holonomy (t : ℝ) (y : Site) (μ ν : Fin 3) :
    orientedPlaqHolS 2 (field t) y μ ν =
      torus (((Multiplicative.toAdd (orientedPlaqHolS 2 qField y μ ν) : ℚ) : ℝ) * t) :=
  plaq_map (torusScale t) 2 qField y μ ν

theorem input_at_origin (t : ℝ) : orientedPlaqHolS 2 (field t) origin 0 1 = torus t := by
  rw [input_holonomy, origin_input_coefficient]
  norm_num

theorem input_bound (t : ℝ) : SublatticePlaqBound 2 (field t) (radius t) := by
  intro y _ μ ν
  rw [input_holonomy]
  rcases input_coefficients y μ ν with h | h | h
  · rw [h]
    norm_num only [Rat.cast_zero, zero_mul, torus_zero, frobNorm_one_sub_one]
    exact radius_nonneg t
  · rw [h]
    norm_num [radius]
  · rw [h]
    norm_num only [Rat.cast_neg, Rat.cast_one, neg_one_mul]
    rw [← torus_inv, frobNorm_inv_sub_one]
    exact le_rfl

theorem radius_le_of_input (t β : ℝ) (h : SublatticePlaqBound 2 (field t) β) :
    radius t ≤ β := by
  have horigin : origin ∈ CoarseLattice witL 2 := by
    rw [mem_CoarseLattice]
    intro μ
    rfl
  have hp := h origin horigin 0 1
  rw [input_at_origin] at hp
  exact hp

theorem double_bound (t : ℝ) :
    frobNorm (((torus (2 * t) : SU2) : M2) - 1) ≤ 2 * radius t := by
  have heq : torus (2 * t) = torus t * torus t := by
    rw [← torus_add]
    congr 1
    ring
  rw [heq]
  calc
    _ ≤ radius t + radius t :=
      AdalyFormal.Balaban.RegularUQChain.frobNorm_su_mul_sub_one_le _ _
    _ = _ := by ring

theorem output_bound (t : ℝ) (ht : |t| ≤ 1/10) :
    SublatticePlaqBound 4 (ubarSU2 2 2 (field t)) (2 * radius t) := by
  intro y hy μ ν
  rw [fitted_holonomy t ht y hy μ ν]
  rcases fitted_output_coefficients y hy μ ν with h | h | h
  · rw [h]
    norm_num only [Rat.cast_zero, zero_mul, torus_zero, frobNorm_one_sub_one]
    exact mul_nonneg (by norm_num) (radius_nonneg t)
  · rw [h]
    norm_num only [Rat.cast_ofNat]
    exact double_bound t
  · rw [h]
    norm_num only [Rat.cast_neg, Rat.cast_ofNat, neg_mul]
    rw [← torus_inv, frobNorm_inv_sub_one]
    exact double_bound t

/-- The EXACT conclusion polynomial and input/output scales of the imported
ScaleFittedPropagation at s=2, ell=2. The witness passes for EVERY allowed beta,
not just a convenient positive radius, and for every C0 >= 0. -/
theorem stride_witness_passes_scaleFitted (C0 c2' t β : ℝ) (hC0 : 0 ≤ C0)
    (ht : |t| ≤ 1/10) (hβ : 0 ≤ β) (_hc : β ≤ c2')
    (hinput : SublatticePlaqBound 2 (field t) β) :
    SublatticePlaqBound (2 * 2) (ubarSU2 2 2 (field t))
      ((2 : ℝ)^2 * β + C0 * ((2 : ℝ)^2 * β)^2) := by
  intro y hy μ ν
  have hout := output_bound t ht y hy μ ν
  have hin := radius_le_of_input t β hinput
  have hquad : 0 ≤ C0 * ((2 : ℝ)^2 * β)^2 := mul_nonneg hC0 (sq_nonneg _)
  nlinarith

/-- Concrete numeric witness instance, with exact real parameter 1/100. -/
theorem concrete_stride_test (C0 : ℝ) (hC0 : 0 ≤ C0) :
    SublatticePlaqBound 2 (field (1/100)) (radius (1/100)) ∧
    SublatticePlaqBound (2 * 2) (ubarSU2 2 2 (field (1/100)))
      ((2 : ℝ)^2 * radius (1/100) + C0 * ((2 : ℝ)^2 * radius (1/100))^2) := by
  refine ⟨input_bound _, ?_⟩
  exact stride_witness_passes_scaleFitted C0 (radius (1/100)) (1/100) (radius (1/100))
    hC0 (by norm_num) (radius_nonneg _) le_rfl (input_bound _)

end Prop1.ScaleFittedTest.Stride

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`Prop1.ScaleFittedTest.Stride.fitted_bond,
      `Prop1.ScaleFittedTest.Stride.fitted_holonomy,
      `Prop1.ScaleFittedTest.Stride.input_bound,
      `Prop1.ScaleFittedTest.Stride.output_bound,
      `Prop1.ScaleFittedTest.Stride.stride_witness_passes_scaleFitted,
      `Prop1.ScaleFittedTest.Stride.concrete_stride_test] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"STRIDE_SU2_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
