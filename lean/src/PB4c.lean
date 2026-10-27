import GN12
import AdalyFormal.Balaban.ClassPropagationUbar

/-!
# PB4c -- item (4), the form that COEXISTS with the site-coercivity chain: `RegTower` from the TREE's loop bound.

`PB4` (namespace `PortSliceNJ`) is the faithful port of `NonflatJet.regTower_of_small` (it imports `NJ13bReg`, whose closure
`ESmall -> OperatorGaps/T1MainSegment` loads `EstimatesLayer.NormBounds.Foundations`).  The site-coercivity chain
(`SectB*`) loads the parallel lineage `CoeffFoundations`; the two define the same name
`EstimatesLayer.NormBounds.theta`, so `lean` REFUSES to import both into one environment (measured: PB2 + PB4 -> "import
Foundations failed, environment already contains 'EstimatesLayer.NormBounds.theta' from CoeffFoundations").  Hence the final
theorem cannot use `PB4`.  This module re-derives `RegTower` from tree-only facts:
`ClassPropagationUbar.frobNorm_loopVar_sub_one_le : ‖loopVar - 1‖_F ≤ (8 ell - 6) frobSupBond V`  and the chart radius of
`LogReg` (`R2Raw2.LogReg_mem_nhds_one`), with the radius as an explicit hypothesis `hrL` (witnessed by `exists_chart_radius`).
Constants differ from NJ14Final: `(8 ell - 6) ε_j < rL` instead of `π/2 · loopFactorBound ell · ε_j < r₀`.
Standard axioms only (each declaration's printed axiom line).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped Matrix Matrix.Norms.Frobenius
open Metric
namespace AdalyFormal.PortSlice

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp)

theorem norm_frob_eq (M : Matrix (Fin 2) (Fin 2) ℂ) : ‖M‖ = frobNorm M := by
  rw [Matrix.frobenius_norm_def]
  unfold frobNorm frobSq
  simp only [Fin.sum_univ_two]
  rw [Real.sqrt_eq_rpow]
  congr 1
  have h : ∀ z : ℂ, ‖z‖ ^ (2 : ℝ) = Complex.normSq z := fun z => by
    rw [Real.rpow_two]; exact Complex.sq_norm z
  simp only [h]
  ring

/-- a chart radius for `LogReg` at `1` (the existence behind the hypothesis `hrL`). -/
theorem exists_chart_radius : ∃ r : ℝ, 0 < r ∧ ∀ g : M2, frobNorm (g - 1) < r → g ∈ LogReg := by
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp LogReg_mem_nhds_one
  refine ⟨r, hr, fun g hg => hb ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, norm_frob_eq]
  exact hg

/-- **ITEM (4), tree form.**  `RegTower` from level-wise sup-norm smallness `frobSupBond (bg j) ≤ ε j` and `(8 ell - 6) ε_j < rL`. -/
theorem regTower_of_frobSup {L : PeriodicLatticeExtent} {ell : ℕ} (hell : 0 < ell)
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ) (ε : ℕ → ℝ)
    (hV : ∀ j, j < J → frobSupBond (bg j) ≤ ε j)
    (rL : ℝ) (hrL : ∀ g : M2, frobNorm (g - 1) < rL → g ∈ LogReg)
    (hr : ∀ j, j < J → (8 * (ell : ℝ) - 6) * ε j < rL) :
    RegTower ell bg J := by
  intro j hj c x hx
  apply hrL
  have h1 := AdalyFormal.Balaban.ClassPropagationUbar.frobNorm_loopVar_sub_one_le (bg j) c (s := ell ^ j) (ell := ell)
    (pow_pos hell j) x hx
  have hell1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have h2 : (8 * (ell : ℝ) - 6) * frobSupBond (bg j) ≤ (8 * (ell : ℝ) - 6) * ε j :=
    mul_le_mul_of_nonneg_left (hV j hj) (by linarith)
  exact lt_of_le_of_lt (le_trans h1 h2) (hr j hj)

/-- sup-norm of the genuine tower from the sup-norm of `U` (iterated tree blocking estimate; `ell > 0`). -/
theorem frobSup_bgTower_le {L : PeriodicLatticeExtent} (G : TowerGeom L) (hell : 0 < G.ell) (U : Cfg L) (j : ℕ) :
    frobSupBond (bgTower G U j)
      ≤ (AdalyFormal.Balaban.ClassPropagationUbar.blkConstOf G.ell) ^ j * frobSupBond U := by
  induction j with
  | zero => simp [bgTower, AdalyFormal.Balaban.UbarTowerCov.UbarTower]
  | succ j ih =>
    have h := AdalyFormal.Balaban.ClassPropagationUbar.frobSupBond_ubarSU2_le (bgTower G U j)
      (s := G.ell ^ j) (ell := G.ell) (pow_pos hell j) hell
    have hs : bgTower G U (j + 1) = AdalyFormal.Balaban.BlockedBackground.ubarSU2 (G.ell ^ j) G.ell (bgTower G U j) := rfl
    rw [hs, pow_succ]
    have hb : 0 ≤ AdalyFormal.Balaban.ClassPropagationUbar.blkConstOf G.ell := by
      unfold AdalyFormal.Balaban.ClassPropagationUbar.blkConstOf
      have : (0 : ℝ) ≤ G.ell := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ 8 * (G.ell : ℝ) - 6 := by
        have : (1 : ℝ) ≤ G.ell := by exact_mod_cast hell
        linarith
      positivity
    calc _ ≤ AdalyFormal.Balaban.ClassPropagationUbar.blkConstOf G.ell * frobSupBond (bgTower G U j) := h
      _ ≤ AdalyFormal.Balaban.ClassPropagationUbar.blkConstOf G.ell *
            ((AdalyFormal.Balaban.ClassPropagationUbar.blkConstOf G.ell) ^ j * frobSupBond U) :=
          mul_le_mul_of_nonneg_left ih hb
      _ = _ := by ring

#print axioms norm_frob_eq
#print axioms exists_chart_radius
#print axioms regTower_of_frobSup
#print axioms frobSup_bgTower_le

end AdalyFormal.PortSlice
