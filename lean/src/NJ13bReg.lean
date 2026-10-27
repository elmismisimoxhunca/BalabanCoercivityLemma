import NJ13Reg
import R2Raw2

/-!
# NJ13bReg -- the universal chart radius `r₀` and `RegBg` from smallness.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.NonflatJet

open scoped Matrix Matrix.Norms.Frobenius
open Metric
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration PeriodicLatticeEdge)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.IngredientFamilyR2 (LogReg LogReg_mem_nhds_one RegBg)

variable {L : PeriodicLatticeExtent}

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

/-- the radius of the analytic-log chart at `1`: `ball 1 r₀ ⊆ LogReg`. -/
theorem exists_r0 : ∃ r : ℝ, 0 < r ∧ ∀ g : M2, frobNorm (g - 1) < r → g ∈ LogReg := by
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp LogReg_mem_nhds_one
  refine ⟨r, hr, fun g hg => hb ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, norm_frob_eq]
  exact hg

/-- the universal chart radius (non-explicit; positive). -/
noncomputable def r0 : ℝ := Classical.choose exists_r0

theorem r0_pos : 0 < r0 := (Classical.choose_spec exists_r0).1

theorem mem_LogReg_of_frob_lt {g : M2} (h : frobNorm (g - 1) < r0) : g ∈ LogReg :=
  (Classical.choose_spec exists_r0).2 g h

/-- **`RegBg` from smallness.** -/
theorem regBg_of_small {s ell : ℕ} (hs : 0 < s) (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ)
    (hε0 : 0 ≤ ε0) (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0)
    (h : Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε0) < r0) : RegBg s ell V := by
  intro c x hx
  exact mem_LogReg_of_frob_lt (lt_of_le_of_lt (frobNorm_loopVar_le hs V ε0 hε0 hV c x hx) h)

#print axioms regBg_of_small

end AdalyFormal.NonflatJet
