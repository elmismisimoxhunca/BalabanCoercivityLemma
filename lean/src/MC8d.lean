import MC8c
import MF9

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

/-!
# MC8d -- the sine witness is genuinely CURVED: a plaquette with `dv > 0`, every `k`.
-/
namespace AdalyFormal.M0Corollary

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLaneG AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq)
open AdalyFormal.CurvBlock (dv)

theorem Xm_diag (t : ℝ) : Xm t = Matrix.diagonal ![(t : ℂ) * Complex.I, -((t : ℂ) * Complex.I)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xm, sig, Matrix.diagonal]

theorem Ug_entry (t : ℝ) : ((Ug t : G2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = Complex.exp ((t : ℂ) * Complex.I) := by
  show (NormedSpace.exp (Xm t)) 0 0 = _
  rw [Xm_diag, Matrix.exp_diagonal]
  simp [Matrix.diagonal, ← Complex.exp_eq_exp_ℂ]

theorem Ug_ne_one (t : ℝ) (h0 : 0 < t) (h1 : t < 1) : ((Ug t : G2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ≠ 1 := by
  rw [Ug_entry]
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h2 : (t : ℂ) = (n : ℂ) * (2 * Real.pi) := by
    have : (t : ℂ) * Complex.I = ((n : ℂ) * (2 * Real.pi)) * Complex.I := by rw [hn]; ring
    exact mul_right_cancel₀ Complex.I_ne_zero this
  have h3 : t = (n : ℝ) * (2 * Real.pi) := by exact_mod_cast h2
  have hpi := Real.pi_gt_three
  rcases le_or_gt n 0 with hn0 | hn0
  · have : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
    nlinarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    nlinarith

theorem dv_pos_of_entry (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (h : g.1 0 0 ≠ 1) : 0 < dv g := by
  unfold dv frobNorm frobSq
  apply Real.sqrt_pos.mpr
  have hne : (g.1 - 1) 0 0 ≠ 0 := by
    simpa [Matrix.sub_apply, sub_eq_zero] using h
  have h0 := Complex.normSq_pos.mpr hne
  have h1 := Complex.normSq_nonneg ((g.1 - 1) 0 1)
  have h2 := Complex.normSq_nonneg ((g.1 - 1) 1 0)
  have h3 := Complex.normSq_nonneg ((g.1 - 1) 1 1)
  show 0 < Complex.normSq ((g.1 - 1) 0 0) + Complex.normSq ((g.1 - 1) 0 1) + Complex.normSq ((g.1 - 1) 1 0)
    + Complex.normSq ((g.1 - 1) 1 1)
  linarith

end AdalyFormal.M0Corollary
