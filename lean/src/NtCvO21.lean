import NtCvO20

/-!
# CvO21 -- the abelian raw step is the block average of line integrals (lane omega)

For `y` and `cPlusS s ell (y,μ)` both with fitting blocks (`y_ν + s*ell ≤ N_ν`), and any angle field `θ`:
`Rsig s ell θ (y,μ) = (ell³)⁻¹ Σ_{x ∈ B_s(y)} pathAngG s θ x (replicate ell μ)`: the contour terms of `S₋, S₊` and of the loop angles cancel exactly
(CMP96 (2.125), abelian case).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq)
open AdalyFormal.Balaban.TowerLawCov (coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

/-- the staircase has the counts `f 2, f 1, f 0` when `x = y + s f`. -/
theorem gamma_siteOfF (y : PeriodicLatticeSite L) (s ell : ℕ) (hs : 0 < s)
    (hfit : ∀ μ, (y μ).val + s * ell ≤ L μ + 1) (f : Fin 3 → Fin ell) :
    coarseGammaPath s y (siteOfF y s ell hfit hs f) =
      List.replicate (f 2).val 2 ++ (List.replicate (f 1).val 1 ++ List.replicate (f 0).val 0) := by
  have key : ∀ (ν : Fin 3) (w : PeriodicLatticeSite L), (w ν).val = (y ν).val →
      ((siteOfF y s ell hfit hs f) ν - w ν).val / s = (f ν).val := by
    intro ν w hw
    have hle : w ν ≤ (siteOfF y s ell hfit hs f) ν := by
      rw [Fin.le_def, hw]; show (y ν).val ≤ (y ν).val + s * (f ν).val; omega
    rw [Fin.coe_sub_iff_le.mpr hle]
    show ((y ν).val + s * (f ν).val - (w ν).val) / s = _
    rw [hw, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hs]
  unfold coarseGammaPath coarseStraightSegment coarseCoordSteps
  have e2 : ((siteOfF y s ell hfit hs f) 2 - y 2).val / s = (f 2).val := key 2 y rfl
  have e1 : ((siteOfF y s ell hfit hs f) 1 - (Function.update y 2 ((siteOfF y s ell hfit hs f) 2)) 1).val / s = (f 1).val :=
    key 1 _ (by simp [Function.update_of_ne])
  have e0 : ((siteOfF y s ell hfit hs f) 0 - (Function.update (Function.update y 2 ((siteOfF y s ell hfit hs f) 2)) 1
      ((siteOfF y s ell hfit hs f) 1)) 0).val / s = (f 0).val := key 0 _ (by simp [Function.update_of_ne])
  rw [e2, e1, e0]

theorem sum_block_reindex (z : PeriodicLatticeSite L) (s ell : ℕ) (hs : 0 < s)
    (hfit : ∀ μ, (z μ).val + s * ell ≤ L μ + 1) (F : PeriodicLatticeSite L → ℝ) :
    ∑ x ∈ stepBlockOf z s ell, F x = ∑ f : Fin 3 → Fin ell, F (siteOfF z s ell hfit hs f) := by
  rw [stepBlockOf_eq_image z s ell hs hfit, Finset.sum_image (fun f _ g _ h => siteOfF_injective z s ell hs hfit h)]



open AdalyFormal.Balaban.QjComposite (card_stepBlockOf)

/-- **the abelian one-step map is the block average of line integrals.** -/
theorem Rsig_closed {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell) (y : PeriodicLatticeSite L) (μ : Fin 3)
    (hfit : ∀ ν, (y ν).val + s * ell ≤ L ν + 1) (hfit' : ∀ ν, ((cPlusS s ell (y, μ)) ν).val + s * ell ≤ L ν + 1)
    (θ : PeriodicLatticeEdge L → ℝ) :
    Rsig s ell θ (y, μ) = (((ell : ℝ) ^ 3)⁻¹) * ∑ x ∈ stepBlockOf y s ell, pathAngG s θ x (List.replicate ell μ) := by
  set cp := cPlusS s ell (y, μ) with hcp
  have hre : ∑ x ∈ stepBlockOf cp s ell, pathAngG s θ cp (coarseGammaPath s cp x) =
      ∑ x ∈ stepBlockOf y s ell, pathAngG s θ cp (coarseGammaPath s y x) := by
    rw [sum_block_reindex cp s ell hs hfit', sum_block_reindex y s ell hs hfit]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [gamma_siteOfF cp s ell hs hfit' f, gamma_siteOfF y s ell hs hfit f]
  have hcard : (stepBlockOf y s ell).card = ell ^ 3 := card_stepBlockOf y s ell hs hfit
  unfold Rsig blockAngG sAngG loopAngG
  simp only []
  rw [← hcp, hre]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
  have hl : ((ell : ℝ) ^ 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

#print axioms Rsig_closed

end AdalyFormal.CoverOmega
