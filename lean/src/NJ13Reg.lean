import NJ9Drift
import NJ5Path

/-!
# NJ13Reg -- `RegBg s ell V` (R2's regularity predicate) FOLLOWS from per-link smallness `‖V e - 1‖_F ≤ ε₀` with
`(π/2)·n(ell)·ε₀ < r₀`, where `r₀ > 0` is the (universal, non-explicit) radius of the analytic-log chart at `1`
(`LogReg ∈ 𝓝 1`, R2Raw2).  Stride `s` arbitrary.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration PeriodicLatticeEdge)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Angle su2NegOne)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarseCoordSteps)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open SmallnessBridge.Assemble (coarseGammaPath_length coarseCoordSteps_update_ne loopFactors
  loopFactorBound loopFactors_prod loopFactors_length su2Angle_loopFactors_le)

variable {L : PeriodicLatticeExtent}

theorem coarseGammaPath_length_le_of_steps_s (s : ℕ) (a b : PeriodicLatticeSite L) {ell : ℕ}
    (h : ∀ ν : Fin 3, coarseCoordSteps s a b ν < ell) :
    (coarseGammaPath s a b).length ≤ 3 * (ell - 1) := by
  have h1' : coarseCoordSteps s (Function.update a 2 (b 2)) b 1 = coarseCoordSteps s a b 1 :=
    coarseCoordSteps_update_ne s a b (b 2) (by decide : (1 : Fin 3) ≠ 2)
  have h0a : coarseCoordSteps s (Function.update a 2 (b 2)) b 0 = coarseCoordSteps s a b 0 :=
    coarseCoordSteps_update_ne s a b (b 2) (by decide : (0 : Fin 3) ≠ 2)
  have h0' : coarseCoordSteps s (Function.update (Function.update a 2 (b 2)) 1 (b 1)) b 0
      = coarseCoordSteps s a b 0 := by
    rw [coarseCoordSteps_update_ne s (Function.update a 2 (b 2)) b (b 1)
      (by decide : (0 : Fin 3) ≠ 1), h0a]
  rw [coarseGammaPath_length, h1', h0']
  have := h 2; have := h 1; have := h 0
  omega

theorem steps_lt_of_inStepBlock {s ell : ℕ} (hs : 0 < s) {y x : PeriodicLatticeSite L}
    (hx : x ∈ stepBlockOf y s ell) (μ : Fin 3) : coarseCoordSteps s y x μ < ell := by
  obtain ⟨h1, h2, _⟩ := (mem_stepBlockOf.mp hx) μ
  unfold coarseCoordSteps
  rw [Fin.sub_val_of_le (Fin.le_def.mpr h1)]
  rw [Nat.div_lt_iff_lt_mul hs]
  have h3 : (x μ).val < (y μ).val + ell * s := by rw [mul_comm]; exact h2
  exact Nat.sub_lt_left_of_lt_add h1 h3

theorem loopFactors_length_le_s {s ell : ℕ} (hs : 0 < s) (V : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf c.1 s ell) :
    (loopFactors s ell V c x).length ≤ loopFactorBound ell := by
  have hγ : (coarseGammaPath s c.1 x).length ≤ 3 * (ell - 1) :=
    coarseGammaPath_length_le_of_steps_s s c.1 x (fun ν => steps_lt_of_inStepBlock hs hx ν)
  have hlen := loopFactors_length (G := SU2) s ell V c x
  unfold loopFactorBound
  rw [hlen]
  omega

theorem angle_loopVar_le {s ell : ℕ} (hs : 0 < s) (V : PeriodicLinkConfiguration SU2 L) (δ : ℝ)
    (hδ : 0 ≤ δ) (hang : ∀ e, su2Angle (V e) ≤ δ) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf c.1 s ell) :
    su2Angle (loopVar s ell V c x) ≤ (loopFactorBound ell : ℝ) * δ := by
  rw [← loopFactors_prod]
  refine (SmallnessBridge.ProdBound.su2Angle_list_prod_le_length_mul _ δ
    (fun g hg => su2Angle_loopFactors_le s ell V c x δ hang hg)).trans ?_
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (loopFactors_length_le_s hs V c x hx)) hδ

theorem frobNorm_loopVar_le {s ell : ℕ} (hs : 0 < s) (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ)
    (hε0 : 0 ≤ ε0) (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf c.1 s ell) :
    frobNorm (((loopVar s ell V c x : SU2) : M2) - 1)
      ≤ Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε0) := by
  have hδ : 0 ≤ (Real.pi / (2 * Real.sqrt 2)) * ε0 := by positivity
  have hang : ∀ e, su2Angle (V e) ≤ (Real.pi / (2 * Real.sqrt 2)) * ε0 := fun e =>
    (SmallnessBridge.ProdBound.su2Angle_le_frobNorm (V e)).trans
      (mul_le_mul_of_nonneg_left (hV e) (by positivity))
  have h1 := angle_loopVar_le hs V _ hδ hang c x hx
  rw [AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_sub_one_eq]
  have hsin : Real.sin (su2Angle (loopVar s ell V c x) / 2) ≤ su2Angle (loopVar s ell V c x) / 2 :=
    Real.sin_le (by linarith [AdalyFormal.Balaban.Bch2.su2Angle_nonneg (loopVar s ell V c x)])
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hs22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc 2 * Real.sqrt 2 * Real.sin (su2Angle (loopVar s ell V c x) / 2)
      ≤ 2 * Real.sqrt 2 * (su2Angle (loopVar s ell V c x) / 2) :=
        mul_le_mul_of_nonneg_left hsin (by positivity)
    _ = Real.sqrt 2 * su2Angle (loopVar s ell V c x) := by ring
    _ ≤ Real.sqrt 2 * ((loopFactorBound ell : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * ε0)) :=
        mul_le_mul_of_nonneg_left h1 hs2.le
    _ = Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε0) := by
        field_simp

#print axioms frobNorm_loopVar_le

end AdalyFormal.NonflatJet
