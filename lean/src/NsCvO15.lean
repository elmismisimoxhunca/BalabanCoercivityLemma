import NsCvO14
import ZXR2Unit1

/-!
# CvO15 -- the regularity hypotheses of the whole tower of the staggered layer (lane omega)

For the fine torus `scaleUp ell 2 Lu` (`ell` even) and `U = stagCfg c t` (`|t| < π`, layer far from the ends in `x₀`):
* `stag_regTower`: `RegTower2 ell (UbarTower su2LogExp ell U) 2` -- the levels `0` (stride `1`) and `1` (stride `ell`), EVERY base bond;
* `stag_unit_regBg2`: the UNIT-level background `unitBg ell 2 Lu hell (Ū²)` satisfies `RegBg2 1 ell` -- every loop of the unit torus is trivial.
With CvO9 this gives `ContDiffAt ℝ ⊤ (qCompX ell (UbarTower su2LogExp ell U) j) 0` for `j ≤ 2` and `ContDiffAt ℝ ⊤ (qStepX 1 ell unitBg) 0`:
the genuine `Q_j(U)`, `Q₁`, `C̃⁽²⁾` of the staggered layer at the angle `t ≈ π/2` are honest derivatives.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2 (unitBg embY embY_val)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq UbarTower UbarTower_succ UbarTower_zero)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

theorem scaleUp_succ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (μ : Fin 3) :
    scaleUp ell k Lu μ + 1 = (Lu μ + 1) * ell ^ k := by
  unfold scaleUp
  have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

theorem negOne_ne_one : (1 : SU2) ≠ su2NegOne := by
  intro h
  have := congrArg (fun g : SU2 => (g : M2) 0 0) h
  simp [su2NegOne] at this
  norm_num at this

variable {ell : ℕ} {Lu : PeriodicLatticeExtent}

theorem unit_temporal (hell : 0 < ell) (hE : 2 ∣ ell) (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi)
    (hc1 : ell ≤ c) (hc2 : c + ell ≤ scaleUp ell 2 Lu 0 + 1) :
    IsTemporal 1 (unitBg ell 2 Lu hell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 (scaleUp ell 2 Lu)) 2))
      (fun v => (fun w => ∑ j ∈ Finset.range ell, (fun v' => Dfun c ell (scaleUp ell 2 Lu 0 + 1) v' * (t / 2))
        ((w + ell * j) % (scaleUp ell 2 Lu 0 + 1))) (ell ^ 2 * v)) := by
  have hdiv : ∀ μ, ell ∣ scaleUp ell 2 Lu μ + 1 := fun μ => by
    rw [scaleUp_succ ell 2 Lu hell]; exact Dvd.dvd.mul_left (dvd_pow_self ell (by norm_num)) _
  have hN : 2 ∣ scaleUp ell 2 Lu 1 + 1 := dvd_trans hE (hdiv 1)
  have h2 := bg2_temporal hN hE hell hdiv c t htπ hc1 hc2
  intro y _
  have hy : Crs (ell * ell) (embY ell 2 Lu hell y) := by
    intro μ
    rw [embY_val, pow_two]
    exact dvd_mul_right (ell * ell) _
  obtain ⟨a0, a1, a2⟩ := h2 _ hy
  simp only [UbarTower_succ, UbarTower_zero, pow_zero, pow_one] at *
  refine ⟨?_, ?_, ?_⟩
  · show stridedBlockedGauge su2LogExp ell ell (stridedBlockedGauge su2LogExp 1 ell (stagCfg c t)) (embY ell 2 Lu hell y, 0) = _
    rw [a0, embY_val]
  · exact a1
  · exact a2

theorem stag_unit_regBg2 (hell : 0 < ell) (hE : 2 ∣ ell) (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi)
    (hc1 : ell ≤ c) (hc2 : c + ell ≤ scaleUp ell 2 Lu 0 + 1) :
    RegBg2 1 ell (unitBg ell 2 Lu hell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 (scaleUp ell 2 Lu)) 2)) := by
  have hV := unit_temporal (Lu := Lu) hell hE c t htπ hc1 hc2
  apply regBg2_of_ne_negOne
  intro cc x hx
  obtain ⟨y, μ⟩ := cc
  rw [loopVar_temporal (fun μ => one_dvd _) hV (fun μ => one_dvd _) μ hx]
  exact negOne_ne_one

theorem stag_regTower (hell : 0 < ell) (hE : 2 ∣ ell) (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi)
    (hc1 : ell ≤ c) (hc2 : c + ell ≤ scaleUp ell 2 Lu 0 + 1) :
    RegTower2 ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 (scaleUp ell 2 Lu))) 2 := by
  have hdiv : ∀ μ, ell ∣ scaleUp ell 2 Lu μ + 1 := fun μ => by
    rw [scaleUp_succ ell 2 Lu hell]; exact Dvd.dvd.mul_left (dvd_pow_self ell (by norm_num)) _
  have hN : 2 ∣ scaleUp ell 2 Lu 1 + 1 := dvd_trans hE (hdiv 1)
  intro j hj
  have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl
  · simpa [UbarTower_zero] using regBg2_level0 hN hE c t htπ
  · simpa [UbarTower_succ, UbarTower_zero] using regBg2_level1 hN hE hell c t htπ hc1 hc2

#print axioms unit_temporal
#print axioms stag_unit_regBg2
#print axioms stag_regTower



end AdalyFormal.CoverOmega
