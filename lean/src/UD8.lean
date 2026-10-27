import UD7

/-!
# UD8 -- `H0` is bijective from a ROTATED `ℓ¹` drift (lane m2_unitcharts_20261014)

`H0_bij_of_rot_drift`: if `Σ_d ‖H0(Q) w d - ℓ⁻³ O_d(w d)‖ ≤ δ Σ_d ‖w d‖` with each `O_d` norm-preserving and `δ < ℓ⁻³`, then `H0(Q)` is injective, hence bijective.
(`DK3.H0_bij_of_drift` is the case `O_d = id`.)  The rotations `O_d` are what a PER-ROW gauge chart produces (UD9): row `d` of `H0` is compared with `ℓ⁻³` times a
gauge rotation of the column variable, and the gauge needs no relation between different rows.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2UnitCharts

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.IngredientFamilyR2 (H0 Dset iotaD)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA)

theorem norm_RMap (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (x : SuTwo) : ‖RMap g x‖ = ‖x‖ := by
  have h := AdalyFormal.Balaban.SuTwoInner.inner_RMap g x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have h1 := norm_nonneg (RMap g x)
  have h2 := norm_nonneg x
  nlinarith [sq_nonneg (‖RMap g x‖ - ‖x‖), sq_nonneg (‖RMap g x‖ + ‖x‖)]

theorem H0_bij_of_rot_drift {Lu : PeriodicLatticeExtent} {ell : ℕ} (hell : 0 < ell)
    (Lam : Set (PeriodicLatticeSite Lu)) (Q : (Bond Lu → SuTwo) →ₗ[ℝ] (CoarseBond Lu ell → SuTwo)) (δ : ℝ)
    (hδ : δ < 1 / (ell : ℝ) ^ 3) (O : Dset Lu ell Lam → SuTwo → SuTwo) (hO : ∀ d x, ‖O d x‖ = ‖x‖)
    (hdrift : ∀ w : Dset Lu ell Lam → SuTwo,
      ∑ d, ‖H0 Lam Q w d - ((1 : ℝ) / (ell : ℝ) ^ 3) • O d (w d)‖ ≤ δ * ∑ d, ‖w d‖) :
    Function.Bijective (H0 Lam Q) := by
  classical
  have hinj : Function.Injective (H0 Lam Q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hpt : ∀ d, ‖H0 Lam Q w d - ((1 : ℝ) / (ell : ℝ) ^ 3) • O d (w d)‖
        = ((1 : ℝ) / (ell : ℝ) ^ 3) * ‖w d‖ := by
      intro d
      rw [hw]
      simp only [Pi.zero_apply, zero_sub, norm_neg, norm_smul]
      rw [Real.norm_of_nonneg (by positivity), hO]
    have h1 := hdrift w
    rw [Finset.sum_congr rfl (fun d _ => hpt d), ← Finset.mul_sum] at h1
    have hS0 : 0 ≤ ∑ d, ‖w d‖ := Finset.sum_nonneg (fun d _ => norm_nonneg _)
    have hS : ∑ d, ‖w d‖ = 0 := by
      by_contra hne
      have hpos : 0 < ∑ d, ‖w d‖ := lt_of_le_of_ne hS0 (Ne.symm hne)
      have := mul_lt_mul_of_pos_right hδ hpos
      linarith
    funext d
    have hd := (Finset.sum_eq_zero_iff_of_nonneg (fun d _ => norm_nonneg (w d))).mp hS d (Finset.mem_univ _)
    simpa using hd
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

open Classical in
/-- the gauge action commutes with `ι_D`, up to the rotated column variable (no injectivity of `droppedBondLast` needed). -/
theorem gaugeAct_iotaD {Lu : PeriodicLatticeExtent} {ell : ℕ} (Lam : Set (PeriodicLatticeSite Lu))
    (g : GaugeFn Lu) (w : Dset Lu ell Lam → SuTwo) :
    gaugeActA g (iotaD ell Lam w)
      = iotaD ell Lam (fun d => RMap (g (AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell d.1).1)
          (w d)) := by
  funext b
  show RMap (g b.1) (∑ d : Dset Lu ell Lam, if b = AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell d.1 then w d else 0)
    = ∑ d : Dset Lu ell Lam, if b = AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell d.1 then
        RMap (g (AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell d.1).1) (w d) else 0
  rw [map_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases h : b = AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell d.1
  · simp only [h, if_true]
  · simp [h]

end AdalyFormal.M2UnitCharts

#print axioms AdalyFormal.M2UnitCharts.norm_RMap
#print axioms AdalyFormal.M2UnitCharts.H0_bij_of_rot_drift
#print axioms AdalyFormal.M2UnitCharts.gaugeAct_iotaD
