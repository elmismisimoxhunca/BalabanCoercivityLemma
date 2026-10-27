import SectBTransport
import AdalyFormal.Balaban.AlphaAnalyticity
import AdalyFormal.Balaban.RegularUPerturbation
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HConstruction.SectBP1
open HConstruction.GenK
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_mul_apply RMap_one)
open AdalyFormal.Balaban.CoarseRestrictTransported (pathTransport staircaseTransport staircaseBonds)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm norm_RMap_sub_self_le)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond)
variable (M : PeriodicLatticeExtent) {n : ℕ}

/-- The ordered SU(2) product is bounded in its ACTUAL action on a site value;
unitarity prevents exponential accumulation along a staircase. -/
theorem path_action_drift (U : Links M (n := n)) (δ : ℝ)
    (hlink : ∀ b : Bond (fineExtent M n),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ)
    (bs : List (Bond (fineExtent M n))) (X : SuTwo) :
    ‖RMap (pathTransport U bs) X - X‖ ≤ 2*δ*(bs.length:ℝ)*‖X‖ := by
  induction bs with
  | nil => simp [pathTransport, RMap_one]
  | cons b bs ih =>
    have hb := (norm_RMap_sub_self_le (U b) X).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hlink b) (by norm_num : (0:ℝ) ≤ 2)) (norm_nonneg _))
    have ht : RMap (pathTransport U (b :: bs)) X - X =
        RMap (U b) (RMap (pathTransport U bs) X - X) + (RMap (U b) X - X) := by
      simp only [pathTransport, List.map_cons, List.prod_cons, RMap_mul_apply, map_sub]
      abel
    rw [ht]
    calc
      ‖RMap (U b) (RMap (pathTransport U bs) X - X) + (RMap (U b) X - X)‖
        ≤ ‖RMap (U b) (RMap (pathTransport U bs) X - X)‖ +
            ‖RMap (U b) X - X‖ := norm_add_le _ _
      _ ≤ 2*δ*((b :: bs).length:ℝ)*‖X‖ := by
        rw [AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        nlinarith [ih, hb]

/-- Actual (not hypothesized) staircase transport bound under Small n α U,
independent of n and volume, for every x in its n-block. -/
theorem staircase_action_drift (hn : 0 < n) (U : Links M (n := n))
    (α : ℝ) (hsmall : frobSupBond U ≤ α/(n:ℝ))
    (y : Centers M (n := n)) (x : PeriodicLatticeSite (fineExtent M n))
    (hx : x ∈ blockOf y.1 n) (X : SuTwo) :
    ‖RMap (staircaseTransport U y.1 x) X-X‖ ≤ 6*α*‖X‖ := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hlink (b : Bond (fineExtent M n)) :
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α/(n:ℝ) :=
    (frobNorm_le_frobSupBond U b).trans hsmall
  have hα : 0 ≤ α := by
    obtain ⟨b⟩ := (inferInstance : Nonempty (Bond (fineExtent M n)))
    have hz := AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg
      ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1)
    have hd := (le_div_iff₀ hnR).mp (le_trans hz (hlink b))
    nlinarith
  have h := path_action_drift M U (α/(n:ℝ)) hlink (staircaseBonds y.1 x) X
  have hlen := staircase_length_le M hn y x hx
  change ‖RMap (pathTransport U (staircaseBonds y.1 x)) X-X‖ ≤ _
  have hs : 2*(α/(n:ℝ))*((staircaseBonds y.1 x).length:ℝ)*‖X‖ ≤
      2*(α/(n:ℝ))*(3*(n:ℝ))*‖X‖ := by
    gcongr
    exact_mod_cast (le_trans hlen (by omega : 3*(n-1) ≤ 3*n))
  calc
    _ ≤ 2*(α/(n:ℝ))*((staircaseBonds y.1 x).length:ℝ)*‖X‖ := h
    _ ≤ 2*(α/(n:ℝ))*(3*(n:ℝ))*‖X‖ := hs
    _ = 6*α*‖X‖ := by field_simp; ring
/-- Actual A2 pointwise output estimate, with the path bound fully discharged
from Small n α U (unlike the earlier conditional beta interface). -/
theorem qDrift_block_small (hn : 0 < n) (U : Links M (n := n))
    (α : ℝ) (hsmall : frobSupBond U ≤ α/(n:ℝ))
    (y : Centers M (n := n)) (f : Site M (n := n)) :
    ‖qDrift M U f y‖ ≤
      (1/(n:ℝ)^3) * (∑ x ∈ blockOf y.1 n, 6*α*‖f x‖) := by
  rw [qDrift_block, norm_smul, Real.norm_eq_abs]
  have hpos : 0 ≤ (1/(n:ℝ)^3) := by positivity
  rw [abs_of_nonneg hpos]
  apply mul_le_mul_of_nonneg_left _ hpos
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  exact staircase_action_drift M hn U α hsmall y x hx (f x)
end HConstruction.SectBP1
