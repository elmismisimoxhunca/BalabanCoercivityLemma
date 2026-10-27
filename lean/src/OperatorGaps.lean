/-
Operator gaps `‖g-1‖`, `‖gInv-1‖`, `‖exp-1‖` and the resulting E1/E2 operator
bounds on the ball `ν ≤ ρ ≤ π/2`.

Uses the certified SI1 operators and the certified inverse closed form / inverse
norm bound from `EstimatesLayer.NormBounds`. No lattice geometry. No k-uniformity.
-/
import ScalarMajorants
import Bounds
import Adjoint
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace EstimatesLayer.E1E3
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.Bch2
open AdalyFormal.Balaban.SuTwoInner
open OneStep124 (adOp gOp gInvOp expOp gCoeff expCoeff)
open EstimatesLayer.NormBounds
open AdalySI1.DexpRodrigues (adOp_zero_eq)
open AdalySI1.Adjoint (expSummable expOp_zero_eq)
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

theorem gCoeff_abs (n : ℕ) : |gCoeff n| = 1 / (Nat.factorial (n + 1) : ℝ) := by
  rw [gCoeff, abs_div, abs_pow, abs_neg, abs_one, one_pow]
  rw [abs_of_nonneg (Nat.cast_nonneg _)]

theorem gCoeff_abs_le (n : ℕ) : |gCoeff n| ≤ 1 / (Nat.factorial n : ℝ) := by
  rw [gCoeff_abs]
  have hfn : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hle : (Nat.factorial n : ℝ) ≤ (Nat.factorial (n + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  exact one_div_le_one_div_of_le hfn hle

theorem pow_norm_le (T : SuTwo →L[ℝ] SuTwo) (n : ℕ) : ‖T ^ n‖ ≤ ‖T‖ ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    calc ‖T ^ k * T‖ ≤ ‖T ^ k‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖T‖ ^ k * ‖T‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg T)

theorem smul_pow_norm_le (c : ℝ) (T : SuTwo →L[ℝ] SuTwo) (n : ℕ) :
    ‖c • T ^ n‖ ≤ |c| * ‖T ^ n‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((T ^ n).le_opNorm v) (abs_nonneg c)

theorem gOp_summable (T : SuTwo →L[ℝ] SuTwo) :
    Summable (fun n : ℕ => gCoeff n • T ^ n) := by
  have hb : ∀ n : ℕ, ‖gCoeff n • T ^ n‖ ≤ ‖T‖ ^ n / (Nat.factorial n : ℝ) := by
    intro n
    calc ‖gCoeff n • T ^ n‖ ≤ |gCoeff n| * ‖T ^ n‖ := smul_pow_norm_le _ T n
      _ ≤ (1 / (Nat.factorial n : ℝ)) * ‖T‖ ^ n :=
          mul_le_mul (gCoeff_abs_le n) (pow_norm_le T n) (norm_nonneg _) (by positivity)
      _ = ‖T‖ ^ n / (Nat.factorial n : ℝ) := by ring
  exact Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖T‖) hb

theorem gOp_sub_one_eq_tail (T : SuTwo →L[ℝ] SuTwo) :
    gOp T - 1 = ∑' n : ℕ, gCoeff (n + 1) • T ^ (n + 1) := by
  have hsplit := (gOp_summable T).tsum_eq_zero_add
  have h0 : gCoeff 0 • T ^ 0 = 1 := by simp [gCoeff]
  rw [gOp, hsplit, h0]
  abel

theorem expOp_sub_one_eq_tail (T : SuTwo →L[ℝ] SuTwo) :
    expOp T - 1 = ∑' n : ℕ, expCoeff (n + 1) • T ^ (n + 1) := by
  have hsplit := (expSummable T).tsum_eq_zero_add
  have h0 : expCoeff 0 • T ^ 0 = 1 := by simp [expCoeff]
  rw [expOp, hsplit, h0]
  abel

theorem exp_norm_tail (T : SuTwo →L[ℝ] SuTwo) :
    ∑' n : ℕ, ‖T‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) = Real.exp ‖T‖ - 1 := by
  have hs := Real.summable_pow_div_factorial ‖T‖
  have hsplit := hs.tsum_eq_zero_add
  have hexp : Real.exp ‖T‖ = ∑' n : ℕ, ‖T‖ ^ n / (Nat.factorial n : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have h0 : ‖T‖ ^ 0 / (Nat.factorial 0 : ℝ) = 1 := by simp
  rw [hexp, hsplit, h0]
  abel

theorem factorial_tail_summable (x : ℝ) :
    Summable (fun n : ℕ => x ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) :=
  (summable_nat_add_iff (f := fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) 1).2
    (Real.summable_pow_div_factorial x)

theorem norm_gOp_sub_one_le (T : SuTwo →L[ℝ] SuTwo) :
    ‖gOp T - 1‖ ≤ Real.exp ‖T‖ - 1 := by
  have hbound : ∀ n : ℕ,
      ‖gCoeff (n + 1) • T ^ (n + 1)‖ ≤ ‖T‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
    intro n
    calc ‖gCoeff (n + 1) • T ^ (n + 1)‖
        ≤ |gCoeff (n + 1)| * ‖T ^ (n + 1)‖ := smul_pow_norm_le _ T _
      _ ≤ (1 / (Nat.factorial (n + 1) : ℝ)) * ‖T ^ (n + 1)‖ :=
          mul_le_mul_of_nonneg_right (gCoeff_abs_le (n + 1)) (norm_nonneg _)
      _ ≤ (1 / (Nat.factorial (n + 1) : ℝ)) * ‖T‖ ^ (n + 1) :=
          mul_le_mul_of_nonneg_left (pow_norm_le T _) (by positivity)
      _ = ‖T‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by ring
  have hnorm : Summable (fun n : ℕ => ‖gCoeff (n + 1) • T ^ (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (factorial_tail_summable ‖T‖)
  rw [gOp_sub_one_eq_tail]
  have h1 : ‖∑' n : ℕ, gCoeff (n + 1) • T ^ (n + 1)‖ ≤
      ∑' n : ℕ, ‖gCoeff (n + 1) • T ^ (n + 1)‖ :=
    norm_tsum_le_tsum_norm hnorm
  have h2 : ∑' n : ℕ, ‖gCoeff (n + 1) • T ^ (n + 1)‖ ≤
      ∑' n : ℕ, ‖T‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) :=
    hnorm.tsum_le_tsum hbound (factorial_tail_summable ‖T‖)
  have h3 := exp_norm_tail T
  linarith

theorem expCoeff_eq (n : ℕ) : expCoeff n = 1 / (Nat.factorial n : ℝ) := by
  rw [expCoeff]; ring

theorem norm_expOp_sub_one_le (T : SuTwo →L[ℝ] SuTwo) :
    ‖expOp T - 1‖ ≤ Real.exp ‖T‖ - 1 := by
  have hbound : ∀ n : ℕ,
      ‖expCoeff (n + 1) • T ^ (n + 1)‖ ≤ ‖T‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
    intro n
    have hnn : 0 ≤ expCoeff (n + 1) := by rw [expCoeff]; positivity
    calc ‖expCoeff (n + 1) • T ^ (n + 1)‖
        ≤ |expCoeff (n + 1)| * ‖T ^ (n + 1)‖ := smul_pow_norm_le _ T _
      _ = expCoeff (n + 1) * ‖T ^ (n + 1)‖ := by rw [abs_of_nonneg hnn]
      _ ≤ (1 / (Nat.factorial (n + 1) : ℝ)) * ‖T‖ ^ (n + 1) := by
          rw [expCoeff_eq]
          exact mul_le_mul_of_nonneg_left (pow_norm_le T _) (by positivity)
      _ = ‖T‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by ring
  have hnorm : Summable (fun n : ℕ => ‖expCoeff (n + 1) • T ^ (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (factorial_tail_summable ‖T‖)
  rw [expOp_sub_one_eq_tail]
  have h1 : ‖∑' n : ℕ, expCoeff (n + 1) • T ^ (n + 1)‖ ≤
      ∑' n : ℕ, ‖expCoeff (n + 1) • T ^ (n + 1)‖ :=
    norm_tsum_le_tsum_norm hnorm
  have h2 : ∑' n : ℕ, ‖expCoeff (n + 1) • T ^ (n + 1)‖ ≤
      ∑' n : ℕ, ‖T‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) :=
    hnorm.tsum_le_tsum hbound (factorial_tail_summable ‖T‖)
  have h3 := exp_norm_tail T
  linarith

theorem nu_pos_of_ne_zero (Z : SuTwo) (hz : Z ≠ 0) : 0 < nu (Z : M2) := by
  have hn : nu (Z : M2) ≠ 0 := fun he => hz (Subtype.ext ((nu_eq_zero_iff _).mp he))
  exact lt_of_le_of_ne (nu_nonneg _) (Ne.symm hn)

theorem ad_norm_le_two_rho (Z : SuTwo) {ρ : ℝ} (hZ : nu (Z : M2) ≤ ρ) :
    ‖adOp Z‖ ≤ 2 * ρ := by
  have := norm_ad_le Z
  have : 2 * nu (Z : M2) ≤ 2 * ρ := mul_le_mul_of_nonneg_left hZ (by norm_num)
  linarith

theorem neg_ad_norm_le_two_rho (Z : SuTwo) {ρ : ℝ} (hZ : nu (Z : M2) ≤ ρ) :
    ‖-(adOp Z)‖ ≤ 2 * ρ := by
  rw [norm_neg]
  exact ad_norm_le_two_rho Z hZ

theorem exp_two_rho_gap_of_ad (Z : SuTwo) {ρ : ℝ} (_hρ : 0 ≤ ρ) (hZ : nu (Z : M2) ≤ ρ) :
    Real.exp ‖-(adOp Z)‖ - 1 ≤ Real.exp (2 * ρ) - 1 :=
  sub_le_sub_right (Real.exp_le_exp.mpr (neg_ad_norm_le_two_rho Z hZ)) 1

theorem exp_two_rho_gap_of_ad_pos (Z : SuTwo) {ρ : ℝ} (_hρ : 0 ≤ ρ) (hZ : nu (Z : M2) ≤ ρ) :
    Real.exp ‖adOp Z‖ - 1 ≤ Real.exp (2 * ρ) - 1 :=
  sub_le_sub_right (Real.exp_le_exp.mpr (ad_norm_le_two_rho Z hZ)) 1

theorem gInv_zero : gInvOp (-(adOp (0 : SuTwo))) = 1 := by
  simpa [adOp_zero_eq, neg_zero] using operators_zero.2.1

theorem norm_gInv_neg_le_of_ball (Z : SuTwo) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Real.pi / 2) (hZ : nu (Z : M2) ≤ ρ) :
    ‖gInvOp (-(adOp Z))‖ ≤ gInvMajorant ρ := by
  by_cases hz : Z = 0
  · subst hz
    rw [gInv_zero]
    have : ‖(1 : SuTwo →L[ℝ] SuTwo)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have : 1 ≤ gInvMajorant ρ := by
      dsimp [gInvMajorant]; linarith [Real.pi_pos]
    linarith
  · have hr := nu_pos_of_ne_zero Z hz
    have hrπ : nu (Z : M2) ≤ Real.pi / 2 := hZ.trans hρ
    have hs : Real.sin (nu (Z : M2)) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hr (lt_of_le_of_lt hrπ (half_lt_self Real.pi_pos)))
    exact (norm_gInv_neg_le Z hr hs).trans (inv_scalar_le_majorant hr hZ hρ)

theorem norm_gInv_pos_le_of_ball (Z : SuTwo) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Real.pi / 2) (hZ : nu (Z : M2) ≤ ρ) :
    ‖gInvOp (adOp Z)‖ ≤ gInvMajorant ρ := by
  have hn : nu ((-Z : SuTwo) : M2) = nu (Z : M2) := nu_neg _
  have hh := norm_gInv_neg_le_of_ball (-Z) hρ0 hρ (by rwa [hn])
  simpa [ad_neg, neg_neg, hn] using hh

theorem gInv_neg_sub_one_eq_block (Z : SuTwo) (h : 0 < nu (Z : M2))
    (hs : Real.sin (nu (Z : M2)) ≠ 0) :
    gInvOp (-(adOp Z)) - 1 =
      ((nu (Z : M2) * Real.cos (nu (Z : M2)) / Real.sin (nu (Z : M2))) - 1) • Q Z +
        (-nu (Z : M2)) • J Z := by
  rw [gInv_neg_block Z h hs, inverseBlock]
  have hPQ : P Z + Q Z = 1 := (block_relations Z h).1
  set r := nu (Z : M2)
  set c := r * Real.cos r / Real.sin r
  have hsub : (c - 1) • Q Z = c • Q Z - Q Z := by
    apply ContinuousLinearMap.ext
    intro x
    change (c - 1) • Q Z x = c • Q Z x - Q Z x
    rw [sub_smul, one_smul]
  have hlin :
      (P Z + Q Z - 1) + (c - 1) • Q Z + (-r) • J Z =
        P Z + c • Q Z + (-r) • J Z - 1 := by
    rw [hsub]
    abel
  have hz : P Z + Q Z - 1 = 0 := by rw [hPQ, sub_self]
  rw [← hlin, hz, zero_add]

theorem norm_gInv_neg_sub_one_le (Z : SuTwo) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Real.pi / 2) (hZ : nu (Z : M2) ≤ ρ) :
    ‖gInvOp (-(adOp Z)) - 1‖ ≤ ρ * (1 + Real.pi / 2) := by
  by_cases hz : Z = 0
  · subst hz
    rw [gInv_zero, sub_self, norm_zero]
    exact mul_nonneg hρ0 (by linarith [Real.pi_pos])
  · have hr := nu_pos_of_ne_zero Z hz
    have hrπ : nu (Z : M2) ≤ Real.pi / 2 := hZ.trans hρ
    have hs : Real.sin (nu (Z : M2)) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hr (lt_of_le_of_lt hrπ (half_lt_self Real.pi_pos)))
    rw [gInv_neg_sub_one_eq_block Z hr hs]
    set r := nu (Z : M2)
    set c := r * Real.cos r / Real.sin r
    have htri :
        ‖(c - 1) • Q Z + (-r) • J Z‖ ≤ |c - 1| * ‖Q Z‖ + r * ‖J Z‖ := by
      have h1 : ‖(c - 1) • Q Z + (-r) • J Z‖ ≤ ‖(c - 1) • Q Z‖ + ‖(-r) • J Z‖ :=
        norm_add_le _ _
      have h2 : ‖(c - 1) • Q Z‖ = |c - 1| * ‖Q Z‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      have h3 : ‖(-r) • J Z‖ = r * ‖J Z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hr]
      linarith
    have hQ : ‖Q Z‖ ≤ 1 := norm_Q_le Z hr
    have hJ : ‖J Z‖ ≤ 1 := norm_J_le Z hr
    have habs : |c - 1| * ‖Q Z‖ + r * ‖J Z‖ ≤ |c - 1| + r := by
      nlinarith [abs_nonneg (c - 1), le_of_lt hr]
    have hsc := inverse_gap_scalar hr hZ hρ
    linarith

theorem norm_gInv_pos_sub_one_le (Z : SuTwo) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Real.pi / 2) (hZ : nu (Z : M2) ≤ ρ) :
    ‖gInvOp (adOp Z) - 1‖ ≤ ρ * (1 + Real.pi / 2) := by
  have hn : nu ((-Z : SuTwo) : M2) = nu (Z : M2) := nu_neg _
  have hh := norm_gInv_neg_sub_one_le (-Z) hρ0 hρ (by rwa [hn])
  simpa [ad_neg, neg_neg, hn] using hh

theorem mul_sub_one_eq {A B : SuTwo →L[ℝ] SuTwo} :
    A * B - 1 = (A - 1) * B + (B - 1) := by
  calc A * B - 1
      = A * B - B + (B - 1) := by abel
    _ = (A - 1) * B + (B - 1) := by rw [sub_mul, one_mul]

theorem E1_operators_norm_le (Z Zx : SuTwo) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Real.pi / 2)
    (hZ : nu (Z : M2) ≤ ρ) (hZx : nu (Zx : M2) ≤ ρ) :
    ‖gOp (-(adOp Z)) * gInvOp (-(adOp Zx)) - 1‖ ≤ e1Majorant ρ := by
  have hg : ‖gOp (-(adOp Z)) - 1‖ ≤ Real.exp (2 * ρ) - 1 :=
    (norm_gOp_sub_one_le (-(adOp Z))).trans (exp_two_rho_gap_of_ad Z hρ0 hZ)
  have hB := norm_gInv_neg_le_of_ball Zx hρ0 hρ hZx
  have hB1 := norm_gInv_neg_sub_one_le Zx hρ0 hρ hZx
  rw [mul_sub_one_eq]
  have hsum :
      ‖(gOp (-(adOp Z)) - 1) * gInvOp (-(adOp Zx)) + (gInvOp (-(adOp Zx)) - 1)‖ ≤
        ‖(gOp (-(adOp Z)) - 1) * gInvOp (-(adOp Zx))‖ + ‖gInvOp (-(adOp Zx)) - 1‖ :=
    norm_add_le _ _
  have hmul : ‖(gOp (-(adOp Z)) - 1) * gInvOp (-(adOp Zx))‖ ≤
      ‖gOp (-(adOp Z)) - 1‖ * ‖gInvOp (-(adOp Zx))‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have hA := exp_two_rho_sub_one_nonneg hρ0
  have hprod : ‖gOp (-(adOp Z)) - 1‖ * ‖gInvOp (-(adOp Zx))‖ ≤
      (Real.exp (2 * ρ) - 1) * gInvMajorant ρ :=
    mul_le_mul hg hB (norm_nonneg _) hA
  have hfinal : ‖gOp (-(adOp Z)) - 1‖ * ‖gInvOp (-(adOp Zx))‖ + ‖gInvOp (-(adOp Zx)) - 1‖ ≤
      e1Majorant ρ := by
    dsimp [e1Majorant]
    linarith [hprod, hB1]
  calc ‖(gOp (-(adOp Z)) - 1) * gInvOp (-(adOp Zx)) + (gInvOp (-(adOp Zx)) - 1)‖
      ≤ ‖(gOp (-(adOp Z)) - 1) * gInvOp (-(adOp Zx))‖ + ‖gInvOp (-(adOp Zx)) - 1‖ := hsum
    _ ≤ ‖gOp (-(adOp Z)) - 1‖ * ‖gInvOp (-(adOp Zx))‖ + ‖gInvOp (-(adOp Zx)) - 1‖ :=
        add_le_add hmul le_rfl
    _ ≤ e1Majorant ρ := hfinal

theorem mul_mul_sub_one_eq {A B U : SuTwo →L[ℝ] SuTwo} :
    A * B * U - 1 = (A - 1) * B * U + (B - 1) * U + (U - 1) := by
  have h1 : A * B * U - B * U = (A - 1) * B * U := by
    have hAB : A * B - B = (A - 1) * B := by
      calc A * B - B
          = A * B - 1 * B := by rw [one_mul]
        _ = (A - 1) * B := (sub_mul A 1 B).symm
    calc A * B * U - B * U
        = (A * B) * U - B * U := rfl
      _ = (A * B - B) * U := (sub_mul (A * B) B U).symm
      _ = ((A - 1) * B) * U := by rw [hAB]
  have h2 : B * U - U = (B - 1) * U := by
    calc B * U - U
        = B * U - 1 * U := by rw [one_mul]
      _ = (B - 1) * U := (sub_mul B 1 U).symm
  calc A * B * U - 1
      = (A * B * U - B * U) + (B * U - U) + (U - 1) := by abel
    _ = (A - 1) * B * U + (B - 1) * U + (U - 1) := by rw [h1, h2]

theorem E2_operators_norm_le (Z Zx : SuTwo) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Real.pi / 2)
    (hZ : nu (Z : M2) ≤ ρ) (hZx : nu (Zx : M2) ≤ ρ) :
    ‖gOp (-(adOp Z)) * gInvOp (adOp Zx) * expOp (-(adOp Z)) - 1‖ ≤ e2Majorant ρ := by
  have hg : ‖gOp (-(adOp Z)) - 1‖ ≤ Real.exp (2 * ρ) - 1 :=
    (norm_gOp_sub_one_le (-(adOp Z))).trans (exp_two_rho_gap_of_ad Z hρ0 hZ)
  have hU1 : ‖expOp (-(adOp Z)) - 1‖ ≤ Real.exp (2 * ρ) - 1 :=
    (norm_expOp_sub_one_le (-(adOp Z))).trans (exp_two_rho_gap_of_ad Z hρ0 hZ)
  have hU : ‖expOp (-(adOp Z))‖ ≤ 1 := norm_exp_neg_le Z
  have hB := norm_gInv_pos_le_of_ball Zx hρ0 hρ hZx
  have hB1 := norm_gInv_pos_sub_one_le Zx hρ0 hρ hZx
  rw [mul_mul_sub_one_eq]
  set A : SuTwo →L[ℝ] SuTwo := gOp (-(adOp Z))
  set B : SuTwo →L[ℝ] SuTwo := gInvOp (adOp Zx)
  set U : SuTwo →L[ℝ] SuTwo := expOp (-(adOp Z))
  have hsum : ‖(A - 1) * B * U + (B - 1) * U + (U - 1)‖ ≤
      ‖(A - 1) * B * U‖ + ‖(B - 1) * U‖ + ‖U - 1‖ := by
    calc ‖(A - 1) * B * U + (B - 1) * U + (U - 1)‖
        ≤ ‖(A - 1) * B * U + (B - 1) * U‖ + ‖U - 1‖ := norm_add_le _ _
      _ ≤ (‖(A - 1) * B * U‖ + ‖(B - 1) * U‖) + ‖U - 1‖ :=
          add_le_add (norm_add_le _ _) le_rfl
  have hmul1 : ‖(A - 1) * B * U‖ ≤ ‖A - 1‖ * ‖B‖ * ‖U‖ := by
    calc ‖(A - 1) * B * U‖ ≤ ‖(A - 1) * B‖ * ‖U‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖A - 1‖ * ‖B‖) * ‖U‖ := by
          gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
  have hmul2 : ‖(B - 1) * U‖ ≤ ‖B - 1‖ * ‖U‖ := ContinuousLinearMap.opNorm_comp_le _ _
  have hA0 := exp_two_rho_sub_one_nonneg hρ0
  have hM := gInvMajorant_nonneg hρ0
  have hgap : 0 ≤ ρ * (1 + Real.pi / 2) := mul_nonneg hρ0 (by linarith [Real.pi_pos])
  have hprodAB : ‖A - 1‖ * ‖B‖ ≤ (Real.exp (2 * ρ) - 1) * gInvMajorant ρ :=
    mul_le_mul hg hB (norm_nonneg _) hA0
  have hprodABU : ‖A - 1‖ * ‖B‖ * ‖U‖ ≤ (Real.exp (2 * ρ) - 1) * gInvMajorant ρ := by
    have h1 : ‖A - 1‖ * ‖B‖ * ‖U‖ ≤
        ((Real.exp (2 * ρ) - 1) * gInvMajorant ρ) * ‖U‖ :=
      mul_le_mul_of_nonneg_right hprodAB (norm_nonneg _)
    have h2 : ((Real.exp (2 * ρ) - 1) * gInvMajorant ρ) * ‖U‖ ≤
        ((Real.exp (2 * ρ) - 1) * gInvMajorant ρ) * 1 :=
      mul_le_mul_of_nonneg_left hU (mul_nonneg hA0 hM)
    linarith
  have hprodBU : ‖B - 1‖ * ‖U‖ ≤ ρ * (1 + Real.pi / 2) := by
    have h1 : ‖B - 1‖ * ‖U‖ ≤ (ρ * (1 + Real.pi / 2)) * ‖U‖ :=
      mul_le_mul_of_nonneg_right hB1 (norm_nonneg _)
    have h2 : (ρ * (1 + Real.pi / 2)) * ‖U‖ ≤ (ρ * (1 + Real.pi / 2)) * 1 :=
      mul_le_mul_of_nonneg_left hU hgap
    linarith
  have hfinal : ‖A - 1‖ * ‖B‖ * ‖U‖ + ‖B - 1‖ * ‖U‖ + ‖U - 1‖ ≤ e2Majorant ρ := by
    dsimp [e2Majorant, e1Majorant]
    linarith [hprodABU, hprodBU, hU1]
  calc ‖(A - 1) * B * U + (B - 1) * U + (U - 1)‖
      ≤ ‖(A - 1) * B * U‖ + ‖(B - 1) * U‖ + ‖U - 1‖ := hsum
    _ ≤ ‖A - 1‖ * ‖B‖ * ‖U‖ + ‖B - 1‖ * ‖U‖ + ‖U - 1‖ :=
        add_le_add (add_le_add hmul1 hmul2) le_rfl
    _ ≤ e2Majorant ρ := hfinal

#print axioms gOp_summable
#print axioms norm_gOp_sub_one_le
#print axioms norm_expOp_sub_one_le
#print axioms norm_gInv_neg_sub_one_le
#print axioms E1_operators_norm_le
#print axioms E2_operators_norm_le
end EstimatesLayer.E1E3
