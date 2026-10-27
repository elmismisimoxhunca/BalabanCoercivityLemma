/-
Independent audit fixture, not the missing dexp_eq_gOp certificate.
Uses the unchanged imported adOp/gOp definitions. All operator-norm analysis
below is instantiated only on the ambient M2 continuous endomorphisms.
The hCoeff majorant proof is the generic proof in the candidate source.
-/
import T1MainSegment
import NonzeroExpDeriv
import AdalyFormal.Balaban.Bch2
import AdalyFormal.Balaban.RegularityGap
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace AdalySI1.M2RouteAudit
open Matrix
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2 su2Exp)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)

/-- A genuine continuous commutator on the ambient matrix algebra. -/
def adM2 (Z : M2) : M2 →L[ℝ] M2 :=
  (ContinuousLinearMap.mul ℝ M2) Z - (ContinuousLinearMap.mul ℝ M2).flip Z

theorem adM2_apply (Z X : M2) : adM2 Z X = Z * X - X * Z := rfl

theorem adM2_coe (Z X : SuTwo) :
    adM2 (Z : M2) (X : M2) = ((OneStep124.adOp Z X : SuTwo) : M2) := rfl

def hCoeff (n : ℕ) : ℝ := ((Nat.factorial (n + 1) : ℝ))⁻¹

theorem hCoeff_le (n : ℕ) : hCoeff n ≤ 1 / (Nat.factorial n : ℝ) := by
  have hfn : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hle : (Nat.factorial n : ℝ) ≤ (Nat.factorial (n + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  rw [hCoeff, inv_eq_one_div]
  exact one_div_le_one_div_of_le hfn hle

theorem hCoeff_nonneg (n : ℕ) : 0 ≤ hCoeff n := by rw [hCoeff]; positivity

theorem hSummable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) : Summable (fun n : ℕ => hCoeff n • T ^ n) := by
  have hb : ∀ n : ℕ, ‖hCoeff n • T ^ n‖ ≤ ‖T‖ ^ n / (Nat.factorial n : ℝ) := by
    intro n
    have hpow : ‖T ^ n‖ ≤ ‖T‖ ^ n := by
      induction n with
      | zero => simp only [pow_zero]; exact ContinuousLinearMap.norm_id_le
      | succ k ih =>
        rw [pow_succ, pow_succ]
        calc ‖T ^ k * T‖ ≤ ‖T ^ k‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖T‖ ^ k * ‖T‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg T)
    have hsmul : ‖hCoeff n • T ^ n‖ ≤ |hCoeff n| * ‖T ^ n‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro v
      rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((T ^ n).le_opNorm v) (abs_nonneg (hCoeff n))
    calc ‖hCoeff n • T ^ n‖ ≤ |hCoeff n| * ‖T ^ n‖ := hsmul
      _ ≤ (1 / (Nat.factorial n : ℝ)) * ‖T‖ ^ n :=
          mul_le_mul (by rw [abs_of_nonneg (hCoeff_nonneg n)]; exact hCoeff_le n) hpow
            (norm_nonneg _) (by positivity)
      _ = ‖T‖ ^ n / (Nat.factorial n : ℝ) := by ring
  exact Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖T‖) hb

/-- The genuine CMP98 coefficient series, now on ambient endomorphisms. -/
def gOpM2 (T : M2 →L[ℝ] M2) : M2 →L[ℝ] M2 :=
  ∑' n : ℕ, OneStep124.gCoeff n • T ^ n

theorem gCoeff_neg_pow_smul (T : M2 →L[ℝ] M2) (n : ℕ) :
    OneStep124.gCoeff n • (-T) ^ n = hCoeff n • T ^ n := by
  have hneg : (-T) ^ n = ((-1 : ℝ) ^ n) • T ^ n := by
    suffices h : ∀ x, ((-T) ^ n) x = (((-1 : ℝ) ^ n) • T ^ n) x by
      exact ContinuousLinearMap.ext h
    induction n with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      simp only [pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.smul_apply, ih, map_neg, smul_neg, smul_smul, neg_smul]
      module
  have hcoeff : OneStep124.gCoeff n * (-1 : ℝ) ^ n = hCoeff n := by
    rw [OneStep124.gCoeff, hCoeff, div_mul_eq_mul_div, ← mul_pow]
    norm_num
  rw [hneg, smul_smul, hcoeff]

/-- Ambient endomorphism summability, not a SuTwo endomorphism instantiation. -/
theorem ambient_series_summable (Z : M2) :
    Summable (fun n : ℕ => hCoeff n • adM2 Z ^ n) :=
  hSummable (adM2 Z)

theorem ambient_g_series_summable (Z : M2) :
    Summable (fun n : ℕ => OneStep124.gCoeff n • (-adM2 Z) ^ n) := by
  simp_rw [gCoeff_neg_pow_smul]
  exact ambient_series_summable Z

theorem gOpM2_neg_adM2 (Z : M2) :
    gOpM2 (-adM2 Z) = ∑' n : ℕ, hCoeff n • adM2 Z ^ n := by
  unfold gOpM2
  exact tsum_congr (fun n => gCoeff_neg_pow_smul (adM2 Z) n)

/-- Finite powers agree on SuTwo, independently of any infinite-sum transport. -/
theorem adM2_pow_coe (Z v : SuTwo) (n : ℕ) :
    (adM2 (Z : M2) ^ n) (v : M2) = (((OneStep124.adOp Z ^ n) v : SuTwo) : M2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ih]
    exact adM2_coe Z ((OneStep124.adOp Z ^ n) v)

/-- The helper proves only the arbitrary-basepoint ambient derivative bridge. -/
theorem ambient_bridge (Z v : SuTwo) :
    HasDerivAt (fun t : ℝ => ((su2Exp ((Z : M2) + t • (v : M2)) : SU2) : M2))
      ((fderiv ℝ (NormedSpace.exp : M2 → M2) (Z : M2)) (v : M2)) 0 :=
  AdalySI1.NonzeroExpDeriv.hasDerivAt_su2Exp_coe_add_smul Z.2.1 v.2.1 Z.2.2 v.2.2

#print axioms adM2_coe
#print axioms adM2_pow_coe
#print axioms ambient_series_summable
#print axioms ambient_g_series_summable
#print axioms gOpM2_neg_adM2
#print axioms ambient_bridge
#print axioms OneStep124.gOp
#print axioms AdalyFormal.Balaban.Bch2.exp_form

run_cmd do
  let names : List Lean.Name := [
    `AdalySI1.M2RouteAudit.adM2_coe,
    `AdalySI1.M2RouteAudit.adM2_pow_coe,
    `AdalySI1.M2RouteAudit.ambient_series_summable,
    `AdalySI1.M2RouteAudit.ambient_g_series_summable,
    `AdalySI1.M2RouteAudit.gOpM2_neg_adM2,
    `AdalySI1.M2RouteAudit.ambient_bridge,
    `OneStep124.gOp,
    `AdalyFormal.Balaban.Bch2.exp_form]
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in names do
    unless (← Lean.getEnv).contains name do
      throwError "Missing audited declaration: {name}"
    for axiomName in (← Lean.collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "Nonstandard axiom in {name}: {axiomName}"
  Lean.logInfo "AUDIT_STANDARD_AXIOMS_PASS"

end AdalySI1.M2RouteAudit
