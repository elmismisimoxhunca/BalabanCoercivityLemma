/-
Owned lane compute/m1_si1_step2/c1/. The referenced f1/Adjoint.lean was never produced (the prior
f1 lane crashed before writing any file: "Error: Workflow worker failed", empty report). This is a
fresh, from-scratch closure of unpaid clause A only (compute/m1_si1_step2/inv/UNPAID_MAP.md §A):

  RMap (su2Exp Z) v = expOp (adOp Z) v      for Z v : SuTwo

proved via the Rodrigues/dexp route the HANDOFF requires (NOT the r88 AdjointExpBridge cone: no
import of compute/deltak_r88/AdjointExpBridge.lean anywhere below). Both sides are computed in
closed form on the {v, adOp Z v, (adOp Z)^2 v} basis and matched coefficientwise; the expOp-side
closed form reuses the already-paid `w`/`w_odd_even`/`hSummable`-style machinery from
`AdalySI1.DexpRodrigues` (compute/m1_si1_step2/deps/DexpRodriguesG.lean), adapted from `gCoeff` to
`expCoeff` (no sign flip, so the summable bound is simpler and the even-slot sum coincides
literally with the already-proven `hasSum_Q1`... here re-derived fresh under `expCoeff`'s own name
to avoid a fragile cross-file `hCoeff`/`expCoeff` defeq unfold).

Clause B (compute/m1_si1_step2/inv/UNPAID_MAP.md §B,
`gInvOp (-adOp Zx) * expOp (adOp Zx) = gInvOp (adOp Zx)`) is NOT attempted here: it needs
`IsUnit (gOp (adOp Zx))` ("g_pos_unit"), which is not implied by A alone or by anything paid in
`deps/`. Two routes were identified but not verified/compiled in this lane's budget:
(i) `principalSuTwoLog (g⁻¹) = -(principalSuTwoLog g)` (derivable from `Yof`/`su2Angle`
    invariance under `g ↦ g⁻¹ = gᴴ`), applied to the already-paid
    `AdalySI1.L4Audit.gOp_principalLog_isUnit` at `g⁻¹` instead of `g`
    (`adOp` linear ⇒ `-(adOp (-Zx)) = adOp Zx`);
(ii) the pure power-series identity `gOp (-T) = expOp T * gOp T`, combined with A applied at `-Zx`
     to get `IsUnit (expOp (-(adOp Zx)))`, giving `gOp (adOp Zx)` as a product of two units.
Neither is compiled; this file contains ONLY clause A, standard-only axioms, no `sorry`.
-/
import T1MainSegment
import NonzeroExpDeriv
import GopTransport
import DexpRodriguesG
import L4AuditCompletion
import AdalyFormal.Balaban.Bch2
import AdalyFormal.Balaban.RegularityGap
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace AdalySI1.Adjoint

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
open scoped Nat
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2 su2Exp su2Exp_zero su2NegOne)
open AdalyFormal.Balaban.CovariantOperators
  (SuTwo RMap RMap_coe_apply RMap_one RMap_mul RMap_mul_apply)
open OneStep124 (adOp gOp gCoeff expCoeff expOp gInvOp)
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open AdalySI1.DexpRodrigues (isSu2_coe adOp_apply_coe zxz double_comm adOp_cube_apply
  w w_succ w_eq_pow_apply w_rec3 w_rec3' w_odd_even hSummable adOp_zero_eq
  hCoeff hCoeff_nonneg hCoeff_le hasSum_Q1 hasSum_Q2 gOp_neg_adOp_apply gOp_zero_eq
  gCoeff_neg_pow_smul)

/-! ## §0 — a small conjugate-transpose helper for real scalars on `M2` -/

theorem real_smul_conjTranspose (r : ℝ) (X : M2) : (r • X)ᴴ = r • Xᴴ := by
  rw [← AdalyFormal.Balaban.RegularityGap.real_smul_eq r X,
      AdalyFormal.Balaban.Bch2.conjT_real_smul,
      AdalyFormal.Balaban.RegularityGap.real_smul_eq]

/-! ## §1 — summability of the `expCoeff` series (no sign flip needed, simpler bound than
`hSummable`'s `hCoeff` case since `expCoeff n = 1/n!` already IS the bound). -/

theorem expCoeff_nonneg (n : ℕ) : 0 ≤ expCoeff n := by rw [expCoeff]; positivity

theorem expSummable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) : Summable (fun n : ℕ => expCoeff n • T ^ n) := by
  have hb : ∀ n : ℕ, ‖expCoeff n • T ^ n‖ ≤ ‖T‖ ^ n / (Nat.factorial n : ℝ) := by
    intro n
    have hpow : ‖T ^ n‖ ≤ ‖T‖ ^ n := by
      induction n with
      | zero => simp only [pow_zero]; exact ContinuousLinearMap.norm_id_le
      | succ k ih =>
        rw [pow_succ, pow_succ]
        calc ‖T ^ k * T‖ ≤ ‖T ^ k‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖T‖ ^ k * ‖T‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg T)
    have hsmul : ‖expCoeff n • T ^ n‖ ≤ |expCoeff n| * ‖T ^ n‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro v
      rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((T ^ n).le_opNorm v) (abs_nonneg (expCoeff n))
    calc ‖expCoeff n • T ^ n‖ ≤ |expCoeff n| * ‖T ^ n‖ := hsmul
      _ ≤ expCoeff n * ‖T‖ ^ n := by
          rw [abs_of_nonneg (expCoeff_nonneg n)]
          exact mul_le_mul_of_nonneg_left hpow (expCoeff_nonneg n)
      _ = ‖T‖ ^ n / (Nat.factorial n : ℝ) := by rw [expCoeff]; ring
  exact Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖T‖) hb

/-! ## §2 — the two coefficient sums, `expCoeff`'s own odd/even split (fresh, not a reuse of
`hCoeff`'s reindexed sums, to avoid a fragile cross-file defeq unfold). -/

theorem hasSum_expOdd (r0 : ℝ) (hr0 : 0 < r0) :
    HasSum (fun k : ℕ => expCoeff (2 * k + 1) * (-4 * r0 ^ 2) ^ k)
      (Real.sin (2 * r0) / (2 * r0)) := by
  have hexp : ∀ n : ℕ, (-1 : ℝ) ^ n * (2 * r0) ^ (2 * n) = (-4 * r0 ^ 2) ^ n := by
    intro n
    rw [pow_mul, show (2 * r0) ^ 2 = 4 * r0 ^ 2 from by ring, ← mul_pow]
    congr 1; ring
  have hr0ne : (2 * r0 : ℝ) ≠ 0 := by positivity
  have h0 := Real.hasSum_sin (2 * r0)
  have heq : ∀ n : ℕ, (-1 : ℝ) ^ n * (2 * r0) ^ (2 * n + 1) / (2 * n + 1)!
      = (2 * r0) * ((-4 * r0 ^ 2) ^ n / (2 * n + 1)!) := by
    intro n; rw [← hexp n]; ring
  have h1 : HasSum (fun n : ℕ => (2 * r0) * ((-4 * r0 ^ 2) ^ n / (2 * n + 1)!)) (Real.sin (2 * r0)) := by
    have heqf : (fun n : ℕ => (-1 : ℝ) ^ n * (2 * r0) ^ (2 * n + 1) / (2 * n + 1)!)
        = (fun n : ℕ => (2 * r0) * ((-4 * r0 ^ 2) ^ n / (2 * n + 1)!)) := by funext n; rw [heq n]
    rwa [heqf] at h0
  have h2 := h1.div_const (2 * r0)
  have hfe : (fun n : ℕ => (2 * r0) * ((-4 * r0 ^ 2) ^ n / (2 * n + 1)!) / (2 * r0))
      = (fun n : ℕ => (-4 * r0 ^ 2) ^ n / (2 * n + 1)!) := by
    funext n; rw [mul_div_assoc']; field_simp
  rw [hfe] at h2
  have heqf2 : (fun k : ℕ => expCoeff (2 * k + 1) * (-4 * r0 ^ 2) ^ k)
      = (fun k : ℕ => (-4 * r0 ^ 2) ^ k / (2 * k + 1)!) := by
    funext k; rw [expCoeff]; ring
  rw [heqf2]
  exact h2

theorem hasSum_expEven (r0 : ℝ) (hr0 : 0 < r0) :
    HasSum (fun k : ℕ => expCoeff (2 * k + 2) * (-4 * r0 ^ 2) ^ k)
      ((1 - Real.cos (2 * r0)) / (4 * r0 ^ 2)) := by
  have hexp : ∀ n : ℕ, (-1 : ℝ) ^ n * (2 * r0) ^ (2 * n) = (-4 * r0 ^ 2) ^ n := by
    intro n
    rw [pow_mul, show (2 * r0) ^ 2 = 4 * r0 ^ 2 from by ring, ← mul_pow]
    congr 1; ring
  have hf : HasSum (fun n : ℕ => (-4 * r0 ^ 2) ^ n / (2 * n)!) (Real.cos (2 * r0)) := by
    have h0 := Real.hasSum_cos (2 * r0)
    have heq : (fun n : ℕ => (-1 : ℝ) ^ n * (2 * r0) ^ (2 * n) / (2 * n)!)
        = (fun n : ℕ => (-4 * r0 ^ 2) ^ n / (2 * n)!) := by funext n; rw [hexp n]
    rwa [heq] at h0
  have hs : Summable (fun n : ℕ => (-4 * r0 ^ 2) ^ n / (2 * n)!) := hf.summable
  have hcos_shift : Real.cos (2 * r0) - 1 = ∑' n : ℕ, (-4 * r0 ^ 2) ^ (n + 1) / (2 * (n + 1))! := by
    have hz := hs.tsum_eq_zero_add
    rw [hf.tsum_eq] at hz
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hz
    linarith [hz]
  have hterm : ∀ k : ℕ, (4 * r0 ^ 2) * ((-4 * r0 ^ 2) ^ k / (2 * k + 2)!)
      = -((-4 * r0 ^ 2) ^ (k + 1) / (2 * (k + 1))!) := by
    intro k
    rw [pow_succ, show 2 * (k + 1) = 2 * k + 2 from by ring]
    ring
  have hshift_sum : Summable (fun k : ℕ => (-4 * r0 ^ 2) ^ (k + 1) / (2 * (k + 1))!) :=
    hs.comp_injective (add_left_injective 1)
  have hQ1sum : Summable (fun k : ℕ => (-4 * r0 ^ 2) ^ k / (2 * k + 2)!) :=
    (hshift_sum.mul_right ((-4 * r0 ^ 2)⁻¹)).congr (fun k => by
      rw [pow_succ, show 2 * (k + 1) = 2 * k + 2 from by ring]
      field_simp)
  have h4mul : (4 * r0 ^ 2) * (∑' k : ℕ, (-4 * r0 ^ 2) ^ k / (2 * k + 2)!)
      = ∑' k : ℕ, -((-4 * r0 ^ 2) ^ (k + 1) / (2 * (k + 1))!) := by
    rw [← tsum_mul_left]; exact tsum_congr hterm
  have h4mul' : (4 * r0 ^ 2) * (∑' k : ℕ, (-4 * r0 ^ 2) ^ k / (2 * k + 2)!) = 1 - Real.cos (2 * r0) := by
    rw [h4mul, tsum_neg, ← hcos_shift]; ring
  have h4ne : (4 * r0 ^ 2 : ℝ) ≠ 0 := by positivity
  have htsum_val : (∑' k : ℕ, (-4 * r0 ^ 2) ^ k / (2 * k + 2)!) = (1 - Real.cos (2 * r0)) / (4 * r0 ^ 2) := by
    rw [eq_div_iff h4ne, mul_comm]; exact h4mul'
  have heqf : (fun k : ℕ => expCoeff (2 * k + 2) * (-4 * r0 ^ 2) ^ k)
      = (fun k : ℕ => (-4 * r0 ^ 2) ^ k / (2 * k + 2)!) := by
    funext k; rw [expCoeff]; ring
  rw [heqf, ← htsum_val]
  exact hQ1sum.hasSum

/-! ## §3 — closed value of `expOp (adOp Z) v`, mirroring `DexpRodrigues.gOp_neg_adOp_apply`
but for the un-negated series (no `gCoeff_neg_pow_smul`-style sign reindex needed). -/

theorem expOp_adOp_apply (Z v : SuTwo) (hZ : Z ≠ 0) :
    (expOp (adOp Z) v : SuTwo)
      = v + (Real.sin (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))
              / (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))) • w Z v 1
        + ((1 - Real.cos (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2)))
              / (4 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2)) • w Z v 2 := by
  have hr0 : 0 < AdalyFormal.Balaban.Bch2.nu (Z : M2) := by
    rcases lt_or_eq_of_le (AdalyFormal.Balaban.Bch2.nu_nonneg (Z : M2)) with h | h
    · exact h
    · exact absurd (Subtype.ext ((AdalyFormal.Balaban.Bch2.nu_eq_zero_iff (Z : M2)).mp h.symm)) hZ
  set r0 := AdalyFormal.Balaban.Bch2.nu (Z : M2) with hr0def
  have step1 : (expOp (adOp Z) v : SuTwo) = (∑' n : ℕ, expCoeff n • (adOp Z) ^ n) v := rfl
  have step2 : (∑' n : ℕ, expCoeff n • (adOp Z) ^ n) v
      = ∑' n : ℕ, expCoeff n • (((adOp Z) ^ n) v) :=
    (ContinuousLinearMap.apply ℝ SuTwo v).map_tsum (expSummable (adOp Z))
  have step3 : (∑' n : ℕ, expCoeff n • (((adOp Z) ^ n) v)) = ∑' n : ℕ, expCoeff n • w Z v n :=
    tsum_congr (fun n => by rw [w_eq_pow_apply])
  have hodd : HasSum (fun k : ℕ => expCoeff (2 * k + 1) • w Z v (2 * k + 1))
      ((Real.sin (2 * r0) / (2 * r0)) • w Z v 1) := by
    have h := (hasSum_expOdd r0 hr0).smul_const (w Z v 1)
    convert h using 1
    funext k
    rw [(w_odd_even Z v k).1, smul_smul]
  have heven : HasSum (fun k : ℕ => expCoeff (2 * k + 2) • w Z v (2 * k + 2))
      (((1 - Real.cos (2 * r0)) / (4 * r0 ^ 2)) • w Z v 2) := by
    have h := (hasSum_expEven r0 hr0).smul_const (w Z v 2)
    convert h using 1
    funext k
    rw [(w_odd_even Z v k).2, smul_smul]
  have heo : HasSum (fun n : ℕ => expCoeff (n + 1) • w Z v (n + 1))
      ((Real.sin (2 * r0) / (2 * r0)) • w Z v 1
        + ((1 - Real.cos (2 * r0)) / (4 * r0 ^ 2)) • w Z v 2) :=
    HasSum.even_add_odd hodd heven
  have hza := (hasSum_nat_add_iff (f := fun m : ℕ => expCoeff m • w Z v m) 1).mp heo
  simp only [Finset.sum_range_one] at hza
  have hf0 : expCoeff 0 • w Z v 0 = v := by show expCoeff 0 • v = v; simp [expCoeff, w]
  rw [hf0] at hza
  rw [step1, step2, step3, hza.tsum_eq]
  abel

theorem expOp_zero_eq : expOp (0 : SuTwo →L[ℝ] SuTwo) = 1 := by
  rw [expOp, tsum_eq_single 0]
  · simp [expCoeff]
  · intro n hn
    rw [zero_pow hn]
    ext x
    simp

/-! ## §4 — the adjoint-exponential identity A, `Z ≠ 0` case: both sides computed on the
`{v, adOp Z v, (adOp Z)^2 v}` basis and matched coefficientwise. -/

theorem rmap_su2Exp_apply_eq_expOp_ad_pos (Z v : SuTwo) (hZ : Z ≠ 0) :
    RMap (su2Exp (Z : M2)) v = expOp (adOp Z) v := by
  apply Subtype.ext
  have hr0 : 0 < AdalyFormal.Balaban.Bch2.nu (Z : M2) := by
    rcases lt_or_eq_of_le (AdalyFormal.Balaban.Bch2.nu_nonneg (Z : M2)) with h | h
    · exact h
    · exact absurd (Subtype.ext ((AdalyFormal.Balaban.Bch2.nu_eq_zero_iff (Z : M2)).mp h.symm)) hZ
  set r0 := AdalyFormal.Balaban.Bch2.nu (Z : M2) with hr0def
  set p := AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2) with hpdef
  have hexp : ((su2Exp (Z : M2) : SU2) : M2)
      = Real.cos r0 • (1 : M2) + (Real.sin r0 * r0⁻¹) • (Z : M2) :=
    AdalyFormal.Balaban.Bch2.exp_form (isSu2_coe Z)
  have hexpH : ((su2Exp (Z : M2) : SU2) : M2)ᴴ
      = Real.cos r0 • (1 : M2) - (Real.sin r0 * r0⁻¹) • (Z : M2) := by
    rw [hexp, Matrix.conjTranspose_add, real_smul_conjTranspose, real_smul_conjTranspose,
        Matrix.conjTranspose_one, (isSu2_coe Z).1]
    module
  have hRMap : (RMap (su2Exp (Z : M2)) v : M2)
      = (Real.cos r0 • (1 : M2) + (Real.sin r0 * r0⁻¹) • (Z : M2)) * (v : M2)
          * (Real.cos r0 • (1 : M2) - (Real.sin r0 * r0⁻¹) • (Z : M2)) := by
    rw [RMap_coe_apply, hexpH, hexp]
  have hAv : (Real.cos r0 • (1 : M2) + (Real.sin r0 * r0⁻¹) • (Z : M2)) * (v : M2)
      = Real.cos r0 • (v : M2) + (Real.sin r0 * r0⁻¹) • ((Z : M2) * (v : M2)) := by
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
  have hzxz := zxz Z v
  have hAvB : (Real.cos r0 • (v : M2) + (Real.sin r0 * r0⁻¹) • ((Z : M2) * (v : M2)))
        * (Real.cos r0 • (1 : M2) - (Real.sin r0 * r0⁻¹) • (Z : M2))
      = (Real.cos r0 * Real.cos r0 - Real.sin r0 * r0⁻¹ * (Real.sin r0 * r0⁻¹) * r0 ^ 2) • (v : M2)
        + (Real.sin r0 * r0⁻¹ * Real.cos r0) • ((Z : M2) * (v : M2) - (v : M2) * (Z : M2))
        + (Real.sin r0 * r0⁻¹ * (Real.sin r0 * r0⁻¹) * p) • (Z : M2) := by
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one]
    rw [hzxz]
    module
  rw [hAv, hAvB] at hRMap
  have hw1 : ((w Z v 1 : SuTwo) : M2) = (Z : M2) * (v : M2) - (v : M2) * (Z : M2) := by
    show ((adOp Z v : SuTwo) : M2) = _
    exact adOp_apply_coe Z v
  have hw2 : ((w Z v 2 : SuTwo) : M2) = (-4 * r0 ^ 2) • (v : M2) + (2 * p) • (Z : M2) := by
    show ((adOp Z (adOp Z v) : SuTwo) : M2) = _
    rw [hr0def, hpdef]
    exact double_comm Z v
  have hexpOp := expOp_adOp_apply Z v hZ
  have hcoeRHS : ((expOp (adOp Z) v : SuTwo) : M2)
      = (v : M2) + (Real.sin (2 * r0) / (2 * r0)) • ((Z : M2) * (v : M2) - (v : M2) * (Z : M2))
        + ((1 - Real.cos (2 * r0)) / (4 * r0 ^ 2)) • ((-4 * r0 ^ 2) • (v : M2) + (2 * p) • (Z : M2)) := by
    rw [hexpOp]
    simp only [Submodule.coe_add, Submodule.coe_smul, hw1, hw2, ← hr0def]
  have hsin2r0 : Real.sin (2 * r0) / (2 * r0) = Real.sin r0 * Real.cos r0 / r0 := by
    rw [Real.sin_two_mul]; ring
  have hcos2r0 : (1 - Real.cos (2 * r0)) / (4 * r0 ^ 2) = Real.sin r0 ^ 2 / (2 * r0 ^ 2) := by
    have h : Real.cos (2 * r0) = 1 - 2 * Real.sin r0 ^ 2 := by
      rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq r0]
    rw [h]; ring
  rw [hRMap, hcoeRHS, hsin2r0, hcos2r0]
  have hr0ne : r0 ≠ 0 := hr0.ne'
  match_scalars <;> (try field_simp) <;>
    first
      | ring1
      | nlinarith [Real.sin_sq_add_cos_sq r0]

theorem rmap_su2Exp_apply_eq_expOp_ad_zero (v : SuTwo) :
    RMap (su2Exp ((0 : SuTwo) : M2)) v = expOp (adOp (0 : SuTwo)) v := by
  have h0 : ((0 : SuTwo) : M2) = (0 : M2) := Submodule.coe_zero
  rw [h0, su2Exp_zero, RMap_one, adOp_zero_eq, expOp_zero_eq]
  simp

theorem rmap_su2Exp_apply_eq_expOp_ad (Z v : SuTwo) :
    RMap (su2Exp (Z : M2)) v = expOp (adOp Z) v := by
  rcases eq_or_ne Z 0 with hZ | hZ
  · subst hZ; exact rmap_su2Exp_apply_eq_expOp_ad_zero v
  · exact rmap_su2Exp_apply_eq_expOp_ad_pos Z v hZ

#print axioms rmap_su2Exp_apply_eq_expOp_ad

/-! ## §5 — clause B: `gInvOp (-ad Zx) * expOp (ad Zx) = gInvOp (ad Zx)`. Needs
`IsUnit (gOp (adOp Zx))` ("g_pos_unit"), obtained from a fresh `gOp (adOp Z)` closed form
(coefficient-flipped from paid `gOp_neg_adOp_apply`), the algebraic identity
`expOp T * gOp T = gOp (-T)`, and a left-inverse/finite-dimension bijectivity argument — per
compute/m1_si1_step2/diag/PATCH.md. -/

theorem gCoeff_eq_neg_pow_hCoeff (n : ℕ) :
    gCoeff n = (-1 : ℝ) ^ n * hCoeff n := by
  rw [gCoeff, hCoeff, div_eq_mul_inv]

theorem gCoeff_odd (k : ℕ) : gCoeff (2 * k + 1) = - hCoeff (2 * k + 1) := by
  rw [gCoeff_eq_neg_pow_hCoeff, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul]

theorem gCoeff_even_succ (k : ℕ) : gCoeff (2 * k + 2) = hCoeff (2 * k + 2) := by
  rw [gCoeff_eq_neg_pow_hCoeff, show 2 * k + 2 = 2 * (k + 1) from by ring,
      pow_mul, neg_one_sq, one_pow, one_mul]

theorem gSummable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) : Summable (fun n : ℕ => gCoeff n • T ^ n) := by
  have hb : ∀ n : ℕ, ‖gCoeff n • T ^ n‖ ≤ ‖T‖ ^ n / (Nat.factorial n : ℝ) := by
    intro n
    have hpow : ‖T ^ n‖ ≤ ‖T‖ ^ n := by
      induction n with
      | zero => simp only [pow_zero]; exact ContinuousLinearMap.norm_id_le
      | succ k ih =>
        rw [pow_succ, pow_succ]
        calc ‖T ^ k * T‖ ≤ ‖T ^ k‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖T‖ ^ k * ‖T‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg T)
    have habs : |gCoeff n| = hCoeff n := by
      rw [gCoeff_eq_neg_pow_hCoeff, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (hCoeff_nonneg n)]
    have hsmul : ‖gCoeff n • T ^ n‖ ≤ |gCoeff n| * ‖T ^ n‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro v
      rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((T ^ n).le_opNorm v) (abs_nonneg (gCoeff n))
    calc ‖gCoeff n • T ^ n‖ ≤ |gCoeff n| * ‖T ^ n‖ := hsmul
      _ = hCoeff n * ‖T ^ n‖ := by rw [habs]
      _ ≤ (1 / (Nat.factorial n : ℝ)) * ‖T‖ ^ n :=
          mul_le_mul (hCoeff_le n) hpow (norm_nonneg _) (by positivity)
      _ = ‖T‖ ^ n / (Nat.factorial n : ℝ) := by ring
  exact Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖T‖) hb

theorem w_one_eq (Z u : SuTwo) : w Z u 1 = adOp Z u := rfl

theorem w_two_eq (Z u : SuTwo) : w Z u 2 = adOp Z (adOp Z u) := rfl

theorem gOp_adOp_apply (Z v : SuTwo) (hZ : Z ≠ 0) :
    (gOp (adOp Z) v : SuTwo)
      = v
        - ((1 - Real.cos (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2)))
            / (4 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2)) • w Z v 1
        + ((2 * AdalyFormal.Balaban.Bch2.nu (Z : M2)
            - Real.sin (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2)))
            / (8 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 3)) • w Z v 2 := by
  have hr0 : 0 < AdalyFormal.Balaban.Bch2.nu (Z : M2) := by
    rcases lt_or_eq_of_le (AdalyFormal.Balaban.Bch2.nu_nonneg (Z : M2)) with h | h
    · exact h
    · exact absurd (Subtype.ext ((AdalyFormal.Balaban.Bch2.nu_eq_zero_iff (Z : M2)).mp h.symm)) hZ
  set r0 := AdalyFormal.Balaban.Bch2.nu (Z : M2) with hr0def
  have step1 : (gOp (adOp Z) v : SuTwo) = (∑' n : ℕ, gCoeff n • (adOp Z) ^ n) v := rfl
  have step2 : (∑' n : ℕ, gCoeff n • (adOp Z) ^ n) v = ∑' n : ℕ, gCoeff n • (((adOp Z) ^ n) v) :=
    (ContinuousLinearMap.apply ℝ SuTwo v).map_tsum (gSummable (adOp Z))
  have step3 : (∑' n : ℕ, gCoeff n • (((adOp Z) ^ n) v)) = ∑' n : ℕ, gCoeff n • w Z v n :=
    tsum_congr (fun n => by rw [w_eq_pow_apply])
  have hodd : HasSum (fun k : ℕ => gCoeff (2 * k + 1) • w Z v (2 * k + 1))
      ((-((1 - Real.cos (2 * r0)) / (4 * r0 ^ 2))) • w Z v 1) := by
    have h2 : HasSum (fun k : ℕ => -(hCoeff (2 * k + 1) * (-4 * r0 ^ 2) ^ k))
        (-((1 - Real.cos (2 * r0)) / (4 * r0 ^ 2))) := (hasSum_Q1 r0 hr0).neg
    have h3 := h2.smul_const (w Z v 1)
    have hfun : (fun k : ℕ => gCoeff (2 * k + 1) • w Z v (2 * k + 1))
        = (fun k : ℕ => (-(hCoeff (2 * k + 1) * (-4 * r0 ^ 2) ^ k)) • w Z v 1) := by
      funext k
      rw [gCoeff_odd, (w_odd_even Z v k).1]
      module
    rw [hfun]
    exact h3
  have heven : HasSum (fun k : ℕ => gCoeff (2 * k + 2) • w Z v (2 * k + 2))
      (((2 * r0 - Real.sin (2 * r0)) / (8 * r0 ^ 3)) • w Z v 2) := by
    have h := (hasSum_Q2 r0 hr0).smul_const (w Z v 2)
    convert h using 1
    funext k
    rw [gCoeff_even_succ, (w_odd_even Z v k).2]
    module
  have heo : HasSum (fun n : ℕ => gCoeff (n + 1) • w Z v (n + 1))
      ((-((1 - Real.cos (2 * r0)) / (4 * r0 ^ 2))) • w Z v 1
        + ((2 * r0 - Real.sin (2 * r0)) / (8 * r0 ^ 3)) • w Z v 2) :=
    HasSum.even_add_odd hodd heven
  have hza := (hasSum_nat_add_iff (f := fun m : ℕ => gCoeff m • w Z v m) 1).mp heo
  simp only [Finset.sum_range_one] at hza
  have hf0 : gCoeff 0 • w Z v 0 = v := by show gCoeff 0 • v = v; simp [gCoeff, w]
  rw [hf0] at hza
  rw [step1, step2, step3, hza.tsum_eq]
  module

theorem expOp_ad_mul_gOp_ad_eq_gOp_neg_ad (Z : SuTwo) :
    expOp (adOp Z) * gOp (adOp Z) = gOp (-(adOp Z)) := by
  rcases eq_or_ne Z 0 with hZ | hZ
  · subst hZ
    rw [adOp_zero_eq, neg_zero, expOp_zero_eq, gOp_zero_eq, one_mul]
  · apply ContinuousLinearMap.ext
    intro v
    show expOp (adOp Z) (gOp (adOp Z) v) = gOp (-(adOp Z)) v
    have hr0 : 0 < AdalyFormal.Balaban.Bch2.nu (Z : M2) := by
      rcases lt_or_eq_of_le (AdalyFormal.Balaban.Bch2.nu_nonneg (Z : M2)) with h | h
      · exact h
      · exact absurd (Subtype.ext ((AdalyFormal.Balaban.Bch2.nu_eq_zero_iff (Z : M2)).mp h.symm)) hZ
    set r0 := AdalyFormal.Balaban.Bch2.nu (Z : M2) with hr0def
    have hu : (gOp (adOp Z) v : SuTwo)
        = v - ((1 - Real.cos (2 * r0)) / (4 * r0 ^ 2)) • w Z v 1
            + ((2 * r0 - Real.sin (2 * r0)) / (8 * r0 ^ 3)) • w Z v 2 := gOp_adOp_apply Z v hZ
    have hw1 : adOp Z v = w Z v 1 := (w_one_eq Z v).symm
    have hw2 : adOp Z (w Z v 1) = w Z v 2 := by rw [w_one_eq]; exact (w_two_eq Z v).symm
    have hw3 : adOp Z (w Z v 2) = (-4 * r0 ^ 2) • w Z v 1 := w_rec3' Z v 0
    have hau : adOp Z (gOp (adOp Z) v)
        = (1 - (2 * r0 - Real.sin (2 * r0)) / (8 * r0 ^ 3) * (4 * r0 ^ 2)) • w Z v 1
            - ((1 - Real.cos (2 * r0)) / (4 * r0 ^ 2)) • w Z v 2 := by
      rw [hu]
      simp only [map_sub, map_add, map_smul, hw1, hw2, hw3, smul_smul]
      module
    have hau2 : adOp Z (adOp Z (gOp (adOp Z) v))
        = ((1 - Real.cos (2 * r0)) / (4 * r0 ^ 2) * (4 * r0 ^ 2)) • w Z v 1
            + (1 - (2 * r0 - Real.sin (2 * r0)) / (8 * r0 ^ 3) * (4 * r0 ^ 2)) • w Z v 2 := by
      rw [hau]
      simp only [map_sub, map_smul, hw2, hw3, smul_smul]
      module
    have hexpu : expOp (adOp Z) (gOp (adOp Z) v)
        = (gOp (adOp Z) v : SuTwo)
            + (Real.sin (2 * r0) / (2 * r0)) • adOp Z (gOp (adOp Z) v)
            + ((1 - Real.cos (2 * r0)) / (4 * r0 ^ 2)) • adOp Z (adOp Z (gOp (adOp Z) v)) := by
      have h := expOp_adOp_apply Z (gOp (adOp Z) v) hZ
      rwa [w_one_eq, w_two_eq] at h
    have hrhs : (gOp (-(adOp Z)) v : SuTwo)
        = v + ((1 - Real.cos (2 * r0)) / (4 * r0 ^ 2)) • w Z v 1
            + ((2 * r0 - Real.sin (2 * r0)) / (8 * r0 ^ 3)) • w Z v 2 :=
      gOp_neg_adOp_apply Z v hZ
    rw [hexpu, hau2, hau, hu, hrhs]
    have hr0ne : r0 ≠ 0 := hr0.ne'
    match_scalars <;> (try field_simp) <;>
      first
        | ring1
        | nlinarith [Real.sin_sq_add_cos_sq (2 * r0), Real.sin_sq_add_cos_sq r0]

theorem expOp_adOp_eq_toCLM_RMap (Z : SuTwo) :
    expOp (adOp Z)
      = LinearMap.toContinuousLinearMap (RMap (su2Exp (Z : M2))) := by
  apply ContinuousLinearMap.ext
  intro v
  exact (rmap_su2Exp_apply_eq_expOp_ad Z v).symm

theorem isUnit_toCLM_RMap (g : SU2) :
    IsUnit (LinearMap.toContinuousLinearMap (RMap g)) := by
  refine ⟨⟨LinearMap.toContinuousLinearMap (RMap g),
           LinearMap.toContinuousLinearMap (RMap g⁻¹), ?val_inv, ?inv_val⟩, rfl⟩
  · apply ContinuousLinearMap.ext
    intro x
    change RMap g (RMap g⁻¹ x) = x
    rw [RMap_mul_apply, mul_inv_cancel, RMap_one]; rfl
  · apply ContinuousLinearMap.ext
    intro x
    change RMap g⁻¹ (RMap g x) = x
    rw [RMap_mul_apply, inv_mul_cancel, RMap_one]; rfl

theorem isUnit_expOp_adOp (Z : SuTwo) : IsUnit (expOp (adOp Z)) := by
  rw [expOp_adOp_eq_toCLM_RMap]
  exact isUnit_toCLM_RMap _

theorem gOp_ad_principalLog_isUnit {g : SU2} (hne : g ≠ su2NegOne) :
    IsUnit (gOp (adOp (principalSuTwoLog g))) := by
  set Z := principalSuTwoLog g
  set T := adOp Z
  have hneg : IsUnit (gOp (-T)) := AdalySI1.L4Audit.gOp_principalLog_isUnit hne
  have hL : (gInvOp (-T) * expOp T) * gOp T = 1 := by
    rw [mul_assoc, expOp_ad_mul_gOp_ad_eq_gOp_neg_ad, gInvOp,
        Ring.inverse_mul_cancel _ hneg]
  have hLapp : ∀ z : SuTwo, gInvOp (-T) (expOp T (gOp T z)) = z := by
    intro z
    have h := congrArg (fun f : SuTwo →L[ℝ] SuTwo => f z) hL
    simpa using h
  have hinj : Function.Injective (gOp T) := by
    intro x y hxy
    have hx := hLapp x
    rw [hxy, hLapp y] at hx
    exact hx.symm
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (gOp T).toLinearMap)).mp hinj⟩

theorem gInvOp_neg_ad_mul_expOp_ad_eq_gInvOp_ad
    {g : SU2} (hne : g ≠ su2NegOne) :
    gInvOp (-(adOp (principalSuTwoLog g))) * expOp (adOp (principalSuTwoLog g))
      = gInvOp (adOp (principalSuTwoLog g)) := by
  set T := adOp (principalSuTwoLog g)
  have hneg := AdalySI1.L4Audit.gOp_principalLog_isUnit hne
  have hpos := gOp_ad_principalLog_isUnit hne
  rw [gInvOp, gInvOp]
  apply (Ring.inverse_mul_eq_iff_eq_mul (gOp (-T)) (expOp T)
      (Ring.inverse (gOp T)) hneg).2
  rw [← expOp_ad_mul_gOp_ad_eq_gOp_neg_ad, mul_assoc,
      Ring.mul_inverse_cancel (gOp T) hpos, mul_one]

#print axioms gInvOp_neg_ad_mul_expOp_ad_eq_gInvOp_ad

end AdalySI1.Adjoint
