/-
Owned SI1 L3-adaptive scratch file (compute/m1_si1_l3_adapt/dexp/). Imports the frozen `AdalyFormal`
package read-only, plus two READ-ONLY hash-verified copies placed in `dexp/deps/`:
`T1MainSegment.lean` (`ecdd95ec…`) for the campaign's own `OneStep124.adOp/gOp/gCoeff` slice, and
`NonzeroExpDeriv.lean` (`e950ff15…`) for the arbitrary-basepoint ambient Fréchet-derivative bridge
`hasDerivAt_su2Exp_coe_add_smul`. Neither file is edited. `AdalyFormal.Balaban.Bch2` is read from
the frozen baseline (`compute/forall_u_rung/deps`), already on the default search path.

TARGET (owed L3 equality, independent of whether `adj/` succeeded):
  (fderiv ℝ NormedSpace.exp (Z:M2)) (v:M2) * NormedSpace.exp (-(Z:M2))
    = ((OneStep124.gOp (-(OneStep124.adOp Z)) v : SuTwo) : M2)      for Z v : SuTwo.

Route: `cone/RODRIGUES.md`'s AdalyFormal.Balaban.Bch2.exp_form + ad-cubic + gOp-series sketch, reproved from scratch
(the slice carries only the raw `adOp/gOp/gCoeff` definitions, not their summability/zero lemmas).
No commutative same-generator Mathlib exponential lemma is used for this equality.
-/
import T1MainSegment
import NonzeroExpDeriv
import GopTransport
import AdalyFormal.Balaban.Bch2
import AdalyFormal.Balaban.RegularityGap

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace AdalySI1.DexpRodrigues

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
open scoped Nat
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2 su2Exp su2Exp_of_mem)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.RegularityGap (real_smul_eq)
open OneStep124 (adOp gOp gCoeff)

/-! ## §0 — membership -/

theorem isSu2_coe (X : SuTwo) : AdalyFormal.Balaban.Bch2.IsSu2 (X : M2) := X.2

/-! ## §1 — `adOp`'s faithfulness, reproved locally (the slice drops the original lemma) -/

theorem adOp_apply_coe (Y X : SuTwo) :
    ((adOp Y X : SuTwo) : M2) = (Y : M2) * (X : M2) - (X : M2) * (Y : M2) := rfl

/-! ## §2 — the `zxz` brick: `Z*X*Z = ν(Z)²•X − ip(Z,X)•Z` on `𝔰𝔲(2)` -/

theorem zxz (Z X : SuTwo) :
    (Z : M2) * (X : M2) * (Z : M2)
      = (AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2) • (X : M2) - (AdalyFormal.Balaban.Bch2.ip (Z : M2) (X : M2)) • (Z : M2) := by
  have hz : AdalyFormal.Balaban.Bch2.IsSu2 (Z : M2) := isSu2_coe Z
  have hx : AdalyFormal.Balaban.Bch2.IsSu2 (X : M2) := isSu2_coe X
  have hsq : (Z : M2) * (Z : M2) = (-(AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2)) • (1 : M2) := AdalyFormal.Balaban.Bch2.sq_eq_real hz
  have hac : (Z : M2) * (X : M2) + (X : M2) * (Z : M2)
      = (-(AdalyFormal.Balaban.Bch2.ip (Z : M2) (X : M2))) • (1 : M2) := by
    rw [AdalyFormal.Balaban.Bch2.anticomm hz hx, real_smul_eq]
  have hstep : (Z : M2) * (X : M2) * (Z : M2) + (-(AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2)) • (X : M2)
      = (-(AdalyFormal.Balaban.Bch2.ip (Z : M2) (X : M2))) • (Z : M2) := by
    have e : (Z : M2) * ((Z : M2) * (X : M2) + (X : M2) * (Z : M2))
        = (Z : M2) * ((-(AdalyFormal.Balaban.Bch2.ip (Z : M2) (X : M2))) • (1 : M2)) := by rw [hac]
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hsq, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_smul, Matrix.mul_one] at e
    rw [add_comm] at e
    exact e
  have hfinal : (Z : M2) * (X : M2) * (Z : M2)
      = (-(AdalyFormal.Balaban.Bch2.ip (Z : M2) (X : M2))) • (Z : M2) - (-(AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2)) • (X : M2) :=
    eq_sub_of_add_eq hstep
  rw [hfinal]; module

/-! ## §3 — the double commutator, for arbitrary `X : SuTwo` -/

theorem double_comm (Z X : SuTwo) :
    ((adOp Z (adOp Z X) : SuTwo) : M2)
      = (-4 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2) • (X : M2) + (2 * AdalyFormal.Balaban.Bch2.ip (Z : M2) (X : M2)) • (Z : M2) := by
  have hsq : (Z : M2) * (Z : M2) = (-(AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2)) • (1 : M2) :=
    AdalyFormal.Balaban.Bch2.sq_eq_real (isSu2_coe Z)
  have hzz_x : (Z : M2) * (Z : M2) * (X : M2) = (-(AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2)) • (X : M2) := by
    rw [hsq, Matrix.smul_mul, Matrix.one_mul]
  have hx_zz : (X : M2) * (Z : M2) * (Z : M2) = (-(AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2)) • (X : M2) := by
    rw [Matrix.mul_assoc, hsq, Matrix.mul_smul, Matrix.mul_one]
  have hzxz := zxz Z X
  rw [adOp_apply_coe, adOp_apply_coe]
  simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc]
  rw [hzz_x, hx_zz, hzxz]
  module

/-! ## §4 — the cubic, in the "one more `adOp`" shifted form: `w_{n+3} = c•w_{n+1}` -/

theorem adOp_cube_apply (Z X : SuTwo) :
    ((adOp Z (adOp Z (adOp Z X)) : SuTwo) : M2)
      = (-4 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2) • ((adOp Z X : SuTwo) : M2) := by
  rw [adOp_apply_coe Z (adOp Z (adOp Z X)), double_comm Z X, adOp_apply_coe Z X]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
    Matrix.sub_mul]
  module

/-! ## §5 — the recursive iterate sequence `w n := (adOp Z)^n v` -/

/-- The plain (non-`pow`) iterate sequence: `w 0 = v`, `w (n+1) = adOp Z (w n)`. -/
def w (Z v : SuTwo) : ℕ → SuTwo
  | 0 => v
  | n + 1 => adOp Z (w Z v n)

theorem w_succ (Z v : SuTwo) (n : ℕ) : w Z v (n + 1) = adOp Z (w Z v n) := rfl

theorem w_eq_pow_apply (Z v : SuTwo) (n : ℕ) : w Z v n = ((adOp Z) ^ n) v := by
  induction n with
  | zero => simp [w]
  | succ k ih => rw [w_succ, ih, pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]

theorem w_rec3 (Z v : SuTwo) (n : ℕ) :
    ((w Z v (n + 3) : SuTwo) : M2) = (-4 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2) • ((w Z v (n + 1) : SuTwo) : M2) := by
  have h := adOp_cube_apply Z (w Z v n)
  simpa [w_succ] using h

theorem w_rec3' (Z v : SuTwo) (n : ℕ) :
    w Z v (n + 3) = (-4 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2) • w Z v (n + 1) := by
  apply Subtype.ext
  rw [w_rec3]
  exact (Submodule.coe_smul _ _).symm

theorem w_odd_even (Z v : SuTwo) (k : ℕ) :
    w Z v (2 * k + 1) = (-4 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2) ^ k • w Z v 1
      ∧ w Z v (2 * k + 2) = (-4 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2) ^ k • w Z v 2 := by
  induction k with
  | zero => constructor <;> simp
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [show 2 * (n + 1) + 1 = 2 * n + 3 from by ring, w_rec3' Z v (2 * n), ih1, smul_smul,
        ← pow_succ']
    · rw [show 2 * (n + 1) + 2 = 2 * n + 1 + 3 from by ring, w_rec3' Z v (2 * n + 1),
        show 2 * n + 1 + 1 = 2 * n + 2 from by ring, ih2, smul_smul, ← pow_succ']

/-! ## §6 — the operator series: sign cancellation, summability, closed value -/

noncomputable def hCoeff (n : ℕ) : ℝ := ((Nat.factorial (n + 1) : ℝ))⁻¹

-- `smul_pow` on the raw endomorphism ring `SuTwo →L[ℝ] SuTwo` needs `IsScalarTower`/
-- `SMulCommClass` instances that fail to synthesize on this type (the same family of diamond as
-- `norm_pow_le'`); proved by hand instead, via `ContinuousLinearMap.ext` + induction at the level
-- of concrete applications (where only `SuTwo`'s own, clean scalar action is needed).
theorem neg_pow_smul_hand (T : SuTwo →L[ℝ] SuTwo) (n : ℕ) :
    (-T) ^ n = ((-1 : ℝ) ^ n) • T ^ n := by
  suffices h : ∀ x, ((-T) ^ n) x = (((-1 : ℝ) ^ n) • T ^ n) x by
    exact ContinuousLinearMap.ext h
  induction n with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    simp only [pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.smul_apply, ih, map_neg, smul_neg, smul_smul, neg_smul]
    module

theorem gCoeff_neg_pow_smul (T : SuTwo →L[ℝ] SuTwo) (n : ℕ) :
    gCoeff n • (-T) ^ n = hCoeff n • T ^ n := by
  have h1 : (-T) ^ n = ((-1 : ℝ) ^ n) • T ^ n := neg_pow_smul_hand T n
  have e1 : gCoeff n = (-1 : ℝ) ^ n / (Nat.factorial (n + 1) : ℝ) := rfl
  have e2 : hCoeff n = ((Nat.factorial (n + 1) : ℝ))⁻¹ := rfl
  have h2 : gCoeff n * (-1 : ℝ) ^ n = hCoeff n := by
    rw [e1, e2, div_mul_eq_mul_div, ← mul_pow]
    norm_num
  rw [h1, smul_smul, h2]

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

/-- The real coefficient series matching `cos`'s doubled-argument shift. -/
theorem hasSum_Q1 (r0 : ℝ) (hr0 : 0 < r0) :
    HasSum (fun k : ℕ => hCoeff (2 * k + 1) * (-4 * r0 ^ 2) ^ k)
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
  have hne : (-4 * r0 ^ 2 : ℝ) ≠ 0 := by nlinarith [sq_nonneg r0, hr0, sq_pos_of_pos hr0]
  have hshift_sum : Summable (fun k : ℕ => (-4 * r0 ^ 2) ^ (k + 1) / (2 * (k + 1))!) :=
    hs.comp_injective (add_left_injective 1)
  have hQ1sum : Summable (fun k : ℕ => (-4 * r0 ^ 2) ^ k / (2 * k + 2)!) :=
    (hshift_sum.mul_right ((-4 * r0 ^ 2)⁻¹)).congr (fun k => by
      rw [pow_succ, show 2 * (k + 1) = 2 * k + 2 from by ring]
      field_simp)
  have heqf : (fun k : ℕ => hCoeff (2 * k + 1) * (-4 * r0 ^ 2) ^ k)
      = (fun k : ℕ => (-4 * r0 ^ 2) ^ k / (2 * k + 2)!) := by
    funext k; rw [hCoeff]; ring
  have h4mul : (4 * r0 ^ 2) * (∑' k : ℕ, (-4 * r0 ^ 2) ^ k / (2 * k + 2)!)
      = ∑' k : ℕ, -((-4 * r0 ^ 2) ^ (k + 1) / (2 * (k + 1))!) := by
    rw [← tsum_mul_left]; exact tsum_congr hterm
  have h4mul' : (4 * r0 ^ 2) * (∑' k : ℕ, (-4 * r0 ^ 2) ^ k / (2 * k + 2)!) = 1 - Real.cos (2 * r0) := by
    rw [h4mul, tsum_neg, ← hcos_shift]; ring
  have h4ne : (4 * r0 ^ 2 : ℝ) ≠ 0 := by positivity
  have htsum_val : (∑' k : ℕ, (-4 * r0 ^ 2) ^ k / (2 * k + 2)!) = (1 - Real.cos (2 * r0)) / (4 * r0 ^ 2) := by
    rw [eq_div_iff h4ne, mul_comm]; exact h4mul'
  rw [heqf, ← htsum_val]
  exact hQ1sum.hasSum

/-- The real coefficient series matching `sin`'s doubled-argument shift. -/
theorem hasSum_Q2 (r0 : ℝ) (hr0 : 0 < r0) :
    HasSum (fun k : ℕ => hCoeff (2 * k + 2) * (-4 * r0 ^ 2) ^ k)
      ((2 * r0 - Real.sin (2 * r0)) / (8 * r0 ^ 3)) := by
  have hexp : ∀ n : ℕ, (-1 : ℝ) ^ n * (2 * r0) ^ (2 * n) = (-4 * r0 ^ 2) ^ n := by
    intro n
    rw [pow_mul, show (2 * r0) ^ 2 = 4 * r0 ^ 2 from by ring, ← mul_pow]
    congr 1; ring
  have hr0ne : (2 * r0 : ℝ) ≠ 0 := by positivity
  have hg : HasSum (fun n : ℕ => (-4 * r0 ^ 2) ^ n / (2 * n + 1)!) (Real.sin (2 * r0) / (2 * r0)) := by
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
    rwa [hfe] at h2
  have hs : Summable (fun n : ℕ => (-4 * r0 ^ 2) ^ n / (2 * n + 1)!) := hg.summable
  have hsin_shift : Real.sin (2 * r0) / (2 * r0) - 1
      = ∑' n : ℕ, (-4 * r0 ^ 2) ^ (n + 1) / (2 * (n + 1) + 1)! := by
    have hz := hs.tsum_eq_zero_add
    rw [hg.tsum_eq] at hz
    simp only [pow_zero, mul_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hz
    linarith [hz]
  have hterm : ∀ k : ℕ, (-4 * r0 ^ 2) * (hCoeff (2 * k + 2) * (-4 * r0 ^ 2) ^ k)
      = (-4 * r0 ^ 2) ^ (k + 1) / (2 * (k + 1) + 1)! := by
    intro k
    rw [hCoeff, pow_succ, show 2 * (k + 1) + 1 = 2 * k + 3 from by ring]
    field_simp; ring
  have hne : (-4 * r0 ^ 2 : ℝ) ≠ 0 := by nlinarith [sq_nonneg r0, hr0, sq_pos_of_pos hr0]
  have hshift_sum : Summable (fun k : ℕ => (-4 * r0 ^ 2) ^ (k + 1) / (2 * (k + 1) + 1)!) :=
    hs.comp_injective (add_left_injective 1)
  have hQ2sum : Summable (fun k : ℕ => hCoeff (2 * k + 2) * (-4 * r0 ^ 2) ^ k) :=
    (hshift_sum.mul_right ((-4 * r0 ^ 2)⁻¹)).congr (fun k => by
      rw [← hterm k]
      field_simp)
  have h4mul : (-4 * r0 ^ 2) * (∑' k : ℕ, hCoeff (2 * k + 2) * (-4 * r0 ^ 2) ^ k)
      = ∑' k : ℕ, (-4 * r0 ^ 2) ^ (k + 1) / (2 * (k + 1) + 1)! := by
    rw [← tsum_mul_left]; exact tsum_congr hterm
  have h4mul' : (-4 * r0 ^ 2) * (∑' k : ℕ, hCoeff (2 * k + 2) * (-4 * r0 ^ 2) ^ k)
      = Real.sin (2 * r0) / (2 * r0) - 1 := by rw [h4mul, hsin_shift]
  have htsum_val : (∑' k : ℕ, hCoeff (2 * k + 2) * (-4 * r0 ^ 2) ^ k)
      = (2 * r0 - Real.sin (2 * r0)) / (8 * r0 ^ 3) := by
    rw [eq_div_iff (by positivity : (8 * r0 ^ 3 : ℝ) ≠ 0)]
    have := h4mul'
    field_simp at this ⊢
    nlinarith [this]
  rw [← htsum_val]
  exact hQ2sum.hasSum

/-! ## §6b — assembling the closed value of `gOp (-(adOp Z)) v` -/

theorem gOp_neg_adOp_apply (Z v : SuTwo) (hZ : Z ≠ 0) :
    (gOp (-(adOp Z)) v : SuTwo)
      = v + ((1 - Real.cos (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))) / (4 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2)) • w Z v 1
          + ((2 * AdalyFormal.Balaban.Bch2.nu (Z : M2) - Real.sin (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))) / (8 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 3))
              • w Z v 2 := by
  have hr0 : 0 < AdalyFormal.Balaban.Bch2.nu (Z : M2) := by
    rcases lt_or_eq_of_le (AdalyFormal.Balaban.Bch2.nu_nonneg (Z : M2)) with h | h
    · exact h
    · exact absurd (Subtype.ext ((AdalyFormal.Balaban.Bch2.nu_eq_zero_iff (Z : M2)).mp h.symm)) hZ
  have step1 : (gOp (-(adOp Z)) v : SuTwo) = (∑' n : ℕ, hCoeff n • (adOp Z) ^ n) v := by
    show (∑' n : ℕ, gCoeff n • (-(adOp Z)) ^ n) v = _
    congr 1
    exact tsum_congr (fun n => gCoeff_neg_pow_smul (adOp Z) n)
  have step2 : (∑' n : ℕ, hCoeff n • (adOp Z) ^ n) v = ∑' n : ℕ, hCoeff n • (((adOp Z) ^ n) v) :=
    (ContinuousLinearMap.apply ℝ SuTwo v).map_tsum (hSummable (adOp Z))
  have step3 : (∑' n : ℕ, hCoeff n • (((adOp Z) ^ n) v)) = ∑' n : ℕ, hCoeff n • w Z v n := by
    exact tsum_congr (fun n => by rw [w_eq_pow_apply])
  have hodd : HasSum (fun k : ℕ => hCoeff (2 * k + 1) • w Z v (2 * k + 1))
      (((1 - Real.cos (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))) / (4 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2)) • w Z v 1) := by
    have h := (hasSum_Q1 (AdalyFormal.Balaban.Bch2.nu (Z : M2)) hr0).smul_const (w Z v 1)
    convert h using 1
    funext k
    rw [(w_odd_even Z v k).1, smul_smul]
  have heven : HasSum (fun k : ℕ => hCoeff (2 * k + 2) • w Z v (2 * k + 2))
      (((2 * AdalyFormal.Balaban.Bch2.nu (Z : M2) - Real.sin (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))) / (8 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 3))
        • w Z v 2) := by
    have h := (hasSum_Q2 (AdalyFormal.Balaban.Bch2.nu (Z : M2)) hr0).smul_const (w Z v 2)
    convert h using 1
    funext k
    rw [(w_odd_even Z v k).2, smul_smul]
  have heo : HasSum (fun n : ℕ => hCoeff (n + 1) • w Z v (n + 1))
      (((1 - Real.cos (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))) / (4 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2)) • w Z v 1
        + ((2 * AdalyFormal.Balaban.Bch2.nu (Z : M2) - Real.sin (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))) / (8 * AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 3))
            • w Z v 2) :=
    HasSum.even_add_odd hodd heven
  -- prepend the `n = 0` term with `f` supplied by name (`HasSum.zero_add` on an inlined lambda
  -- fails higher-order unification; `hasSum_nat_add_iff (f := _)` does not)
  have hza := (hasSum_nat_add_iff (f := fun m : ℕ => hCoeff m • w Z v m) 1).mp heo
  simp only [Finset.sum_range_one] at hza
  have hf0 : hCoeff 0 • w Z v 0 = v := by show hCoeff 0 • v = v; simp [hCoeff, w]
  rw [hf0] at hza
  rw [step1, step2, step3, hza.tsum_eq]
  abel

/-! ## §7 — the ambient bridge, closed-form differentiation, and right-trivialization -/

theorem ambient_bridge (Z v : SuTwo) :
    HasDerivAt (fun t : ℝ => ((su2Exp ((Z : M2) + t • (v : M2)) : SU2) : M2))
      ((fderiv ℝ (NormedSpace.exp : M2 → M2) (Z : M2)) (v : M2)) 0 :=
  AdalySI1.NonzeroExpDeriv.hasDerivAt_su2Exp_coe_add_smul
    (isSu2_coe Z).1 (isSu2_coe v).1 (isSu2_coe Z).2 (isSu2_coe v).2

theorem curve_eq_closed (Z v : SuTwo) (t : ℝ) :
    ((su2Exp ((Z : M2) + t • (v : M2)) : SU2) : M2)
      = Real.cos (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2))) • (1 : M2)
          + (Real.sin (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2))) * (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2)))⁻¹)
              • ((Z : M2) + t • (v : M2)) :=
  AdalyFormal.Balaban.Bch2.exp_form ((isSu2_coe Z).add ((isSu2_coe v).smul t))

theorem rho_sq_eq (Z v : SuTwo) (t : ℝ) :
    AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2)) ^ 2
      = AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2 + t * (AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2))
          + t ^ 2 * (AdalyFormal.Balaban.RMapLipschitz.frobSq (v : M2) / 2) := by
  have h1 : AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2 = AdalyFormal.Balaban.RMapLipschitz.frobSq (Z : M2) / 2 :=
    AdalyFormal.Balaban.Bch2.nu_sq _
  rw [AdalyFormal.Balaban.Bch2.nu_sq, AdalyFormal.Balaban.Bch2.frobSq_add, AdalyFormal.Balaban.Bch2.frobSq_smul, AdalyFormal.Balaban.Bch2.ip_smul_right, h1]; ring

theorem hasDerivAt_rho (Z v : SuTwo) (hZ : Z ≠ 0) :
    HasDerivAt (fun t : ℝ => AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2)))
      (AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2) / (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))) 0 := by
  have hr0 : 0 < AdalyFormal.Balaban.Bch2.nu (Z : M2) := by
    rcases lt_or_eq_of_le (AdalyFormal.Balaban.Bch2.nu_nonneg (Z : M2)) with h | h
    · exact h
    · exact absurd (Subtype.ext ((AdalyFormal.Balaban.Bch2.nu_eq_zero_iff (Z : M2)).mp h.symm)) hZ
  set p := AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2)
  set fw := AdalyFormal.Balaban.RMapLipschitz.frobSq (v : M2)
  have hq : HasDerivAt (fun t : ℝ => AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2 + t * p + t ^ 2 * (fw / 2)) p 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * p) p 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const p
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * (fw / 2)) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).mul_const (fw / 2)
    have h0 : HasDerivAt (fun _ : ℝ => AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2) (0 : ℝ) 0 :=
      hasDerivAt_const 0 (AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2)
    have h01 : HasDerivAt (fun t : ℝ => AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2 + t * p) (0 + p) 0 :=
      h0.add h1
    have h012 : HasDerivAt
        (fun t : ℝ => AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2 + t * p + t ^ 2 * (fw / 2))
        (0 + p + 0) 0 :=
      h01.add h2
    simpa using h012
  have hq0ne : AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2 + (0 : ℝ) * p + (0 : ℝ) ^ 2 * (fw / 2) ≠ 0 := by
    simpa using hr0.ne'
  have hsqrt := hq.sqrt hq0ne
  have hval : Real.sqrt (AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2 + (0 : ℝ) * p + (0 : ℝ) ^ 2 * (fw / 2))
      = AdalyFormal.Balaban.Bch2.nu (Z : M2) := by simp; exact Real.sqrt_sq (AdalyFormal.Balaban.Bch2.nu_nonneg _)
  rw [hval] at hsqrt
  have hfun : (fun t : ℝ => AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2)))
      = (fun t : ℝ => Real.sqrt (AdalyFormal.Balaban.Bch2.nu (Z : M2) ^ 2 + t * p + t ^ 2 * (fw / 2))) := by
    funext t; rw [← rho_sq_eq Z v t, Real.sqrt_sq (AdalyFormal.Balaban.Bch2.nu_nonneg _)]
  rw [hfun]
  simpa [div_eq_mul_inv] using hsqrt

theorem hasDerivAt_bracket (Z v : SuTwo) (hZ : Z ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.cos (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2))) • (1 : M2)
        + (Real.sin (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2))) * (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2)))⁻¹)
            • ((Z : M2) + t • (v : M2)))
      ((-(Real.sin (AdalyFormal.Balaban.Bch2.nu (Z : M2))) * (AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2) / (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))))
          • (1 : M2)
        + ((Real.cos (AdalyFormal.Balaban.Bch2.nu (Z : M2)) * (AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2) / (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2)))
                * (AdalyFormal.Balaban.Bch2.nu (Z : M2))⁻¹
              + Real.sin (AdalyFormal.Balaban.Bch2.nu (Z : M2))
                  * (-(AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2) / (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))) / (AdalyFormal.Balaban.Bch2.nu (Z : M2)) ^ 2))
              • (Z : M2)
            + (Real.sin (AdalyFormal.Balaban.Bch2.nu (Z : M2)) * (AdalyFormal.Balaban.Bch2.nu (Z : M2))⁻¹) • (v : M2))) 0 := by
  -- Rewritten without `simpa`: every `simpa using` site failed only because `simpa` checks the
  -- produced-vs-expected `HasDerivAt` instances at *reducible* transparency; the ℝ self-module
  -- and `M2` restrict-scalars paths are defeq at default transparency, which is what term-mode
  -- ascriptions and `HasDerivAt.congr_deriv` use (same discipline as `deps/NonzeroExpDeriv`:
  -- un-ascribed combinators for the `M2` affine curve, shape fixed only at the end).
  have hrho := hasDerivAt_rho Z v hZ
  have hr0 : 0 < AdalyFormal.Balaban.Bch2.nu (Z : M2) := by
    rcases lt_or_eq_of_le (AdalyFormal.Balaban.Bch2.nu_nonneg (Z : M2)) with h | h
    · exact h
    · exact absurd (Subtype.ext ((AdalyFormal.Balaban.Bch2.nu_eq_zero_iff (Z : M2)).mp h.symm)) hZ
  have hpt : AdalyFormal.Balaban.Bch2.nu ((Z : M2) + (0 : ℝ) • (v : M2)) = AdalyFormal.Balaban.Bch2.nu (Z : M2) := by
    simp
  have h0 : (Z : M2) + (0 : ℝ) • (v : M2) = (Z : M2) := by simp
  have hne0 : AdalyFormal.Balaban.Bch2.nu ((Z : M2) + (0 : ℝ) • (v : M2)) ≠ 0 := by
    rw [hpt]; exact hr0.ne'
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2))))
      (-(Real.sin (AdalyFormal.Balaban.Bch2.nu (Z : M2))) * (AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2) / (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2)))) 0 :=
    hrho.cos.congr_deriv (by rw [hpt])
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2))))
      (Real.cos (AdalyFormal.Balaban.Bch2.nu (Z : M2)) * (AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2) / (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2)))) 0 :=
    hrho.sin.congr_deriv (by rw [hpt])
  have hinv : HasDerivAt (fun t : ℝ => (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2)))⁻¹)
      (-(AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2) / (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))) / (AdalyFormal.Balaban.Bch2.nu (Z : M2)) ^ 2) 0 :=
    (hrho.inv hne0).congr_deriv (by rw [hpt])
  have hc : HasDerivAt
      (fun t : ℝ => Real.sin (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2))) * (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2)))⁻¹)
      (Real.cos (AdalyFormal.Balaban.Bch2.nu (Z : M2)) * (AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2) / (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2)))
          * (AdalyFormal.Balaban.Bch2.nu (Z : M2))⁻¹
        + Real.sin (AdalyFormal.Balaban.Bch2.nu (Z : M2))
            * (-(AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2) / (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))) / (AdalyFormal.Balaban.Bch2.nu (Z : M2)) ^ 2)) 0 :=
    (hsin.mul hinv).congr_deriv (by rw [hpt])
  have hg0 := (hasDerivAt_id (0 : ℝ)).smul_const (v : M2)
  simp only [one_smul] at hg0
  have hg1 := hg0.const_add (Z : M2)
  have hg : HasDerivAt (fun t : ℝ => (Z : M2) + t • (v : M2)) (v : M2) 0 := hg1
  have hterm2 : HasDerivAt
      (fun t : ℝ => (Real.sin (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2))) * (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2)))⁻¹)
          • ((Z : M2) + t • (v : M2)))
      ((Real.cos (AdalyFormal.Balaban.Bch2.nu (Z : M2)) * (AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2) / (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2)))
              * (AdalyFormal.Balaban.Bch2.nu (Z : M2))⁻¹
            + Real.sin (AdalyFormal.Balaban.Bch2.nu (Z : M2))
                * (-(AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2) / (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))) / (AdalyFormal.Balaban.Bch2.nu (Z : M2)) ^ 2))
            • (Z : M2)
          + (Real.sin (AdalyFormal.Balaban.Bch2.nu (Z : M2)) * (AdalyFormal.Balaban.Bch2.nu (Z : M2))⁻¹) • (v : M2)) 0 :=
    (hc.smul hg).congr_deriv (by rw [hpt, h0]; exact add_comm _ _)
  have hterm1 : HasDerivAt (fun t : ℝ => Real.cos (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2))) • (1 : M2))
      ((-(Real.sin (AdalyFormal.Balaban.Bch2.nu (Z : M2))) * (AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2) / (2 * AdalyFormal.Balaban.Bch2.nu (Z : M2))))
        • (1 : M2)) 0 :=
    hcos.smul_const (1 : M2)
  exact hterm1.add hterm2

/-! ## §8 — final assembly -/

theorem dexp_eq_gOp_pos (Z v : SuTwo) (hZ : Z ≠ 0) :
    (fderiv ℝ (NormedSpace.exp : M2 → M2) (Z : M2)) (v : M2) * NormedSpace.exp (-(Z : M2))
      = ((gOp (-(adOp Z)) v : SuTwo) : M2) := by
  have hF1 : HasDerivAt
      (fun t : ℝ => ((su2Exp ((Z : M2) + t • (v : M2)) : SU2) : M2) * NormedSpace.exp (-(Z : M2)))
      ((fderiv ℝ (NormedSpace.exp : M2 → M2) (Z : M2)) (v : M2) * NormedSpace.exp (-(Z : M2))) 0 :=
    (ambient_bridge Z v).mul_const _
  have hcong : (fun t : ℝ => ((su2Exp ((Z : M2) + t • (v : M2)) : SU2) : M2) * NormedSpace.exp (-(Z : M2)))
      = (fun t : ℝ => (Real.cos (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2))) • (1 : M2)
            + (Real.sin (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2))) * (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2)))⁻¹)
                • ((Z : M2) + t • (v : M2))) * NormedSpace.exp (-(Z : M2))) :=
    funext (fun t => by rw [curve_eq_closed])
  have hF1' : HasDerivAt (fun t : ℝ => (Real.cos (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2))) • (1 : M2)
        + (Real.sin (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2))) * (AdalyFormal.Balaban.Bch2.nu ((Z : M2) + t • (v : M2)))⁻¹)
            • ((Z : M2) + t • (v : M2))) * NormedSpace.exp (-(Z : M2)))
      ((fderiv ℝ (NormedSpace.exp : M2 → M2) (Z : M2)) (v : M2) * NormedSpace.exp (-(Z : M2))) 0 := by
    have h1 : HasDerivAt
        (fun t : ℝ => ((su2Exp ((Z : M2) + t • (v : M2)) : SU2) : M2) * NormedSpace.exp (-(Z : M2)))
        ((fderiv ℝ (NormedSpace.exp : M2 → M2) (Z : M2)) (v : M2) * NormedSpace.exp (-(Z : M2))) 0 :=
      (ambient_bridge Z v).mul_const _
    rwa [hcong] at h1
  have hF2' := (hasDerivAt_bracket Z v hZ).mul_const (NormedSpace.exp (-(Z : M2)))
  have hEq := hF1'.unique hF2'
  rw [hEq]
  set r0 := AdalyFormal.Balaban.Bch2.nu (Z : M2) with hr0def
  set p := AdalyFormal.Balaban.Bch2.ip (Z : M2) (v : M2) with hpdef
  have hr0 : 0 < r0 := by
    rcases lt_or_eq_of_le (AdalyFormal.Balaban.Bch2.nu_nonneg (Z : M2)) with h | h
    · exact h
    · exact absurd (Subtype.ext ((AdalyFormal.Balaban.Bch2.nu_eq_zero_iff (Z : M2)).mp h.symm)) hZ
  have hexpz : NormedSpace.exp (-(Z : M2)) = Real.cos r0 • (1 : M2) - (Real.sin r0 / r0) • (Z : M2) := by
    have h := AdalyFormal.Balaban.Bch2.exp_form ((isSu2_coe Z).neg)
    rw [AdalyFormal.Balaban.Bch2.nu_neg] at h
    have hco : ((su2Exp (-(Z : M2)) : SU2) : M2) = NormedSpace.exp (-(Z : M2)) :=
      su2Exp_of_mem (AdalyFormal.Balaban.ClassPropagationUbar.exp_mem_special
        (isSu2_coe Z).neg.1 (isSu2_coe Z).neg.2)
    rw [hco] at h
    rw [h]; module
  rw [hexpz]
  have hzz : (Z : M2) * (Z : M2) = (-(r0 ^ 2)) • (1 : M2) := AdalyFormal.Balaban.Bch2.sq_eq_real (isSu2_coe Z)
  have hvz : (v : M2) * (Z : M2)
      = (-(p / 2)) • (1 : M2) - (1 / 2 : ℝ) • ((Z : M2) * (v : M2) - (v : M2) * (Z : M2)) := by
    have hac : (Z : M2) * (v : M2) + (v : M2) * (Z : M2) = (-p) • (1 : M2) := by
      rw [AdalyFormal.Balaban.Bch2.anticomm (isSu2_coe Z) (isSu2_coe v), real_smul_eq]
    have hZv : (Z : M2) * (v : M2) = (-p) • (1 : M2) - (v : M2) * (Z : M2) := eq_sub_of_add_eq hac
    rw [hZv]
    module
  have hexpand : ((-(Real.sin r0) * (p / (2 * r0))) • (1 : M2)
        + ((Real.cos r0 * (p / (2 * r0)) * r0⁻¹ + Real.sin r0 * (-(p / (2 * r0)) / r0 ^ 2)) • (Z : M2)
            + (Real.sin r0 * r0⁻¹) • (v : M2)))
        * (Real.cos r0 • (1 : M2) - (Real.sin r0 / r0) • (Z : M2))
      = (((Real.sin r0) ^ 2 + (Real.cos r0) ^ 2 - 1) * (p / (2 * r0 ^ 2))) • (Z : M2)
        + (p * (r0 - Real.sin r0 * Real.cos r0) / (2 * r0 ^ 3)) • (Z : M2)
        + (Real.sin r0 * Real.cos r0 / r0) • (v : M2)
        + ((Real.sin r0) ^ 2 / (2 * r0 ^ 2)) • ((Z : M2) * (v : M2) - (v : M2) * (Z : M2)) := by
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    rw [hzz]
    -- rewrite `v * Z` on the LEFT only: the right-hand side keeps `Z * v - v * Z` as its own atoms
    -- (the old `rw [hzz, hvz]` also rewrote the right-hand `v * Z`, producing a false
    -- coefficient goal `0 = sin² p /(4 r0²)` on the `1` atom)
    conv_lhs => rw [hvz]
    simp only [smul_smul, smul_sub, smul_add, smul_neg]
    have hr0ne : r0 ≠ 0 := hr0.ne'
    match_scalars <;> (try field_simp) <;> ring1
  have hpyth : (Real.sin r0) ^ 2 + (Real.cos r0) ^ 2 - 1 = 0 := by
    have := Real.sin_sq_add_cos_sq r0; linarith
  rw [hpyth, zero_mul, zero_smul, zero_add] at hexpand
  rw [hexpand]
  have hZne : Z ≠ 0 := hZ
  have hgop := gOp_neg_adOp_apply Z v hZne
  rw [← hr0def] at hgop
  have hw1 : ((w Z v 1 : SuTwo) : M2) = (Z : M2) * (v : M2) - (v : M2) * (Z : M2) := by
    show ((adOp Z v : SuTwo) : M2) = _
    exact adOp_apply_coe Z v
  have hw2 : ((w Z v 2 : SuTwo) : M2)
      = (-4 * r0 ^ 2) • (v : M2) + (2 * p) • (Z : M2) := by
    show ((adOp Z (adOp Z v) : SuTwo) : M2) = _
    rw [hr0def, hpdef]
    exact double_comm Z v
  have hQ1a : (1 - Real.cos (2 * r0)) / (4 * r0 ^ 2) = (Real.sin r0) ^ 2 / (2 * r0 ^ 2) := by
    have h : Real.cos (2 * r0) = 1 - 2 * (Real.sin r0) ^ 2 := by
      rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq r0]
    rw [h]; ring
  have hQ2a : (2 * r0 - Real.sin (2 * r0)) / (8 * r0 ^ 3)
      = (r0 - Real.sin r0 * Real.cos r0) / (4 * r0 ^ 3) := by
    rw [Real.sin_two_mul]; ring
  have hcoe : ((gOp (-(adOp Z)) v : SuTwo) : M2)
      = (v : M2)
        + ((1 - Real.cos (2 * r0)) / (4 * r0 ^ 2)) • ((Z : M2) * (v : M2) - (v : M2) * (Z : M2))
        + ((2 * r0 - Real.sin (2 * r0)) / (8 * r0 ^ 3))
            • ((-4 * r0 ^ 2) • (v : M2) + (2 * p) • (Z : M2)) := by
    rw [hgop]
    simp [hw1, hw2]
  rw [hcoe, hQ1a, hQ2a]
  have hr0ne : r0 ≠ 0 := hr0.ne'
  -- coefficientwise, then clear the `r0⁻¹` powers `ring` cannot cancel on its own
  match_scalars <;> (try field_simp) <;> ring1

/-! ## §9 — the `Z = 0` identity branch and final assembly -/

theorem adOp_zero_eq : adOp (0 : SuTwo) = 0 := by
  apply ContinuousLinearMap.ext
  intro X
  apply Subtype.ext
  rw [adOp_apply_coe]
  simp

theorem gOp_zero_eq : gOp (0 : SuTwo →L[ℝ] SuTwo) = 1 := by
  rw [gOp, tsum_eq_single 0]
  · simp [gCoeff]
  · intro n hn
    rw [zero_pow hn]
    -- `smul_zero` cannot see the endomorphism `SMul`; go pointwise
    ext x
    simp

theorem dexp_eq_gOp_zero (v : SuTwo) :
    (fderiv ℝ (NormedSpace.exp : M2 → M2) ((0 : SuTwo) : M2)) (v : M2)
        * NormedSpace.exp (-((0 : SuTwo) : M2))
      = ((gOp (-(adOp (0 : SuTwo))) v : SuTwo) : M2) := by
  have h0 : ((0 : SuTwo) : M2) = (0 : M2) := Submodule.coe_zero
  have hfd : fderiv ℝ (NormedSpace.exp : M2 → M2) (0 : M2) = 1 :=
    (hasFDerivAt_exp_zero (𝕂 := ℝ)).fderiv
  rw [h0, hfd, neg_zero, NormedSpace.exp_zero]
  simp only [ContinuousLinearMap.one_apply, mul_one]
  rw [adOp_zero_eq, neg_zero, gOp_zero_eq]
  rfl

theorem dexp_eq_gOp (Z v : SuTwo) :
    (fderiv ℝ (NormedSpace.exp : M2 → M2) (Z : M2)) (v : M2) * NormedSpace.exp (-(Z : M2))
      = ((gOp (-(adOp Z)) v : SuTwo) : M2) := by
  rcases eq_or_ne Z 0 with hZ | hZ
  · subst hZ; exact dexp_eq_gOp_zero v
  · exact dexp_eq_gOp_pos Z v hZ


/-- The same owed equality with the right-hand side in `M2RouteAudit`'s ambient-series form,
through the paid transport `AdalySI1.GopTransport.gOpM2_apply_coe_eq_gOp`. -/
theorem dexp_eq_gOpM2 (Z v : SuTwo) :
    (fderiv ℝ (NormedSpace.exp : M2 → M2) (Z : M2)) (v : M2) * NormedSpace.exp (-(Z : M2))
      = (AdalySI1.M2RouteAudit.gOpM2 (-AdalySI1.M2RouteAudit.adM2 (Z : M2))) (v : M2) := by
  rw [AdalySI1.GopTransport.gOpM2_apply_coe_eq_gOp Z v]
  exact dexp_eq_gOp Z v

#print axioms dexp_eq_gOp
#print axioms dexp_eq_gOpM2

end AdalySI1.DexpRodrigues
