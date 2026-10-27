import DLR39

/-!
# DL40 -- the scaled inputs of the genuine chain at M0, each bounded by its k-free parameter (DL38)

`m0_hcoerS` (`cS‖f‖² ≤ n²⟪f,Δ'_a f⟫`), `m0_hbox` (top-level box oscillation `≤ 3θ`), `m0_hDD`, `m0_hQQ`, `m0_hQbS`,
`m0_extS` (the right inverse of `√m_k n·Qtop` with energy `≤ bS‖u‖²`), `m0_hC'`, `m0_hK'`, `m0_hdK'`, `m0_hν'`, `m0_hdν'`, `m0_hB'`,
`GinvFull_isUnit`.  All bounds are uniform in `k` and the volume.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.AsmM0 (M0RegimeR rhoM0 Mc KhatM0)
open AdalyFormal.BondComposite (rr TowerClass thetaOf)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
  (R : M0RegimeR ell k Lu U a t e q0)
include R

theorem m0_hcoerS (f : SiteL2 (scaleUp ell k Lu)) :
    cS a (rhoM0 ell k e q0) * ‖f‖ ^ 2 ≤ ((ell : ℝ) ^ k) ^ 2 * ⟪f, DelpA (GF ell k Lu) U a f⟫ := by
  have h := m0_site ell k Lu U a t e q0 R f
  have hM : 0 < Mc a := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  unfold cS
  rw [div_mul_eq_mul_div, div_le_iff₀ hM]
  linarith

theorem m0_hbox (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hφ : WtLip (θ / (ell : ℝ) ^ k) φ) :
    ∀ y ∈ (GF ell k Lu).Lam (GF ell k Lu).k, ∀ x ∈ boxF y (ell ^ k), |φ y - φ x| ≤ 3 * θ := by
  intro y _ x hx
  have hn1 := m0_n_ge_one ell k Lu U a t e q0 R
  have hr := Reach_lip _ φ hφ (box_reach y x (ell ^ k) hx)
  rw [abs_sub_comm]
  refine hr.trans ?_
  have hn0 : (0 : ℝ) < (ell : ℝ) ^ k := by linarith
  have e1 : ((3 * (ell ^ k - 1) : ℕ) : ℝ) ≤ 3 * (ell : ℝ) ^ k := by
    have : (3 * (ell ^ k - 1) : ℕ) ≤ 3 * ell ^ k := by omega
    exact_mod_cast this
  calc ((3 * (ell ^ k - 1) : ℕ) : ℝ) * (θ / (ell : ℝ) ^ k) ≤ 3 * (ell : ℝ) ^ k * (θ / (ell : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_right e1 (by positivity)
    _ = 3 * θ := by field_simp

theorem m0_hDD (θ : ℝ) (hθ : 0 ≤ θ) :
    (ell : ℝ) ^ k * (Real.sqrt 3 * (Real.exp (θ / (ell : ℝ) ^ k) - 1)) ≤ δDS θ := by
  have h := n_expm1_le _ θ (m0_n_ge_one ell k Lu U a t e q0 R) hθ
  unfold δDS
  calc (ell : ℝ) ^ k * (Real.sqrt 3 * (Real.exp (θ / (ell : ℝ) ^ k) - 1))
      = Real.sqrt 3 * ((ell : ℝ) ^ k * (Real.exp (θ / (ell : ℝ) ^ k) - 1)) := by ring
    _ ≤ Real.sqrt 3 * (θ * Real.exp θ) := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)

theorem m0_hQQ (θ : ℝ) (hθ : 0 ≤ θ) :
    Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k * (Real.sqrt ((1 / (ell : ℝ) ^ 3) ^ k) * (Real.exp (3 * θ) - 1))
      ≤ δQS a θ := by
  have h := m0_sqm_le ell k Lu U a t e q0 R
  have hpos : 0 ≤ Real.exp (3 * θ) - 1 := by linarith [Real.add_one_le_exp (3 * θ)]
  unfold δQS
  calc _ = (Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k * Real.sqrt ((1 / (ell : ℝ) ^ 3) ^ k)) * (Real.exp (3 * θ) - 1) := by
        ring
    _ ≤ Real.sqrt a * (Real.exp (3 * θ) - 1) := mul_le_mul_of_nonneg_right h hpos

theorem m0_hQbS : ‖(Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k) • Qtop (GF ell k Lu) U‖ ≤ qS a := by
  have hell0 : 0 < ell := by have := R.hell; omega
  have hm := m0_sqm_le ell k Lu U a t e q0 R
  have e1 : (1 / (ell : ℝ) ^ 3) ^ k = 1 / ((ell : ℝ) ^ k) ^ 3 := by
    rw [div_pow, one_pow, ← pow_mul, ← pow_mul, mul_comm]
  rw [e1] at hm
  refine opnorm_le_of _ _ (Real.sqrt_nonneg _) (fun f => ?_)
  rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hq := AdalyFormal.PortSlice.hQq_ported ell k Lu hell0 U f
  calc Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k * ‖Qtop (GF ell k Lu) U f‖
      ≤ Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k * (Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) * ‖f‖) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ = (Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3)) * ‖f‖ := by ring
    _ ≤ qS a * ‖f‖ := mul_le_mul_of_nonneg_right hm (norm_nonneg _)

/-- `B'² = n (√78732 + 27√12 ρ)²/(1−162ρ)²` -/
theorem m0_Bsq :
    ((AdalyFormal.FlatExt.bFE ell k + (Real.sqrt 12 * (rhoM0 ell k e q0 / (ell : ℝ) ^ k)) * AdalyFormal.FlatExt.aFE ell k)
      / (1 - (6 * rhoM0 ell k e q0 * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3)) * AdalyFormal.FlatExt.aFE ell k)) ^ 2
      = (ell : ℝ) ^ k * (Real.sqrt 78732 + 27 * Real.sqrt 12 * rhoM0 ell k e q0) ^ 2
        / (1 - 162 * rhoM0 ell k e q0) ^ 2 := by
  have hell0 : 0 < ell := by have := R.hell; omega
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  have hq := AdalyFormal.AsmM0.aFE_mul_q ell k hell0
  have hden : (6 * rhoM0 ell k e q0 * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3)) * AdalyFormal.FlatExt.aFE ell k
      = 162 * rhoM0 ell k e q0 := by
    calc _ = 6 * rhoM0 ell k e q0 * (AdalyFormal.FlatExt.aFE ell k * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3)) := by ring
      _ = 162 * rhoM0 ell k e q0 := by rw [hq]; ring
  have hsn : Real.sqrt ((ell : ℝ) ^ k) ^ 2 = (ell : ℝ) ^ k := Real.sq_sqrt hn.le
  have hb : AdalyFormal.FlatExt.bFE ell k = Real.sqrt 78732 * Real.sqrt ((ell : ℝ) ^ k) := by
    unfold AdalyFormal.FlatExt.bFE; rw [Real.sqrt_mul (by norm_num)]
  have ha : AdalyFormal.FlatExt.aFE ell k = 27 * (ell : ℝ) ^ k * Real.sqrt ((ell : ℝ) ^ k) := by
    unfold AdalyFormal.FlatExt.aFE
    rw [show 729 * ((ell : ℝ) ^ k) ^ 3 = (27 * (ell : ℝ) ^ k) ^ 2 * (ell : ℝ) ^ k by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hden, hb, ha]
  have e2 : Real.sqrt 78732 * Real.sqrt ((ell : ℝ) ^ k)
      + Real.sqrt 12 * (rhoM0 ell k e q0 / (ell : ℝ) ^ k) * (27 * (ell : ℝ) ^ k * Real.sqrt ((ell : ℝ) ^ k))
      = Real.sqrt ((ell : ℝ) ^ k) * (Real.sqrt 78732 + 27 * Real.sqrt 12 * rhoM0 ell k e q0) := by
    field_simp
  rw [e2, div_pow, mul_pow, hsn]

theorem m0_extS (θ : ℝ) (hc : CondM0 ell a (rhoM0 ell k e q0) θ) (u : coarseC (GF ell k Lu)) :
    ∃ g, ((Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k) • Qtop (GF ell k Lu) U) g = u ∧
      ((ell : ℝ) ^ k) ^ 2 * ⟪g, DelpA (GF ell k Lu) U a g⟫ ≤ bS ell a (rhoM0 ell k e q0) * ‖u‖ ^ 2 := by
  have hell0 : 0 < ell := by have := R.hell; omega
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  have hmpos := m0_mTop_pos ell k Lu U a t e q0 R
  set r := Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k with hr
  have hrpos : 0 < r := by rw [hr]; have := Real.sqrt_pos.mpr hmpos; positivity
  have hρnn := m0_rho_nonneg ell k Lu U a t e q0 R
  obtain ⟨g, hg, hgE⟩ := extM0 ell k Lu hell0 U a hmpos.le (Real.sqrt 12 * (rhoM0 ell k e q0 / (ell : ℝ) ^ k))
    (6 * rhoM0 ell k e q0 * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3)) (by positivity) (by positivity)
    (m0_hεa ell k Lu U a t e q0 R) (m0_hd ell k Lu U a t e q0 R) (m0_hQdrift ell k Lu U a t e q0 R) (r⁻¹ • u)
  refine ⟨g, ?_, ?_⟩
  · rw [ContinuousLinearMap.smul_apply, hg, smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
  · have hw : ‖r⁻¹ • u‖ ^ 2 = ‖u‖ ^ 2 / r ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hrpos]; field_simp
    rw [L_eq_DelpA, m0_Bsq ell k Lu U a t e q0 R, hw] at hgE
    have hr2 : r ^ 2 = mTop ell k a * ((ell : ℝ) ^ k) ^ 2 := by
      rw [hr, mul_pow, Real.sq_sqrt hmpos.le]
    have hmk : ajSeq a ell k * (ell : ℝ) ^ k = mTop ell k a := rfl
    have hage := ajSeq_ge ell R.hell a R.ha k
    have hl : (2 : ℝ) ≤ ell := by exact_mod_cast R.hell
    have h1l : 0 < 1 - 1 / ((ell : ℝ) * ell) := by rw [sub_pos, div_lt_one (by positivity)]; nlinarith
    have h162 : 0 < 1 - 162 * rhoM0 ell k e q0 := by linarith [hc.h162]
    set B2 := (Real.sqrt 78732 + 27 * Real.sqrt 12 * rhoM0 ell k e q0) ^ 2 with hB2
    have hB20 : 0 ≤ B2 := sq_nonneg _
    -- n²⟪g,Δ'g⟫ ≤ n² (n B2/(1−162ρ)² + m) ‖u‖²/r² = (n B2/(1−162ρ)²/m + 1)‖u‖²
    have key : ((ell : ℝ) ^ k) ^ 2 * ⟪g, DelpA (GF ell k Lu) U a g⟫
        ≤ (((ell : ℝ) ^ k * B2 / (1 - 162 * rhoM0 ell k e q0) ^ 2) / mTop ell k a + 1) * ‖u‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hgE (sq_nonneg ((ell : ℝ) ^ k))
      refine this.trans (le_of_eq ?_)
      rw [hr2]
      field_simp
    refine key.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    unfold bS
    rw [← hB2]
    have hmt : a * (1 - 1 / ((ell : ℝ) * ell)) * (ell : ℝ) ^ k ≤ mTop ell k a := by
      rw [← hmk]; exact mul_le_mul_of_nonneg_right hage hn.le
    have hden : 0 < (1 - 162 * rhoM0 ell k e q0) ^ 2 * (a * (1 - 1 / ((ell : ℝ) * ell))) := by
      have := R.ha; positivity
    have : (ell : ℝ) ^ k * B2 / (1 - 162 * rhoM0 ell k e q0) ^ 2 / mTop ell k a
        ≤ B2 / ((1 - 162 * rhoM0 ell k e q0) ^ 2 * (a * (1 - 1 / ((ell : ℝ) * ell)))) := by
      rw [div_div, div_le_div_iff₀ (by positivity) hden]
      have : (ell : ℝ) ^ k * B2 * ((1 - 162 * rhoM0 ell k e q0) ^ 2 * (a * (1 - 1 / ((ell : ℝ) * ell))))
          ≤ B2 * ((1 - 162 * rhoM0 ell k e q0) ^ 2 * mTop ell k a) := by
        have h2 := mul_le_mul_of_nonneg_left hmt (mul_nonneg hB20 (sq_nonneg (1 - 162 * rhoM0 ell k e q0)))
        nlinarith [h2]
      linarith
    linarith

end

#print axioms m0_hcoerS
#print axioms m0_hbox
#print axioms m0_hDD
#print axioms m0_hQQ
#print axioms m0_hQbS
#print axioms m0_Bsq
#print axioms m0_extS

end AdalyFormal.DLayer
