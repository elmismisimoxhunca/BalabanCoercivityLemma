import DLR37

/-!
# DL38 -- the k-FREE scaled constants of the `G⁻¹` chain, the k-free conditions, and the elementary scaling bounds

Explicit functions of `(ℓ, a, ρ, θ)` only (no `k`, no volume, no `U`, no weight):
`cS = (1−216ρ²)/Mc(a)`, `δDS = √3 θe^θ`, `δQS = √a (e^{3θ}−1)`, `qS = √a`,
`bS = (√78732 + 27√12 ρ)²/((1−162ρ)² a (1−ℓ⁻²)) + 1`, `epsXf` (the `X`-commutator formula of DL12 with `m = 1`), `cGS`,
`δCS = 6θe^θ`, `κS = 6ρ/(3π)`, `δKS = κS(e^{2θ}−1)`, `νS = 816 ρ/(3π·4√2)`, `δνS = νS(e^{2θ}−1)`,
`δBS = √a e^{3600ℓρ/r} (e^{5θ}−1) √648` (`r = ℓ^{-1/2}`).
* `CondM0` : the k-free smallness conditions;  **`EGM0`** : the `G⁻¹` Combes–Thomas error constant (DL17 `EG`) evaluated on the
  model structure of DL36 with these parameters — a function of `(ℓ, a, ρ, θ)` alone.
* Elementary bounds used to verify the scaled inputs: `n_expm1_le` (`n(e^{θ/n}−1) ≤ θe^θ`), `box_reach`, `ajSeq_le`, `ajSeq_ge`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.AsmM0 (M0RegimeR rhoM0 Mc)
open AdalyFormal.BondComposite (rr)

/-! ## the k-free parameters -/

noncomputable def cS (a ρ : ℝ) : ℝ := (1 - 216 * ρ ^ 2) / Mc a
noncomputable def δDS (θ : ℝ) : ℝ := Real.sqrt 3 * (θ * Real.exp θ)
noncomputable def δQS (a θ : ℝ) : ℝ := Real.sqrt a * (Real.exp (3 * θ) - 1)
noncomputable def qS (a : ℝ) : ℝ := Real.sqrt a
noncomputable def bS (ell : ℕ) (a ρ : ℝ) : ℝ :=
  (Real.sqrt 78732 + 27 * Real.sqrt 12 * ρ) ^ 2 / ((1 - 162 * ρ) ^ 2 * (a * (1 - 1 / ((ell : ℝ) * ell)))) + 1
/-- the `X`-commutator constant `epsX` of DL12 (with `m = 1`), as an explicit formula -/
noncomputable def epsXf (c δD δQ q : ℝ) : ℝ :=
  (4 / c) * δQ + (4 / c) * δD * (q / Real.sqrt c)
    + (Real.sqrt (48 / c) * δD + (8 / c) * δD ^ 2 + (4 / c) * 1 * (2 * q * δQ + δQ ^ 2)) * (q / c)
noncomputable def cGS (ell : ℕ) (a ρ θ : ℝ) : ℝ :=
  1 / (2 * (qS a * bS ell a ρ) ^ 2) - 3 * epsXf (cS a ρ) (δDS θ) (δQS a θ) (qS a) ^ 2
noncomputable def δCS (θ : ℝ) : ℝ := 6 * (θ * Real.exp θ)
noncomputable def κS (ρ : ℝ) : ℝ := 6 * (ρ / (3 * Real.pi))
noncomputable def δKS (ρ θ : ℝ) : ℝ := κS ρ * (Real.exp (2 * θ) - 1)
noncomputable def νS (ρ : ℝ) : ℝ := 816 * (ρ / (3 * Real.pi) / (4 * Real.sqrt 2))
noncomputable def δνS (ρ θ : ℝ) : ℝ := νS ρ * (Real.exp (2 * θ) - 1)
noncomputable def δBS (ell : ℕ) (a ρ θ : ℝ) : ℝ :=
  Real.sqrt a * Real.exp (3600 * (ell : ℝ) * ρ / rr ell) * (Real.exp (5 * θ) - 1) * Real.sqrt 648

/-- the k-free conditions of the `G⁻¹` Combes–Thomas step -/
structure CondM0 (ell : ℕ) (a ρ θ : ℝ) : Prop where
  hell : 2 ≤ ell
  ha : 0 < a
  hρ0 : 0 ≤ ρ
  h216 : 216 * ρ ^ 2 < 1
  h162 : 162 * ρ < 1
  hθ : 0 ≤ θ
  hS1 : 24 * (δDS θ ^ 2 + 1 * δQS a θ ^ 2) ≤ cS a ρ
  hS2 : 4 * δDS θ ^ 2 ≤ cS a ρ
  hcG : 0 < cGS ell a ρ θ

namespace CondM0
variable {ell : ℕ} {a ρ θ : ℝ} (h : CondM0 ell a ρ θ)
include h

theorem cS_pos : 0 < cS a ρ := by
  unfold cS Mc
  have : 0 < 1 - 216 * ρ ^ 2 := by linarith [h.h216]
  have : 0 < max 6 (16 / (3 * a)) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  positivity

theorem δDS_nonneg : 0 ≤ δDS θ := by unfold δDS; have := h.hθ; positivity
theorem δQS_nonneg : 0 ≤ δQS a θ := by
  unfold δQS
  have : 0 ≤ Real.exp (3 * θ) - 1 := by linarith [Real.add_one_le_exp (3 * θ), h.hθ]
  positivity
theorem qS_nonneg : 0 ≤ qS a := Real.sqrt_nonneg _
theorem bS_pos : 0 < bS ell a ρ := by
  unfold bS
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast h.hell
  have h1 : 0 < 1 - 1 / ((ell : ℝ) * ell) := by
    rw [sub_pos, div_lt_one (by positivity)]; nlinarith
  have h2 : 0 < 1 - 162 * ρ := by linarith [h.h162]
  have := h.ha
  positivity
theorem δCS_nonneg : 0 ≤ δCS θ := by unfold δCS; have := h.hθ; positivity
theorem κS_nonneg : 0 ≤ κS ρ := by unfold κS; have := h.hρ0; have := Real.pi_pos; positivity
theorem δKS_nonneg : 0 ≤ δKS ρ θ := by
  unfold δKS
  have : 0 ≤ Real.exp (2 * θ) - 1 := by linarith [Real.add_one_le_exp (2 * θ), h.hθ]
  have := h.κS_nonneg
  positivity
theorem νS_nonneg : 0 ≤ νS ρ := by unfold νS; have := h.hρ0; have := Real.pi_pos; positivity
theorem δνS_nonneg : 0 ≤ δνS ρ θ := by
  unfold δνS
  have : 0 ≤ Real.exp (2 * θ) - 1 := by linarith [Real.add_one_le_exp (2 * θ), h.hθ]
  have := h.νS_nonneg
  positivity
theorem δBS_nonneg : 0 ≤ δBS ell a ρ θ := by
  unfold δBS
  have : 0 ≤ Real.exp (5 * θ) - 1 := by linarith [Real.add_one_le_exp (5 * θ), h.hθ]
  positivity

/-- the model site of the k-free parameters -/
noncomputable def site : SiteHyp Z0 Z0 Z0 :=
  modelSite (cS a ρ) (δDS θ) (δQS a θ) h.cS_pos h.δDS_nonneg h.δQS_nonneg h.hS1 h.hS2

theorem site_epsX : h.site.epsX (qS a) = epsXf (cS a ρ) (δDS θ) (δQS a θ) (qS a) := rfl

/-- the model `G⁻¹` structure of the k-free parameters -/
noncomputable def ginv : GinvHyp Z0 Z0 Z0 Z0 Z0 :=
  modelGinv (cS a ρ) (δDS θ) (δQS a θ) h.cS_pos h.δDS_nonneg h.δQS_nonneg h.hS1 h.hS2
    (qS a) (bS ell a ρ) (cGS ell a ρ θ) h.qS_nonneg h.bS_pos.le h.hcG (le_of_eq rfl)
    (δCS θ) (κS ρ) (δKS ρ θ) (νS ρ) (δνS ρ θ) (δBS ell a ρ θ)
    h.δCS_nonneg h.κS_nonneg h.δKS_nonneg h.νS_nonneg h.δνS_nonneg h.δBS_nonneg

end CondM0

/-- **the k-free `G⁻¹` Combes–Thomas error constant** -/
noncomputable def EGM0 (ell : ℕ) (a ρ θ : ℝ) (h : CondM0 ell a ρ θ) : ℝ := h.ginv.EG

/-! ## elementary scaling bounds -/

theorem expm1_le_mul_exp (x : ℝ) (hx : 0 ≤ x) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h1 := Real.add_one_le_exp (-x)
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp x := Real.exp_pos x
  nlinarith

theorem n_expm1_le (n θ : ℝ) (hn : 1 ≤ n) (hθ : 0 ≤ θ) : n * (Real.exp (θ / n) - 1) ≤ θ * Real.exp θ := by
  have hn0 : 0 < n := by linarith
  have hx : 0 ≤ θ / n := div_nonneg hθ hn0.le
  have h1 := expm1_le_mul_exp (θ / n) hx
  have h2 : Real.exp (θ / n) ≤ Real.exp θ := Real.exp_le_exp.mpr (div_le_self hθ hn)
  calc n * (Real.exp (θ / n) - 1) ≤ n * (θ / n * Real.exp (θ / n)) := mul_le_mul_of_nonneg_left h1 hn0.le
    _ = θ * Real.exp (θ / n) := by field_simp
    _ ≤ θ * Real.exp θ := mul_le_mul_of_nonneg_left h2 hθ

theorem n_expm1_le' (n θ : ℝ) (c : ℝ) (hc : 0 ≤ c) (hn : 1 ≤ n) (hθ : 0 ≤ θ) :
    Real.exp (c * θ / n) - 1 ≤ Real.exp (c * θ) - 1 := by
  have hn0 : 0 < n := by linarith
  have : c * θ / n ≤ c * θ := div_le_self (by positivity) hn
  linarith [Real.exp_le_exp.mpr this]

theorem cs_val {L : PeriodicLatticeExtent} (w : PeriodicLatticeSite L) (d : ℕ) (μ ν : Fin 3) :
    ((AdalyFormal.Balaban.CoarseCurl.coarseShift w d μ) ν).val
      = if ν = μ then ((w ν).val + d) % (L ν + 1) else (w ν).val := by
  split_ifs with h
  · subst h; exact AdalyFormal.Balaban.CoarseCurl.coarseShift_val_eq w d ν
  · rw [AdalyFormal.Balaban.CoarseCurl.coarseShift_apply_ne w d μ ν h]

theorem box_reach {L : PeriodicLatticeExtent} (y x : PeriodicLatticeSite L) (m : ℕ)
    (hx : x ∈ boxF y m) : Reach (3 * (m - 1)) y x := by
  rw [mem_boxF] at hx
  set d : Fin 3 → ℕ := fun ν => (x ν).val - (y ν).val with hd
  have hdle : ∀ ν, d ν ≤ m - 1 := fun ν => by have := hx ν; simp only [hd]; omega
  set z := AdalyFormal.Balaban.CoarseCurl.coarseShift
    (AdalyFormal.Balaban.CoarseCurl.coarseShift (AdalyFormal.Balaban.CoarseCurl.coarseShift y (d 0) 0) (d 1) 1) (d 2) 2
    with hz
  have a0 := hx 0
  have a1 := hx 1
  have a2 := hx 2
  have l0 := (x 0).isLt
  have l1 := (x 1).isLt
  have l2 := (x 2).isLt
  have k0 : (z 0).val = (x 0).val := by
    rw [hz, cs_val, cs_val, cs_val]
    simp only [hd, show (0 : Fin 3) ≠ 2 by decide, show (0 : Fin 3) ≠ 1 by decide, if_false, if_true]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have k1 : (z 1).val = (x 1).val := by
    rw [hz, cs_val, cs_val, cs_val]
    simp only [hd, show (1 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, if_false, if_true]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have k2 : (z 2).val = (x 2).val := by
    rw [hz, cs_val, cs_val, cs_val]
    simp only [hd, show (2 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 0 by decide, if_false, if_true]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hzx : z = x := by
    funext ν
    apply Fin.ext
    fin_cases ν
    · exact k0
    · exact k1
    · exact k2
  rw [← hzx]
  have r := Reach_trans (Reach_trans (Reach_coarseShift (d 0) y 0) (Reach_coarseShift (d 1) _ 1))
    (Reach_coarseShift (d 2) _ 2)
  exact Reach_mono (by have := hdle 0; have := hdle 1; have := hdle 2; omega) r

theorem ajSeq_le (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) (j : ℕ) : ajSeq a ell j ≤ a := by
  unfold ajSeq
  split_ifs with h
  · exact le_rfl
  · have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
    have hd : 0 < a / ((ell : ℝ) * ell) := by positivity
    have h4 : (4 : ℝ) ≤ (ell : ℝ) * ell := by nlinarith
    have hda : a / ((ell : ℝ) * ell) < a := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith [mul_le_mul_of_nonneg_left h4 ha.le]
    exact (AdalyFormal.Balaban.ConstantA.aSeqAux_invariant a (a / ((ell : ℝ) * ell)) ha hd hda (j - 1)).2

theorem ajSeq_ge (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) (j : ℕ) :
    a * (1 - 1 / ((ell : ℝ) * ell)) ≤ ajSeq a ell j := by
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have e : a * (1 - 1 / ((ell : ℝ) * ell)) = a - a / ((ell : ℝ) * ell) := by ring
  rw [e]
  unfold ajSeq
  split_ifs with h
  · have : 0 ≤ a / ((ell : ℝ) * ell) := by positivity
    linarith
  · have hd : 0 < a / ((ell : ℝ) * ell) := by positivity
    have h4 : (4 : ℝ) ≤ (ell : ℝ) * ell := by nlinarith
    have hda : a / ((ell : ℝ) * ell) < a := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith [mul_le_mul_of_nonneg_left h4 ha.le]
    exact (AdalyFormal.Balaban.ConstantA.aSeqAux_invariant a (a / ((ell : ℝ) * ell)) ha hd hda (j - 1)).1

#print axioms CondM0.ginv
#print axioms EGM0
#print axioms expm1_le_mul_exp
#print axioms n_expm1_le
#print axioms n_expm1_le'
#print axioms cs_val
#print axioms box_reach
#print axioms ajSeq_le
#print axioms ajSeq_ge

end AdalyFormal.DLayer
