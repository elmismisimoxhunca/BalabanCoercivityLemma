import GG5

/-!
# GG6 -- GChart calculus and the C^{1,1} step cut-off (m2_glue2, 2026-10-15)

* `GChart.mono`, `GChart.congr`, `GChart.const_mul`.
* `rho t = max(t,0)²` (Taylor remainder ≤ (b−a)², derivative 2-Lipschitz), the step
  `S t = 2(ρ t − 2ρ(t−½) + ρ(t−1))` (`S = 0` on `t ≤ 0`, `S = 1` on `t ≥ 1`, `0 ≤ S ≤ 1`, `|S'| ≤ 2`,
  `S'` 16-Lipschitz, Taylor remainder ≤ 8(b−a)²) and `step_second`: the second difference of `S ∘ f`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Glue2

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log coe_mul coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.Bch2 (frobNorm_nonneg)
open scoped Matrix

variable {L : PeriodicLatticeExtent}

/-! ## §1 GChart calculus -/

theorem GChart.mono {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {D D' : Set (PeriodicLatticeSite L)}
    {t1 t2 t1' t2' : ℝ} (h : GChart U g D t1 t2) (hD : D' ⊆ D) (h1 : t1 ≤ t1') (h2 : t2 ≤ t2') :
    GChart U g D' t1' t2' :=
  ⟨fun x ν a b => (h.1 x ν (hD a) (hD b)).trans h1,
   fun x μ ν a b c d => (h.2 x μ ν (hD a) (hD b) (hD c) (hD d)).trans h2⟩

theorem gauge_congr {U : LinkCfg L} {g g' : PeriodicLatticeSite L → SU2} {x : PeriodicLatticeSite L} {ν : Fin 3}
    (h0 : g' x = g x) (h1 : g' (periodicLatticeShift x ν) = g (periodicLatticeShift x ν)) :
    periodicGaugeTransform g' U (x, ν) = periodicGaugeTransform g U (x, ν) := by
  simp only [periodicGaugeTransform, h0, h1]

theorem GChart.congr {U : LinkCfg L} {g g' : PeriodicLatticeSite L → SU2} {D : Set (PeriodicLatticeSite L)}
    {t1 t2 : ℝ} (h : GChart U g D t1 t2) (he : ∀ x ∈ D, g' x = g x) : GChart U g' D t1 t2 := by
  refine ⟨fun x ν a b => ?_, fun x μ ν a b c d => ?_⟩
  · rw [gauge_congr (he x a) (he _ b)]; exact h.1 x ν a b
  · rw [gauge_congr (he x a) (he _ b), gauge_congr (he _ c) (he _ d)]; exact h.2 x μ ν a b c d

theorem gauge_const_mul (U : LinkCfg L) (g : PeriodicLatticeSite L → SU2) (C : SU2) (e : PeriodicLatticeEdge L) :
    periodicGaugeTransform (fun x => C * g x) U e = C * periodicGaugeTransform g U e * C⁻¹ := by
  simp only [periodicGaugeTransform]; group

theorem frobNorm_conj_sub (C G G' : SU2) :
    frobNorm (((C * G' * C⁻¹ : SU2) : M2) - ((C * G * C⁻¹ : SU2) : M2)) = frobNorm ((G' : M2) - (G : M2)) := by
  simp only [coe_mul, coe_inv]
  rw [show (C : M2) * (G' : M2) * (C : M2)ᴴ - (C : M2) * (G : M2) * (C : M2)ᴴ
      = (C : M2) * ((G' : M2) - (G : M2)) * (C : M2)ᴴ by noncomm_ring, frobNorm_mul_su2_star, frobNorm_su2_mul]

theorem frobNorm_conj_sub_one (C G : SU2) :
    frobNorm (((C * G * C⁻¹ : SU2) : M2) - 1) = frobNorm ((G : M2) - 1) := by
  have := frobNorm_conj_sub C 1 G
  simpa using this

theorem GChart.const_mul {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {D : Set (PeriodicLatticeSite L)}
    {t1 t2 : ℝ} (h : GChart U g D t1 t2) (C : SU2) : GChart U (fun x => C * g x) D t1 t2 := by
  refine ⟨fun x ν a b => ?_, fun x μ ν a b c d => ?_⟩
  · rw [gauge_const_mul, frobNorm_conj_sub_one]; exact h.1 x ν a b
  · rw [gauge_const_mul, gauge_const_mul, frobNorm_conj_sub]; exact h.2 x μ ν a b c d

/-! ## §2 the step function -/

theorem abs_add' (a b : ℝ) : |a + b| ≤ |a| + |b| :=
  abs_le.mpr ⟨by linarith [neg_abs_le a, neg_abs_le b], by linarith [le_abs_self a, le_abs_self b]⟩

noncomputable def relu (t : ℝ) : ℝ := max t 0
noncomputable def rho (t : ℝ) : ℝ := relu t ^ 2
noncomputable def rho' (t : ℝ) : ℝ := 2 * relu t

theorem relu_nonneg (t : ℝ) : 0 ≤ relu t := le_max_right _ _

theorem relu_lip (a b : ℝ) : |relu b - relu a| ≤ |b - a| := by
  unfold relu; exact abs_max_sub_max_le_abs b a 0

theorem rho_taylor (a b : ℝ) : |rho b - rho a - rho' a * (b - a)| ≤ (b - a) ^ 2 := by
  unfold rho rho' relu
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_right ha, max_eq_right hb]; simp; positivity
  · rw [max_eq_right ha, max_eq_left hb]
    rw [abs_le]; constructor <;> nlinarith
  · rw [max_eq_left ha, max_eq_right hb]
    rw [abs_le]; constructor <;> nlinarith
  · rw [max_eq_left ha, max_eq_left hb]
    rw [abs_le]; constructor <;> nlinarith

theorem rho'_lip (a b : ℝ) : |rho' b - rho' a| ≤ 2 * |b - a| := by
  unfold rho'
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left (relu_lip a b) (by norm_num)

noncomputable def stepS (t : ℝ) : ℝ := 2 * (rho t - 2 * rho (t - 1 / 2) + rho (t - 1))
noncomputable def stepS' (t : ℝ) : ℝ := 2 * (rho' t - 2 * rho' (t - 1 / 2) + rho' (t - 1))

theorem stepS_of_nonpos {t : ℝ} (ht : t ≤ 0) : stepS t = 0 := by
  unfold stepS rho relu
  rw [max_eq_right ht, max_eq_right (by linarith), max_eq_right (by linarith)]; ring

theorem stepS_of_one_le {t : ℝ} (ht : 1 ≤ t) : stepS t = 1 := by
  unfold stepS rho relu
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]; ring

theorem stepS_mem (t : ℝ) : 0 ≤ stepS t ∧ stepS t ≤ 1 := by
  unfold stepS rho relu
  rcases le_total t 0 with h0 | h0
  · rw [max_eq_right h0, max_eq_right (by linarith), max_eq_right (by linarith)]; norm_num
  rcases le_total t (1 / 2) with h1 | h1
  · rw [max_eq_left h0, max_eq_right (by linarith), max_eq_right (by linarith)]
    constructor <;> nlinarith
  rcases le_total t 1 with h2 | h2
  · rw [max_eq_left h0, max_eq_left (by linarith), max_eq_right (by linarith)]
    constructor <;> nlinarith
  · rw [max_eq_left h0, max_eq_left (by linarith), max_eq_left (by linarith)]
    constructor <;> nlinarith

theorem stepS'_abs (t : ℝ) : |stepS' t| ≤ 2 := by
  unfold stepS' rho' relu
  rcases le_total t 0 with h0 | h0
  · rw [max_eq_right h0, max_eq_right (by linarith), max_eq_right (by linarith)]; norm_num
  rcases le_total t (1 / 2) with h1 | h1
  · rw [max_eq_left h0, max_eq_right (by linarith), max_eq_right (by linarith)]
    rw [abs_le]; constructor <;> nlinarith
  rcases le_total t 1 with h2 | h2
  · rw [max_eq_left h0, max_eq_left (by linarith), max_eq_right (by linarith)]
    rw [abs_le]; constructor <;> nlinarith
  · rw [max_eq_left h0, max_eq_left (by linarith), max_eq_left (by linarith)]
    rw [abs_le]; constructor <;> nlinarith

theorem stepS'_lip (a b : ℝ) : |stepS' b - stepS' a| ≤ 16 * |b - a| := by
  unfold stepS'
  have h1 := rho'_lip a b
  have h2 := rho'_lip (a - 1 / 2) (b - 1 / 2)
  have h3 := rho'_lip (a - 1) (b - 1)
  rw [show b - 1 / 2 - (a - 1 / 2) = b - a by ring] at h2
  rw [show b - 1 - (a - 1) = b - a by ring] at h3
  have e : 2 * (rho' b - 2 * rho' (b - 1 / 2) + rho' (b - 1)) - 2 * (rho' a - 2 * rho' (a - 1 / 2) + rho' (a - 1))
      = 2 * (rho' b - rho' a) - 4 * (rho' (b - 1 / 2) - rho' (a - 1 / 2)) + 2 * (rho' (b - 1) - rho' (a - 1)) := by
    ring
  rw [e]
  have := abs_add' (2 * (rho' b - rho' a) - 4 * (rho' (b - 1 / 2) - rho' (a - 1 / 2))) (2 * (rho' (b - 1) - rho' (a - 1)))
  have := abs_sub (2 * (rho' b - rho' a)) (4 * (rho' (b - 1 / 2) - rho' (a - 1 / 2)))
  simp only [abs_mul] at *
  norm_num at *
  linarith

theorem stepS_taylor (a b : ℝ) : |stepS b - stepS a - stepS' a * (b - a)| ≤ 8 * (b - a) ^ 2 := by
  unfold stepS stepS'
  have h1 := rho_taylor a b
  have h2 := rho_taylor (a - 1 / 2) (b - 1 / 2)
  have h3 := rho_taylor (a - 1) (b - 1)
  rw [show b - 1 / 2 - (a - 1 / 2) = b - a by ring] at h2
  rw [show b - 1 - (a - 1) = b - a by ring] at h3
  have e : 2 * (rho b - 2 * rho (b - 1 / 2) + rho (b - 1)) - 2 * (rho a - 2 * rho (a - 1 / 2) + rho (a - 1))
      - 2 * (rho' a - 2 * rho' (a - 1 / 2) + rho' (a - 1)) * (b - a)
      = 2 * (rho b - rho a - rho' a * (b - a)) - 4 * (rho (b - 1 / 2) - rho (a - 1 / 2) - rho' (a - 1 / 2) * (b - a))
        + 2 * (rho (b - 1) - rho (a - 1) - rho' (a - 1) * (b - a)) := by ring
  rw [e]
  set X := rho b - rho a - rho' a * (b - a)
  set Y := rho (b - 1 / 2) - rho (a - 1 / 2) - rho' (a - 1 / 2) * (b - a)
  set Z := rho (b - 1) - rho (a - 1) - rho' (a - 1) * (b - a)
  have := abs_add' (2 * X - 4 * Y) (2 * Z)
  have := abs_sub (2 * X) (4 * Y)
  simp only [abs_mul] at *
  norm_num at *
  nlinarith [sq_nonneg (b - a)]

theorem stepS_lip (a b : ℝ) : |stepS b - stepS a| ≤ 2 * |b - a| + 8 * (b - a) ^ 2 := by
  have h := stepS_taylor a b
  have h2 := stepS'_abs a
  have : |stepS' a * (b - a)| ≤ 2 * |b - a| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  have := abs_sub_le (stepS b - stepS a) (stepS' a * (b - a)) 0
  simp only [sub_zero] at this
  have e : |stepS b - stepS a| ≤ |stepS b - stepS a - stepS' a * (b - a)| + |stepS' a * (b - a)| := by
    have := abs_add' (stepS b - stepS a - stepS' a * (b - a)) (stepS' a * (b - a))
    simpa using this
  linarith

/-- **second difference of `S ∘ f`.** -/
theorem stepS_second (f0 f1 f2 f3 : ℝ) :
    |stepS f3 - stepS f2 - stepS f1 + stepS f0|
      ≤ 2 * |f3 - f2 - f1 + f0| + 16 * |f2 - f0| * |f1 - f0| + 8 * (f3 - f2) ^ 2 + 8 * (f1 - f0) ^ 2 := by
  have t2 := stepS_taylor f2 f3
  have t0 := stepS_taylor f0 f1
  have d := stepS'_lip f0 f2
  have b2 := stepS'_abs f2
  have e : stepS f3 - stepS f2 - stepS f1 + stepS f0
      = (stepS f3 - stepS f2 - stepS' f2 * (f3 - f2)) - (stepS f1 - stepS f0 - stepS' f0 * (f1 - f0))
        + stepS' f2 * (f3 - f2 - f1 + f0) + (stepS' f2 - stepS' f0) * (f1 - f0) := by ring
  rw [e]
  set A := stepS f3 - stepS f2 - stepS' f2 * (f3 - f2)
  set B := stepS f1 - stepS f0 - stepS' f0 * (f1 - f0)
  have h1 : |stepS' f2 * (f3 - f2 - f1 + f0)| ≤ 2 * |f3 - f2 - f1 + f0| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right b2 (abs_nonneg _)
  have h2 : |(stepS' f2 - stepS' f0) * (f1 - f0)| ≤ 16 * |f2 - f0| * |f1 - f0| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right d (abs_nonneg _)
  have tri : |A - B + stepS' f2 * (f3 - f2 - f1 + f0) + (stepS' f2 - stepS' f0) * (f1 - f0)|
      ≤ |A| + |B| + |stepS' f2 * (f3 - f2 - f1 + f0)| + |(stepS' f2 - stepS' f0) * (f1 - f0)| := by
    have a1 := abs_add' (A - B + stepS' f2 * (f3 - f2 - f1 + f0)) ((stepS' f2 - stepS' f0) * (f1 - f0))
    have a2 := abs_add' (A - B) (stepS' f2 * (f3 - f2 - f1 + f0))
    have a3 := abs_sub A B
    linarith
  linarith

end AdalyFormal.M2Glue2
