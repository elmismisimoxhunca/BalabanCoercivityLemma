import OL10

/-!
# OLN -- the Schur numerics with a GIVEN right-inverse constant `bN` (lane m2_oplayer_20261015)

DN3 `num_ball2` fixes `bN` to the M1 formula `bNF`.  Here `bN > 0` is arbitrary (the constant of an energy right inverse
supplied from outside); the four `bN`-dependent conditions are re-derived by continuity at `0` (`EN → 0`, the `CHw`
denominators stay positive):
* **`num_ballB`** : for `ℓ ≥ 2`, `a > 0`, `cw > 0`, `bN > 0` there are bounds and `δ > 0` such that on `dist z 0 < δ`:
  `NumOK2` (DN3), `ENx < 1/bN`, `CHwF(…, bN) < CHB`, `EN1F < 1/((1 + z₂₁/cw) bN)`, `CHwF(…, (1 + z₂₁/cw) bN) < CH1B`.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open Filter Topology
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (Estar rho1 SstarM delStar Ctheta)

section ballB
variable {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) {cw : ℝ} (hcw : 0 < cw) {bN : ℝ} (hbN : 0 < bN)
include hell ha hcw hbN

theorem cont_CHB : ContinuousAt (fun x : ℝ × ℝ × ℝ × ℝ => CHwF (kapNF ell a cw x) (CQF ell a cw x)
    (d3c ell a (SsF ell x.2.1) (3 * x.1 * ell)) cw bN) 0 := by
  have hk := cont_kap hell ha hcw; have hq := cont_CQ hell ha hcw; have h3 := cont_d3 (ell := ell) hell ha (a := a)
  have hE : ContinuousAt (fun x => ENF (kapNF ell a cw x) (CQF ell a cw x) (d3c ell a (SsF ell x.2.1) (3 * x.1 * ell)) cw)
      0 := cont_EN hell ha hcw
  have h1 : Real.sqrt cw ≠ 0 := (Real.sqrt_pos.mpr hcw).ne'
  have h2 : 1 - kapNF ell a cw 0 ≠ 0 := by rw [kap0]; norm_num
  have hb0 := hbN.ne'
  have h4 : 1 / bN - ENF (kapNF ell a cw 0) (CQF ell a cw 0) (d3c ell a (SsF ell (0 : ℝ × ℝ × ℝ × ℝ).2.1)
      (3 * (0 : ℝ × ℝ × ℝ × ℝ).1 * ell)) cw ≠ 0 := by
    have e := EN0 (ell := ell) (a := a) (cw := cw); simp only [ENx] at e; rw [e, sub_zero]; positivity
  simp only [CHwF, CyF]
  fun_prop (disch := first | exact h1 | exact h2 | exact hb0 | exact h4 | positivity)

theorem cont_CH1B : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => CHwF (kap1F ell a cw z) (CQ1F ell a cw z)
    (d3c ell a (SsF ell z.1.2.1) (3 * z.1.1 * ell)) (cw - z.2.1) ((1 + z.2.1 / cw) * bN)) 0 := by
  have hk := cont_kap1 hell ha hcw
  have hq := cont_CQ1 hell ha hcw
  have h3 := cont_d3z hell ha hcw
  have hE : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => ENF (kap1F ell a cw z) (CQ1F ell a cw z)
      (d3c ell a (SsF ell z.1.2.1) (3 * z.1.1 * ell)) (cw - z.2.1)) 0 := cont_EN1 hell ha hcw
  have h1 : Real.sqrt (cw - (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).2.1) ≠ 0 := by
    simp only [Prod.snd_zero, Prod.fst_zero, sub_zero]; exact (Real.sqrt_pos.mpr hcw).ne'
  have h2 : 1 - kap1F ell a cw 0 ≠ 0 := by rw [kap1_0 hell ha hcw]; norm_num
  have hb0 : (1 + (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).2.1 / cw) * bN ≠ 0 := by
    simp only [Prod.snd_zero, Prod.fst_zero, zero_div, add_zero, one_mul]; exact hbN.ne'
  have h4 : 1 / ((1 + (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).2.1 / cw) * bN) - ENF (kap1F ell a cw 0) (CQ1F ell a cw 0)
      (d3c ell a (SsF ell (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1.2.1) (3 * (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1.1 * ell))
      (cw - (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).2.1) ≠ 0 := by
    have e := EN1_0 hell ha hcw; simp only [EN1F] at e; rw [e, sub_zero]
    simp only [Prod.snd_zero, Prod.fst_zero, zero_div, add_zero, one_mul]; positivity
  simp only [CHwF, CyF]
  fun_prop (disch := first | exact h1 | exact h2 | exact hb0 | exact h4 | exact hcw.ne' | positivity)

/-- **the ball with a given `bN`** -/
theorem num_ballB : ∃ CHb : ℝ, 0 ≤ CHb ∧ ∃ CWb : ℝ, 0 ≤ CWb ∧ ∃ KWb : ℝ, 0 ≤ KWb ∧ ∃ CH1b : ℝ, 0 ≤ CH1b ∧
    ∃ CHB : ℝ, 0 ≤ CHB ∧ ∃ CH1B : ℝ, 0 ≤ CH1B ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ), dist z 0 < δ → NumOK2 ell a cw CHb CWb KWb CH1b z ∧
      ENx ell a cw z.1 < 1 / bN ∧
      CHwF (kapNF ell a cw z.1) (CQF ell a cw z.1) (d3c ell a (SsF ell z.1.2.1) (3 * z.1.1 * ell)) cw bN < CHB ∧
      EN1F ell a cw z < 1 / ((1 + z.2.1 / cw) * bN) ∧
      CHwF (kap1F ell a cw z) (CQ1F ell a cw z) (d3c ell a (SsF ell z.1.2.1) (3 * z.1.1 * ell)) (cw - z.2.1)
        ((1 + z.2.1 / cw) * bN) < CH1B := by
  obtain ⟨CHb, hCHb, CWb, hCWb, KWb, hKWb, CH1b, hCH1b, δ2, hδ2, hb2⟩ := num_ball2 hell ha hcw
  have e0 : ∀ᶠ z in 𝓝 (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)), NumOK2 ell a cw CHb CWb KWb CH1b z :=
    Metric.eventually_nhds_iff.mpr ⟨δ2, hδ2, fun {z} hz => hb2 z hz⟩
  have hEx : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => ENx ell a cw z.1) 0 := by
    have h := ContinuousAt.comp (f := Prod.fst) (x := (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ))) (cont_EN hell ha hcw)
      continuousAt_fst
    exact h
  have e1 : ∀ᶠ z in 𝓝 (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)), ENx ell a cw z.1 < 1 / bN :=
    hEx.eventually_lt continuousAt_const (by
      show ENx ell a cw (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1 < 1 / bN
      rw [Prod.fst_zero, EN0]; positivity)
  have hCB : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => CHwF (kapNF ell a cw z.1) (CQF ell a cw z.1)
      (d3c ell a (SsF ell z.1.2.1) (3 * z.1.1 * ell)) cw bN) 0 := by
    have h := ContinuousAt.comp (f := Prod.fst) (x := (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ))) (cont_CHB hell ha hcw hbN)
      continuousAt_fst
    exact h
  set v0 : ℝ := CHwF (kapNF ell a cw (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1) (CQF ell a cw (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1)
      (d3c ell a (SsF ell (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1.2.1) (3 * (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1.1 * ell)) cw bN
    with hv0
  have e2 : ∀ᶠ z in 𝓝 (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)), CHwF (kapNF ell a cw z.1) (CQF ell a cw z.1)
      (d3c ell a (SsF ell z.1.2.1) (3 * z.1.1 * ell)) cw bN < |v0| + 1 :=
    hCB.eventually_lt continuousAt_const (by have := le_abs_self v0; linarith)
  have hE1 := cont_EN1 hell ha hcw
  have hden : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => 1 / ((1 + z.2.1 / cw) * bN)) 0 := by
    have hb0 : (1 + (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).2.1 / cw) * bN ≠ 0 := by
      simp only [Prod.snd_zero, Prod.fst_zero, zero_div, add_zero, one_mul]; exact hbN.ne'
    fun_prop (disch := first | exact hb0 | exact hcw.ne')
  have e3 : ∀ᶠ z in 𝓝 (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)), EN1F ell a cw z < 1 / ((1 + z.2.1 / cw) * bN) :=
    hE1.eventually_lt hden (by
      rw [EN1_0 hell ha hcw]
      simp only [Prod.snd_zero, Prod.fst_zero, zero_div, add_zero, one_mul]; positivity)
  have hC1 := cont_CH1B hell ha hcw hbN
  set v1 : ℝ := CHwF (kap1F ell a cw 0) (CQ1F ell a cw 0)
      (d3c ell a (SsF ell (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1.2.1) (3 * (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1.1 * ell))
      (cw - (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).2.1) ((1 + (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).2.1 / cw) * bN) with hv1
  have e4 : ∀ᶠ z in 𝓝 (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)), CHwF (kap1F ell a cw z) (CQ1F ell a cw z)
      (d3c ell a (SsF ell z.1.2.1) (3 * z.1.1 * ell)) (cw - z.2.1) ((1 + z.2.1 / cw) * bN) < |v1| + 1 :=
    hC1.eventually_lt continuousAt_const (by have := le_abs_self v1; linarith)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (e0.and (e1.and (e2.and (e3.and e4))))
  exact ⟨CHb, hCHb, CWb, hCWb, KWb, hKWb, CH1b, hCH1b, |v0| + 1, by positivity, |v1| + 1, by positivity, δ, hδ,
    fun z hz => hball hz⟩

end ballB

end AdalyFormal.M1DStrat

#print axioms AdalyFormal.M1DStrat.cont_CHB
#print axioms AdalyFormal.M1DStrat.cont_CH1B
#print axioms AdalyFormal.M1DStrat.num_ballB
