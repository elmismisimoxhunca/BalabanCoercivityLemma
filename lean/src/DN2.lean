import DN1

/-!
# DN2 -- all numeric conditions of `clause1_Ug` on a ball around `0` (M1 D-layer lane, 2026-10-14)

`NumOK ℓ a cw CHb CWb x` is the conjunction of the sixteen strict numeric conditions of DX2 at `x = (θ, r, p, q)`.
* **`num_ball`** : for `ℓ ≥ 2`, `a > 0`, `cw > 0` there are `CHb ≥ 0`, `CWb ≥ 0` and `δ > 0` with `NumOK` on the
  `δ`-ball around `0` (sup distance).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open Filter Topology
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (Estar rho1 SstarM delStar Ctheta)
open AdalyFormal.M1GaugeW4 (rhoT epsXnum)
open AdalyFormal.W6 (CwE CgE CEp)

/-- the sixteen numeric conditions at `x = (θ, r, p, q)` -/
def NumOK (ell : ℕ) (a cw CHb CWb : ℝ) (x : ℝ × ℝ × ℝ × ℝ) : Prop :=
  24 * ((Real.sqrt 3 * (Real.exp x.2.2.1 - 1)) ^ 2 + 1 * (Real.sqrt a * (Real.exp x.2.2.2 - 1)) ^ 2) < csF ell a x ∧
  4 * (Real.sqrt 3 * (Real.exp x.2.2.1 - 1)) ^ 2 < csF ell a x ∧
  24 * ((Real.sqrt 3 * (Real.exp (ThF ell x) - 1)) ^ 2 + 1 * (Real.sqrt a * (Real.exp (DeF x) - 1)) ^ 2)
    < csF ell a x ∧
  4 * (Real.sqrt 3 * (Real.exp (ThF ell x) - 1)) ^ 2 < csF ell a x ∧
  Real.sqrt (max a 1) * ((1 + 12 * rTF ell x.2.1) ^ 2 + (512 * rTF ell x.2.1 ^ 2 + 4704) / a) * epsXF ell a x
    < (1 - 12 * rTF ell x.2.1) ^ 2 ∧
  4000000 * (ell : ℝ) ^ 2 * x.2.1 < 1 ∧
  (1 + 3 * Real.pi) * x.2.1 < 1 / (1000 * (ell : ℝ) ^ 4) ∧
  Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * x.2.1))
    < AdalyFormal.NonflatJet.r0 ∧
  3 * delStar ell (SsF ell x.2.1) ^ 2 * CEp < 1 ∧
  3 * (ell : ℝ) ^ 2 * delStar ell (SsF ell x.2.1) ^ 2 * CwE ell < 1 / 4 ∧
  epsGN ell a (csF ell a x) (ThF ell x) (DeF x) * gamF ell a x < 1 ∧
  0 < cGN ell a (csF ell a x) (ThF ell x) (DeF x) (gamF ell a x) ∧
  kapNF ell a cw x < 1 ∧
  ENx ell a cw x < 1 / bNF ell a x ∧
  CHF ell a cw x < CHb ∧
  CWF ell a x ^ 2 < CWb

section ball
variable {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) {cw : ℝ} (hcw : 0 < cw)
include hell ha

/-- `f < g` near `0` from continuity and the strict inequality at `0` -/
theorem ev_lt {f g : ℝ × ℝ × ℝ × ℝ → ℝ} (hf : ContinuousAt f 0) (hg : ContinuousAt g 0) (h : f 0 < g 0) :
    ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ), f x < g x :=
  hf.eventually_lt hg h

omit hell ha in
theorem dS0 : delStar ell (SsF ell (0 : ℝ × ℝ × ℝ × ℝ).2.1) = 0 := by
  simp only [delStar, SsF, Prod.snd_zero, Prod.fst_zero, mul_zero, zero_div, zero_mul]

include hcw in
/-- **the ball** -/
theorem num_ball : ∃ CHb : ℝ, 0 ≤ CHb ∧ ∃ CWb : ℝ, 0 ≤ CWb ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ x : ℝ × ℝ × ℝ × ℝ, dist x 0 < δ → NumOK ell a cw CHb CWb x := by
  have hc := cont_cs hell ha
  have hc0 := cs0 hell ha
  have hT := cont_Th (ell := ell)
  have hD := cont_De
  have hEx := cont_epsX hell ha
  have hg := cont_gam hell ha
  have hG := cont_cG hell ha
  have hk := cont_kap hell ha hcw
  have hE := cont_EN hell ha hcw
  have hb := cont_bN hell ha
  have hb0 := bN0 hell ha
  have hCH := cont_CH hell ha hcw
  have hCW := cont_CW hell ha
  have hr : ContinuousAt (fun x : ℝ × ℝ × ℝ × ℝ => x.2.1) 0 := by fun_prop
  have hl : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  -- the sixteen eventualities
  have e1 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ),
      24 * ((Real.sqrt 3 * (Real.exp x.2.2.1 - 1)) ^ 2 + 1 * (Real.sqrt a * (Real.exp x.2.2.2 - 1)) ^ 2)
        < csF ell a x :=
    ev_lt hell ha (by fun_prop) hc (by simpa using hc0)
  have e2 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ), 4 * (Real.sqrt 3 * (Real.exp x.2.2.1 - 1)) ^ 2 < csF ell a x :=
    ev_lt hell ha (by fun_prop) hc (by simpa using hc0)
  have e3 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ),
      24 * ((Real.sqrt 3 * (Real.exp (ThF ell x) - 1)) ^ 2 + 1 * (Real.sqrt a * (Real.exp (DeF x) - 1)) ^ 2)
        < csF ell a x :=
    ev_lt hell ha (by fun_prop) hc (by rw [Th0, De0]; simpa using hc0)
  have e4 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ), 4 * (Real.sqrt 3 * (Real.exp (ThF ell x) - 1)) ^ 2 < csF ell a x :=
    ev_lt hell ha (by fun_prop) hc (by rw [Th0]; simpa using hc0)
  have e5 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ),
      Real.sqrt (max a 1) * ((1 + 12 * rTF ell x.2.1) ^ 2 + (512 * rTF ell x.2.1 ^ 2 + 4704) / a) * epsXF ell a x
        < (1 - 12 * rTF ell x.2.1) ^ 2 :=
    ev_lt hell ha (by simp only [rTF]; fun_prop) (by simp only [rTF]; fun_prop)
      (by rw [epsX0, rT0]; norm_num)
  have e6 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ), 4000000 * (ell : ℝ) ^ 2 * x.2.1 < 1 :=
    ev_lt hell ha (by fun_prop) continuousAt_const (by simp)
  have e7 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ), (1 + 3 * Real.pi) * x.2.1 < 1 / (1000 * (ell : ℝ) ^ 4) :=
    ev_lt hell ha (by fun_prop) continuousAt_const (by simp only [Prod.snd_zero, Prod.fst_zero, mul_zero]; positivity)
  have e8 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ),
      Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * x.2.1))
        < AdalyFormal.NonflatJet.r0 :=
    ev_lt hell ha (by fun_prop) continuousAt_const
      (by simp only [Prod.snd_zero, Prod.fst_zero, mul_zero]; exact AdalyFormal.NonflatJet.r0_pos)
  have e9 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ), 3 * delStar ell (SsF ell x.2.1) ^ 2 * CEp < 1 :=
    ev_lt hell ha (by simp only [delStar, SsF]; fun_prop) continuousAt_const
      (by rw [dS0]; norm_num)
  have e10 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ), 3 * (ell : ℝ) ^ 2 * delStar ell (SsF ell x.2.1) ^ 2 * CwE ell < 1 / 4 :=
    ev_lt hell ha (by simp only [delStar, SsF]; fun_prop) continuousAt_const
      (by rw [dS0]; norm_num)
  have e11 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ),
      epsGN ell a (csF ell a x) (ThF ell x) (DeF x) * gamF ell a x < 1 := by
    have h1 : Real.sqrt (csF ell a 0) ≠ 0 := (Real.sqrt_pos.mpr hc0).ne'
    refine ev_lt hell ha ?_ continuousAt_const ?_
    · simp only [epsGN, EXN, dQN, dDN, qN]
      fun_prop (disch := first | exact hc0.ne' | exact h1 | positivity)
    · rw [Th0, De0, epsG0]; norm_num
  have e12 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ),
      0 < cGN ell a (csF ell a x) (ThF ell x) (DeF x) (gamF ell a x) :=
    ev_lt hell ha continuousAt_const hG (cG0 hell ha)
  have e13 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ), kapNF ell a cw x < 1 :=
    ev_lt hell ha hk continuousAt_const (by rw [kap0]; norm_num)
  have e14 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ), ENx ell a cw x < 1 / bNF ell a x :=
    ev_lt hell ha hE (by fun_prop (disch := exact hb0.ne')) (by rw [EN0]; positivity)
  have e15 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ), CHF ell a cw x < |CHF ell a cw 0| + 1 :=
    ev_lt hell ha hCH continuousAt_const (by have := le_abs_self (CHF ell a cw 0); linarith)
  have e16 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ), CWF ell a x ^ 2 < (|CWF ell a 0| + 1) ^ 2 :=
    ev_lt hell ha (by fun_prop) continuousAt_const (by
      have h1 := abs_nonneg (CWF ell a 0)
      have h2 : CWF ell a 0 ^ 2 = |CWF ell a 0| ^ 2 := (sq_abs _).symm
      rw [h2]; nlinarith)
  have hall := e1.and (e2.and (e3.and (e4.and (e5.and (e6.and (e7.and (e8.and (e9.and (e10.and (e11.and (e12.and
    (e13.and (e14.and (e15.and e16))))))))))))))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hall
  exact ⟨|CHF ell a cw 0| + 1, by positivity, (|CWF ell a 0| + 1) ^ 2, by positivity, δ, hδ, fun x hx => hball hx⟩

end ball

#print axioms NumOK
#print axioms ev_lt
#print axioms dS0
#print axioms num_ball

end AdalyFormal.M1DStrat
