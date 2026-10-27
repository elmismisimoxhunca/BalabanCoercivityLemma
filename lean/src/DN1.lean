import DX1

/-!
# DN1 -- the numeric conditions of `clause1_Ug` hold near the base point (M1 D-layer lane, 2026-10-14)

Every numeric hypothesis of DX2 `clause1_Ug` is a condition on a real function of FOUR real numbers
`x = (θ, r, p, q)` (`θ` the CT rate, `r = rho1 12 M α₀`, `p = 2ℓ² ln ℓ / W`, `q = 3ℓ ln ℓ / W`), for fixed `ℓ, a, cw`
(`ε1 = 1`).  The functions below reproduce DX2's hypotheses DEFINITIONALLY at `x = (θ, rho1 12 M α₀, p, q)`.
Each is continuous at `x = 0`, where every condition holds strictly; hence all hold on a ball around `0`.
* `num_ball` : `∃ δ > 0` such that all conditions hold for `|θ|, |r|, |p|, |q| < δ`.
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

section num
variable (ell : ℕ) (a cw : ℝ)

/-- `rhoT` as a function of `r = rho1` -/
noncomputable def rTF (r : ℝ) : ℝ := ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * r
/-- `S*` as a function of `r` -/
noncomputable def SsF (r : ℝ) : ℝ := Ctheta * (ell : ℝ) ^ 2 * (2 * (1 + 3 * Real.pi) * r)
noncomputable def csF (x : ℝ × ℝ × ℝ × ℝ) : ℝ := csOf a (rTF ell x.2.1)
noncomputable def ThF (x : ℝ × ℝ × ℝ × ℝ) : ℝ := 3 * x.1 * (ell : ℝ) ^ 2 + x.2.2.1
noncomputable def DeF (x : ℝ × ℝ × ℝ × ℝ) : ℝ := 6 * x.1 + x.2.2.2
noncomputable def epsXF (x : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  (4 / csF ell a x) * (Real.sqrt a * (Real.exp x.2.2.2 - 1))
    + (4 / csF ell a x) * (Real.sqrt 3 * (Real.exp x.2.2.1 - 1)) * (Real.sqrt (max a 1) / Real.sqrt (csF ell a x))
    + (Real.sqrt (48 / csF ell a x) * (Real.sqrt 3 * (Real.exp x.2.2.1 - 1))
        + (8 / csF ell a x) * (Real.sqrt 3 * (Real.exp x.2.2.1 - 1)) ^ 2
        + (4 / csF ell a x) * 1 * (2 * Real.sqrt (max a 1) * (Real.sqrt a * (Real.exp x.2.2.2 - 1))
          + (Real.sqrt a * (Real.exp x.2.2.2 - 1)) ^ 2))
      * (Real.sqrt (max a 1) / csF ell a x)
noncomputable def gamF (x : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  (ell : ℝ) * (Real.sqrt (max a 1) * ((1 + 12 * rTF ell x.2.1) ^ 2 + (512 * rTF ell x.2.1 ^ 2 + 4704) / a))
    / ((1 - 12 * rTF ell x.2.1) ^ 2
      - Real.sqrt (max a 1) * ((1 + 12 * rTF ell x.2.1) ^ 2 + (512 * rTF ell x.2.1 ^ 2 + 4704) / a) * epsXF ell a x)
noncomputable def etaF (x : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  1 + (1 + 1 / 1) * (12 * x.2.1 ^ 2 * (ell : ℝ) ^ 8 * (4 * ell / csF ell a x) ^ 2)
    + 2 * ((17 / Real.sqrt 2) * 12 * (x.2.1 * (ell : ℝ) ^ 4)) *
      ((ell : ℝ) * (Real.sqrt (12 / csF ell a x) + Real.sqrt 3 * (Real.exp x.2.2.1 - 1) * (4 / csF ell a x))) ^ 2
noncomputable def bNF (x : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  (1 + etaF ell a x) * (90 * (4 * CgE ell) + (96 * (ell : ℝ) ^ 2 + 24) * x.2.1 ^ 2 * (4 * CwE ell)) / a
    + 2 * ((17 / Real.sqrt 2) * 12 * (x.2.1 * (ell : ℝ) ^ 4)) * (4 * CwE ell) / a + (1 + etaF ell a x)
noncomputable def kapNF (x : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  kapN ell a (csF ell a x) (ThF ell x) (DeF x) (gamF ell a x) (3 * x.1 * (ell : ℝ) ^ 2) (3 * x.1 * ell) x.2.1 cw
    (SsF ell x.2.1)
noncomputable def CQF (x : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  CQN ell a (csF ell a x) (ThF ell x) (DeF x) (gamF ell a x) x.2.1 cw
noncomputable def ENx (x : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  ENF (kapNF ell a cw x) (CQF ell a cw x) (d3c ell a (SsF ell x.2.1) (3 * x.1 * ell)) cw
noncomputable def CHF (x : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  CHwF (kapNF ell a cw x) (CQF ell a cw x) (d3c ell a (SsF ell x.2.1) (3 * x.1 * ell)) cw (bNF ell a x)
noncomputable def CWF (x : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  1 + (ell : ℝ) * ((Real.sqrt 24 + Real.sqrt 3 * (Real.exp x.2.2.1 - 1) * Real.sqrt (48 / csF ell a x))
      + (Real.sqrt (12 / csF ell a x) + Real.sqrt 3 * (Real.exp x.2.2.1 - 1) * (4 / csF ell a x))
        * ((ell : ℝ) ^ 2 * ((4 / csF ell a x)
          * ((Real.sqrt (max a 1) + Real.sqrt a * (Real.exp x.2.2.2 - 1))
            * (gamF ell a x ^ 2 * ((Real.sqrt (12 / csF ell a x)
                + Real.sqrt 3 * (Real.exp x.2.2.1 - 1) * (4 / csF ell a x))
              * (Real.sqrt (max a 1) + Real.sqrt a * (Real.exp x.2.2.2 - 1))))))))

end num

/-! ## continuity at `0` -/

section cont
variable {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) {cw : ℝ} (hcw : 0 < cw)
include hell ha

/-- the discharger: evaluate at `0`, then `positivity` -/
macro "zdisch" : tactic => `(tactic| (simp only [Prod.fst_zero, Prod.snd_zero, Real.exp_zero, sub_self, mul_zero,
  zero_mul, add_zero, zero_add, sub_zero, zero_div, div_zero, Real.sqrt_zero, zero_pow two_ne_zero, one_pow,
  mul_one, one_mul, div_one, neg_zero, add_sub_cancel_right]; positivity))

theorem cont_cs : ContinuousAt (fun x => csF ell a x) 0 := by
  simp only [csF, csOf, rTF]; fun_prop

theorem cs0 : 0 < csF ell a 0 := by
  simp only [csF, csOf, rTF]
  simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, zero_pow two_ne_zero, sub_zero]
  positivity

omit hell ha in
theorem epsX0 : epsXF ell a 0 = 0 := by
  simp only [epsXF]; simp only [Prod.fst_zero, Prod.snd_zero, Real.exp_zero, sub_self, mul_zero, zero_mul, add_zero, zero_add,
    zero_pow two_ne_zero]

omit hell ha in
theorem rT0 : rTF ell (0 : ℝ × ℝ × ℝ × ℝ).2.1 = 0 := by simp only [rTF]; simp

theorem cont_epsX : ContinuousAt (fun x => epsXF ell a x) 0 := by
  have h0 := cs0 hell ha
  have h1 : Real.sqrt (csF ell a 0) ≠ 0 := (Real.sqrt_pos.mpr h0).ne'
  have hc := cont_cs hell ha
  simp only [epsXF]
  fun_prop (disch := first | exact h0.ne' | exact h1 | positivity)

theorem gam0 : 0 < gamF ell a 0 := by
  have hl : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  simp only [gamF]
  rw [epsX0, rT0]
  simp only [mul_zero, add_zero, sub_zero, one_pow, zero_pow two_ne_zero, zero_add]
  positivity

theorem cont_gam : ContinuousAt (fun x => gamF ell a x) 0 := by
  have he := cont_epsX hell ha
  have hd : (1 - 12 * rTF ell (0 : ℝ × ℝ × ℝ × ℝ).2.1) ^ 2 - Real.sqrt (max a 1)
      * ((1 + 12 * rTF ell (0 : ℝ × ℝ × ℝ × ℝ).2.1) ^ 2 + (512 * rTF ell (0 : ℝ × ℝ × ℝ × ℝ).2.1 ^ 2 + 4704) / a)
      * epsXF ell a 0 ≠ 0 := by
    rw [epsX0, rT0]; norm_num
  unfold gamF rTF at *
  fun_prop (disch := exact hd)

omit hell ha in
theorem Th0 : ThF ell (0 : ℝ × ℝ × ℝ × ℝ) = 0 := by simp only [ThF]; simp
omit hell ha in
theorem De0 : DeF (0 : ℝ × ℝ × ℝ × ℝ) = 0 := by simp only [DeF]; simp
omit hell ha in
theorem cont_Th : ContinuousAt (fun x => ThF ell x) 0 := by simp only [ThF]; fun_prop
omit hell ha in
theorem cont_De : ContinuousAt (fun x : ℝ × ℝ × ℝ × ℝ => DeF x) 0 := by simp only [DeF]; fun_prop

omit hell ha in
theorem EX0 (cs : ℝ) : EXN a cs 0 0 = 0 := by
  simp only [EXN, dQN, dDN]; simp only [Real.exp_zero, sub_self, mul_zero, zero_mul, add_zero, zero_add, zero_pow two_ne_zero]

omit hell ha in
theorem epsG0 (cs : ℝ) : epsGN ell a cs 0 0 = 0 := by simp only [epsGN]; rw [EX0]; ring

omit hell ha in
theorem cG0v : cGN ell a (csF ell a 0) (ThF ell 0) (DeF 0) (gamF ell a 0) = 1 / gamF ell a 0 ^ 2 := by
  simp only [cGN]; rw [Th0, De0, epsG0]; ring

theorem cG0 : 0 < cGN ell a (csF ell a 0) (ThF ell 0) (DeF 0) (gamF ell a 0) := by
  rw [cG0v]; have := gam0 hell ha; positivity

theorem cont_cG : ContinuousAt (fun x => cGN ell a (csF ell a x) (ThF ell x) (DeF x) (gamF ell a x)) 0 := by
  have hc := cont_cs hell ha; have hg := cont_gam hell ha; have hT := cont_Th (ell := ell); have hD := cont_De
  have h0 := cs0 hell ha
  have h1 : Real.sqrt (csF ell a 0) ≠ 0 := (Real.sqrt_pos.mpr h0).ne'
  have h2 := (gam0 hell ha).ne'
  simp only [cGN, epsGN, EXN, dQN, dDN, qN]
  fun_prop (disch := first | exact h0.ne' | exact h1 | exact h2 | positivity)

/-- the conjugated-`T` constant along `x` -/
theorem cont_dTc : ContinuousAt (fun x => dTcN ell a (csF ell a x) (ThF ell x) (DeF x) (gamF ell a x)
    (3 * x.1 * (ell : ℝ) ^ 2)) 0 := by
  have hc := cont_cs hell ha; have hg := cont_gam hell ha; have hT := cont_Th (ell := ell); have hD := cont_De
  have hG := cont_cG hell ha
  have h0 := cs0 hell ha
  have h1 : Real.sqrt (csF ell a 0) ≠ 0 := (Real.sqrt_pos.mpr h0).ne'
  have h3 := (cG0 hell ha).ne'
  simp only [dTcN, EXN, K3N, nXN, dGN, EDX'N, EDXN, epsGN, qN, dDN, dQN]
  fun_prop (disch := first | exact h0.ne' | exact h1 | exact h3 | positivity)

omit hell ha in
theorem dTc0 : dTcN ell a (csF ell a 0) (ThF ell 0) (DeF 0) (gamF ell a 0) (3 * (0 : ℝ × ℝ × ℝ × ℝ).1 * (ell : ℝ) ^ 2)
    = 0 := by
  rw [Th0, De0]
  simp only [dTcN, EXN, K3N, nXN, dGN, EDX'N, EDXN, epsGN, dDN, dQN]
  simp only [Prod.fst_zero, Real.exp_zero, sub_self, mul_zero, zero_mul, add_zero, zero_add, zero_pow two_ne_zero,
    zero_div]

theorem cont_kZ : ContinuousAt (fun x => kZcN ell a (csF ell a x) (ThF ell x) (DeF x) (gamF ell a x)) 0 := by
  have hc := cont_cs hell ha; have hg := cont_gam hell ha; have hT := cont_Th (ell := ell); have hD := cont_De
  have hG := cont_cG hell ha
  have h0 := cs0 hell ha
  have h3 := (cG0 hell ha).ne'
  simp only [kZcN, K3N, nXN, qN, dDN, dQN]
  fun_prop (disch := first | exact h0.ne' | exact h3 | positivity)

theorem cont_kW : ContinuousAt (fun x => kWcN ell a (csF ell a x) (ThF ell x) (DeF x) (gamF ell a x)) 0 := by
  have hc := cont_cs hell ha; have hg := cont_gam hell ha; have hT := cont_Th (ell := ell); have hD := cont_De
  have hG := cont_cG hell ha
  have h0 := cs0 hell ha
  have h3 := (cG0 hell ha).ne'
  simp only [kWcN, K3N, nXN, qN, dDN, dQN]
  fun_prop (disch := first | exact h0.ne' | exact h3 | positivity)

include hcw in
theorem cont_kap : ContinuousAt (fun x => kapNF ell a cw x) 0 := by
  have hd := cont_dTc hell ha; have hZ := cont_kZ hell ha; have hW := cont_kW hell ha
  have h1 : Real.sqrt cw ≠ 0 := (Real.sqrt_pos.mpr hcw).ne'
  simp only [kapNF, kapN, kapF, d1c, d3c, cDc, cDc', cYc, kapK, nuD, SsF, Estar]
  fun_prop (disch := first | exact h1 | exact hcw.ne' | positivity)

omit hell ha in
theorem kap0 : kapNF ell a cw 0 = 0 := by
  simp only [kapNF, kapN, kapF]
  rw [dTc0]
  simp only [d1c, d3c, cDc, cDc', cYc, kapK, nuD, SsF]
  simp only [Prod.fst_zero, Prod.snd_zero, Real.exp_zero, sub_self, mul_zero, zero_mul, add_zero, zero_add,
    zero_pow two_ne_zero, zero_div, Real.sqrt_zero]

include hcw in
theorem cont_CQ : ContinuousAt (fun x => CQF ell a cw x) 0 := by
  have hZ := cont_kZ hell ha; have hW := cont_kW hell ha
  have h1 : Real.sqrt cw ≠ 0 := (Real.sqrt_pos.mpr hcw).ne'
  simp only [CQF, CQN, cDc, cYc, kapK, nuD]
  fun_prop (disch := first | exact h1 | exact hcw.ne' | positivity)

omit hell ha in
theorem d30 : d3c ell a (SsF ell (0 : ℝ × ℝ × ℝ × ℝ).2.1) (3 * (0 : ℝ × ℝ × ℝ × ℝ).1 * ell) = 0 := by
  simp only [d3c, SsF]
  simp only [Prod.fst_zero, Prod.snd_zero, Real.exp_zero, sub_self, mul_zero, zero_mul, zero_pow two_ne_zero,
    Real.sqrt_zero]

theorem cont_d3 : ContinuousAt (fun x : ℝ × ℝ × ℝ × ℝ => d3c ell a (SsF ell x.2.1) (3 * x.1 * ell)) 0 := by
  simp only [d3c, SsF, Estar]; fun_prop

include hcw in
theorem cont_EN : ContinuousAt (fun x => ENx ell a cw x) 0 := by
  have hk := cont_kap hell ha hcw; have hq := cont_CQ hell ha hcw; have h3 := cont_d3 (ell := ell) hell ha (a := a)
  have h1 : Real.sqrt cw ≠ 0 := (Real.sqrt_pos.mpr hcw).ne'
  have h2 : 1 - kapNF ell a cw 0 ≠ 0 := by rw [kap0]; norm_num
  simp only [ENx, ENF, CyF]
  fun_prop (disch := first | exact h1 | exact h2 | positivity)

omit hell ha in
theorem EN0 : ENx ell a cw 0 = 0 := by
  simp only [ENx, ENF]; rw [kap0, d30]; simp

theorem bN0 : 0 < bNF ell a 0 := by
  have := AdalyFormal.W6.CE_pos; have := AdalyFormal.W6.GE_pos
  simp only [bNF, etaF, CwE, CgE]
  simp only [Prod.fst_zero, Prod.snd_zero, Real.exp_zero, sub_self, mul_zero, zero_mul, add_zero, zero_add,
    zero_pow two_ne_zero]
  positivity

theorem cont_bN : ContinuousAt (fun x => bNF ell a x) 0 := by
  have hc := cont_cs hell ha
  have h0 := cs0 hell ha
  simp only [bNF, etaF]
  fun_prop (disch := first | exact h0.ne' | exact ha.ne' | positivity)

include hcw in
theorem cont_CH : ContinuousAt (fun x => CHF ell a cw x) 0 := by
  have hk := cont_kap hell ha hcw; have hq := cont_CQ hell ha hcw; have h3 := cont_d3 (ell := ell) hell ha (a := a)
  have hb := cont_bN hell ha
  have hE : ContinuousAt (fun x => ENF (kapNF ell a cw x) (CQF ell a cw x) (d3c ell a (SsF ell x.2.1) (3 * x.1 * ell)) cw)
      0 := cont_EN hell ha hcw
  have h1 : Real.sqrt cw ≠ 0 := (Real.sqrt_pos.mpr hcw).ne'
  have h2 : 1 - kapNF ell a cw 0 ≠ 0 := by rw [kap0]; norm_num
  have hb0 := (bN0 hell ha).ne'
  have h4 : 1 / bNF ell a 0 - ENF (kapNF ell a cw 0) (CQF ell a cw 0) (d3c ell a (SsF ell (0 : ℝ × ℝ × ℝ × ℝ).2.1)
      (3 * (0 : ℝ × ℝ × ℝ × ℝ).1 * ell)) cw ≠ 0 := by
    have e := EN0 (ell := ell) (a := a) (cw := cw); simp only [ENx] at e; rw [e, sub_zero]; have := bN0 hell ha; positivity
  simp only [CHF, CHwF, CyF]
  fun_prop (disch := first | exact h1 | exact h2 | exact hb0 | exact h4 | positivity)

theorem cont_CW : ContinuousAt (fun x => CWF ell a x) 0 := by
  have hc := cont_cs hell ha; have hg := cont_gam hell ha
  have h0 := cs0 hell ha
  simp only [CWF]
  fun_prop (disch := first | exact h0.ne' | positivity)

end cont

#print axioms rTF
#print axioms csF
#print axioms cont_cs
#print axioms cs0
#print axioms cont_epsX
#print axioms epsX0
#print axioms gam0
#print axioms cont_gam
#print axioms Th0
#print axioms De0
#print axioms cont_Th
#print axioms cont_De
#print axioms EX0
#print axioms epsG0
#print axioms cG0v
#print axioms cG0
#print axioms cont_cG
#print axioms cont_dTc
#print axioms dTc0
#print axioms cont_kZ
#print axioms cont_kW
#print axioms cont_kap
#print axioms kap0
#print axioms cont_CQ
#print axioms d30
#print axioms cont_d3
#print axioms cont_EN
#print axioms EN0
#print axioms bN0
#print axioms cont_bN
#print axioms cont_CH
#print axioms cont_CW

end AdalyFormal.M1DStrat
