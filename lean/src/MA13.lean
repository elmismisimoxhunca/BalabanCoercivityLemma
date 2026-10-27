import MA12

/-!
# MA13 -- uniform positivity of `cwW4` (lane m1_assembly_20261014)

`Psi ell a eps1 eps2 m s x K`: `cwR` at the arguments of `w4_M1_final` (with `s = 12 M alpha0`, `x = 1/W`, `K = KG`).
`Psi_zero_pos`: `Psi .. 0 0 0 > 0`.  `Psi_continuousAt`: continuity at `(0,0,0)`.  `cw_uniform`: a uniform positive lower bound near `(0,0,0)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1Num

open AdalyFormal.M1IMS AdalyFormal.M1GaugeW4 AdalyFormal.TowerLoc

noncomputable def rhoH (s : ℝ) : ℝ := (4 * Real.pi + 4) * s
noncomputable def rhoTs (ell : ℕ) (s : ℝ) : ℝ := ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * rhoH s
noncomputable def Ssr (ell : ℕ) (s : ℝ) : ℝ := Ctheta * (ell : ℝ) ^ 2 * (2 * (1 + 3 * Real.pi) * rhoH s)

noncomputable def Psi (ell : ℕ) (a ε1 ε2 m : ℝ) (s x K : ℝ) : ℝ :=
  cwR ell x K a (rhoTs ell s) (rhoH s) ε1 ε2
    ((1 - etaR ell x (csOf a (rhoTs ell s)) (rhoH s) ε1) * m - 2 * nuC ell (rhoH s))
    (epsXR ell x a (rhoTs ell s))
    (a * Estar ell (Ssr ell s) ^ 2 * (49 * (ell : ℝ) ^ 2 * K) * (1944 * (ell : ℝ) ^ 2))

theorem Psi_zero_pos (ell : ℕ) (hell : 0 < ell) (a ε1 ε2 m : ℝ) (ha : 0 < a) (hε1 : 0 < ε1) (hε1' : ε1 < 1)
    (hε2 : 0 < ε2) (hm : 0 < m) : 0 < Psi ell a ε1 ε2 m 0 0 0 := by
  have h6 : (0 : ℝ) < max 6 (16 / (3 * a)) := lt_max_of_lt_left (by norm_num)
  have hcs : csOf a (rhoTs ell 0) = 1 / max 6 (16 / (3 * a)) := by
    unfold csOf rhoTs rhoH; simp
  have hnu : nuC ell (rhoH 0) = 0 := by unfold nuC rhoH; simp
  have hw : wexp ell 0 = 1 := by unfold wexp; simp
  have hq : qexp ell 0 = 1 := by unfold qexp; simp
  have heta : etaR ell 0 (csOf a (rhoTs ell 0)) (rhoH 0) ε1 = ε1 := by
    unfold etaR; rw [hnu, hw]; unfold rhoH; simp
  have hdD : dDR ell 0 = 0 := by unfold dDR; rw [hw]; simp
  have hdQ : dQR ell 0 a = 0 := by unfold dQR; rw [hq]; simp
  have hX : epsXR ell 0 a (rhoTs ell 0) = 0 := by
    unfold epsXR; rw [hdD, hdQ]; simp
  have hCT : ∀ cs γ : ℝ, CTR ell 0 0 a cs γ = 0 := by
    intro cs γ; unfold CTR; simp
  have hC1 : C1R ell 0 0 a (csOf a (rhoTs ell 0)) (gamC ell a (rhoTs ell 0) 0) 0 ε2 = 0 := by
    unfold C1R; rw [hCT]; simp
  unfold Psi cwR
  have hCM : a * Estar ell (Ssr ell 0) ^ 2 * (49 * (ell : ℝ) ^ 2 * 0) * (1944 * (ell : ℝ) ^ 2) = 0 := by simp
  rw [heta, hnu, hX, hCM, hC1]
  have hnu' : nuC ell (rhoH 0) = 0 := hnu
  simp only [hnu', mul_zero, zero_add, add_zero, sub_zero]
  have hd : 0 < 1 + ((1 + ε1) * (1 + ε2) / (1 - ε1) - 1) := by
    have : 0 < (1 + ε1) * (1 + ε2) / (1 - ε1) := by apply div_pos <;> nlinarith
    have h1 : 1 ≤ (1 + ε1) * (1 + ε2) / (1 - ε1) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    linarith
  apply div_pos _ hd
  have := mul_pos (by linarith : 0 < 1 - ε1) hm
  simpa using this


theorem cs_pos (ell : ℕ) (a : ℝ) : 0 < csOf a (rhoTs ell 0) := by
  have h6 : (0 : ℝ) < max 6 (16 / (3 * a)) := lt_max_of_lt_left (by norm_num)
  unfold csOf rhoTs rhoH; simp


theorem cs_cont (ell : ℕ) (a : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => csOf a (rhoTs ell p.1)) (0, 0, 0) := by
  unfold csOf rhoTs rhoH
  fun_prop

theorem eta_cont (ell : ℕ) (a ε1 : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => etaR ell p.2.1 (csOf a (rhoTs ell p.1)) (rhoH p.1) ε1) (0, 0, 0) := by
  have hne : csOf a (rhoTs ell 0) ≠ 0 := (cs_pos ell a).ne'
  unfold etaR nuC wexp csOf rhoTs rhoH at *
  fun_prop (disch := first | exact hne | simpa using hne)

theorem epsX_cont (ell : ℕ) (a : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => epsXR ell p.2.1 a (rhoTs ell p.1)) (0, 0, 0) := by
  have hne : csOf a (rhoTs ell 0) ≠ 0 := (cs_pos ell a).ne'
  have hne2 : Real.sqrt (csOf a (rhoTs ell 0)) ≠ 0 := (Real.sqrt_pos.2 (cs_pos ell a)).ne'
  unfold epsXR dDR dQR wexp qexp csOf rhoTs rhoH at *
  fun_prop (disch := first | exact hne | simpa using hne | exact hne2 | simpa using hne2)

theorem eta0 (ell : ℕ) (a ε1 : ℝ) : etaR ell 0 (csOf a (rhoTs ell 0)) (rhoH 0) ε1 = ε1 := by
  unfold etaR nuC wexp rhoH; simp

theorem epsX0 (ell : ℕ) (a : ℝ) : epsXR ell 0 a (rhoTs ell 0) = 0 := by
  unfold epsXR dDR dQR wexp qexp; simp

theorem gam_cont (ell : ℕ) (a : ℝ) (ha : 0 < a) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => gamC ell a (rhoTs ell p.1) (epsXR ell p.2.1 a (rhoTs ell p.1))) (0, 0, 0) := by
  have hX := epsX_cont ell a
  have h0 : (1 - 12 * rhoTs ell 0) ^ 2 - Real.sqrt (max a 1) * ((1 + 12 * rhoTs ell 0) ^ 2 + (512 * rhoTs ell 0 ^ 2 + 4704) / a)
      * epsXR ell 0 a (rhoTs ell 0) ≠ 0 := by
    rw [epsX0]; unfold rhoTs rhoH; simp
  unfold gamC
  have hr : ContinuousAt (fun p : ℝ × ℝ × ℝ => rhoTs ell p.1) (0, 0, 0) := by unfold rhoTs rhoH; fun_prop
  fun_prop (disch := first | exact h0 | simpa using h0)

theorem psi_cont (ell : ℕ) (a ε1 ε2 m : ℝ) (ha : 0 < a) (hε1 : 0 < ε1) (hε1' : ε1 < 1) (hε2 : 0 < ε2) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => Psi ell a ε1 ε2 m p.1 p.2.1 p.2.2) (0, 0, 0) := by
  have hc := cs_pos ell a
  have hne : csOf a (rhoTs ell 0) ≠ 0 := hc.ne'
  have hη := eta_cont ell a ε1
  have hG := gam_cont ell a ha
  have hX := epsX_cont ell a
  have hcs := cs_cont ell a
  have hnu : ContinuousAt (fun p : ℝ × ℝ × ℝ => nuC ell (rhoH p.1)) (0, 0, 0) := by unfold nuC rhoH; fun_prop
  have e0 := eta0 ell a ε1
  have h1 : (1 - etaR ell 0 (csOf a (rhoTs ell 0)) (rhoH 0) ε1) ≠ 0 := by rw [e0]; linarith
  have h2 : 1 + ((1 + etaR ell 0 (csOf a (rhoTs ell 0)) (rhoH 0) ε1) * (1 + ε2) / (1 - etaR ell 0 (csOf a (rhoTs ell 0)) (rhoH 0) ε1) - 1) ≠ 0 := by
    rw [e0]
    have : 0 < (1 + ε1) * (1 + ε2) / (1 - ε1) := by apply div_pos <;> nlinarith
    intro h; linarith [this]
  unfold Psi cwR C1R CTR
  have hE : ContinuousAt (fun p : ℝ × ℝ × ℝ => Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell * p.2.1)) (0, 0, 0) := by fun_prop
  have hE2 : ContinuousAt (fun p : ℝ × ℝ × ℝ => Real.exp (3 * (ell : ℝ) * Real.log ell * p.2.1)) (0, 0, 0) := by fun_prop
  have hSs : ContinuousAt (fun p : ℝ × ℝ × ℝ => Estar ell (Ssr ell p.1)) (0, 0, 0) := by
    unfold Estar Ssr rhoH; fun_prop
  unfold wexp at *
  fun_prop (disch := first | exact h1 | exact h2 | exact hne | simpa using hne | simpa using h1 | simpa using h2)

open Filter Topology in
/-- **uniform positivity**: a neighbourhood of `(s, x, K) = (0, 0, 0)` on which `Psi` is bounded below by a positive constant. -/
theorem cw_uniform (ell : ℕ) (hell : 0 < ell) (a ε1 ε2 m : ℝ) (ha : 0 < a) (hε1 : 0 < ε1) (hε1' : ε1 < 1)
    (hε2 : 0 < ε2) (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ c : ℝ, 0 < c ∧ ∀ s x K : ℝ, |s| < δ → |x| < δ → |K| < δ → c ≤ Psi ell a ε1 ε2 m s x K := by
  have h0 := Psi_zero_pos ell hell a ε1 ε2 m ha hε1 hε1' hε2 hm
  have hc := psi_cont ell a ε1 ε2 m ha hε1 hε1' hε2
  have hev : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ), (0 : ℝ)), Psi ell a ε1 ε2 m 0 0 0 / 2 < Psi ell a ε1 ε2 m p.1 p.2.1 p.2.2 :=
    hc.eventually (lt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, Psi ell a ε1 ε2 m 0 0 0 / 2, by linarith, fun s x K hs hx hK => ?_⟩
  have hd : dist (s, x, K) ((0 : ℝ), (0 : ℝ), (0 : ℝ)) < δ := by
    rw [Prod.dist_eq, Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt hs (max_lt hx hK)
  exact (hball hd).le

end AdalyFormal.M1Num

#print axioms AdalyFormal.M1Num.Psi_zero_pos
#print axioms AdalyFormal.M1Num.psi_cont
#print axioms AdalyFormal.M1Num.cw_uniform
