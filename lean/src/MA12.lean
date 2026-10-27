import W4N5

/-!
# MA12 -- real-parameter form of the W4 constant `cwW4` (lane m1_assembly_20261014)

`cwR ell x K ...` is `cwW4 ell M kappa c W ...` with `W` replaced by `x = 1/W` and `KG ell M kappa c` replaced by a free real `K`
(`cwW4_eq_cwR`).  Used for the uniform positivity of `cwW4` (continuity at `(s, x, K) = (0, 0, 0)`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1Num

open AdalyFormal.M1IMS AdalyFormal.M1GaugeW4 AdalyFormal.TowerLoc

/-- `exp (2 ell^2 log ell * x)`, `x = 1/W`. -/
noncomputable def wexp (ell : ℕ) (x : ℝ) : ℝ := Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell * x)
noncomputable def qexp (ell : ℕ) (x : ℝ) : ℝ := Real.exp (3 * (ell : ℝ) * Real.log ell * x)

noncomputable def etaR (ell : ℕ) (x : ℝ) (cs ρ ε1 : ℝ) : ℝ :=
  ε1 + (1 + 1 / ε1) * (12 * ρ ^ 2 * (ell : ℝ) ^ 8 * (4 * ell / cs) ^ 2)
    + 2 * nuC ell ρ * ((ell : ℝ) * (Real.sqrt (12 / cs)
        + Real.sqrt 3 * (wexp ell x - 1) * (4 / cs))) ^ 2

noncomputable def CTR (ell : ℕ) (x K a cs γ : ℝ) : ℝ :=
  (5 * ((ell * Real.sqrt (48 / cs)) ^ 2 * (3 * K)
      + (4 * ell / cs) ^ 2 * (3 * (ell : ℝ) ^ 4 * K) *
          ((ell * (Real.sqrt (12 / cs) + Real.sqrt 3 * (wexp ell x - 1) * (4 / cs)))
            * Real.sqrt (max a 1) * γ) ^ 2
      + (4 * ell / cs) ^ 2 * (max a 1 * (9 * a * K))
      + (4 * ell / cs) ^ 2 * (9 * a * K * max a 1)
      + (4 * ell / cs) ^ 2 * (9 * a * K * γ ^ 2)))
    * ((ell * (Real.sqrt (12 / cs) + Real.sqrt 3 * (wexp ell x - 1) * (4 / cs)))
        * Real.sqrt (max a 1) * γ) ^ 2
    + 3 * K

noncomputable def C1R (ell : ℕ) (x K a cs γ CM ε2 : ℝ) : ℝ :=
  (1 + 1 / ε2) * (12 * (ell : ℝ) ^ 2 * K) + 2 * (1 + 1 / ε2) * CTR ell x K a cs γ + (1 + 1 / ε2) * CM

noncomputable def dDR (ell : ℕ) (x : ℝ) : ℝ := Real.sqrt 3 * (wexp ell x - 1)
noncomputable def dQR (ell : ℕ) (x a : ℝ) : ℝ := Real.sqrt a * (qexp ell x - 1)

noncomputable def epsXR (ell : ℕ) (x a ρ : ℝ) : ℝ :=
  (4 / csOf a ρ) * dQR ell x a + (4 / csOf a ρ) * dDR ell x * (Real.sqrt (max a 1) / Real.sqrt (csOf a ρ))
    + (Real.sqrt (48 / csOf a ρ) * dDR ell x + (8 / csOf a ρ) * dDR ell x ^ 2
        + (4 / csOf a ρ) * 1 * (2 * Real.sqrt (max a 1) * dQR ell x a + dQR ell x a ^ 2))
      * (Real.sqrt (max a 1) / csOf a ρ)

noncomputable def cwR (ell : ℕ) (x K a ρ ρh ε1 ε2 cP eX CM : ℝ) : ℝ :=
  (cP - ((1 + etaR ell x (csOf a ρ) ρh ε1) * (1 + ε2) * (2 * nuC ell ρh) / (1 - etaR ell x (csOf a ρ) ρh ε1)
      + (1 + etaR ell x (csOf a ρ) ρh ε1) * C1R ell x K a (csOf a ρ) (gamC ell a ρ eX) CM ε2
      + 2 * nuC ell ρh))
    / (1 + ((1 + etaR ell x (csOf a ρ) ρh ε1) * (1 + ε2) / (1 - etaR ell x (csOf a ρ) ρh ε1) - 1))

theorem wexp_eq (ell W : ℕ) : Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) = wexp ell ((W : ℝ)⁻¹) := by
  unfold wexp; rw [div_eq_mul_inv]

theorem qexp_eq (ell W : ℕ) : Real.exp (3 * (ell : ℝ) * Real.log ell / W) = qexp ell ((W : ℝ)⁻¹) := by
  unfold qexp; rw [div_eq_mul_inv]

theorem etaC_eq (ell W : ℕ) (cs ρ ε1 : ℝ) : etaC ell W cs ρ ε1 = etaR ell ((W : ℝ)⁻¹) cs ρ ε1 := by
  unfold etaC etaR; rw [wexp_eq]

theorem CTc_eq (ell M κ c W : ℕ) (a cs γ : ℝ) :
    CTc ell M κ c W a cs γ = CTR ell ((W : ℝ)⁻¹) (KG ell M κ c) a cs γ := by
  unfold CTc CTR; rw [wexp_eq]

theorem C1c_eq (ell M κ c W : ℕ) (a cs γ CM ε2 : ℝ) :
    C1c ell M κ c W a cs γ CM ε2 = C1R ell ((W : ℝ)⁻¹) (KG ell M κ c) a cs γ CM ε2 := by
  unfold C1c C1R; rw [CTc_eq]

theorem epsXnum_eq (ell W : ℕ) (a ρ : ℝ) : epsXnum ell W a ρ = epsXR ell ((W : ℝ)⁻¹) a ρ := by
  unfold epsXnum epsXR dDnum dQnum dDR dQR; rw [wexp_eq, qexp_eq]

theorem cwW4_eq (ell M κ c W : ℕ) (a ρ ρh ε1 ε2 cP eX CM : ℝ) :
    cwW4 ell M κ c W a ρ ρh ε1 ε2 cP eX CM = cwR ell ((W : ℝ)⁻¹) (KG ell M κ c) a ρ ρh ε1 ε2 cP eX CM := by
  unfold cwW4 cwR; rw [etaC_eq, C1c_eq]

end AdalyFormal.M1Num

#print axioms AdalyFormal.M1Num.cwW4_eq
#print axioms AdalyFormal.M1Num.epsXnum_eq
