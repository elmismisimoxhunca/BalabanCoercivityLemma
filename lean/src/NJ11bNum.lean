import NJ11Num

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open EstimatesLayer.E1E3

theorem pi_div_le : Real.pi / (2 * Real.sqrt 2) ≤ 6 / 5 := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hs : (1.41 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem loopFactorBound_le (ell : ℕ) : (SmallnessBridge.Assemble.loopFactorBound ell : ℝ) ≤ 8 * ell := by
  unfold SmallnessBridge.Assemble.loopFactorBound
  have : 2 * ell + 6 * (ell - 1) ≤ 8 * ell := by omega
  exact_mod_cast this

theorem rhoOf_le {ell : ℕ} (ε0 : ℝ) (hε0 : 0 ≤ ε0) : rhoOf ell ε0 ≤ 8 * ell * (6 / 5 * ε0) := by
  unfold rhoOf
  have h1 := pi_div_le
  have h2 := loopFactorBound_le ell
  calc _ ≤ (8 * (ell : ℝ)) * ((Real.pi / (2 * Real.sqrt 2)) * ε0) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ ≤ (8 * (ell : ℝ)) * (6 / 5 * ε0) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hε0) (by positivity)

/-- **Explicit threshold.**  `0 ≤ ε₀ ≤ 1/(1000 ell⁴)` gives all numeric hypotheses of `H0_bijective_of_small`. -/
theorem numeric_small {ell : ℕ} (hell : 0 < ell) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hle : ε0 ≤ 1 / (1000 * (ell : ℝ) ^ 4)) :
    rhoOf ell ε0 < Real.pi / 2 ∧
      8 * ell * ε0 + 8 * e2Majorant (rhoOf ell ε0) < 1 / (ell : ℝ) ^ 3 := by
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpos : (0 : ℝ) < (ell : ℝ) ^ 4 := by positivity
  have hρ := rhoOf_le (ell := ell) ε0 hε0
  have hρ0 : 0 ≤ rhoOf ell ε0 := by unfold rhoOf; positivity
  -- ε0 * ell^4 ≤ 1/1000
  have hk : ε0 * (ell : ℝ) ^ 4 ≤ 1 / 1000 := by
    have := mul_le_mul_of_nonneg_right hle hpos.le
    calc _ ≤ 1 / (1000 * (ell : ℝ) ^ 4) * (ell : ℝ) ^ 4 := this
      _ = 1 / 1000 := by field_simp
  have hell3 : (ell : ℝ) ≤ (ell : ℝ) ^ 3 := by nlinarith [sq_nonneg ((ell : ℝ) - 1)]
  have hρ' : rhoOf ell ε0 ≤ 48 / 5 * (ell * ε0) := by nlinarith [hρ]
  have hsmall10 : rhoOf ell ε0 ≤ 1 / 10 := by
    have : ell * ε0 ≤ 1 / 1000 := by
      have h4 : ell * ε0 ≤ ell ^ 4 * ε0 := by
        have : (ell : ℝ) ≤ (ell : ℝ) ^ 4 := by nlinarith [sq_nonneg ((ell : ℝ) - 1), sq_nonneg ((ell : ℝ)^2 - 1)]
        nlinarith
      nlinarith [hk]
    nlinarith [hρ']
  refine ⟨lt_of_le_of_lt hsmall10 (by nlinarith [Real.pi_gt_three]), ?_⟩
  have h12 := e2Majorant_le_twelve hρ0 hsmall10
  have hmain : ell * ε0 * (ell : ℝ) ^ 3 ≤ 1 / 1000 := by nlinarith [hk]
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [hmain, hρ', h12, hρ0]

#print axioms numeric_small

end AdalyFormal.NonflatJet
