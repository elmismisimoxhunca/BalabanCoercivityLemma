import NJ8Eb

/-!
# NJ11Num -- explicit numeric threshold: `ε₀ ≤ 1/(1000 ell⁴)` implies every hypothesis of `H0_bijective_of_small`.
-/
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

theorem exp_two_sub_one_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10) : Real.exp (2 * ρ) - 1 ≤ 5 / 2 * ρ := by
  rcases h0.eq_or_lt with rfl | hp
  · simp
  · have hx : 0 < 2 * ρ := by positivity
    have hlt : 2 * ρ < 1 := by linarith
    have := Real.exp_bound_div_one_sub_of_interval' hx hlt
    have h2 : Real.exp (2 * ρ) ≤ 1 / (1 - 2 * ρ) := this.le
    have h3 : 1 / (1 - 2 * ρ) ≤ 1 + 5 / 2 * ρ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith

theorem e2Majorant_le_twelve {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10) : e2Majorant ρ ≤ 12 * ρ := by
  have he := exp_two_sub_one_le h0 h1
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hg : gInvMajorant ρ ≤ 2.7 := by unfold gInvMajorant; linarith
  have hexp0 : 0 ≤ Real.exp (2 * ρ) - 1 := exp_two_rho_sub_one_nonneg h0
  unfold e2Majorant e1Majorant
  have h1' : (Real.exp (2 * ρ) - 1) * gInvMajorant ρ ≤ (5 / 2 * ρ) * 2.7 :=
    mul_le_mul he hg (gInvMajorant_nonneg h0) (by positivity)
  nlinarith [h1', he, hpi, h0]

#print axioms e2Majorant_le_twelve

end AdalyFormal.NonflatJet
