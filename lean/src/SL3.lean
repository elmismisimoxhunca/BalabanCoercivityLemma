import SL2

/-!
# SL3 -- assembly: slice coercivity at `U` from the flat inequality, then `Ginv` coercivity (abstract)

* `slice_from_flat`: the flat inequality `c1‖x‖² ≤ n²(Φ1 x + ‖R1 D1* x‖²)` (from `scaled_G1inv2_simple` + B1 at
  `U = 1`), the bound `‖R1 D1* x‖ ≤ γ‖x‖` on the `U`-slice (SL2) and a drift `Φ1 x ≤ (1+t) ΦU x + e‖x‖²` give
  `(c1 - n²γ² - n²e)/(1+t) · ‖x‖² ≤ n² ΦU x`.
* `ginv_of_slice` (the B1 assembly): if `G = Y + ‖T A‖²` (B1: `Y = ⟪A',ΔA'⟫ + mass(A')`), `cs‖A'‖² ≤ Y`
  (slice coercivity) and `‖A - A'‖² ≤ p‖TA‖²` (Poincare on `N(Q')` + NF2b), then `‖A‖² ≤ max(2/cs, 2p) G`.
* `delta_prime_absorb`: `|Δ'(A')| ≤ θ‖A'‖²` turns curl-coercivity into `Δ`-coercivity with `cs - θ`.
-/
set_option autoImplicit false
namespace AdalyFormal.SliceCoerc

theorem slice_from_flat (nsq c1 γ e t normx2 Φ1 ΦU R1x : ℝ) (hn : 0 ≤ nsq) (ht : 0 ≤ t)
    (hflat : c1 * normx2 ≤ nsq * (Φ1 + R1x ^ 2))
    (hR : R1x ^ 2 ≤ γ ^ 2 * normx2)
    (hdrift : Φ1 ≤ (1 + t) * ΦU + e * normx2) :
    (c1 - nsq * γ ^ 2 - nsq * e) / (1 + t) * normx2 ≤ nsq * ΦU := by
  have h1t : 0 < 1 + t := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ h1t]
  have a1 : nsq * R1x ^ 2 ≤ nsq * (γ ^ 2 * normx2) := mul_le_mul_of_nonneg_left hR hn
  have a2 : nsq * Φ1 ≤ nsq * ((1 + t) * ΦU + e * normx2) := mul_le_mul_of_nonneg_left hdrift hn
  nlinarith

theorem delta_prime_absorb (cs θ normx2 curl2 dp mass : ℝ)
    (hs : cs * normx2 ≤ curl2 + mass) (hdp : |dp| ≤ θ * normx2) :
    (cs - θ) * normx2 ≤ (curl2 + dp) + mass := by
  have := neg_abs_le dp
  nlinarith

theorem ginv_of_slice (cs p normA2 normAp2 normD2 Y T2 G : ℝ) (hcs : 0 < cs)
    (hT2 : 0 ≤ T2) (hAp : 0 ≤ normAp2)
    (htri : normA2 ≤ 2 * normAp2 + 2 * normD2)
    (hB1 : G = Y + T2) (hslice : cs * normAp2 ≤ Y) (hpoinc : normD2 ≤ p * T2) :
    normA2 ≤ max (2 / cs) (2 * p) * G := by
  have hY : 0 ≤ Y := le_trans (mul_nonneg hcs.le hAp) hslice
  have hm1 : 2 / cs ≤ max (2 / cs) (2 * p) := le_max_left _ _
  have hm2 : 2 * p ≤ max (2 / cs) (2 * p) := le_max_right _ _
  have e1 : 2 * normAp2 ≤ 2 / cs * Y := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcs]; nlinarith
  have e2 : 2 / cs * Y ≤ max (2 / cs) (2 * p) * Y := mul_le_mul_of_nonneg_right hm1 hY
  have e3 : 2 * normD2 ≤ 2 * p * T2 := by nlinarith
  have e4 : 2 * p * T2 ≤ max (2 / cs) (2 * p) * T2 := mul_le_mul_of_nonneg_right hm2 hT2
  rw [hB1]; nlinarith

#print axioms slice_from_flat
#print axioms delta_prime_absorb
#print axioms ginv_of_slice

end AdalyFormal.SliceCoerc
