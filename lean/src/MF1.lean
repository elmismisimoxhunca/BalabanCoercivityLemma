import Mathlib

/-!
# MF1 -- the real-arithmetic combination of the M0 route (no lattice objects).

Inputs (all reals; the lattice meaning is fixed by the consumer MF4):
`xx = ‖x‖²` (x = W_U A, the U-slice part of the U-minimiser), `X = ⟨x, Δ_U x⟩`, `β = ‖B_U‖` (B_U = C_U B̃), `bt² = ‖B̃‖²`,
`Kq` = unit curl energy of the flat top restriction of `x`, `K1` = unit curl energy of `B₁ = C₁ B̃`, `Kd` = unit curl energy of the
difference, `dd` = its bond energy, `cU2`/`c12` = squared masked curl norms of `x` at `U`/at `1`, `g` = genForm at `U`.
The hypotheses `h1..h10` are exactly the estimates MF2-MF4 supply; the conclusion is the explicit lower bound
`γ0M0form · bt² ≤ g`.
-/
set_option autoImplicit false

namespace AdalyFormal.M0Finish

/-- the explicit constant produced by the route (`Et` = the scaled error budget, `cB` = `‖C_U‖`-type bound). -/
noncomputable def gam0Form (γ a ε' εJ Et dC cB : ℝ) : ℝ :=
  (1 - ε') * (γ - (Et * a + 128 * dC ^ 2) * cB ^ 2) / (4 + Et) - (ε' * a + 2 * εJ) * cB ^ 2

theorem mf_combine (n γ Kh a θ δc dq dC cB ε' εJ : ℝ)
    (X xx β bt Kq K1 Kd dd cU2 c12 g : ℝ)
    (hn : 0 < n) (hKh : 0 ≤ Kh) (ha : 0 ≤ a) (hθ : 0 ≤ θ)
    (hxx : 0 ≤ xx) (hβ : 0 ≤ β) (hbt : 0 ≤ bt) (hcB : 0 ≤ cB)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' ≤ 1) (hεJ : 0 ≤ εJ)
    (h1 : xx ≤ n ^ 2 * Kh * (X + a * n * β ^ 2))
    (h2 : cU2 ≤ X + θ * xx)
    (h3 : c12 ≤ 2 * cU2 + 2 * δc ^ 2 * xx)
    (h4 : n * Kq ≤ c12)
    (h5 : K1 ≤ 2 * Kq + 2 * Kd)
    (h6 : Kd ≤ 32 * dd)
    (h7 : dd ≤ 2 * dC ^ 2 * β ^ 2 + 2 * dq ^ 2 * xx)
    (h8 : γ * bt ^ 2 ≤ K1)
    (h9 : β ≤ cB * bt)
    (h10 : (1 - ε') * (X / n) - (ε' * a + 2 * εJ) * β ^ 2 ≤ g) :
    gam0Form γ a ε' εJ ((4 * θ + 4 * δc ^ 2 + 128 * n * dq ^ 2) * n ^ 2 * Kh) dC cB * bt ^ 2 ≤ g := by
  set E := 4 * θ + 4 * δc ^ 2 + 128 * n * dq ^ 2 with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  set Et := E * n ^ 2 * Kh with hEt
  have hEt0 : 0 ≤ Et := by rw [hEt]; positivity
  -- s1 : n Kq ≤ 2X + (2θ + 2δc²) xx
  have s1 : n * Kq ≤ 2 * X + (2 * θ + 2 * δc ^ 2) * xx := by
    linear_combination h4 + h3 + 2 * h2
  -- s2 : γ bt² ≤ 2Kq + 128 dC² β² + 128 dq² xx
  have s2 : γ * bt ^ 2 ≤ 2 * Kq + 128 * dC ^ 2 * β ^ 2 + 128 * dq ^ 2 * xx := by
    linear_combination h8 + h5 + 2 * h6 + 64 * h7
  -- s3 : n γ bt² ≤ 4X + E xx + 128 n dC² β²
  have s3 : n * (γ * bt ^ 2) ≤ 4 * X + E * xx + 128 * n * dC ^ 2 * β ^ 2 := by
    have hs2 := mul_le_mul_of_nonneg_left s2 hn.le
    rw [hE]
    linear_combination hs2 + 2 * s1
  -- s4 : E xx ≤ Et X + Et a n β²
  have s4 : E * xx ≤ Et * X + Et * a * n * β ^ 2 := by
    have hs := mul_le_mul_of_nonneg_left h1 hE0
    rw [hEt]
    linear_combination hs
  -- s5 : γ bt² ≤ (4+Et) (X/n) + (Et a + 128 dC²) β²
  have s5 : γ * bt ^ 2 ≤ (4 + Et) * (X / n) + (Et * a + 128 * dC ^ 2) * β ^ 2 := by
    have h : n * (γ * bt ^ 2) ≤ n * ((4 + Et) * (X / n) + (Et * a + 128 * dC ^ 2) * β ^ 2) := by
      have e1 : n * ((4 + Et) * (X / n) + (Et * a + 128 * dC ^ 2) * β ^ 2)
          = (4 + Et) * X + Et * a * n * β ^ 2 + 128 * n * dC ^ 2 * β ^ 2 := by
        field_simp
        ring
      rw [e1]
      linear_combination s3 + s4
    exact le_of_mul_le_mul_left h hn
  -- s6 : β² ≤ cB² bt²
  have s6 : β ^ 2 ≤ cB ^ 2 * bt ^ 2 := by
    have := pow_le_pow_left₀ hβ h9 2
    rw [mul_pow] at this; exact this
  have hc0 : 0 ≤ Et * a + 128 * dC ^ 2 := by positivity
  -- s7 : (γ - (Et a + 128dC²) cB²) bt² / (4+Et) ≤ X/n
  have h4E : 0 < 4 + Et := by linarith
  have s7 : (γ - (Et * a + 128 * dC ^ 2) * cB ^ 2) * bt ^ 2 / (4 + Et) ≤ X / n := by
    rw [div_le_iff₀ h4E]
    have h6' := mul_le_mul_of_nonneg_left s6 hc0
    have e3 : X / n * (4 + Et) = (4 + Et) * (X / n) := by ring
    rw [e3]
    linear_combination s5 + h6' 
  have s8 : (1 - ε') * ((γ - (Et * a + 128 * dC ^ 2) * cB ^ 2) * bt ^ 2 / (4 + Et)) ≤ (1 - ε') * (X / n) :=
    mul_le_mul_of_nonneg_left s7 (by linarith)
  have s9 : (ε' * a + 2 * εJ) * β ^ 2 ≤ (ε' * a + 2 * εJ) * (cB ^ 2 * bt ^ 2) :=
    mul_le_mul_of_nonneg_left s6 (by positivity)
  have e2 : gam0Form γ a ε' εJ Et dC cB * bt ^ 2
      = (1 - ε') * ((γ - (Et * a + 128 * dC ^ 2) * cB ^ 2) * bt ^ 2 / (4 + Et))
        - (ε' * a + 2 * εJ) * (cB ^ 2 * bt ^ 2) := by
    unfold gam0Form; field_simp
  rw [e2]; linarith

theorem mf_combine_ub (n γ Kh a θ δc dq dC cB ε' εJ Et : ℝ)
    (X xx β bt Kq K1 Kd dd cU2 c12 g : ℝ)
    (hn : 0 < n) (hKh : 0 < Kh)
    (hEt : (4 * θ + 4 * δc ^ 2 + 128 * n * dq ^ 2) * n ^ 2 * Kh ≤ Et) (ha : 0 ≤ a) (hθ : 0 ≤ θ)
    (hxx : 0 ≤ xx) (hβ : 0 ≤ β) (hbt : 0 ≤ bt) (hcB : 0 ≤ cB)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' ≤ 1) (hεJ : 0 ≤ εJ)
    (h1 : xx ≤ n ^ 2 * Kh * (X + a * n * β ^ 2))
    (h2 : cU2 ≤ X + θ * xx)
    (h3 : c12 ≤ 2 * cU2 + 2 * δc ^ 2 * xx)
    (h4 : n * Kq ≤ c12)
    (h5 : K1 ≤ 2 * Kq + 2 * Kd)
    (h6 : Kd ≤ 32 * dd)
    (h7 : dd ≤ 2 * dC ^ 2 * β ^ 2 + 2 * dq ^ 2 * xx)
    (h8 : γ * bt ^ 2 ≤ K1)
    (h9 : β ≤ cB * bt)
    (h10 : (1 - ε') * (X / n) - (ε' * a + 2 * εJ) * β ^ 2 ≤ g) :
    gam0Form γ a ε' εJ Et dC cB * bt ^ 2 ≤ g := by
  set E := 4 * θ + 4 * δc ^ 2 + 128 * n * dq ^ 2 with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hEt0 : 0 ≤ Et := le_trans (mul_nonneg (mul_nonneg hE0 (sq_nonneg n)) hKh.le) hEt
  have hXp : 0 ≤ X + a * n * β ^ 2 := by
    have h := le_trans hxx h1
    have hc : 0 < n ^ 2 * Kh := by positivity
    by_contra hneg
    push_neg at hneg
    nlinarith
  -- s1 : n Kq ≤ 2X + (2θ + 2δc²) xx
  have s1 : n * Kq ≤ 2 * X + (2 * θ + 2 * δc ^ 2) * xx := by
    linear_combination h4 + h3 + 2 * h2
  -- s2 : γ bt² ≤ 2Kq + 128 dC² β² + 128 dq² xx
  have s2 : γ * bt ^ 2 ≤ 2 * Kq + 128 * dC ^ 2 * β ^ 2 + 128 * dq ^ 2 * xx := by
    linear_combination h8 + h5 + 2 * h6 + 64 * h7
  -- s3 : n γ bt² ≤ 4X + E xx + 128 n dC² β²
  have s3 : n * (γ * bt ^ 2) ≤ 4 * X + E * xx + 128 * n * dC ^ 2 * β ^ 2 := by
    have hs2 := mul_le_mul_of_nonneg_left s2 hn.le
    rw [hE]
    linear_combination hs2 + 2 * s1
  -- s4 : E xx ≤ Et X + Et a n β²
  have s4 : E * xx ≤ Et * X + Et * a * n * β ^ 2 := by
    have hs := mul_le_mul_of_nonneg_left h1 hE0
    have hs2 := mul_le_mul_of_nonneg_right hEt hXp
    linear_combination hs + hs2
  -- s5 : γ bt² ≤ (4+Et) (X/n) + (Et a + 128 dC²) β²
  have s5 : γ * bt ^ 2 ≤ (4 + Et) * (X / n) + (Et * a + 128 * dC ^ 2) * β ^ 2 := by
    have h : n * (γ * bt ^ 2) ≤ n * ((4 + Et) * (X / n) + (Et * a + 128 * dC ^ 2) * β ^ 2) := by
      have e1 : n * ((4 + Et) * (X / n) + (Et * a + 128 * dC ^ 2) * β ^ 2)
          = (4 + Et) * X + Et * a * n * β ^ 2 + 128 * n * dC ^ 2 * β ^ 2 := by
        field_simp
        ring
      rw [e1]
      linear_combination s3 + s4
    exact le_of_mul_le_mul_left h hn
  -- s6 : β² ≤ cB² bt²
  have s6 : β ^ 2 ≤ cB ^ 2 * bt ^ 2 := by
    have := pow_le_pow_left₀ hβ h9 2
    rw [mul_pow] at this; exact this
  have hc0 : 0 ≤ Et * a + 128 * dC ^ 2 := by positivity
  -- s7 : (γ - (Et a + 128dC²) cB²) bt² / (4+Et) ≤ X/n
  have h4E : 0 < 4 + Et := by linarith
  have s7 : (γ - (Et * a + 128 * dC ^ 2) * cB ^ 2) * bt ^ 2 / (4 + Et) ≤ X / n := by
    rw [div_le_iff₀ h4E]
    have h6' := mul_le_mul_of_nonneg_left s6 hc0
    have e3 : X / n * (4 + Et) = (4 + Et) * (X / n) := by ring
    rw [e3]
    linear_combination s5 + h6' 
  have s8 : (1 - ε') * ((γ - (Et * a + 128 * dC ^ 2) * cB ^ 2) * bt ^ 2 / (4 + Et)) ≤ (1 - ε') * (X / n) :=
    mul_le_mul_of_nonneg_left s7 (by linarith)
  have s9 : (ε' * a + 2 * εJ) * β ^ 2 ≤ (ε' * a + 2 * εJ) * (cB ^ 2 * bt ^ 2) :=
    mul_le_mul_of_nonneg_left s6 (by positivity)
  have e2 : gam0Form γ a ε' εJ Et dC cB * bt ^ 2
      = (1 - ε') * ((γ - (Et * a + 128 * dC ^ 2) * cB ^ 2) * bt ^ 2 / (4 + Et))
        - (ε' * a + 2 * εJ) * (cB ^ 2 * bt ^ 2) := by
    unfold gam0Form; field_simp
  rw [e2]; linarith

/-- the flat value: with no perturbation the constant is `γ/4`. -/
theorem gam0Form_flat (γ a cB : ℝ) : gam0Form γ a 0 0 0 0 cB = γ / 4 := by
  unfold gam0Form; ring

#print axioms mf_combine
#print axioms gam0Form_flat
#print axioms mf_combine_ub

end AdalyFormal.M0Finish
