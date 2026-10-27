import Mathlib

/-!
# MA2 -- the real-number assembly of the M1 inequality (lane m1_assembly_20261014)

Pure real arithmetic (no lattice objects).  Variables (all at one fixed configuration):
`n = ell^k`, `xx = ||y||_w^2`, `X = G - a n beta^2`, `Xbox` = curl_U energy of `y` on the good boxes, `c12` = flat curl energy of `y` on the good boxes,
`Kq` = unit-torus curl energy of the restriction on good unit plaquettes, `dd` = bond defect on good unit bonds, `beta = ||C Bt||`, `bt = ||Bt||`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace AdalyFormal.M1Assembly

/-- the explicit constant produced by the M1 route. -/
noncomputable def gam1 (γf a ε' εJ ε1 Et dC cB : ℝ) : ℝ :=
  (1 - ε') * (γf - (Et * a + 128 * dC ^ 2) * cB ^ 2) / (4 / (1 - ε1) + Et) - (ε' * a + 2 * εJ) * cB ^ 2

theorem assemble_real (n γf a ε' εJ cw ν δc2 q dC cB ε1 Et : ℝ)
    (X xx β bt Kq Xbox c12 dd g : ℝ)
    (hn : 0 < n) (hcw : 0 < cw) (hε1 : 0 < ε1) (hε1' : ε1 < 1) (ha : 0 ≤ a) (hν : 0 ≤ ν) (hδ : 0 ≤ δc2) (hq : 0 ≤ q)
    (hxx : 0 ≤ xx) (hβ : 0 ≤ β) (hbt : 0 ≤ bt) (hcB : 0 ≤ cB) (hε'0 : 0 ≤ ε') (hε'1 : ε' ≤ 1) (hεJ : 0 ≤ εJ)
    (hEt : (8 * ν / (1 - ε1) + 4 * δc2 + 128 * q) / cw ≤ Et)
    (h1 : cw * xx ≤ X + a * n * β ^ 2)
    (h2 : (1 - ε1) * Xbox ≤ X + 2 * ν * xx)
    (h3 : c12 ≤ 2 * Xbox + 2 * δc2 * xx)
    (h4 : n * Kq ≤ c12)
    (h5 : γf * bt ^ 2 ≤ 2 * Kq + 64 * dd)
    (h7 : dd ≤ 2 * dC ^ 2 * β ^ 2 + 2 * (q / n) * xx)
    (h9 : β ≤ cB * bt)
    (h10 : (1 - ε') * (X / n) - (ε' * a + 2 * εJ) * β ^ 2 ≤ g) :
    gam1 γf a ε' εJ ε1 Et dC cB * bt ^ 2 ≤ g := by
  have hd1 : 0 < 1 - ε1 := by linarith
  set c4 := 4 / (1 - ε1) with hc4
  have hc4p : 0 < c4 := by positivity
  set E := 8 * ν / (1 - ε1) + 4 * δc2 + 128 * q with hE
  have hE0 : 0 ≤ E := by positivity
  have hEt0 : 0 ≤ Et := le_trans (div_nonneg hE0 hcw.le) hEt
  -- Xbox bound
  have hX1 : Xbox ≤ (X + 2 * ν * xx) / (1 - ε1) := by rw [le_div_iff₀ hd1]; linarith
  -- s1 : n gamma bt^2 <= 2 c12 + 128 n dC^2 beta^2 + 128 q xx
  have s1 : n * (γf * bt ^ 2) ≤ 2 * c12 + 128 * n * dC ^ 2 * β ^ 2 + 128 * q * xx := by
    have hs := mul_le_mul_of_nonneg_left h5 hn.le
    have hk : n * (2 * Kq + 64 * dd) ≤ 2 * c12 + 64 * (n * dd) := by nlinarith
    have hdd : n * dd ≤ 2 * n * dC ^ 2 * β ^ 2 + 2 * q * xx := by
      have := mul_le_mul_of_nonneg_left h7 hn.le
      have e : n * (2 * (q / n) * xx) = 2 * q * xx := by field_simp
      nlinarith
    nlinarith
  -- s2 : n gamma bt^2 <= c4 X + E xx + 128 n dC^2 beta^2
  have s2 : n * (γf * bt ^ 2) ≤ c4 * X + E * xx + 128 * n * dC ^ 2 * β ^ 2 := by
    have e1 : 4 * Xbox ≤ c4 * X + (8 * ν / (1 - ε1)) * xx := by
      have h4X : 4 * Xbox ≤ 4 * ((X + 2 * ν * xx) / (1 - ε1)) := by linarith
      have : 4 * ((X + 2 * ν * xx) / (1 - ε1)) = c4 * X + (8 * ν / (1 - ε1)) * xx := by
        rw [hc4]; field_simp; ring
      linarith
    have hEx : E * xx = (8 * ν / (1 - ε1)) * xx + 4 * δc2 * xx + 128 * q * xx := by rw [hE]; ring
    linarith [s1, h3, e1, hEx]
  -- s3 : E xx <= Et (X + a n beta^2)
  have s3 : E * xx ≤ Et * (X + a * n * β ^ 2) := by
    have hxx' : xx ≤ (X + a * n * β ^ 2) / cw := by rw [le_div_iff₀ hcw]; linarith
    have h0 : E * xx ≤ E * ((X + a * n * β ^ 2) / cw) := mul_le_mul_of_nonneg_left hxx' hE0
    have hX0 : 0 ≤ X + a * n * β ^ 2 := by nlinarith
    have : E * ((X + a * n * β ^ 2) / cw) = (E / cw) * (X + a * n * β ^ 2) := by field_simp
    have h6 : (E / cw) * (X + a * n * β ^ 2) ≤ Et * (X + a * n * β ^ 2) :=
      mul_le_mul_of_nonneg_right hEt hX0
    linarith
  -- s4 : gamma bt^2 <= (c4+Et)(X/n) + (Et a + 128 dC^2) beta^2
  have s4 : γf * bt ^ 2 ≤ (c4 + Et) * (X / n) + (Et * a + 128 * dC ^ 2) * β ^ 2 := by
    have h : n * (γf * bt ^ 2) ≤ n * ((c4 + Et) * (X / n) + (Et * a + 128 * dC ^ 2) * β ^ 2) := by
      have e1 : n * ((c4 + Et) * (X / n) + (Et * a + 128 * dC ^ 2) * β ^ 2)
          = (c4 + Et) * X + Et * a * n * β ^ 2 + 128 * n * dC ^ 2 * β ^ 2 := by
        field_simp
        ring
      rw [e1]
      nlinarith
    exact le_of_mul_le_mul_left h hn
  have s5 : β ^ 2 ≤ cB ^ 2 * bt ^ 2 := by
    have := pow_le_pow_left₀ hβ h9 2
    rw [mul_pow] at this; exact this
  have hc0 : 0 ≤ Et * a + 128 * dC ^ 2 := by positivity
  have h4E : 0 < c4 + Et := by linarith
  have s6 : (γf - (Et * a + 128 * dC ^ 2) * cB ^ 2) * bt ^ 2 / (c4 + Et) ≤ X / n := by
    rw [div_le_iff₀ h4E]
    have h6' := mul_le_mul_of_nonneg_left s5 hc0
    have e3 : X / n * (c4 + Et) = (c4 + Et) * (X / n) := by ring
    rw [e3]
    nlinarith
  have s7 : (1 - ε') * ((γf - (Et * a + 128 * dC ^ 2) * cB ^ 2) * bt ^ 2 / (c4 + Et)) ≤ (1 - ε') * (X / n) :=
    mul_le_mul_of_nonneg_left s6 (by linarith)
  have s8 : (ε' * a + 2 * εJ) * β ^ 2 ≤ (ε' * a + 2 * εJ) * (cB ^ 2 * bt ^ 2) :=
    mul_le_mul_of_nonneg_left s5 (by positivity)
  have e2 : gam1 γf a ε' εJ ε1 Et dC cB * bt ^ 2
      = (1 - ε') * ((γf - (Et * a + 128 * dC ^ 2) * cB ^ 2) * bt ^ 2 / (c4 + Et))
        - (ε' * a + 2 * εJ) * (cB ^ 2 * bt ^ 2) := by
    unfold gam1; rw [hc4]; field_simp
  rw [e2]; linarith

end AdalyFormal.M1Assembly

#print axioms AdalyFormal.M1Assembly.assemble_real
