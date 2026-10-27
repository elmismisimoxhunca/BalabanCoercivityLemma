import Mathlib

/-!
# ASC2 -- the FlatExt-derived constants do not alter the structure: `nsq * S^2` is `n`-free.

Pure real algebra.  With `n = s^2`, `aE = sqrt(729 n^3) = 27 n s`, `bE = sqrt(78732 n) = 162 sqrt3 s`, `q = sqrt(1/n^3) = 1/(n s)`,
`δ = sqrt12 ρ/n = 2 sqrt3 ρ/n`, `P = C n` (`C^2 = max(6, 16/(3a))`), `ε0 = 6ρ q`, the smallness quantity of `hsmall`
`S = A (δ P + A P^2 (δ + Â ε0)) + δ`, `A = Â q`, `Â = (bE + δ aE)/(1 - ε0 aE)` satisfies `n * S = Stil(ρ, C)` EXACTLY:
no `n`, no `k`, no volume.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.AsmM0

/-- `W(ρ) = 54 sqrt3 (3+ρ)/(1-162ρ)` -/
noncomputable def Wc (R3 ρ : ℝ) : ℝ := 54 * R3 * (3 + ρ) / (1 - 162 * ρ)

/-- `V(ρ) = W C^2 (2 sqrt3 ρ + 324 sqrt3 ρ (3+ρ)/(1-162ρ))` -/
noncomputable def Vc (R3 C ρ : ℝ) : ℝ := Wc R3 ρ * C ^ 2 * (2 * R3 * ρ + 324 * R3 * ρ * (3 + ρ) / (1 - 162 * ρ))

/-- `S̃(ρ, C) = W (2 sqrt3 ρ C + V) + 2 sqrt3 ρ` -/
noncomputable def Stil (R3 C ρ : ℝ) : ℝ := Wc R3 ρ * (2 * R3 * ρ * C + Vc R3 C ρ) + 2 * R3 * ρ

theorem S_scaling (n s R3 C ρ : ℝ) (hs : 0 < s) (hn : n = s ^ 2) (hρ : 0 < 1 - 162 * ρ)
    (aE bE q δ P ε0 : ℝ) (haE : aE = 27 * n * s) (hbE : bE = 162 * R3 * s) (hq : q = 1 / (n * s))
    (hδ : δ = 2 * R3 * ρ / n) (hP : P = C * n) (hε0 : ε0 = 6 * ρ * q) :
    n * ((((bE + δ * aE) / (1 - ε0 * aE)) * q) * (δ * P + (((bE + δ * aE) / (1 - ε0 * aE)) * q) * P ^ 2
        * (δ + ((bE + δ * aE) / (1 - ε0 * aE)) * ε0)) + δ) = Stil R3 C ρ := by
  have hn0 : 0 < n := by rw [hn]; positivity
  have hns : n * s ≠ 0 := by positivity
  have hεa : ε0 * aE = 162 * ρ := by
    rw [hε0, hq, haE]; field_simp; ring
  have hden : 1 - ε0 * aE = 1 - 162 * ρ := by rw [hεa]
  have hhat : (bE + δ * aE) / (1 - ε0 * aE) = 54 * R3 * s * (3 + ρ) / (1 - 162 * ρ) := by
    rw [hden, hbE, hδ, haE]; field_simp; ring
  rw [hhat]
  have hA : 54 * R3 * s * (3 + ρ) / (1 - 162 * ρ) * q = Wc R3 ρ / n := by
    rw [hq]; unfold Wc; field_simp
  rw [hA]
  have hdelta : δ = 2 * R3 * ρ / n := hδ
  have hAe : 54 * R3 * s * (3 + ρ) / (1 - 162 * ρ) * ε0 = 324 * R3 * ρ * (3 + ρ) / (1 - 162 * ρ) / n := by
    rw [hε0, hq]; field_simp; ring
  rw [hAe, hdelta, hP]
  unfold Stil Vc Wc
  have h1 : (1 - 162 * ρ) ≠ 0 := ne_of_gt hρ
  field_simp

#print axioms S_scaling

end AdalyFormal.AsmM0
