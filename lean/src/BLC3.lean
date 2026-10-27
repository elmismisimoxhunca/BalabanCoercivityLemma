import BLC2

/-!
# BLC3 -- scaling of the gluing constants (m2_ballcharts, 2026-10-15)

`glue_scale`: if `t₁ ≤ a X u`, `t₂ ≤ b X u²`, `τ ≤ c X`, `κ₁ ≤ d u`, `κ₂ ≤ e u²` with `0 ≤ X ≤ 1`, `0 ≤ u`, then
`glueT1 t₁ τ κ₁ ≤ sc1 a c d · X u` and `glueT2 t₁ t₂ τ κ₁ κ₂ ≤ sc2 a b c d e · X u²`.  So one gluing level maps the scale
class `(X u, X u²)` to itself with explicit coefficients (`X = 12 M α₀`, `u = ℓ^{-(j-1)}`): this is what keeps the
three levels from compounding with `k`.  Also `kap_bounds`: `κ₁(s-12) ≤ 6/s`, `κ₂(s-12) ≤ 128/s²` for `s ≥ 24`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2BallCharts

open AdalyFormal.M2Glue2

noncomputable def sk (a c d : ℝ) : ℝ := d * c + 4 * a
noncomputable def sc1 (a c d : ℝ) : ℝ := a + 9 / 2 * sk a c d
noncomputable def sc2 (a b c d e : ℝ) : ℝ :=
  b + 9 * a * sk a c d + 81 / 4 * sk a c d ^ 2 + 9 / 2 * (e * c + 8 * d * a + 4 * b + 28 * a ^ 2)
    + 27 / 2 * sk a c d ^ 2

theorem sk_nonneg {a c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) : 0 ≤ sk a c d := by
  unfold sk; positivity

theorem sc1_nonneg {a c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) : 0 ≤ sc1 a c d := by
  unfold sc1; have := sk_nonneg ha hc hd; positivity

theorem sc2_nonneg {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ sc2 a b c d e := by
  unfold sc2; have := sk_nonneg ha hc hd; positivity

theorem glue_scale {t1 t2 τ κ1 κ2 a b c d e X u : ℝ} (hX0 : 0 ≤ X) (hX1 : X ≤ 1) (hu : 0 ≤ u)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (h1 : 0 ≤ t1) (h1' : t1 ≤ a * X * u) (h2 : 0 ≤ t2) (h2' : t2 ≤ b * X * u ^ 2)
    (hτ : 0 ≤ τ) (hτ' : τ ≤ c * X) (hk1 : 0 ≤ κ1) (hk1' : κ1 ≤ d * u) (hk2 : 0 ≤ κ2) (hk2' : κ2 ≤ e * u ^ 2) :
    glueT1 t1 τ κ1 ≤ sc1 a c d * X * u ∧ glueT2 t1 t2 τ κ1 κ2 ≤ sc2 a b c d e * X * u ^ 2 := by
  have hK0 : 0 ≤ glueK t1 τ κ1 := by unfold glueK; positivity
  have hkτ : κ1 * τ ≤ (d * u) * (c * X) := mul_le_mul hk1' hτ' hτ (by positivity)
  have hK : glueK t1 τ κ1 ≤ sk a c d * X * u := by
    unfold glueK sk
    have : (d * u) * (c * X) = d * c * X * u := by ring
    nlinarith
  have hsk := sk_nonneg ha hc hd
  have hXX : X * X ≤ X := by nlinarith
  -- squares and products in the scale class
  have p1 : t1 * glueK t1 τ κ1 ≤ a * sk a c d * X * u ^ 2 := by
    calc t1 * glueK t1 τ κ1 ≤ (a * X * u) * (sk a c d * X * u) := mul_le_mul h1' hK hK0 (by positivity)
      _ = a * sk a c d * u ^ 2 * (X * X) := by ring
      _ ≤ a * sk a c d * u ^ 2 * X := mul_le_mul_of_nonneg_left hXX (by positivity)
      _ = a * sk a c d * X * u ^ 2 := by ring
  have p2 : glueK t1 τ κ1 * glueK t1 τ κ1 ≤ sk a c d ^ 2 * X * u ^ 2 := by
    calc glueK t1 τ κ1 * glueK t1 τ κ1 ≤ (sk a c d * X * u) * (sk a c d * X * u) := mul_le_mul hK hK hK0 (by positivity)
      _ = sk a c d ^ 2 * u ^ 2 * (X * X) := by ring
      _ ≤ sk a c d ^ 2 * u ^ 2 * X := mul_le_mul_of_nonneg_left hXX (by positivity)
      _ = sk a c d ^ 2 * X * u ^ 2 := by ring
  have p3 : t1 ^ 2 ≤ a ^ 2 * X * u ^ 2 := by
    calc t1 ^ 2 = t1 * t1 := by ring
      _ ≤ (a * X * u) * (a * X * u) := mul_le_mul h1' h1' h1 (by positivity)
      _ = a ^ 2 * u ^ 2 * (X * X) := by ring
      _ ≤ a ^ 2 * u ^ 2 * X := mul_le_mul_of_nonneg_left hXX (by positivity)
      _ = a ^ 2 * X * u ^ 2 := by ring
  have p4 : κ2 * τ ≤ e * c * X * u ^ 2 := by
    calc κ2 * τ ≤ (e * u ^ 2) * (c * X) := mul_le_mul hk2' hτ' hτ (by positivity)
      _ = e * c * X * u ^ 2 := by ring
  have p5 : κ1 * t1 ≤ d * a * X * u ^ 2 := by
    calc κ1 * t1 ≤ (d * u) * (a * X * u) := mul_le_mul hk1' h1' h1 (by positivity)
      _ = d * a * X * u ^ 2 := by ring
  constructor
  · unfold glueT1 sc1; nlinarith
  · unfold glueT2 sc2
    nlinarith

theorem kap_bounds {s : ℝ} (hs : 24 ≤ s) :
    kap1 (s - 12) ≤ 6 / s ∧ kap2 (s - 12) ≤ 128 / s ^ 2 ∧ 0 ≤ kap1 (s - 12) ∧ 0 ≤ kap2 (s - 12) := by
  have hw : s / 2 ≤ s - 12 := by linarith
  have hw0 : 0 < s - 12 := by linarith
  have hs0 : 0 < s := by linarith
  have i1 : 1 / (s - 12) ≤ 2 / s := by
    rw [div_le_div_iff₀ hw0 hs0]; linarith
  have i2 : 1 / (s - 12) ^ 2 ≤ 4 / s ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have i3 : 32 / s ^ 2 ≤ 2 / s := by
    rw [div_le_div_iff₀ (by positivity) hs0]; nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold kap1
    have e1 : 2 / (s - 12) = 2 * (1 / (s - 12)) := by ring
    have e2 : 8 / (s - 12) ^ 2 = 8 * (1 / (s - 12) ^ 2) := by ring
    have e3 : 6 / s = 2 * (2 / s) + 2 / s := by ring
    rw [e1, e2, e3]
    have : 8 * (1 / (s - 12) ^ 2) ≤ 32 / s ^ 2 := by
      have : 8 * (4 / s ^ 2) = 32 / s ^ 2 := by ring
      linarith
    linarith
  · unfold kap2
    have e2 : 32 / (s - 12) ^ 2 = 32 * (1 / (s - 12) ^ 2) := by ring
    have : 32 * (4 / s ^ 2) = 128 / s ^ 2 := by ring
    rw [e2]; linarith
  · unfold kap1; positivity
  · unfold kap2; positivity

end AdalyFormal.M2BallCharts
