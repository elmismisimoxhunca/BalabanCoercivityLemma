import W4N1
import GW6

/-!
# W4N2 -- `w4Num_exists`, `qsNum_small_exists` (lane m1_w4num_20261014)

Both numeric bundles of `GW9` are satisfied by explicit `k`-free, `U`-free choices:
`W := R * M * ell` with `R ≥ W₀(ell, a)`, `ε1 := 1/4`, and `12 M α₀ ≤ a₁(ell, a)` (resp. `a₂(ell)`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1W4Num

open AdalyFormal.M1GaugeW4
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (rho1 SstarM rho1_nonneg)
open AdalyFormal.W6 (CEp)

theorem rho1_le (M : ℕ) (α₀ : ℝ) (h : 0 ≤ α₀) :
    rho1 12 M α₀ ≤ 20 * ((12 : ℝ) * M * α₀) := by
  unfold AdalyFormal.TowerLoc.rho1
  have hp := Real.pi_lt_four
  have : 0 ≤ ((12 : ℕ) : ℝ) * M * α₀ := by positivity
  push_cast at *
  nlinarith

theorem rhoT_le_lin (ell M : ℕ) (hell : 1 ≤ ell) (α₀ : ℝ) (h : 0 ≤ α₀) :
    rhoT ell 12 M α₀ ≤ 260 * (ell : ℝ) ^ 2 * ((12 : ℝ) * M * α₀) := by
  have h1 := rhoT_le ell 12 M α₀ h hell
  have h2 := rho1_le M α₀ h
  have hl : (0 : ℝ) ≤ (ell : ℝ) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 13 * (ell : ℝ) ^ 2)
  linarith

/-- **`w4Num_exists`**: the numeric bundle `W4Num` holds with `W = R·M·ell`, `ε1 = 1/4`, as soon as `R ≥ W₀(ell,a)` and
`12 M α₀ ≤ a₁(ell,a)`.  `W₀, ε1, a₁` depend on `ell, a` only (not on `M, R, k, Lu, U`). -/
theorem w4Num_exists (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ W₀ : ℕ, 1 ≤ W₀ ∧ ∃ ε1 : ℝ, 0 < ε1 ∧ ∃ a₁ : ℝ, 0 < a₁ ∧
      ∀ M R : ℕ, 0 < M → W₀ ≤ R → ∀ α₀ : ℝ, 0 ≤ α₀ → (12 : ℝ) * M * α₀ ≤ a₁ →
        1 ≤ R * M * ell ∧ R * M * ell ≤ R * M * ell ∧ W4Num ell M 12 (R * M * ell) a α₀ ε1 := by
  obtain ⟨W₁, hW₁⟩ := w4Num_real ell hell a ha
  have hρ0 := rho0Of_pos ell (by omega) a ha
  have hl : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast (by omega : 0 < ell)
  refine ⟨max W₁ 1, le_max_right _ _, 1 / 4, by norm_num, rho0Of ell a / (260 * (ell : ℝ) ^ 2), by positivity, ?_⟩
  intro M R hM hR α₀ hα hsm
  have hRW : W₁ ≤ R * M * ell := by
    have : R ≤ R * M * ell := by
      calc R = R * 1 * 1 := by ring
        _ ≤ R * M * ell := Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) (by omega)
    exact le_trans (le_trans (le_max_left _ _) hR) this
  have h1 : 1 ≤ R * M * ell := by
    have : 1 ≤ R := le_trans (le_max_right _ _) hR
    exact Nat.mul_pos (Nat.mul_pos (by omega) hM) (by omega)
  have hT := rhoT_le_lin ell M (by omega) α₀ hα
  have h260 : 260 * (ell : ℝ) ^ 2 * ((12 : ℝ) * M * α₀) ≤ rho0Of ell a := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 260 * (ell : ℝ) ^ 2)).1 hsm
    linarith
  have hρT : rhoT ell 12 M α₀ ≤ rho0Of ell a := le_trans hT h260
  have hρ1 : rho1 12 M α₀ ≤ rho0Of ell a := by
    have := rho1_le M α₀ hα
    have h2 : (20 : ℝ) * ((12 : ℝ) * M * α₀) ≤ 260 * (ell : ℝ) ^ 2 * ((12 : ℝ) * M * α₀) := by
      have : (1 : ℝ) ≤ (ell : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ ell := by exact_mod_cast (by omega : 1 ≤ ell)
        nlinarith
      have : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
      nlinarith
    linarith
  obtain ⟨a1, a2, a3, a4⟩ := hW₁ (R * M * ell) hRW (rhoT ell 12 M α₀) (rho1 12 M α₀)
    (rhoT_nonneg ell 12 M α₀ hα) hρT (rho1_nonneg 12 M α₀ hα) hρ1
  exact ⟨h1, le_refl _, ⟨a1, a2, a3, a4⟩⟩

/-- **headline quantifier order**: `∃ m₀`, for `M = ell^m`, `m ≥ m₀`, `∃ R₀`, for `R ≥ R₀` there are `W ∈ [1, R M ell]`, `ε1 > 0`,
`a₁ > 0` with `W4Num` whenever `12 M α₀ ≤ a₁`. -/
theorem w4Num_exists_headline (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ∃ W : ℕ, 1 ≤ W ∧ W ≤ R * ell ^ m * ell ∧ ∃ ε1 : ℝ, 0 < ε1 ∧ ∃ a₁ : ℝ, 0 < a₁ ∧
        ∀ α₀ : ℝ, 0 ≤ α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₁ → W4Num ell (ell ^ m) 12 W a α₀ ε1 := by
  obtain ⟨W₀, hW₀, ε1, hε1, a₁, ha₁, h⟩ := w4Num_exists ell hell a ha
  refine ⟨0, fun m _ => ⟨W₀, fun R hR => ⟨R * ell ^ m * ell, ?_⟩⟩⟩
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  obtain ⟨h1, h2, _⟩ := h (ell ^ m) R hM hR 0 le_rfl (by simpa using ha₁.le)
  exact ⟨h1, h2, ε1, hε1, a₁, ha₁, fun α₀ hα hs => (h (ell ^ m) R hM hR α₀ hα hs).2.2⟩

/-- **`qsNum_small_exists`**: `QsNum` follows from `12 M α₀ ≤ a₂`, with `a₂` depending on `ell` only. -/
theorem qsNum_small_exists (ell : ℕ) (hell : 0 < ell) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ M : ℕ, ∀ α₀ : ℝ, 0 ≤ α₀ → (12 : ℝ) * M * α₀ ≤ a₂ → QsNum ell 12 M α₀ := by
  have hr := AdalyFormal.W6.rr_pos hell
  have hCt : 0 < AdalyFormal.TowerLoc.Ctheta := by
    unfold AdalyFormal.TowerLoc.Ctheta; positivity
  have hl : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  set r := AdalyFormal.BondComposite.rr ell with hrdef
  set q := 1 + 6 * Real.sqrt CEp with hq
  have hq1 : 1 ≤ q := by have := Real.sqrt_nonneg CEp; linarith
  have hq0 : 0 < q := by linarith
  refine ⟨r / (520 * AdalyFormal.TowerLoc.Ctheta * (ell : ℝ) ^ 2 * q), by positivity, ?_⟩
  intro M α₀ hα ht
  have hS : SstarM ell 12 M α₀ ≤ 520 * AdalyFormal.TowerLoc.Ctheta * (ell : ℝ) ^ 2 * ((12 : ℝ) * M * α₀) := by
    unfold AdalyFormal.TowerLoc.SstarM
    have h1 := rho1_le M α₀ hα
    have hp := Real.pi_lt_four
    have hpp := Real.pi_pos
    have hr0 := rho1_nonneg 12 M α₀ hα
    have : 2 * (1 + 3 * Real.pi) * rho1 12 M α₀ ≤ 26 * (20 * ((12 : ℝ) * M * α₀)) := by
      have h3 : 2 * (1 + 3 * Real.pi) ≤ 26 := by linarith
      calc 2 * (1 + 3 * Real.pi) * rho1 12 M α₀ ≤ 26 * rho1 12 M α₀ := by nlinarith
        _ ≤ 26 * (20 * ((12 : ℝ) * M * α₀)) := by linarith
    have hc : 0 ≤ AdalyFormal.TowerLoc.Ctheta * (ell : ℝ) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left this hc
    nlinarith
  have hS0 : 0 ≤ SstarM ell 12 M α₀ := by
    have := rho1_nonneg 12 M α₀ hα
    have := Real.pi_pos
    unfold AdalyFormal.TowerLoc.SstarM
    positivity
  have hX : SstarM ell 12 M α₀ / r ≤ 1 / q := by
    rw [div_le_div_iff₀ hr hq0]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 520 * AdalyFormal.TowerLoc.Ctheta * (ell : ℝ) ^ 2 * q)).1 ht
    nlinarith
  have hX0 : 0 ≤ SstarM ell 12 M α₀ / r := div_nonneg hS0 hr.le
  constructor
  · have : 1 / q ≤ 1 := by rw [div_le_one hq0]; exact hq1
    linarith
  · have h1 : (SstarM ell 12 M α₀ / r) * q ≤ 1 := by
      calc (SstarM ell 12 M α₀ / r) * q ≤ (1 / q) * q := by gcongr
        _ = 1 := by field_simp
    have := Real.sqrt_nonneg CEp
    nlinarith

end AdalyFormal.M1W4Num
