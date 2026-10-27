import SC5a
import GFC7

/-!
# SC5b -- THE EXPLICIT CELL COERCIVITY THEOREM (all twists, all cell sides `n`, all mass weights `κ`).
`cellC n κ · Σ‖w_μ‖² ≤ g1 + κ g2 + S`, with `cellC` an explicit closed form (no compactness).
Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped ComplexInnerProductSpace BigOperators ComplexConjugate
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

section Cell
variable {n : ℕ}

noncomputable def cA : ℝ := 4 / Real.pi ^ 2 * (2 / Real.pi) ^ 6

noncomputable def muStar (a : ℝ) : ℝ :=
  cA * a / (3 * Real.pi ^ 2 + a + a * (3 * Real.pi ^ 2) / 4)

/-- the explicit cell constant -/
noncomputable def cellC (n : ℕ) (κ : ℝ) : ℝ :=
  muStar (κ * (n : ℝ) ^ 7) / (1 + muStar (κ * (n : ℝ) ^ 7)) *
    lamN κ (4 / (n : ℝ) ^ 2) ((n : ℝ) * ‖epsV n‖) (cn n * (2 * (n : ℝ) / Real.pi) ^ 4)

theorem cA_pos : 0 < cA := by unfold cA; positivity

theorem muStar_nonneg (a : ℝ) (ha : 0 ≤ a) : 0 ≤ muStar a := by
  unfold muStar
  have := cA_pos
  positivity

theorem lamN_nonneg (κ G A q0 : ℝ) (hκ : 0 ≤ κ) (hG : 0 ≤ G) : 0 ≤ lamN κ G A q0 := by
  unfold lamN
  exact le_min (by positivity) (by positivity)

theorem cellC_nonneg (hn : 0 < n) (κ : ℝ) (hκ : 0 ≤ κ) : 0 ≤ cellC n κ := by
  unfold cellC
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := muStar_nonneg (κ * (n : ℝ) ^ 7) (by positivity)
  have h2 := lamN_nonneg κ (4 / (n : ℝ) ^ 2) ((n : ℝ) * ‖epsV n‖) (cn n * (2 * (n : ℝ) / Real.pi) ^ 4)
    hκ (by positivity)
  positivity

theorem cellC_le_lamN (hn : 0 < n) (κ : ℝ) (hκ : 0 ≤ κ) :
    cellC n κ ≤ lamN κ (4 / (n : ℝ) ^ 2) ((n : ℝ) * ‖epsV n‖) (cn n * (2 * (n : ℝ) / Real.pi) ^ 4) := by
  unfold cellC
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := muStar_nonneg (κ * (n : ℝ) ^ 7) (by positivity)
  have h2 := lamN_nonneg κ (4 / (n : ℝ) ^ 2) ((n : ℝ) * ‖epsV n‖) (cn n * (2 * (n : ℝ) / Real.pi) ^ 4)
    hκ (by positivity)
  have h3 : muStar (κ * (n : ℝ) ^ 7) / (1 + muStar (κ * (n : ℝ) ^ 7)) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  exact mul_le_of_le_one_left h2 h3

/-- the cell coercivity theorem with explicit constant -/
theorem cell_coercive_explicit (hn : 0 < n) (κ : ℝ) (hκ : 0 < κ) (z : Fin 3 → Circle) (w : Fin 3 → CV n)
    (S : ℝ) (hS0 : 0 ≤ S)
    (hS : ∀ u : CV n, ⟪epsV n, u⟫ = 0 →
      ‖⟪(cellSym hn z).Dstar w, (cellSym hn z).Lap u⟫‖ ^ 2 ≤ S * ‖(cellSym hn z).Lap u‖ ^ 2) :
    cellC n κ * ∑ μ, ‖w μ‖ ^ 2 ≤ g1 hn (z, w) + κ * g2 hn (z, w) + S := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcn : 0 ≤ cn n := by unfold cn; positivity
  have hepsn : 0 < ‖epsV n‖ := norm_pos_iff.mpr (epsV_ne hn)
  set A : ℝ := (n : ℝ) * ‖epsV n‖ with hA
  set q0 : ℝ := cn n * (2 * (n : ℝ) / Real.pi) ^ 4 with hq0
  have hApos : 0 < A := by positivity
  have hq0nn : 0 ≤ q0 := by have := Real.pi_pos; positivity
  have hAq : ∀ μ x, ‖(cellSym hn z).Qm μ x‖ ≤ A * ‖x‖ := by
    intro μ x
    have := Qm_norm_le (cellSym hn z) μ x
    exact this
  have hq : ∀ μ, q0 ≤ ‖(cellSym hn z).Qm μ (cellMode hn z).e0‖ := fun μ => Qm_e0_lower hn z μ
  have hg1 : g1 hn (z, w) = g1b (cellSym hn z) w := rfl
  have hg2 : g2 hn (z, w) = g2b (cellSym hn z) w := rfl
  rw [hg1, hg2]
  by_cases hall : ∀ μ, ((z μ : Circle) : ℂ) = 1
  · have := cell_abstract_trivial (cellMode hn z) κ A q0 hκ.le hApos hq0nn hq hAq (fun μ => hall μ) w S hS0 hS
    have h2 := cellC_le_lamN hn κ hκ.le
    have h3 : 0 ≤ ∑ μ, ‖w μ‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
    have h4 : cellC n κ * ∑ μ, ‖w μ‖ ^ 2 ≤ lamN κ (cellMode hn z).G A q0 * ∑ μ, ‖w μ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h2 h3
    exact h4.trans this
  · push_neg at hall
    obtain ⟨μ0, hμ0⟩ := hall
    have hl0 : 0 < (cellMode hn z).l0 := lam0_pos hn z μ0 hμ0
    set β : ℝ := cn n ^ 2 * (2 * (n : ℝ) / Real.pi) ^ 6 with hβ
    have hβ0 : 0 ≤ β := by positivity
    have hβle : β ≤ ‖⟪(cellMode hn z).e0, (cellSym hn z).eps⟫‖ ^ 2 := inner_e0_eps_lower hn z
    have key := cell_abstract_nontrivial (cellMode hn z) κ A q0 β hκ hApos hq0nn hl0 hq hAq hβle hβ0 μ0 hμ0
      w S hS0 hS
    -- identification of constants
    set u : ℝ := (cellMode hn z).l0 with hu
    have hGv : (cellMode hn z).G = 4 / (n : ℝ) ^ 2 := rfl
    have hu_def : u = lam n z (k0 hn) := rfl
    have hcn2 : cn n ^ 2 * (n : ℝ) ^ 3 = 1 := cn_sq hn
    have hβv : β = (2 / Real.pi) ^ 6 * (n : ℝ) ^ 3 := by
      rw [hβ]
      have : (2 * (n : ℝ) / Real.pi) ^ 6 = (2 / Real.pi) ^ 6 * (n : ℝ) ^ 6 := by
        rw [show 2 * (n : ℝ) / Real.pi = (2 / Real.pi) * n by ring, mul_pow]
      rw [this]
      calc cn n ^ 2 * ((2 / Real.pi) ^ 6 * (n : ℝ) ^ 6)
          = (cn n ^ 2 * (n : ℝ) ^ 3) * ((2 / Real.pi) ^ 6 * (n : ℝ) ^ 3) := by ring
        _ = _ := by rw [hcn2, one_mul]
    have hA2 : A ^ 2 = (n : ℝ) ^ 5 := by
      rw [hA, mul_pow, norm_epsV_sq hn]; ring
    have hq02 : q0 ^ 2 = (2 / Real.pi) ^ 8 * (n : ℝ) ^ 5 := by
      rw [hq0, mul_pow, ← pow_mul]
      have : (2 * (n : ℝ) / Real.pi) ^ (4 * 2) = (2 / Real.pi) ^ 8 * (n : ℝ) ^ 8 := by
        rw [show 2 * (n : ℝ) / Real.pi = (2 / Real.pi) * n by ring, mul_pow]
      rw [this]
      calc cn n ^ 2 * ((2 / Real.pi) ^ 8 * (n : ℝ) ^ 8)
          = (cn n ^ 2 * (n : ℝ) ^ 3) * ((2 / Real.pi) ^ 8 * (n : ℝ) ^ 5) := by ring
        _ = _ := by rw [hcn2, one_mul]
    have hΘ := Th2_le z
    have hu_le : u ≤ Th2 z / (n : ℝ) ^ 2 := lam0_le hn z
    have hn2u : (n : ℝ) ^ 2 * u ≤ Th2 z := by
      have h1 := (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).mp hu_le
      calc (n : ℝ) ^ 2 * u = u * (n : ℝ) ^ 2 := by ring
        _ ≤ _ := h1
    have hζ := zeta_ge z
    set a : ℝ := κ * (n : ℝ) ^ 7 with ha
    set x : ℝ := (n : ℝ) ^ 2 * u with hx
    have hxpos : 0 < x := by positivity
    have hxX : x ≤ 3 * Real.pi ^ 2 := le_trans hn2u hΘ
    set ζ2 : ℝ := ∑ μ, ‖((cellSym hn z).ph μ) - 1‖ ^ 2 with hζ2
    have hζ2ge : 4 / Real.pi ^ 2 * x ≤ ζ2 := by
      have : 4 / Real.pi ^ 2 * Th2 z ≤ ζ2 := hζ
      have h5 : 0 ≤ 4 / Real.pi ^ 2 := by positivity
      calc 4 / Real.pi ^ 2 * x ≤ 4 / Real.pi ^ 2 * Th2 z := mul_le_mul_of_nonneg_left hn2u h5
        _ ≤ ζ2 := this
    set G2 : ℝ := ζ2 * β / u ^ 2 with hG2
    set S2 : ℝ := A ^ 2 * (1 / u + 1 / (4 / (n : ℝ) ^ 2)) with hS2
    have hP : cA * a / x ≤ κ * G2 := by
      have e1 : cA * a / x = κ * ((4 / Real.pi ^ 2 * x) * β / u ^ 2) := by
        rw [hx, ha, hβv]; unfold cA
        field_simp
      rw [e1, hG2]
      have : (4 / Real.pi ^ 2 * x) * β / u ^ 2 ≤ ζ2 * β / u ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hζ2ge hβ0
      exact mul_le_mul_of_nonneg_left this hκ.le
    have hQeq : κ * S2 = a / x + a / 4 := by
      rw [hS2, hA2, hx, ha]
      field_simp
    have hQ0 : 0 ≤ κ * S2 := by rw [hQeq]; positivity
    have hmu := mu_lower a cA x (3 * Real.pi ^ 2) (κ * G2) (κ * S2) (by positivity) cA_pos.le hxpos hxX hP
      (by rw [hQeq]) hQ0
    have hμ0eq : mu0c κ G2 S2 = κ * G2 / (1 + κ * S2) := rfl
    have hms : muStar a ≤ mu0c κ G2 S2 := by
      rw [hμ0eq]; unfold muStar; exact hmu
    have hms0 : 0 ≤ muStar a := muStar_nonneg a (by positivity)
    have hratio := ratio_mono hms0 hms
    have hlN : 0 ≤ lamN κ (cellMode hn z).G A q0 := lamN_nonneg κ _ A q0 hκ.le (by rw [hGv]; positivity)
    have h3 : 0 ≤ ∑ μ, ‖w μ‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
    have hfin : cellC n κ * ∑ μ, ‖w μ‖ ^ 2
        ≤ mu0c κ G2 S2 / (1 + mu0c κ G2 S2) * lamN κ (cellMode hn z).G A q0 * ∑ μ, ‖w μ‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ h3
      unfold cellC
      exact mul_le_mul_of_nonneg_right hratio hlN
    exact hfin.trans key

end Cell

#print axioms cell_coercive_explicit

end AdalyFormal.ScaledCoercivity
