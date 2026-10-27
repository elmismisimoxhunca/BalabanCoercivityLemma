import NsCvO12

/-!
# CvO13 -- `RegBg2` for the staggered layer at levels `0` and `1` (all base bonds) (lane omega)

* `cartan_ne_negOne`: `cartan φ ≠ -1` for `|φ| < π`;
* `regBg2_level0`: loops of `stagCfg c t` at stride `1`, every base bond: `RegBg2 1 ell (stagCfg c t)`;
* `bg1_isUTemp`: the first blocked level is in the class `𝒞(D,u₁)`, `D(v) = [v=c] - [(v+ell) mod N₀ = c]`, `|u₁| ≤ |t|/2`;
* `regBg2_level1`: loops of that level at stride `ell`, every base bond, have `|angle| ≤ |t|`: `RegBg2 ell ell (bg1)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2 (LogReg)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

theorem cartan_ne_negOne (φ : ℝ) (h : |φ| < Real.pi) : cartan φ ≠ su2NegOne := by
  intro he
  have h1 : su2Angle (cartan φ) = |φ| := su2Angle_cartan φ h.le
  have h2 : su2Angle su2NegOne = Real.pi := by
    unfold su2Angle
    simp [Matrix.trace_neg, Matrix.trace_one]
  rw [he, h2] at h1
  linarith

theorem regBg2_level0 (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : 2 ∣ ell) (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi) :
    RegBg2 1 ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) := by
  apply regBg2_of_ne_negOne
  intro cc x hx
  obtain ⟨y, μ⟩ := cc
  rw [loopVar_stag hN hE c t y x μ]
  exact cartan_ne_negOne _ (stagPhi_abs_lt c t htπ μ ell y x)

/-- the telescoping bound: `|Σ_{j<m} D((y₀ + ell j) mod N₀)| ≤ 1`. -/
theorem sumD_abs_le (c ell N0 y0 m : ℕ) :
    |∑ j ∈ Finset.range m, Dfun c ell N0 ((y0 + ell * j) % N0)| ≤ 1 := by
  have h : ∀ j, Dfun c ell N0 ((y0 + ell * j) % N0) =
      (if (y0 + ell * j) % N0 = c then (1 : ℝ) else 0) - (if (y0 + ell * (j + 1)) % N0 = c then (1 : ℝ) else 0) := by
    intro j
    unfold Dfun
    rw [Nat.mod_add_mod]
    have : y0 + ell * j + ell = y0 + ell * (j + 1) := by ring
    rw [this]
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_range_sub' (fun j => if (y0 + ell * j) % N0 = c then (1 : ℝ) else 0)]
  have key : ∀ (a b : Prop) [Decidable a] [Decidable b], |(if a then (1 : ℝ) else 0) - (if b then (1 : ℝ) else 0)| ≤ 1 := by
    intro a b _ _; split_ifs <;> simp
  exact key _ _

theorem Ubg_abs_le {ell : ℕ} (hell : 0 < ell) (t : ℝ) (z : PeriodicLatticeSite L) : |Ubg ell t z| ≤ |t| / 2 := by
  unfold Ubg
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  have h0 : (((min ell (L 0 + 1 - (z 0).val) : ℕ)) : ℝ) ≤ ell := by exact_mod_cast min_le_left _ _
  have h2 : (((min ell (L 2 + 1 - (z 2).val) : ℕ)) : ℝ) ≤ ell := by exact_mod_cast min_le_left _ _
  have h1 : ((((min ell (L 1 + 1 - (z 1).val)) / 2 : ℕ)) : ℝ) ≤ (ell : ℝ) / 2 := by
    have : (min ell (L 1 + 1 - (z 1).val)) / 2 ≤ ell / 2 := Nat.div_le_div_right (min_le_left _ _)
    calc ((((min ell (L 1 + 1 - (z 1).val)) / 2 : ℕ)) : ℝ) ≤ ((ell / 2 : ℕ) : ℝ) := by exact_mod_cast this
      _ ≤ (ell : ℝ) / 2 := Nat.cast_div_le
  have hs := sgnNat_abs_le (z 1).val
  have hc0 : (0 : ℝ) ≤ (((min ell (L 0 + 1 - (z 0).val) : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hc2 : (0 : ℝ) ≤ (((min ell (L 2 + 1 - (z 2).val) : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hc1 : (0 : ℝ) ≤ ((((min ell (L 1 + 1 - (z 1).val)) / 2 : ℕ)) : ℝ) := Nat.cast_nonneg _
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
  have e1 : |(((ell : ℝ) ^ 3)⁻¹)| = ((ell : ℝ) ^ 3)⁻¹ := abs_of_pos (by positivity)
  rw [e1, abs_of_nonneg hc0, abs_of_nonneg hc2, abs_of_nonneg hc1]
  have key : ((ell : ℝ) ^ 3)⁻¹ * |t| * ((((min ell (L 0 + 1 - (z 0).val) : ℕ)) : ℝ) * (((min ell (L 2 + 1 - (z 2).val) : ℕ)) : ℝ)) *
      (((((min ell (L 1 + 1 - (z 1).val)) / 2 : ℕ)) : ℝ) * |sgnNat (z 1).val|) ≤
      ((ell : ℝ) ^ 3)⁻¹ * |t| * ((ell : ℝ) * (ell : ℝ)) * (((ell : ℝ) / 2) * 1) := by
    gcongr
  calc _ ≤ _ := key
    _ = |t| / 2 := by field_simp



/-- the transverse profile of the first blocked level with the `x₀`-count frozen at `ell`. -/
noncomputable def u1 (ell : ℕ) (t : ℝ) (a1 a2 : ℕ) : ℝ :=
  ((((ell : ℝ) ^ 3)⁻¹ * t * ((ell : ℝ) * (((min ell (L 2 + 1 - a2) : ℕ)) : ℝ)))) *
    ((((min ell (L 1 + 1 - a1)) / 2 : ℕ) : ℝ) * sgnNat a1)

theorem u1_abs_le {ell : ℕ} (hell : 0 < ell) (t : ℝ) (a1 a2 : ℕ) : |u1 (L := L) ell t a1 a2| ≤ |t| / 2 := by
  unfold u1
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  have h2 : (((min ell (L 2 + 1 - a2) : ℕ)) : ℝ) ≤ ell := by exact_mod_cast min_le_left _ _
  have h1 : ((((min ell (L 1 + 1 - a1)) / 2 : ℕ)) : ℝ) ≤ (ell : ℝ) / 2 := by
    have : (min ell (L 1 + 1 - a1)) / 2 ≤ ell / 2 := Nat.div_le_div_right (min_le_left _ _)
    calc ((((min ell (L 1 + 1 - a1)) / 2 : ℕ)) : ℝ) ≤ ((ell / 2 : ℕ) : ℝ) := by exact_mod_cast this
      _ ≤ (ell : ℝ) / 2 := Nat.cast_div_le
  have hs := sgnNat_abs_le a1
  have hc2 : (0 : ℝ) ≤ (((min ell (L 2 + 1 - a2) : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hc1 : (0 : ℝ) ≤ ((((min ell (L 1 + 1 - a1)) / 2 : ℕ)) : ℝ) := Nat.cast_nonneg _
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
  have e1 : |(((ell : ℝ) ^ 3)⁻¹)| = ((ell : ℝ) ^ 3)⁻¹ := abs_of_pos (by positivity)
  rw [e1, abs_of_nonneg hc2, abs_of_nonneg hc1, abs_of_pos hl]
  have key : ((ell : ℝ) ^ 3)⁻¹ * |t| * ((ell : ℝ) * (((min ell (L 2 + 1 - a2) : ℕ)) : ℝ)) *
      (((((min ell (L 1 + 1 - a1)) / 2 : ℕ)) : ℝ) * |sgnNat a1|) ≤
      ((ell : ℝ) ^ 3)⁻¹ * |t| * ((ell : ℝ) * (ell : ℝ)) * (((ell : ℝ) / 2) * 1) := by
    gcongr
  calc _ ≤ _ := key
    _ = |t| / 2 := by field_simp

/-- where `D ≠ 0` the `x₀`-block is full. -/
theorem cnt0_eq {ell c N0 v : ℕ} (hc1 : ell ≤ c) (hc2 : c + ell ≤ N0) (hv : v < N0) (hD : Dfun c ell N0 v ≠ 0) :
    min ell (N0 - v) = ell := by
  unfold Dfun at hD
  by_cases h1 : v = c
  · subst h1; omega
  · by_cases h2 : (v + ell) % N0 = c
    · rcases Nat.lt_or_ge (v + ell) N0 with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at h2; omega
      · have : (v + ell) % N0 = v + ell - N0 := by
          rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
        omega
    · simp [h1, h2] at hD

theorem bg1_isUTemp (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : 2 ∣ ell) (hell : 0 < ell) (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi)
    (hc1 : ell ≤ c) (hc2 : c + ell ≤ L 0 + 1) :
    IsUTemp (Dfun c ell (L 0 + 1)) (u1 (L := L) ell t)
      (stridedBlockedGauge su2LogExp 1 ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) := by
  intro z
  refine ⟨?_, ?_, ?_⟩
  · rw [bg1_stag_all hN hE hell c t htπ z 0, if_pos rfl]
    congr 1
    by_cases hD : Dfun c ell (L 0 + 1) (z 0).val = 0
    · rw [hD, zero_mul, zero_mul]
    · congr 1
      unfold Ubg u1
      rw [cnt0_eq hc1 hc2 (z 0).isLt hD]
  · rw [bg1_stag_all hN hE hell c t htπ z 1, if_neg (by decide)]; exact cartan_zero
  · rw [bg1_stag_all hN hE hell c t htπ z 2, if_neg (by decide)]; exact cartan_zero

theorem regBg2_level1 (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : 2 ∣ ell) (hell : 0 < ell) (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi)
    (hc1 : ell ≤ c) (hc2 : c + ell ≤ L 0 + 1) :
    RegBg2 ell ell (stridedBlockedGauge su2LogExp 1 ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) := by
  have hV := bg1_isUTemp hN hE hell c t htπ hc1 hc2
  apply regBg2_of_ne_negOne
  intro cc x hx
  obtain ⟨y, μ⟩ := cc
  rw [loopVar_uTemp hV y μ hx]
  apply cartan_ne_negOne
  have hb : ∀ (S p q : ℝ), |S| ≤ 1 → |p| ≤ |t| / 2 → |q| ≤ |t| / 2 → |S * (p - q)| < Real.pi := by
    intro S p q hS hp hq
    rw [abs_mul]
    have : |p - q| ≤ |t| := by
      calc |p - q| ≤ |p| + |q| := abs_sub _ _
        _ ≤ |t| := by linarith
    calc |S| * |p - q| ≤ 1 * |t| := by gcongr
      _ < Real.pi := by linarith
  have hu := u1_abs_le (L := L) hell t
  split_ifs
  · exact hb _ _ _ (sumD_abs_le c ell (L 0 + 1) (y 0).val ell) (hu _ _) (hu _ _)
  · exact hb _ _ _ (sumD_abs_le c ell (L 0 + 1) (y 0).val _) (hu _ _) (hu _ _)
  · exact hb _ _ _ (sumD_abs_le c ell (L 0 + 1) (y 0).val _) (hu _ _) (hu _ _)

#print axioms u1_abs_le
#print axioms cnt0_eq
#print axioms bg1_isUTemp
#print axioms regBg2_level1

end AdalyFormal.CoverOmega
