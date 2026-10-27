import RB2

/-!
# RB3 -- consumption: the sharp collar and the frozen headline restated with the PRINTED tower conditions.

* `cube5_class_box_printed` : the exact-collar sufficiency (`cube5_is_class_box_sharp`, lane p409_sharp_20261019) with the hypothesis
  `Admissible` replaced by `PrintedTower ∧ PadAbove` (same `R`, same `collarOK`).
* `collar_threshold_iff_printed`, `collar_power_*`: the threshold in printed units (identity map `R_print = R_formal`), and the
  smallest power `R = ell^r` of the print's convention "R, M powers of L" (p.408).
* `core8Applied_iff_print` / `headline_in_print_terms`: `P428Core8Applied` (the unfolded frozen headline block) is equivalent to the
  same statement over printed towers, so the frozen headline reads with the printed (2.1),(2.2) conditions.
* `headline_R_before_k` : in the frozen headline `R_0` is chosen before `k`; so a `k`-dependent radius is not an instance of it.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.RBridge

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.P409S
open AdalyFormal.M2Bridge AdalyFormal.GeneralClass
open AdalyFormal.P409 AdalyFormal.P409W AdalyFormal.P409C5 AdalyFormal.P409L

variable {L : PeriodicLatticeExtent}

/-- the exact collar for the class box, on the printed tower conditions. -/
theorem cube5_class_box_printed {ell M R k j' : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hcol : collarOK ell M R (j' + 1))
    (hP : PrintedTower ell M R k S) (hPad : PadAbove k S) (hD : IsDCube ell M k S (j' + 1) c) :
    ∃ i f : ℕ, ((i = j' + 1 ∧ f = 12) ∨ (i + 1 = j' + 1 ∧ f = 12 * ell)) ∧ 10 ≤ f ∧
      DescribedAt ell M f k S (printedCube5 (bigSide M ell (j' + 1)) c) i ∧
      IsClassCubeG ell M f k S (printedCube5 (bigSide M ell (j' + 1)) c) i :=
  cube5_is_class_box_sharp hell hM hcol ((admissible_iff_print (by omega) hM S).2 ⟨hP, hPad⟩) hD

/-- the threshold iff of the sharp lane, with the hypothesis on towers read as the printed conditions. -/
theorem collar_threshold_iff_printed {ell M R k j' : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hjk : j' + 1 ≤ k) :
    (∀ (Lf : PeriodicLatticeExtent) (S : Tower Lf) (c : PeriodicLatticeSite Lf),
        PrintedTower ell M R k S → PadAbove k S → (∀ μ : Fin 3, bigSide M ell k < Lf μ + 1) →
        IsDCube ell M k S (j' + 1) c →
        ∃ i f : ℕ, ((i = j' + 1 ∧ f = 12) ∨ (i + 1 = j' + 1 ∧ f = 12 * ell)) ∧
          DescribedAt ell M f k S (printedCube5 (bigSide M ell (j' + 1)) c) i) ↔
      collarOK ell M R (j' + 1) := by
  rw [← cube5_threshold_iff (R := R) (k := k) hell hM hjk]
  constructor
  · intro h Lf S c hA hbig hD
    obtain ⟨hP, hPad⟩ := (admissible_iff_print (by omega) hM S).1 hA
    exact h Lf S c hP hPad hbig hD
  · intro h Lf S c hP hPad hbig hD
    exact h Lf S c ((admissible_iff_print (by omega) hM S).2 ⟨hP, hPad⟩) hbig hD

/-- smallest power of `ell = 2` above the integer threshold `18 ell - 2 = 34` (valid once `M ell^(j-1) >= 3`). -/
theorem collar_power_ell2 : ∀ r : ℕ, 34 ≤ 2 ^ r ↔ 6 ≤ r := by
  intro r
  constructor
  · intro h
    by_contra hr
    push Not at hr
    interval_cases r <;> omega
  · intro h
    calc 34 ≤ 2 ^ 6 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h

theorem collar_power_ell3 : ∀ r : ℕ, 52 ≤ 3 ^ r ↔ 4 ≤ r := by
  intro r
  constructor
  · intro h
    by_contra hr
    push Not at hr
    interval_cases r <;> omega
  · intro h
    calc 52 ≤ 3 ^ 4 := by norm_num
      _ ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) h

/-! ## the headline block over printed towers -/

/-- `P428Core8Applied` with the tower hypothesis `Admissible` replaced by the printed conditions. -/
def Core8AppliedPrint (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
        TorusOK ell M Lu → ∀ (S : Tower (scaleUp ell k Lu)), PrintedTower ell M R k S → PadAbove k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
          InstIneq ell k hell a Lu γ₀ S Lam U ∧
            ∀ p ∈ plaqIn (S.Om 0), PlaqGaugeAt ell M 12 α₀ ((ell : ℝ) ^ k)⁻¹ U p

theorem core8Applied_iff_print {ell M R : ℕ} (hell : 0 < ell) (hM : 0 < M) (a : ℝ) :
    P428Core8Applied ell M R hell a ↔ Core8AppliedPrint ell M R hell a := by
  constructor
  · rintro ⟨a₀, ha, γ₀, hγ, h⟩
    exact ⟨a₀, ha, γ₀, hγ, fun k hk Lu α₀ h1 h2 hT S hP hPad Lam hL U hCU =>
      h k hk Lu α₀ h1 h2 hT S ((admissible_iff_print hell hM S).2 ⟨hP, hPad⟩) Lam hL U hCU⟩
  · rintro ⟨a₀, ha, γ₀, hγ, h⟩
    exact ⟨a₀, ha, γ₀, hγ, fun k hk Lu α₀ h1 h2 hT S hA Lam hL U hCU =>
      have hh := (admissible_iff_print hell hM S).1 hA
      h k hk Lu α₀ h1 h2 hT S hh.1 hh.2 Lam hL U hCU⟩

/-- the frozen headline, read with the printed tower conditions. -/
theorem headline_in_print_terms (hH : P428Target8) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      Core8AppliedPrint ell (ell ^ m) R (by omega) a := by
  obtain ⟨m₀, hm₀, h⟩ := hH ell hell a ha
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR₀⟩ := h m hm
  refine ⟨R₀, fun R hR => ?_⟩
  have hg := (hR₀ R hR).apply_gauge
  exact (core8Applied_iff_print (by omega) (pow_pos (by omega) m) a).1 hg

/-- in the frozen headline the radius threshold `R_0` is chosen BEFORE `k`: a radius `ell^k R_p` (reading B,
`T_1` = the level-`k` unit lattice) is not an instance of "all `R >= R_0`, all `k`". -/
theorem headline_R_before_k (hH : P428Target8) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ k : ℕ, 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
          (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ → CoercG8At ell (ell ^ m) R k (by omega) a Lu 12 α₀ γ₀ := by
  obtain ⟨m₀, hm₀, h⟩ := hH ell hell a ha
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR₀⟩ := h m hm
  exact ⟨R₀, fun R hR => (hR₀ R hR).2⟩

end AdalyFormal.RBridge
