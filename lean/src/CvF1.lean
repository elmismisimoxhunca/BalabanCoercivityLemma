import CvSl1

/-!
# CvF1 -- the EXACT pointwise content of `¬ P428Target8NCWDH` (lane cover_finish_20261016)

`P428Target8NCWDH` (CvS1) is the frozen headline with `CoversOm0p` removed and `WellDefG` a HYPOTHESIS of the inequality.

Proved here (no new headline variant; `FailPt`, `FailAt`, `FailRHS` are predicates on points / outer data):
* `perCube_mono`: the class `PerCubeRegular2 .. α₀ η ..` is monotone in `α₀` (for `η ≥ 0`).
* **`not_WDH_iff : ¬ P428Target8NCWDH ↔ FailRHS`**, where `FailRHS` says: for some `ell ≥ 2`, `a > 0`, for infinitely many `m`
  and, for each of them, infinitely many `R`, the statement `FailAt` holds: for EVERY `α > 0` and EVERY `γ > 0` there is ONE
  in-regime point (depth `k ≥ 1`, torus, admissible tower, `Λ` with `LambdaOK2`, `U` in the factor-12 class at `α`, every printed
  object existing) and an admissible `B̃` with `⟨C B̃, Δ_k C B̃⟩ < γ ‖B̃‖²`.
  So a refutation needs neither `form ≤ 0` (CvSl1 `StrongWitness`) nor a single point per `(m, R)`: an infimum `≤ 0`
  over in-class, all-objects-exist points suffices, and it is also necessary.
* `failAt_iff_diag`: `FailAt` is equivalent to its diagonal `∀ ε > 0, FailPt .. ε ε` (monotonicity in `α` and `γ`).
* `failAt_of_strongWitness`: CvSl1's `StrongWitness` gives `FailAt` (consistency with CvSl1).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverFinish

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NoCover
open AdalyFormal.CoverStrong
open AdalyFormal.CoverSlab
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-! ## 1. monotonicity of the class in `α₀` -/

theorem perCube_mono {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L} {α₀ α η : ℝ} {U : LinkCfg L}
    (hη : 0 ≤ η) (hle : α₀ ≤ α) (h : PerCubeRegular2 ell M f k S α₀ η U) :
    PerCubeRegular2 ell M f k S α η U := by
  intro sites j hq
  obtain ⟨g, A, h1, h2, h3⟩ := h sites j hq
  have key : ∀ p : ℕ, (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ p)
      ≤ (f : ℝ) * M * α * (((ell : ℝ) ^ j * η)⁻¹ ^ p) := by
    intro p
    have hX : 0 ≤ (((ell : ℝ) ^ j * η)⁻¹ ^ p) :=
      pow_nonneg (inv_nonneg.mpr (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hη)) _
    have hfM : (0 : ℝ) ≤ (f : ℝ) * M := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hfM) hX
  refine ⟨g, A, fun e he => ?_, fun μ ν x hx₁ hx₂ => ?_, fun μ x hx => ?_⟩
  · obtain ⟨a1, a2, a3⟩ := h1 e he
    exact ⟨a1, a2, lt_of_lt_of_le a3 (key 1)⟩
  · exact lt_of_lt_of_le (h2 μ ν x hx₁ hx₂) (key 2)
  · exact lt_of_lt_of_le (h3 μ x hx) (key 3)

/-! ## 2. one approximate failure point -/

/-- **one failure point** at `(ell, M, R, a)`, class constant `α`, bound `γ`: depth `k ≥ 1`, torus, admissible tower, `Λ` with
`LambdaOK2`, `U` in the factor-12 class at `α`, every printed object existing (`WellDefG`), and an admissible `B̃` with
`⟨C B̃, Δ_k C B̃⟩ < γ ‖B̃‖²`. -/
def FailPt (ell M R : ℕ) (hell : 0 < ell) (a α γ : ℝ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ∃ Lu : PeriodicLatticeExtent, TorusOK ell M Lu ∧
  ∃ S : Tower (scaleUp ell k Lu), Admissible ell M R k S ∧
  ∃ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 ell M R k S Lam ∧
  ∃ U : LinkCfg (scaleUp ell k Lu),
    PerCubeRegular2 ell M 12 k S α ((ell : ℝ) ^ k)⁻¹ U ∧
    GenP.WellDefG (gparams ell k Lu hell S U a Lam) ∧
  ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧
    GenP.genForm (gparams ell k Lu hell S U a Lam)
      (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt)) < γ * bondEnergy Bt

/-- at one `(m, R)`: failure points for every class constant and every bound. -/
def FailAt (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∀ γ : ℝ, 0 < γ → FailPt ell M R hell a α γ

/-- the outer quantifiers: some `ell ≥ 2`, `a > 0`; infinitely many `m`; for each, infinitely many `R`. -/
def FailRHS : Prop :=
  ∃ ell : ℕ, ∃ hell : 2 ≤ ell, ∃ a : ℝ, 0 < a ∧
    ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧
      FailAt ell (ell ^ m) R (by omega) a

theorem failPt_mono {ell M R : ℕ} {hell : 0 < ell} {a α α' γ γ' : ℝ} (hα : α ≤ α') (hγ : γ ≤ γ')
    (h : FailPt ell M R hell a α γ) : FailPt ell M R hell a α' γ' := by
  obtain ⟨k, hk, Lu, hT, S, hS, Lam, hL, U, hU, hW, Bt, h1, h2, hlt⟩ := h
  have hη : (0 : ℝ) ≤ ((ell : ℝ) ^ k)⁻¹ := inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)
  have hE : 0 ≤ bondEnergy Bt := AdalyFormal.Balaban.RegularUPerturbation.bondEnergy_nonneg Bt
  refine ⟨k, hk, Lu, hT, S, hS, Lam, hL, U, perCube_mono hη hα hU, hW, Bt, h1, h2, ?_⟩
  exact lt_of_lt_of_le hlt (mul_le_mul_of_nonneg_right hγ hE)

/-- `FailAt` is its own diagonal. -/
theorem failAt_iff_diag {ell M R : ℕ} {hell : 0 < ell} {a : ℝ} :
    FailAt ell M R hell a ↔ ∀ ε : ℝ, 0 < ε → FailPt ell M R hell a ε ε := by
  constructor
  · intro h ε hε; exact h ε hε ε hε
  · intro h α hα γ hγ
    exact failPt_mono (min_le_left α γ) (min_le_right α γ) (h (min α γ) (lt_min hα hγ))

/-- CvSl1's strong witness gives failure points at every `α`, `γ`. -/
theorem failAt_of_strongWitness {ell M R : ℕ} {hell : 0 < ell} {a : ℝ} (hw : StrongWitness ell M R hell a) :
    FailAt ell M R hell a := by
  intro α hα γ hγ
  obtain ⟨k, hk, Lu, hT, S, hS, Lam, hL, U, hU, hW, Bt, h1, h2, hE, hF⟩ := hw
  have : 0 < γ * bondEnergy Bt := mul_pos hγ hE
  exact ⟨k, hk, Lu, hT, S, hS, Lam, hL, U, hU α hα, hW, Bt, h1, h2, by linarith⟩

/-! ## 3. the exact characterization -/

theorem not_WDH_of_fail (h : FailRHS) : ¬ P428Target8NCWDH := by
  obtain ⟨ell, hell, a, ha, hF⟩ := h
  intro H
  obtain ⟨m₀, -, hm⟩ := H ell hell a ha
  obtain ⟨m, hmm, hR⟩ := hF m₀
  obtain ⟨R₀, hR₀⟩ := hm m hmm
  obtain ⟨R, hRR, hw⟩ := hR R₀
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hc⟩ := hR₀ R hRR
  have hMpos : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by
    have : 0 < ell ^ m := pow_pos (by omega) m
    exact_mod_cast this
  have hα : 0 < a₀ / (12 * ((ell ^ m : ℕ) : ℝ)) := by positivity
  have hle : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * (a₀ / (12 * ((ell ^ m : ℕ) : ℝ))) ≤ a₀ := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]
  obtain ⟨k, hk, Lu, hT, S, hS, Lam, hL, U, hU, hW, Bt, h1, h2, hlt⟩ := hw _ hα γ₀ hγ
  have hge := hc k hk Lu _ hα hle hT S hS Lam hL U hU hW Bt h1 h2
  linarith

theorem fail_of_not_WDH (h : ¬ P428Target8NCWDH) : FailRHS := by
  by_contra hF
  apply h
  intro ell hell a ha
  have hF' : ¬ ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧
      FailAt ell (ell ^ m) R (by omega) a :=
    fun h' => hF ⟨ell, hell, a, ha, h'⟩
  push Not at hF'
  obtain ⟨m₀, hm₀⟩ := hF'
  refine ⟨max m₀ 1, le_max_right _ _, fun m hm => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hm₀ m (le_trans (le_max_left _ _) hm)
  refine ⟨R₀, fun R hR => ?_⟩
  have hnA : ¬ FailAt ell (ell ^ m) R (by omega) a := hR₀ R hR
  have hnA' : ∃ α : ℝ, 0 < α ∧ ∃ γ : ℝ, 0 < γ ∧ ¬ FailPt ell (ell ^ m) R (by omega) a α γ := by
    by_contra hc
    push Not at hc
    exact hnA hc
  obtain ⟨α, hα, γ, hγ, hnot⟩ := hnA'
  have hMpos : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by
    have : 0 < ell ^ m := pow_pos (by omega) m
    exact_mod_cast this
  refine ⟨⟨hell, ⟨m, le_trans (le_max_right _ _) hm, rfl⟩, ha⟩,
    12 * ((ell ^ m : ℕ) : ℝ) * α, by positivity, γ, hγ, ?_⟩
  intro k hk Lu α₀ hα₀ hle hT S hS Lam hL U hU hW Bt h1 h2
  by_contra hlt
  push Not at hlt
  apply hnot
  have h12 : (0 : ℝ) < 12 * ((ell ^ m : ℕ) : ℝ) := by positivity
  have hα₀α : α₀ ≤ α := le_of_mul_le_mul_left hle h12
  have hη : (0 : ℝ) ≤ ((ell : ℝ) ^ k)⁻¹ := inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)
  exact ⟨k, hk, Lu, hT, S, hS, Lam, hL, U, perCube_mono hη hα₀α hU, hW, Bt, h1, h2, hlt⟩

/-- **the exact pointwise content of the strong coverage refutation.** -/
theorem not_WDH_iff : ¬ P428Target8NCWDH ↔ FailRHS :=
  ⟨fail_of_not_WDH, not_WDH_of_fail⟩

/-- `coverage_necessary_strong` is equivalent to `FailRHS` (the r8 headline `P428Target8` is proved). -/
theorem coverage_necessary_strong_iff :
    (AdalyFormal.StatementLaneG.P428Target8 ∧ ¬ P428Target8NCWDH) ↔ FailRHS :=
  ⟨fun h => fail_of_not_WDH h.2, fun h => ⟨AdalyFormal.M2RightInv.p428Target8, not_WDH_of_fail h⟩⟩

end AdalyFormal.CoverFinish
