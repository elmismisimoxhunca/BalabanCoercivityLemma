import CvF1
import CvS1

/-!
# NsCS1 -- the coverage-free headline AT CUBE FACTOR `c`, its per-`ell` body, and the failure predicates (lane ncwdh_strong_20261017)

`CvS1.P428Target8NCWDH` is the coverage-free headline with `WellDefG` as a HYPOTHESIS, at the FIXED cube factor `12`.  Here the `12`
is replaced by a parameter `c : ℕ` and NOTHING else is changed:

* `P428Core8NCWDHc c` : `P428Core8NCWDH` with `(12 : ℝ)` -> `(c : ℝ)` and class slot `12` -> `c` (the inner claim
  `CvS1.CoercG8AtNCWDH` already carries `c` as a parameter and is REUSED verbatim).
* `NcwdhBodyAt c ell hell a` : the body of `P428Target8NCWDHc c` at one `(ell, a)`:
  `∃ m₀ ≥ 1, ∀ m ≥ m₀, ∃ R₀, ∀ R ≥ R₀, P428Genuine8NCWDHc c ell (ell^m) R a`.
* `P428Target8NCWDHc c := ∀ ell ≥ 2, ∀ a > 0, NcwdhBodyAt c ell _ a`;  `FailsAtEll c ell a := ¬ NcwdhBodyAt c ell _ a`.
* `P428Target8NCWDHc_twelve_iff : P428Target8NCWDHc 12 ↔ CvS1.P428Target8NCWDH` (the faithfulness pin).
* `FailPtC / FailAtC / FailEllC` : copies of CvF1's `FailPt / FailAt` with the class factor `c`; `not_body_of_failEll`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.NcwdhStrong

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NoCover
open AdalyFormal.CoverStrong
open AdalyFormal.CoverFinish (perCube_mono)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-! ## the statement at cube factor `c` (CvS1's `P428Core8NCWDH` with `12` replaced by `c`) -/

/-- `CvS1.P428Core8NCWDH` with `12 -> c` (both occurrences). -/
def P428Core8NCWDHc (c ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtNCWDH ell M R k hell a Lu c α₀ γ₀

/-- `CvS1.P428Genuine8NCWDH` at factor `c`. -/
def P428Genuine8NCWDHc (c ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ P428Core8NCWDHc c ell M R hell a

/-- the per-`(ell, a)` body of the coverage-free headline at factor `c`. -/
def NcwdhBodyAt (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=
  ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
    P428Genuine8NCWDHc c ell (ell ^ m) R (by omega) a

/-- **the coverage-free headline (WellDefG as hypothesis) at cube factor `c`.** -/
def P428Target8NCWDHc (c : ℕ) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → NcwdhBodyAt c ell hell a

/-- the per-`ell` strong form: the body FAILS at `(c, ell, a)`. -/
def FailsAtEll (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop := ¬ NcwdhBodyAt c ell hell a

/-- the target is refuted as soon as ONE `(ell, a > 0)` fails. -/
theorem not_target_of_failsAtEll {c ell : ℕ} {hell : 2 ≤ ell} {a : ℝ} (ha : 0 < a) (h : FailsAtEll c ell hell a) :
    ¬ P428Target8NCWDHc c := fun H => h (H ell hell a ha)

/-! ## the faithfulness pin: at `c = 12` this IS the frozen `P428Target8NCWDH` -/

theorem core_twelve_iff (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) :
    P428Core8NCWDHc 12 ell M R hell a ↔ P428Core8NCWDH ell M R hell a := by
  unfold P428Core8NCWDHc P428Core8NCWDH
  simp only [Nat.cast_ofNat]

theorem target_twelve_iff : P428Target8NCWDHc 12 ↔ P428Target8NCWDH := by
  unfold P428Target8NCWDHc NcwdhBodyAt P428Genuine8NCWDHc P428Target8NCWDH P428Genuine8NCWDH
  simp only [core_twelve_iff]

/-! ## failure points at factor `c` (copies of CvF1's `FailPt` / `FailAt`) -/

def FailPtC (c ell M R : ℕ) (hell : 0 < ell) (a α γ : ℝ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ∃ Lu : PeriodicLatticeExtent, TorusOK ell M Lu ∧
  ∃ S : Tower (scaleUp ell k Lu), Admissible ell M R k S ∧
  ∃ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 ell M R k S Lam ∧
  ∃ U : LinkCfg (scaleUp ell k Lu),
    PerCubeRegular2 ell M c k S α ((ell : ℝ) ^ k)⁻¹ U ∧
    GenP.WellDefG (gparams ell k Lu hell S U a Lam) ∧
  ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧
    GenP.genForm (gparams ell k Lu hell S U a Lam)
      (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt)) < γ * bondEnergy Bt

def FailAtC (c ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∀ γ : ℝ, 0 < γ → FailPtC c ell M R hell a α γ

/-- failure along the outer data at one `(c, ell, a)`: infinitely many `m`, and for each infinitely many `R`. -/
def FailEllC (c ell : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ FailAtC c ell (ell ^ m) R hell a

theorem failsAtEll_of_failEllC {c ell : ℕ} (hc : 0 < c) (hell : 2 ≤ ell) {a : ℝ} (h : FailEllC c ell (by omega) a) :
    FailsAtEll c ell hell a := by
  intro H
  obtain ⟨m₀, -, hm⟩ := H
  obtain ⟨m, hmm, hR⟩ := h m₀
  obtain ⟨R₀, hR₀⟩ := hm m hmm
  obtain ⟨R, hRR, hw⟩ := hR R₀
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hc'⟩ := hR₀ R hRR
  have hMpos : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by
    have : 0 < ell ^ m := pow_pos (by omega) m
    exact_mod_cast this
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hα : 0 < a₀ / ((c : ℝ) * ((ell ^ m : ℕ) : ℝ)) := by positivity
  have hle : (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * (a₀ / ((c : ℝ) * ((ell ^ m : ℕ) : ℝ))) ≤ a₀ := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]
  obtain ⟨k, hk, Lu, hT, S, hS, Lam, hL, U, hU, hW, Bt, h1, h2, hlt⟩ := hw _ hα γ₀ hγ
  have hge := hc' k hk Lu _ hα hle hT S hS Lam hL U hU hW Bt h1 h2
  linarith

#print axioms core_twelve_iff
#print axioms target_twelve_iff
#print axioms failsAtEll_of_failEllC

end AdalyFormal.NcwdhStrong
