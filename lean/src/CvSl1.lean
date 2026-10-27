import CvS1

/-!
# CvSl1 -- what a refutation of `P428Target8NCWDH` needs: ONE point per `(m, R)` (lane cover_slab_20261016)

`P428Target8NCWDH` (CvS1) is the frozen headline with `CoversOm0p` removed and `WellDefG` a HYPOTHESIS of the inequality.

Facts proved here (no new headline variant is defined; `StrongWitness` is a predicate on one point):
* `perCube_of_classTriv`: a configuration equal to `1` on every bond of every factor-12 class cube is in the class
  `PerCubeRegular2 .. 12 ..` for EVERY `α₀ > 0` (so the adversary's smallness threshold `a₀` plays no role).
* `not_coerc_of_witness`: one in-class point where every printed object exists (`WellDefG`) and some admissible `B̃` with
  `‖B̃‖² > 0` has `⟨C B̃, Δ_k C B̃⟩ ≤ 0` refutes the inner claim `CoercG8AtNCWDH` for EVERY `α₀ > 0` and EVERY `γ₀ > 0`.
* **`not_WDH_of_witness`**: if for some `ell ≥ 2`, `a > 0` there are such points for infinitely many `m` and, for each of
  those `m`, infinitely many `R`, then `¬ P428Target8NCWDH`.  The witness is chosen AFTER `m, R` and does not depend on
  `a₀, γ₀`: the size of the negative value is irrelevant, only its sign.
* `coverage_necessary_strong_of_witness`: the same hypothesis gives `P428Target8 ∧ ¬ P428Target8NCWDH` and also
  `¬ P428Target8NC ∧ ¬ P428Target8NCWD`.

NOT proved here: the existence of such witnesses (see the lane NOTES/REPORT).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverSlab

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NoCover
open AdalyFormal.CoverStrong
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_zero)

/-! ## 1. class-trivial configurations are in the class at every `α₀` -/

/-- `U = 1` on every bond of every class cube (factor `f`) gives the class at every `α₀ > 0`. -/
theorem perCube_of_classTriv {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (hell : 0 < ell) (hM : 0 < M) (hf : 0 < f) (hα : 0 < α₀) (hη : 0 < η)
    (hU : ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M f k S sites j →
      ∀ e : Bond L, CubeBond sites e → U e = 1) :
    PerCubeRegular2 ell M f k S α₀ η U := by
  intro sites j hq
  refine ⟨fun _ => 1, fun _ => 0, fun e he => ⟨?_, ?_, ?_⟩, fun μ ν x _ _ => ?_, fun μ x _ => ?_⟩
  · simp [HT]
  · simp [periodicGaugeTransform, hU sites j hq e he]
  · rw [frobNorm_zero]; exact classBound_pos hell hM hf hα hη j 1
  · simp only [sub_self, smul_zero, frobNorm_zero]; exact classBound_pos hell hM hf hα hη j 2
  · rw [ddA_zero, frobNorm_zero]; exact classBound_pos hell hM hf hα hη j 3

/-! ## 2. the single-point witness -/

/-- **one strong-failure point** at `(ell, M, R, a)`: depth `k ≥ 1`, torus, admissible tower, `Λ` with `LambdaOK2`, a
configuration in the factor-12 class at EVERY `α₀ > 0`, every printed object existing (`WellDefG`), and an admissible
`B̃ ≠ 0` with `⟨C B̃, Δ_k C B̃⟩ ≤ 0`. -/
def StrongWitness (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ∃ Lu : PeriodicLatticeExtent, TorusOK ell M Lu ∧
  ∃ S : Tower (scaleUp ell k Lu), Admissible ell M R k S ∧
  ∃ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 ell M R k S Lam ∧
  ∃ U : LinkCfg (scaleUp ell k Lu),
    (∀ α₀ : ℝ, 0 < α₀ → PerCubeRegular2 ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U) ∧
    GenP.WellDefG (gparams ell k Lu hell S U a Lam) ∧
  ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧
    GenP.genForm (gparams ell k Lu hell S U a Lam)
      (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt)) ≤ 0

/-- a witness with a class-trivial configuration is a witness (the `∀ α₀` clause from `perCube_of_classTriv`). -/
theorem strongWitness_of_triv {ell M R : ℕ} (hell : 0 < ell) (hM : 0 < M) {a : ℝ} (k : ℕ) (hk : 1 ≤ k)
    (Lu : PeriodicLatticeExtent) (hT : TorusOK ell M Lu) (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S)
    (Lam : Set (PeriodicLatticeSite Lu)) (hL : LambdaOK2 ell M R k S Lam) (U : LinkCfg (scaleUp ell k Lu))
    (hU : ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ), IsClassCube ell M 12 k S sites j →
      ∀ e : Bond (scaleUp ell k Lu), CubeBond sites e → U e = 1)
    (hW : GenP.WellDefG (gparams ell k Lu hell S U a Lam)) (Bt : Bond Lu → SuTwo)
    (h1 : OnLambdaTildeIn Lam ell Bt) (h2 : OnLambdaT Lam Bt) (hE : 0 < bondEnergy Bt)
    (hF : GenP.genForm (gparams ell k Lu hell S U a Lam)
      (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt)) ≤ 0) :
    StrongWitness ell M R hell a := by
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  exact ⟨k, hk, Lu, hT, S, hS, Lam, hL, U,
    fun α₀ hα => perCube_of_classTriv hell hM (by norm_num) hα hη hU, hW, Bt, h1, h2, hE, hF⟩

/-- **one witness point refutes the inner claim at every `α₀ > 0`, `γ₀ > 0`.** -/
theorem not_coerc_of_witness {ell M R : ℕ} {hell : 0 < ell} {a : ℝ} (hw : StrongWitness ell M R hell a)
    {α₀ γ₀ : ℝ} (hα : 0 < α₀) (hγ : 0 < γ₀) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ Lu : PeriodicLatticeExtent, ¬ CoercG8AtNCWDH ell M R k hell a Lu 12 α₀ γ₀ := by
  obtain ⟨k, hk, Lu, hT, S, hS, Lam, hL, U, hU, hW, Bt, h1, h2, hE, hF⟩ := hw
  refine ⟨k, hk, Lu, fun hc => ?_⟩
  have h := hc hT S hS Lam hL U (hU α₀ hα) hW Bt h1 h2
  have : 0 < γ₀ * bondEnergy Bt := mul_pos hγ hE
  linarith

/-! ## 3. the outer quantifiers -/

/-- **a refutation of `P428Target8NCWDH` from witness points**: for some `ell ≥ 2` and `a > 0`, for infinitely many `m`
and, for each of them, infinitely many `R`, one `StrongWitness` point. -/
theorem not_WDH_of_witness (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ StrongWitness ell (ell ^ m) R (by omega) a) :
    ¬ P428Target8NCWDH := by
  intro H
  obtain ⟨m₀, -, hm⟩ := H ell hell a ha
  obtain ⟨m, hmm, hR⟩ := h m₀
  obtain ⟨R₀, hR₀⟩ := hm m hmm
  obtain ⟨R, hRR, hw⟩ := hR R₀
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hc⟩ := hR₀ R hRR
  have hMpos : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by
    have : 0 < ell ^ m := pow_pos (by omega) m
    exact_mod_cast this
  have hα : 0 < a₀ / (12 * ((ell ^ m : ℕ) : ℝ)) := by positivity
  have hle : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * (a₀ / (12 * ((ell ^ m : ℕ) : ℝ))) ≤ a₀ := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]
  obtain ⟨k, hk, Lu, hn⟩ := not_coerc_of_witness hw hα hγ
  exact hn (hc k hk Lu _ hα hle)

/-- the same hypothesis refutes the two other coverage-free readings. -/
theorem not_NC_NCWD_of_witness (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ StrongWitness ell (ell ^ m) R (by omega) a) :
    ¬ AdalyFormal.NoCover.P428Target8NC ∧ ¬ P428Target8NCWD :=
  not_NC_of_not_WDH (not_WDH_of_witness ell hell a ha h)

/-- **`coverage_necessary_strong`, conditional on witness points**: the r8 headline holds and its "granting existence"
coverage-free reading is false. -/
theorem coverage_necessary_strong_of_witness (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ StrongWitness ell (ell ^ m) R (by omega) a) :
    AdalyFormal.StatementLaneG.P428Target8 ∧ ¬ P428Target8NCWDH :=
  ⟨AdalyFormal.M2RightInv.p428Target8, not_WDH_of_witness ell hell a ha h⟩

#print axioms perCube_of_classTriv
#print axioms strongWitness_of_triv
#print axioms not_coerc_of_witness
#print axioms not_WDH_of_witness
#print axioms not_NC_NCWD_of_witness
#print axioms coverage_necessary_strong_of_witness

end AdalyFormal.CoverSlab
