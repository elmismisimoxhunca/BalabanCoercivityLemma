/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import CovLemma24
import AdalyFormal.Balaban.RegularUCurvedWitness

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

/-!
# Non-vacuity and junk-guards for `CovariantLemma24`.

A general-`U` theorem whose hypothesis class contains only `U = 1` proves nothing about general `U`.
This module answers that objection with theorems, not with prose.

* **§2 — the threshold class contains a GENUINELY CURVED background.** `witU` is `rotElem t` on one
  bond of the `9³` torus at `ell = 3`. Its plaquette holonomy is `≠ 1` (`witU_curved`), its
  `α₁ = frobSupBond` is STRICTLY POSITIVE (`witU_alpha_pos`), and it MEETS the threshold
  (`witU_alpha_le_threshold`). So `covariant_lemma24_positive` fires at a background that is not
  flat, not gauge-equivalent to flat (its holonomy is not central), and not `ell = 2`.
* **§3 — the threshold genuinely EXCLUDES.** `bigU` (`rotElem 1` on the same bond) has `α₁ = 2` and
  FAILS the threshold at every `ell ≥ 1` (`bigU_fails_threshold`). A restriction that excludes
  nothing is not a restriction.
* **§4 — a NONZERO admissible `𝔰𝔲(2)` field**, with `bondEnergy > 0`, so both sides of the certified
  inequality are strictly positive numbers (`covariant_lemma24_nonvacuous_curved`), not `0 ≤ 0`.
* **§5 — S82 junk substitution.** At `A = 0` every quantity is `0` and the inequality is
  content-free; at `U = 1` the coefficient is `α₁`-free and the statement degenerates to exactly
  half the flat leg. Both are stated so neither can be mistaken for content.
-/

namespace AdalyFormal.Balaban.CovLemma24Witness

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.BlockPoincareLemma24
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.Lemma24GeneralEll
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.RegularUCurvedWitness
open AdalyFormal.Balaban.CovariantLemma24

/-! ## §1 — the arena: the `9³` torus at `ell = 3` (REUSED from `Lemma24GeneralEll`, LAW-19). -/

/-- The plaquette direction pair `⟨0,1⟩`; the curved bond's own direction is the first slot. -/
def witDir : PeriodicPlaquetteDirections := ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩

/-- The single active bond: direction `0` at the maximal site of `witL3` (REUSED —
`AdmissibleSubspace.generalWrapBond`). -/
def witBond : Bond witL3 := generalWrapBond witL3

theorem witBond_dir : witBond.2 = (0 : Fin 3) := rfl

/-! ## §2 — a GENUINELY CURVED background inside the threshold class. -/

/-- The curved background: `rotElem t` on `witBond`, `1` on every other bond. Uses the tree's own
extent-generic `RegularUCurvedWitness.bondU` (LAW-19); `curvedFamilyU` itself is pinned to `witL5`
and cannot be used at `ell = 3`. -/
noncomputable def witU (t : ℝ) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL3 :=
  bondU witBond (AdalyFormal.Balaban.NonFlatBackground.rotElem t)

/-- The rotation parameter. `10⁻⁵` is chosen with room: it gives `α₁ ≤ 2√2·10⁻⁵ < 1/5022`, the
`ell = 3` threshold. -/
noncomputable def witT : ℝ := 1 / 100000

/-- **`α₁(witU t) = √(8t²/(1+t²))`, EXACTLY** — the same closed form the tree proves for
`curvedFamilyU`, here at the `ell = 3` arena. -/
theorem frobSupBond_witU (t : ℝ) :
    frobSupBond (witU t) = Real.sqrt (8 * t ^ 2 / (1 + t ^ 2)) := by
  rw [witU, frobSupBond_bondU, AdalyFormal.Balaban.NonFlatBackground.rotElem_coe,
    AdalyFormal.Balaban.RMapLipschitz.frobNorm,
    AdalyFormal.Balaban.NonFlatBackground.frobSq_rotM_sub_one]

/-- **`α₁ > 0` at the witness** — the background is seen as non-flat by the very quantity the
theorem's threshold constrains. -/
theorem witU_alpha_pos : 0 < frobSupBond (witU witT) := by
  rw [frobSupBond_witU]
  refine Real.sqrt_pos.mpr ?_
  rw [witT]
  norm_num

/-- **The witness MEETS the `ell = 3` threshold**: `α₁ ≤ 1/(186·3³) = 1/5022`.
`α₁ = √(8t²/(1+t²)) ≤ √(8t²) = 2√2·t ≤ 3t` and `3·10⁻⁵ < 1/5022`. -/
theorem witU_alpha_le_threshold :
    frobSupBond (witU witT) ≤ 1 / (186 * ((3 : ℕ) : ℝ) ^ 3) := by
  rw [frobSupBond_witU]
  have hle : 8 * witT ^ 2 / (1 + witT ^ 2) ≤ (1 / (186 * ((3 : ℕ) : ℝ) ^ 3)) ^ 2 := by
    rw [witT]
    norm_num
  refine (Real.sqrt_le_sqrt hle).trans (le_of_eq ?_)
  exact Real.sqrt_sq (by norm_num)

/-- **THE BACKGROUND IS GENUINELY CURVED**: the plaquette holonomy at `(maximalSite, ⟨0,1⟩)` is
`rotElem witT ≠ 1`, so `witU witT` is not flat and not gauge-equivalent to a flat configuration
through a central holonomy. -/
theorem witU_curved :
    holonomyElem (witU witT) (witBond.1, witDir)
      ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [holonomy_singleBond_base_plaquette (witU witT) witBond.1 witDir
    (AdalyFormal.Balaban.NonFlatBackground.rotElem witT)
    (bondU_at witBond _) (fun _ hb => bondU_off witBond _ hb) (by decide)]
  refine AdalyFormal.Balaban.NonFlatBackground.rotElem_ne_one ?_
  rw [witT]; norm_num

/-! ## §3 — the threshold EXCLUDES. -/

/-- `rotElem 1` on the same bond: `α₁ = √(8/2) = 2`. -/
noncomputable def bigU : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL3 :=
  witU 1

theorem frobSupBond_bigU : frobSupBond bigU = 2 := by
  rw [bigU, frobSupBond_witU]
  rw [show (8 : ℝ) * 1 ^ 2 / (1 + 1 ^ 2) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- **THE THRESHOLD IS A GENUINE RESTRICTION.** `bigU` fails it at EVERY `ell ≥ 1`, because
`1/(186·ell³) ≤ 1/186 < 2`. -/
theorem bigU_fails_threshold {ell : ℕ} (hell : 0 < ell) :
    ¬ (frobSupBond bigU ≤ 1 / (186 * (ell : ℝ) ^ 3)) := by
  rw [frobSupBond_bigU]
  have h1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h3 : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ h1
  have : 1 / (186 * (ell : ℝ) ^ 3) ≤ 1 / 186 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [h3]
  intro hc
  linarith [this, hc]

/-- **AND IT FAILS FOR THE FLOOR, NOT ONLY FOR THE HYPOTHESIS**: at `bigU` the certified
coefficient is strictly NEGATIVE at every `ell ≥ 1`, so the theorem says nothing there. Stated so
no reader can take `covariant_lemma24` for an unconditional positive floor. -/
theorem bigU_coefficient_neg {ell : ℕ} (hell : 0 < ell) :
    (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond bigU ^ 2 < 0 := by
  rw [frobSupBond_bigU]
  have h1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h5 : (1 : ℝ) ≤ (ell : ℝ) ^ 5 := one_le_pow₀ h1
  have : (1 : ℝ) / (ell : ℝ) ^ 5 ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact h5
  nlinarith [this]

/-! ## §4 — a NONZERO admissible `𝔰𝔲(2)` field, and the fully instantiated statement. -/

/-- The nonzero admissible field: the tree's own scalar admissible indicator (REUSED,
`AdmissibleSubspace.generalWrapConfig`) times the fixed unit generator `pauliE1`. -/
noncomputable def witA : Bond witL3 → SuTwo :=
  fun b => generalWrapConfig witL3 b • pauliE1

theorem norm_pauliE1 : ‖pauliE1‖ = 1 := by
  have h : ‖pauliE1‖ ^ 2 = 1 := by rw [normSq_eq_hsInner, hsInner_e1_e1]
  nlinarith [norm_nonneg pauliE1, h]

/-- `witA` satisfies CMP96 (2.121) on the `𝔰𝔲(2)` carrier. -/
theorem witA_admissible : SuAdmissible witL3 3 witA := by
  intro y hy x hx b hb
  have h0 : generalWrapConfig witL3 b = 0 :=
    (mem_admissibleSubspaceInter.mp (generalWrapConfig_mem (ell := 3))) y hy x hx b hb
  rw [witA, h0, zero_smul]

/-- `∑_b ‖witA b‖² = ∑_b (generalWrapConfig b)²`, using `‖pauliE1‖ = 1`. -/
theorem bondEnergy_witA : bondEnergy witA = bondNormSq (generalWrapConfig witL3) := by
  unfold bondEnergy bondNormSq
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [witA, norm_smul, norm_pauliE1, Real.norm_eq_abs]
  rw [mul_one, sq_abs]

theorem bondEnergy_witA_pos : 0 < bondEnergy witA := by
  rw [bondEnergy_witA]
  exact witnessNorm_pos

/-- **NON-VACUITY, AT A CURVED BACKGROUND, AT `ell = 3`.** All four facts at once: the background
is curved (`α₁ > 0`), it meets the threshold, the certified coefficient is STRICTLY POSITIVE, the
right-hand side is STRICTLY POSITIVE, and the certified inequality holds between them. Nothing here
is `0 ≤ 0` and nothing here is an `ell = 2` or `U = 1` instance. -/
theorem covariant_lemma24_nonvacuous_curved :
    0 < frobSupBond (witU witT)
    ∧ 0 < (1 / 360) * (1 / ((3 : ℕ) : ℝ) ^ 5) - 96 * frobSupBond (witU witT) ^ 2
    ∧ 0 < ((1 / 360) * (1 / ((3 : ℕ) : ℝ) ^ 5) - 96 * frobSupBond (witU witT) ^ 2)
        * bondEnergy witA
    ∧ ((1 / 360) * (1 / ((3 : ℕ) : ℝ) ^ 5) - 96 * frobSupBond (witU witT) ^ 2)
        * bondEnergy witA
      ≤ ((3 : ℕ) : ℝ) * coarseQEnergyCov (witU witT) 3 witA + curlEnergyCov (witU witT) witA := by
  obtain ⟨hpos, hineq⟩ := covariant_lemma24_positive (L := witL3) (ell := 3) (by norm_num)
    witL3_strict witL3_dvd (witU witT) witU_alpha_le_threshold witA witA_admissible
  exact ⟨witU_alpha_pos, hpos, mul_pos hpos bondEnergy_witA_pos, hineq⟩

/-! ## §5 — S82 GARBAGE SUBSTITUTION: what the theorem does NOT say. -/

/-- **At `A = 0` the certified inequality is `0 ≤ 0`** and carries no information. Stated so the
non-vacuity above is not read off a degenerate point. -/
theorem junk_A_zero {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) :
    coarseQEnergyCov U ell (0 : Bond L → SuTwo) = 0
    ∧ curlEnergyCov U (0 : Bond L → SuTwo) = 0
    ∧ bondEnergy (0 : Bond L → SuTwo) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold coarseQEnergyCov
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rw [show (0 : Bond L → SuTwo) = (0 : ℝ) • (0 : Bond L → SuTwo) by simp,
      lineCoarseRestrictCov_smul]
    simp
  · unfold curlEnergyCov plaqEnergy
    refine Finset.sum_eq_zero (fun p _ => ?_)
    rw [show curlValueCovariant U (0 : Bond L → SuTwo) p = 0 by
      simp [curlValueCovariant]]
    simp
  · unfold bondEnergy
    exact Finset.sum_eq_zero (fun b _ => by simp)

/-- **At `U = 1` the coefficient is `α₁`-free** and the theorem degenerates to exactly HALF the flat
leg `suTwo_lemma24_flat`. So the general-`U` statement is not secretly the flat one dressed up: at
`U = 1` it is strictly weaker than what §3 of `CovLemma24` already gives. -/
theorem junk_trivialU {L : PeriodicLatticeExtent} : frobSupBond (trivialU L) = 0 :=
  AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU L

theorem covariant_coefficient_at_trivialU {L : PeriodicLatticeExtent} (ell : ℕ) :
    (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond (trivialU L) ^ 2
      = (1 / 2) * ((1 / 180) * (1 / (ell : ℝ) ^ 5)) := by
  rw [junk_trivialU]
  ring

#print axioms witDir
#print axioms witBond
#print axioms witU
#print axioms witT
#print axioms frobSupBond_witU
#print axioms witU_alpha_pos
#print axioms witU_alpha_le_threshold
#print axioms witU_curved
#print axioms bigU
#print axioms frobSupBond_bigU
#print axioms bigU_fails_threshold
#print axioms bigU_coefficient_neg
#print axioms witA
#print axioms norm_pauliE1
#print axioms witA_admissible
#print axioms bondEnergy_witA
#print axioms bondEnergy_witA_pos
#print axioms covariant_lemma24_nonvacuous_curved
#print axioms junk_A_zero
#print axioms junk_trivialU
#print axioms covariant_coefficient_at_trivialU
#print axioms witBond_dir

end AdalyFormal.Balaban.CovLemma24Witness
