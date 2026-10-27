/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import CovLemma24Sharp

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# A background OUTSIDE the certified class at which the covariant Lemma 2.4 holds with the FULL
# flat constant — proved, not conjectured.

`CovLemma24Sharp` §3 showed that the covariant CURL at `U ≡ −1` is the flat curl. This module
closes the other half: the covariant AVERAGING operator `Q(U)` at `U ≡ −1` is also the flat one,
because `rZeroA` transports by `RMap (periodicPathHolonomy U ·)` and `RMap` kills the center of
`SU(2)`. The induction over the path list is the only new content.

Consequence (`center_outside_certified_class`), all three facts at once, for every `ell ≥ 2`:

* `frobSupBond (negOneU L) = 2√2`, so the threshold `α₁ ≤ 1/(186·ell³)` **FAILS**;
* the certified coefficient `(1/360)·ell⁻⁵ − 96·α₁²` is **strictly NEGATIVE** there, so
  `covariant_lemma24` says literally nothing at that background;
* and yet the covariant Lemma 2.4 **HOLDS there with the full flat constant `(1/180)·ell⁻⁵`** —
  better than `covariant_lemma24` delivers anywhere.

**So `frobSupBond` is a strictly conservative hypothesis, and this is a proved instance of the gap,
not an estimate of it.** The operators see `U` only through the ADJOINT action `RMap U`; the
natural parameter is `sup_b ‖RMap (U b) − id‖`. Re-deriving the two drift bounds in that parameter
is not done here (see SCOPE §7 for the exact stopping point); what is done here is to prove that
the parameter currently used is not the right one.
-/

namespace AdalyFormal.Balaban.CovLemma24Center

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.Q1Real
open AdalyFormal.Balaban.QOne
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.CovariantLemma24
open AdalyFormal.Balaban.CovLemma24Sharp

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the center element is its own inverse, and its adjoint action is trivial. -/

theorem negOneElem_mul_self : negOneElem * negOneElem = 1 := by
  apply Subtype.ext
  show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * (-1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
  simp

theorem negOneElem_inv : negOneElem⁻¹ = negOneElem :=
  inv_eq_of_mul_eq_one_right negOneElem_mul_self

theorem RMap_negOneElem_inv : RMap negOneElem⁻¹ = (LinearMap.id : SuTwo →ₗ[ℝ] SuTwo) := by
  rw [negOneElem_inv]; exact RMap_negOneElem

/-! ## §2 — the path holonomy of the center background acts trivially. -/

/-- **The only new content of this module.** By induction on the path: every factor is
`negOneElem` or its inverse, and `RMap` sends both to the identity. -/
theorem RMap_periodicPathHolonomy_negOneU :
    ∀ (p : List (Fin 3 × Bool)) (x : PeriodicLatticeSite L),
      RMap (periodicPathHolonomy (negOneU L) x p) = (LinearMap.id : SuTwo →ₗ[ℝ] SuTwo)
  | [], x => by
      show RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = _
      exact RMap_one
  | step :: rest, x => by
      have ih := RMap_periodicPathHolonomy_negOneU rest (periodicLatticeStep x step)
      have hfac : RMap (if step.2 then negOneU L (x, step.1)
          else (negOneU L (periodicLatticeStep x step, step.1))⁻¹)
          = (LinearMap.id : SuTwo →ₗ[ℝ] SuTwo) := by
        by_cases h : step.2
        · rw [if_pos h]; exact RMap_negOneElem
        · rw [if_neg h]; exact RMap_negOneElem_inv
      show RMap ((if step.2 then negOneU L (x, step.1)
        else (negOneU L (periodicLatticeStep x step, step.1))⁻¹)
          * periodicPathHolonomy (negOneU L) (periodicLatticeStep x step) rest) = _
      rw [RMap_mul, hfac, ih]
      exact LinearMap.id_comp _

/-! ## §3 — hence the covariant averaging operator at the center IS the flat one. -/

theorem rZeroA_negOneU (cMinus x : PeriodicLatticeSite L) (A : Bond L → SuTwo) (μ : Fin 3)
    (ell : ℕ) :
    rZeroA (negOneU L) cMinus x A μ ell = ∑ i ∈ Finset.range ell, A (pathSite x μ i, μ) := by
  simp only [rZeroA, RMap_periodicPathHolonomy_negOneU, LinearMap.id_coe, id_eq]

theorem lineCoarseRestrictCov_negOneU (ell : ℕ) (A : Bond L → SuTwo) (b : CoarseBond L ell) :
    lineCoarseRestrictCov (negOneU L) ell A b = lineCoarseRestrictCov (trivialU L) ell A b := by
  simp only [lineCoarseRestrictCov, rZeroA_negOneU, rZeroA_trivialU]

theorem coarseQEnergyCov_negOneU (ell : ℕ) (A : Bond L → SuTwo) :
    coarseQEnergyCov (negOneU L) ell A = coarseQEnergyCov (trivialU L) ell A := by
  unfold coarseQEnergyCov
  exact Finset.sum_congr rfl (fun c _ => by rw [lineCoarseRestrictCov_negOneU])

/-! ## §4 — the payoff. -/

/-- **The covariant Lemma 2.4 holds at `U ≡ −1` with the FULL flat constant `(1/180)·ell⁻⁵`** —
strictly better than `covariant_lemma24`'s own `(1/360)·ell⁻⁵ − 96α₁²`, which is NEGATIVE there. -/
theorem covariant_lemma24_at_center {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) :
    (1 / 180) * (1 / (ell : ℝ) ^ 5) * bondEnergy A
      ≤ (ell : ℝ) * coarseQEnergyCov (negOneU L) ell A + curlEnergyCov (negOneU L) A := by
  rw [coarseQEnergyCov_negOneU, curlEnergyCov_negOneU]
  exact suTwo_lemma24_flat hell2 hstrict hdvd A hadm

/-- **THE HYPOTHESIS IS STRICTLY CONSERVATIVE, EXHIBITED.** At `U ≡ −1`, simultaneously:
the threshold FAILS, the certified coefficient is NEGATIVE, and the full flat floor HOLDS. -/
theorem center_outside_certified_class {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) :
    ¬ (frobSupBond (negOneU L) ≤ 1 / (186 * (ell : ℝ) ^ 3))
    ∧ (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond (negOneU L) ^ 2 < 0
    ∧ (1 / 180) * (1 / (ell : ℝ) ^ 5) * bondEnergy A
        ≤ (ell : ℝ) * coarseQEnergyCov (negOneU L) ell A + curlEnergyCov (negOneU L) A := by
  have hell : 0 < ell := by omega
  refine ⟨negOneU_fails_threshold hell, ?_, covariant_lemma24_at_center hell2 hstrict hdvd A hadm⟩
  have h1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h5 : (1 : ℝ) ≤ (ell : ℝ) ^ 5 := one_le_pow₀ h1
  have hinv : (1 : ℝ) / (ell : ℝ) ^ 5 ≤ 1 := by
    rw [div_le_one (by linarith)]; exact h5
  have hsq : frobSupBond (negOneU L) ^ 2 = 8 := by
    rw [frobSupBond_negOneU, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  rw [hsq]
  nlinarith [hinv]

#print axioms negOneElem_mul_self
#print axioms negOneElem_inv
#print axioms RMap_negOneElem_inv
#print axioms RMap_periodicPathHolonomy_negOneU
#print axioms rZeroA_negOneU
#print axioms lineCoarseRestrictCov_negOneU
#print axioms coarseQEnergyCov_negOneU
#print axioms covariant_lemma24_at_center
#print axioms center_outside_certified_class

end AdalyFormal.Balaban.CovLemma24Center
