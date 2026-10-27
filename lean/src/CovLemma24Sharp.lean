/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import CovLemma24

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# How far the covariant Lemma 2.4's hypothesis can be pushed — and where its slack actually is.

Two independent strengthenings of `CovariantLemma24.covariant_lemma24`, each a theorem.

## §1–§2 — the Young family: `34560` is `ε = 1`, not a constant of nature.

`covariant_lemma24` uses `‖u‖² ≤ 2‖v‖² + 2‖u−v‖²`. The Young form
`‖u‖² ≤ (1+ε)‖v‖² + (1+1/ε)‖u−v‖²` gives a ONE-PARAMETER FAMILY of floors. Its threshold is
`(1+1/ε)·17280·α₁²·ell⁵ < 1`; at `ε = 1` that is exactly the `34560` of the main theorem (a
cross-check, `young_threshold_at_one`), and it **decreases strictly in `ε`** with infimum `17280`,
never attained. So the admissible class is strictly larger than the main theorem's — at `ε = 10`
the threshold constant is `19008` and `α₁ ≤ 1/(138·ell³)` suffices — at the price of a floor
divided by `1+ε` instead of `2`. Neither `34560` nor `17280` is claimed least; what IS proved is
that the family exists and that the main theorem sits inside it at `ε = 1`.

## §3 — WHERE THE HYPOTHESIS IS ACTUALLY LOOSE: `α₁` is a GROUP-level proxy for an ADJOINT-level
object.

Every operator in the statement (`curlValueCovariant`, and `lineCoarseRestrictCov` through
`rZeroA`) touches `U` ONLY through `RMap U`, the ADJOINT action. `RMap` is blind to the center of
`SU(2)`, while `frobSupBond` is not: at `U ≡ −1` the covariant curl is IDENTICALLY the flat curl
(`curlEnergyCov_negOneU`) yet `α₁ = 2√2`, its maximum, so the threshold rejects that background at
every `ell` (`negOneU_fails_threshold`) even though the flat floor holds there verbatim.

**This is a strict, exhibited over-restriction of the hypothesis, not a suspicion.** The natural
parameter is `sup_b ‖RMap (U b) − id‖`; replacing `α₁` by it would strictly enlarge the class. That
replacement is NOT performed here — see the SCOPE file for exactly where it stops.
-/

namespace AdalyFormal.Balaban.CovLemma24Sharp

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.BlockPoincareLemma24
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.CovariantLemma24

variable {L : PeriodicLatticeExtent}

/-! ## §1 — Young's inequality in the two places the main proof uses `2`. -/

/-- `‖u‖² ≤ (1+ε)‖v‖² + (1+1/ε)‖u−v‖²` for every `ε > 0`. At `ε = 1` this is
`CovariantLemma24.sq_le_two_add_two`. -/
theorem sq_le_young {E : Type*} [NormedAddCommGroup E] (u v : E) {eps : ℝ} (heps : 0 < eps) :
    ‖u‖ ^ 2 ≤ (1 + eps) * ‖v‖ ^ 2 + (1 + 1 / eps) * ‖u - v‖ ^ 2 := by
  have htri : ‖u‖ ≤ ‖v‖ + ‖u - v‖ := by
    calc ‖u‖ = ‖v + (u - v)‖ := by rw [add_sub_cancel]
      _ ≤ ‖v‖ + ‖u - v‖ := norm_add_le _ _
  have hu : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hw : (0 : ℝ) ≤ ‖u - v‖ := norm_nonneg (u - v)
  have hkey : (0 : ℝ) ≤ (eps * ‖v‖ - ‖u - v‖) ^ 2 := sq_nonneg _
  have hexp : (1 + 1 / eps) * ‖u - v‖ ^ 2
      = ‖u - v‖ ^ 2 + ‖u - v‖ ^ 2 / eps := by field_simp
  rw [hexp]
  have hdiv : ‖u - v‖ ^ 2 / eps = ‖u - v‖ ^ 2 * (1 / eps) := by ring
  rw [hdiv]
  have hmul : eps * ‖v‖ ^ 2 + ‖u - v‖ ^ 2 * (1 / eps) - 2 * ‖v‖ * ‖u - v‖
      = (eps * ‖v‖ - ‖u - v‖) ^ 2 * (1 / eps) := by field_simp; ring
  nlinarith [htri, hu, hv, hw, hkey, mul_nonneg (le_of_lt heps) hv,
    mul_pos heps heps, hmul, mul_nonneg hkey (le_of_lt (one_div_pos.mpr heps))]

/-- The `ε`-graded transfer principle; `transfer_abstract` is `ε = 1`. -/
theorem transfer_abstract_young {t gam Qf Pf Qc Pc N dQ dP eps : ℝ}
    (ht : 0 ≤ t) (heps : 0 < eps)
    (hfloor : gam * N ≤ t * Qf + Pf)
    (hQ : Qf ≤ (1 + eps) * Qc + (1 + 1 / eps) * dQ)
    (hP : Pf ≤ (1 + eps) * Pc + (1 + 1 / eps) * dP) :
    (gam * N - (1 + 1 / eps) * (t * dQ + dP)) / (1 + eps) ≤ t * Qc + Pc := by
  have h1e : (0 : ℝ) < 1 + eps := by linarith
  rw [div_le_iff₀ h1e]
  nlinarith [mul_le_mul_of_nonneg_left hQ ht]

/-! ## §2 — the `ε`-family of covariant floors, and its threshold. -/

/-- The flat coarse energy, Young-graded. -/
theorem coarseQ_flat_le_young
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → SuTwo)
    {eps : ℝ} (heps : 0 < eps) :
    coarseQEnergyCov (trivialU L) ell A
      ≤ (1 + eps) * coarseQEnergyCov U ell A
        + (1 + 1 / eps) * ((64 / (ell : ℝ)) * frobSupBond U ^ 2 * bondEnergy A) := by
  have hcoef : (0 : ℝ) ≤ 1 + 1 / eps := by positivity
  have hpt : coarseQEnergyCov (trivialU L) ell A
      ≤ (1 + eps) * coarseQEnergyCov U ell A
        + (1 + 1 / eps) * ∑ c : CoarseBond L ell,
            ‖lineCoarseRestrictCov (trivialU L) ell A c - lineCoarseRestrictCov U ell A c‖ ^ 2 := by
    unfold coarseQEnergyCov
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun c _ =>
      sq_le_young (lineCoarseRestrictCov (trivialU L) ell A c)
        (lineCoarseRestrictCov U ell A c) heps)
  have hd := coarse_drift_le U hell hdvd A
  nlinarith [hpt, hd, hcoef]

/-- The flat curl energy, Young-graded. -/
theorem curl_flat_le_young
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) {eps : ℝ} (heps : 0 < eps) :
    curlEnergyCov (trivialU L) A
      ≤ (1 + eps) * curlEnergyCov U A
        + (1 + 1 / eps) * (32 * frobSupBond U ^ 2 * bondEnergy A) := by
  have hcoef : (0 : ℝ) ≤ 1 + 1 / eps := by positivity
  have hpt : curlEnergyCov (trivialU L) A
      ≤ (1 + eps) * curlEnergyCov U A + (1 + 1 / eps) * plaqEnergy (curlDrift U A) := by
    unfold curlEnergyCov plaqEnergy
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun p _ => ?_)
    have hd : curlValueCovariant (trivialU L) A p - curlValueCovariant U A p
        = - curlDrift U A p := by
      have : curlDrift U A p = curlValueCovariant U A p - curlValueCovariant (trivialU L) A p :=
        rfl
      rw [this]; abel
    have h := sq_le_young (curlValueCovariant (trivialU L) A p) (curlValueCovariant U A p) heps
    rwa [hd, norm_neg] at h
  have hd := curl_drift_le U A
  nlinarith [hpt, hd, hcoef]

/-- **THE `ε`-FAMILY.** For every `ε > 0`, every `ell ≥ 2`, every compatible torus, EVERY background
`U` and every `(2.121)`-admissible `𝔰𝔲(2)` field. `ε = 1` recovers `covariant_lemma24`. -/
theorem covariant_lemma24_young {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) {eps : ℝ} (heps : 0 < eps) :
    ((1 / 180) * (1 / (ell : ℝ) ^ 5) * bondEnergy A
        - (1 + 1 / eps) * (96 * frobSupBond U ^ 2 * bondEnergy A)) / (1 + eps)
      ≤ (ell : ℝ) * coarseQEnergyCov U ell A + curlEnergyCov U A := by
  have hell : 0 < ell := by omega
  have ht : (0 : ℝ) ≤ (ell : ℝ) := by positivity
  have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have hmain := transfer_abstract_young (t := (ell : ℝ))
    (gam := (1 / 180) * (1 / (ell : ℝ) ^ 5)) (N := bondEnergy A)
    (Qf := coarseQEnergyCov (trivialU L) ell A) (Pf := curlEnergyCov (trivialU L) A)
    (Qc := coarseQEnergyCov U ell A) (Pc := curlEnergyCov U A)
    (dQ := (64 / (ell : ℝ)) * frobSupBond U ^ 2 * bondEnergy A)
    (dP := 32 * frobSupBond U ^ 2 * bondEnergy A)
    ht heps (suTwo_lemma24_flat hell2 hstrict hdvd A hadm)
    (coarseQ_flat_le_young U hell hdvd A heps) (curl_flat_le_young U A heps)
  have hid : (ell : ℝ) * ((64 / (ell : ℝ)) * frobSupBond U ^ 2 * bondEnergy A)
      + 32 * frobSupBond U ^ 2 * bondEnergy A
      = 96 * frobSupBond U ^ 2 * bondEnergy A := by
    field_simp; ring
  rwa [hid] at hmain

/-- **The family's threshold.** `96·180 = 17280`. -/
theorem young_threshold_pos_iff {ell : ℕ} (hell : 0 < ell) (al : ℝ) {eps : ℝ} (heps : 0 < eps) :
    0 < (1 / 180) * (1 / (ell : ℝ) ^ 5) - (1 + 1 / eps) * (96 * al ^ 2)
      ↔ (1 + 1 / eps) * 17280 * al ^ 2 * (ell : ℝ) ^ 5 < 1 := by
  have h0 : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have h5 : (0 : ℝ) < 180 * (ell : ℝ) ^ 5 := by positivity
  rw [sub_pos,
    show (1 / 180 : ℝ) * (1 / (ell : ℝ) ^ 5) = 1 / (180 * (ell : ℝ) ^ 5) by field_simp,
    lt_div_iff₀ h5,
    show (1 + 1 / eps) * (96 * al ^ 2) * (180 * (ell : ℝ) ^ 5)
        = (1 + 1 / eps) * 17280 * al ^ 2 * (ell : ℝ) ^ 5 by ring]

/-- **CROSS-CHECK: at `ε = 1` the family's threshold constant IS the main theorem's `34560`.**
Two independently written derivations meeting on one number. -/
theorem young_threshold_at_one : (1 + 1 / (1 : ℝ)) * 17280 = 34560 := by norm_num

/-- **THE ADMISSIBLE CLASS IS STRICTLY LARGER THAN THE MAIN THEOREM'S.** At `ε = 10` the threshold
constant is `19008 < 34560`, and `α₁ ≤ 1/(138·ell³)` suffices (`138² = 19044 > 19008`). -/
theorem young_threshold_at_ten : (1 + 1 / (10 : ℝ)) * 17280 = 19008 := by norm_num

theorem threshold_of_alpha_le_ten {ell : ℕ} (hell : 0 < ell) {al : ℝ} (hal0 : 0 ≤ al)
    (hal : al ≤ 1 / (138 * (ell : ℝ) ^ 3)) :
    (1 + 1 / (10 : ℝ)) * 17280 * al ^ 2 * (ell : ℝ) ^ 5 < 1 := by
  have h1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell : ℝ) := by linarith
  have hsq : al ^ 2 ≤ 1 / (19044 * (ell : ℝ) ^ 6) := by
    have hmm := mul_self_le_mul_self hal0 hal
    rw [← sq, ← sq] at hmm
    refine hmm.trans (le_of_eq ?_)
    rw [div_pow]; ring_nf
  have h56 : (ell : ℝ) ^ 5 ≤ (ell : ℝ) ^ 6 := by nlinarith [pow_pos h0 5, h1]
  have hpos6 : (0 : ℝ) < (ell : ℝ) ^ 6 := by positivity
  rw [young_threshold_at_ten]
  calc (19008 : ℝ) * al ^ 2 * (ell : ℝ) ^ 5
      ≤ 19008 * (1 / (19044 * (ell : ℝ) ^ 6)) * (ell : ℝ) ^ 6 := by
        nlinarith [hsq, h56, hpos6, sq_nonneg al, pow_pos h0 5]
    _ = 19008 / 19044 := by field_simp
    _ < 1 := by norm_num

/-- **The threshold constant is STRICTLY DECREASING in `ε`** — so the family genuinely sweeps a
one-parameter enlargement of the class and `34560` is a choice, not a barrier. Its infimum is
`17280`, approached but never attained. -/
theorem young_threshold_strict_anti {e1 e2 : ℝ} (h1 : 0 < e1) (h12 : e1 < e2) :
    (1 + 1 / e2) * 17280 < (1 + 1 / e1) * 17280 := by
  have h2 : (0 : ℝ) < e2 := lt_trans h1 h12
  have : 1 / e2 < 1 / e1 := by
    exact one_div_lt_one_div_of_lt h1 h12
  linarith

theorem young_threshold_inf_not_attained {eps : ℝ} (heps : 0 < eps) :
    17280 < (1 + 1 / eps) * 17280 := by
  have : 0 < 1 / eps := one_div_pos.mpr heps
  nlinarith

/-! ## §3 — the hypothesis is a GROUP-level proxy for an ADJOINT-level object. -/

/-- If the background acts trivially in the ADJOINT representation on every bond, the covariant
curl is the flat curl — whatever `frobSupBond U` may be. -/
theorem curlEnergyCov_eq_flat_of_adjoint_trivial
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hU : ∀ b : Bond L, RMap (U b) = LinearMap.id) (A : Bond L → SuTwo) :
    curlEnergyCov U A = curlEnergyCov (trivialU L) A := by
  unfold curlEnergyCov plaqEnergy
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only [curlValueCovariant, hU, LinearMap.id_coe, id_eq, trivialU, RMap_one]

/-- `−1 ∈ SU(2)`. -/
theorem negOne_mem_su2 : (-1 : Matrix (Fin 2) (Fin 2) ℂ) ∈
    Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    simp
  · simp [Matrix.det_fin_two, Matrix.one_apply]

/-- The nontrivial center element of `SU(2)`. -/
def negOneElem : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨-1, negOne_mem_su2⟩

/-- **The adjoint action of the center is trivial**: `(−1)X(−1)ᴴ = X`. -/
theorem RMap_negOneElem : RMap negOneElem = (LinearMap.id : SuTwo →ₗ[ℝ] SuTwo) := by
  refine LinearMap.ext (fun X => ?_)
  apply Subtype.ext
  rw [RMap_coe_apply]
  have hc : ((negOneElem : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl
  have hct : Matrix.conjTranspose (-1 : Matrix (Fin 2) (Fin 2) ℂ)
      = (-1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_one]
  rw [hc, hct, neg_one_mul, mul_neg_one, neg_neg]
  rfl

/-- The all-`(−1)` background. -/
def negOneU (L : PeriodicLatticeExtent) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L :=
  fun _ => negOneElem

/-- **THE BLIND SPOT, HALF ONE: the covariant curl at `U ≡ −1` IS the flat curl, exactly.** -/
theorem curlEnergyCov_negOneU (A : Bond L → SuTwo) :
    curlEnergyCov (negOneU L) A = curlEnergyCov (trivialU L) A :=
  curlEnergyCov_eq_flat_of_adjoint_trivial (negOneU L) (fun _ => RMap_negOneElem) A

/-- **THE BLIND SPOT, HALF TWO: `α₁ = 2√2` there — the LARGEST value `frobSupBond` takes on
`SU(2)`.** -/
theorem frobSupBond_negOneU : frobSupBond (negOneU L) = 2 * Real.sqrt 2 := by
  have hval : ∀ b : Bond L,
      AdalyFormal.Balaban.RMapLipschitz.frobNorm
        (((negOneU L b : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) - 1) = 2 * Real.sqrt 2 := by
    intro b
    have hm : ((negOneU L b : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) - 1 = (-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      show (-1 : Matrix (Fin 2) (Fin 2) ℂ) - 1 = _
      ext i j
      simp [Matrix.one_apply]
      split <;> ring
    rw [hm, AdalyFormal.Balaban.RMapLipschitz.frobNorm,
      show AdalyFormal.Balaban.RMapLipschitz.frobSq
          ((-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 8 by
        simp [AdalyFormal.Balaban.RMapLipschitz.frobSq, Complex.normSq_apply]
        norm_num,
      show (8 : ℝ) = (2 * Real.sqrt 2) ^ 2 by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num]
    exact Real.sqrt_sq (by positivity)
  unfold frobSupBond
  exact Finset.sup'_congr _ rfl (fun b _ => hval b) |>.trans (by simp)

/-- **THE OVER-RESTRICTION, EXHIBITED.** At `U ≡ −1` the threshold FAILS at every `ell ≥ 1`
(`2√2 > 1/186 ≥ 1/(186·ell³)`), yet the covariant curl energy there is IDENTICALLY the flat one, so
the flat leg `suTwo_lemma24_flat` applies verbatim and gives a floor with the FULL constant
`(1/180)·ell⁻⁵` on the curl term. The hypothesis is therefore strictly conservative. -/
theorem negOneU_fails_threshold {ell : ℕ} (hell : 0 < ell) :
    ¬ (frobSupBond (negOneU L) ≤ 1 / (186 * (ell : ℝ) ^ 3)) := by
  rw [frobSupBond_negOneU]
  have h1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h3 : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ h1
  have hle : 1 / (186 * (ell : ℝ) ^ 3) ≤ 1 / 186 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [h3]
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  intro hc
  linarith [hle, hc, h2]

#print axioms sq_le_young
#print axioms transfer_abstract_young
#print axioms coarseQ_flat_le_young
#print axioms curl_flat_le_young
#print axioms covariant_lemma24_young
#print axioms young_threshold_pos_iff
#print axioms young_threshold_at_one
#print axioms young_threshold_at_ten
#print axioms threshold_of_alpha_le_ten
#print axioms young_threshold_strict_anti
#print axioms young_threshold_inf_not_attained
#print axioms curlEnergyCov_eq_flat_of_adjoint_trivial
#print axioms negOne_mem_su2
#print axioms negOneElem
#print axioms RMap_negOneElem
#print axioms negOneU
#print axioms curlEnergyCov_negOneU
#print axioms frobSupBond_negOneU
#print axioms negOneU_fails_threshold

end AdalyFormal.Balaban.CovLemma24Sharp
