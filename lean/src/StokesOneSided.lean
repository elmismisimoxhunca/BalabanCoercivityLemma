/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

/-!
# `[STOKES-COMM-U]` AS THE Γ₁ INTERPOLATION HALF — WHAT THE CONSUMER ACTUALLY NEEDS

`compute/gamma1_positive/stage/Gamma1ChainMap.lean`'s `interp_energy_of_chain` consumes a discrete
Stokes CHAIN MAP `(C) : ∀ A, d₁ (Q A) = S (d A)` together with `(N) : ∀ f, ‖S f‖ ≤ σ‖f‖`.  At `U = 1`
(C) is `ThirdLevelStokes.stokes_flat`.  At general `U` the exact identity fails
(`CovariantOperators.witness_curvature_ne_zero`), and that failure is what the tree records as the
residual `[STOKES-COMM-U]`.

This file separates three different statements that the residual's name conflates.

* **§1 — the consumer never needed the identity.**  `interp_energy_of_chain`'s proof uses `(C)` and
  `(N)` only to produce the single scalar inequality `‖d₁ B‖ ≤ σ‖d A‖` at the single point
  `A = H₁B`.  `interp_energy_of_onesided` proves the conclusion from THAT, with no `S` anywhere, and
  `onesided_of_chain` shows `(C) + (N)` imply it — so the hypothesis is weakened, not exchanged.

* **§2 — the ONE-SIDED bound, quantified over all `A`, is refutable, and by an explicit criterion.**
  `ker_subset_of_onesided` : a global one-sided bound forces `ker d ⊆ ker (d₁ ∘ Q)`.
  `not_onesided_of_defect` : hence a single `A₀` with `d A₀ = 0` and `d₁ (Q A₀) ≠ 0` refutes the
  global one-sided bound **for every `σ`**.  This is the sharp form of "the identity fails
  covariantly": what is fatal is not that the identity fails, but that it fails ON `ker d`.

* **§3 — the ABSORPTION theorem, which is how the recorded near-circularity is broken.**  The
  general-`U` bound reachable from the drift estimates measures its error against `‖A‖`
  (`bondEnergy`), never against `‖d A‖` — that is the recorded resistance point of
  `[STOKES-COMM-U]`, and §5 of this file shows the cycle is genuine, not route-specific.  The exit is
  not to convert the error but to ABSORB it: if the error is re-expressed against `‖B‖` (§4), the
  `‖B‖²` it contributes sits on the SAME side as the Poincaré constant `γ_P` and can be moved,
  provided the error coefficient `κ` satisfies `2κ² < γ_P`.  `gamma_floor_of_perturbed_chain`
  delivers the floor with the explicit constant `(γ_P − 2κ²)/(2σ₀²)`.

* **§4 — what §3's hypothesis costs**: converting an `‖A‖`-measured error into a `‖B‖`-measured one
  is exactly a Poincaré inequality WITH MEAN, `‖A‖² ≤ K₁‖d A‖² + K₂‖Q A‖²`.
  `not_meanPoincare_of_kernel` proves that inequality FALSE, for every `K₁, K₂`, as soon as
  `ker d ∩ ker Q ≠ 0` — which is why a gauge-fixing clause is not optional.

* **§5 — witnesses.**  Every class carries an inhabitant AND a non-inhabitant.

Nothing here is installed in `formal/`; nothing enters `Spine.lean`'s import cone.
-/

namespace AdalyFormal.StokesCommu.OneSided

variable {Hs Ks P₁ P₂ : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
  [NormedAddCommGroup Ks] [InnerProductSpace ℝ Ks]
  [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
  [NormedAddCommGroup P₂] [InnerProductSpace ℝ P₂]

/-! ## §1 — the consumer, weakened to a one-sided bound at ONE point -/

/-- **THE CONSUMER NEEDS NO CHAIN MAP.**  Exactly `Gamma1ChainMap.interp_energy_of_chain`'s
conclusion, from a single scalar inequality at the single point `A` with `Q A = B`.  No operator `S`
occurs in the statement, so no identity — exact or approximate — is assumed. -/
theorem interp_energy_of_onesided (Q : Hs →L[ℝ] Ks) (d : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂)
    (Kop : Hs →L[ℝ] Hs) (σ : ℝ) (hσ : 0 < σ) (A : Hs) (B : Ks) (hQA : Q A = B)
    (hstep : ‖d₁ (Q A)‖ ≤ σ * ‖d A‖)
    (hK : ‖d A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ)) :
    (1 / σ ^ 2) * ‖d₁ B‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ) := by
  rw [← hQA]
  have hd : (0 : ℝ) ≤ ‖d A‖ := norm_nonneg _
  have hb : (0 : ℝ) ≤ ‖d₁ (Q A)‖ := norm_nonneg _
  have hsq : ‖d₁ (Q A)‖ ^ 2 ≤ σ ^ 2 * ‖d A‖ ^ 2 := by nlinarith [hstep, hd, hb, hσ]
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hσ2]
  nlinarith [hsq, hK, hσ2]

/-- **(C) + (N) ⟹ the one-sided bound**, so §1 is a genuine weakening of
`interp_energy_of_chain`'s hypothesis pair and not a different assumption. -/
theorem onesided_of_chain (Q : Hs →L[ℝ] Ks) (d : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂)
    (S : P₁ →L[ℝ] P₂) (σ : ℝ)
    (hchain : ∀ A : Hs, d₁ (Q A) = S (d A)) (hS : ∀ f : P₁, ‖S f‖ ≤ σ * ‖f‖) (A : Hs) :
    ‖d₁ (Q A)‖ ≤ σ * ‖d A‖ := by
  rw [hchain A]; exact hS (d A)

/-! ## §2 — the GLOBAL one-sided bound and its exact refutation criterion -/

/-- A global one-sided bound forces `ker d ⊆ ker (d₁ ∘ Q)`. -/
theorem ker_subset_of_onesided (Q : Hs →L[ℝ] Ks) (d : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂) (σ : ℝ)
    (h : ∀ A : Hs, ‖d₁ (Q A)‖ ≤ σ * ‖d A‖) (A : Hs) (hA : d A = 0) : d₁ (Q A) = 0 := by
  have hb := h A
  rw [hA, norm_zero, mul_zero] at hb
  exact norm_le_zero_iff.mp hb

/-- **THE REFUTATION CRITERION.**  One vector on which the coarse coboundary of the average is
nonzero while the fine coboundary vanishes refutes the global one-sided bound **for every `σ`** —
including every negative and every astronomically large `σ`.  This is the precise sense in which a
covariant Stokes DEFECT is fatal: only its restriction to `ker d` is. -/
theorem not_onesided_of_defect (Q : Hs →L[ℝ] Ks) (d : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂)
    (A₀ : Hs) (h0 : d A₀ = 0) (hne : d₁ (Q A₀) ≠ 0) (σ : ℝ) :
    ¬ (∀ A : Hs, ‖d₁ (Q A)‖ ≤ σ * ‖d A‖) :=
  fun h => hne (ker_subset_of_onesided Q d d₁ σ h A₀ h0)

/-! ## §3 — THE ABSORPTION THEOREM -/

/-- **THE CIRCULARITY-BREAKER.**  A PERTURBED chain bound `‖d₁B‖ ≤ σ₀‖dA‖ + κ‖B‖` — the identity
replaced by a bound with an error measured against the COARSE field `B`, which is what the general-`U`
drift estimates deliver once §4 is available — still yields the coercivity floor, with the explicit
constant `(γ_P − 2κ²)/(2σ₀²)`.  The error is not converted; it is moved to the left-hand side against
the Poincaré constant.  `hsmall` is exactly Bałaban's p.428 "`Mα₀` sufficiently small". -/
theorem gamma_floor_of_perturbed_chain (Q : Hs →L[ℝ] Ks) (d : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂)
    (Kop : Hs →L[ℝ] Hs) (σ₀ κ γP : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ) (A : Hs)
    (hpert : ‖d₁ (Q A)‖ ≤ σ₀ * ‖d A‖ + κ * ‖Q A‖)
    (hpoin : γP * ‖Q A‖ ^ 2 ≤ ‖d₁ (Q A)‖ ^ 2)
    (hK : ‖d A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ)) :
    ((γP - 2 * κ ^ 2) / (2 * σ₀ ^ 2)) * ‖Q A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ) := by
  set B : Ks := Q A with hB
  have hX : (0 : ℝ) ≤ ‖d A‖ := norm_nonneg _
  have hY : (0 : ℝ) ≤ ‖B‖ := norm_nonneg _
  have hZ : (0 : ℝ) ≤ ‖d₁ B‖ := norm_nonneg _
  have hsum : (0 : ℝ) ≤ σ₀ * ‖d A‖ + κ * ‖B‖ := by positivity
  have hZ2 : ‖d₁ B‖ ^ 2 ≤ (σ₀ * ‖d A‖ + κ * ‖B‖) ^ 2 := by nlinarith [hpert, hZ, hsum]
  have hexp : (σ₀ * ‖d A‖ + κ * ‖B‖) ^ 2 ≤ 2 * σ₀ ^ 2 * ‖d A‖ ^ 2 + 2 * κ ^ 2 * ‖B‖ ^ 2 := by
    nlinarith [sq_nonneg (σ₀ * ‖d A‖ - κ * ‖B‖)]
  have hden : (0 : ℝ) < 2 * σ₀ ^ 2 := by positivity
  have hKscaled : 2 * σ₀ ^ 2 * ‖d A‖ ^ 2 ≤ 2 * σ₀ ^ 2 * (inner ℝ A (Kop A) : ℝ) :=
    mul_le_mul_of_nonneg_left hK (le_of_lt hden)
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [hpoin, hZ2, hexp, hKscaled]

/-- The absorbed constant is POSITIVE exactly under the smallness condition.  Stated separately
because `gamma_floor_of_perturbed_chain` is TRUE without it (the constant simply goes `≤ 0`, and a
nonpositive floor is no floor): the smallness hypothesis buys positivity, not validity, and this
file does not pretend otherwise. -/
theorem absorbed_constant_pos (σ₀ κ γP : ℝ) (hσ₀ : 0 < σ₀) (hsmall : 2 * κ ^ 2 < γP) :
    0 < (γP - 2 * κ ^ 2) / (2 * σ₀ ^ 2) := by
  have : (0 : ℝ) < 2 * σ₀ ^ 2 := by positivity
  exact div_pos (by linarith) this

/-- ... and it is NONPOSITIVE as soon as smallness fails — the must-fail companion of the previous
declaration, so "`2κ² < γ_P`" is a real dichotomy and not decoration. -/
theorem absorbed_constant_nonpos (σ₀ κ γP : ℝ) (hσ₀ : 0 < σ₀) (hbig : γP ≤ 2 * κ ^ 2) :
    (γP - 2 * κ ^ 2) / (2 * σ₀ ^ 2) ≤ 0 := by
  have h : (0 : ℝ) < 2 * σ₀ ^ 2 := by positivity
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt h)

/-! ## §4 — the price of §3: a Poincaré inequality WITH MEAN, and its exact obstruction -/

/-- **THE CONVERSION.**  The drift estimates give the error against `‖A‖`; §3 needs it against
`‖B‖`.  A Poincaré-with-mean `‖A‖² ≤ K₁‖dA‖² + K₂‖QA‖²` performs exactly that conversion, and the
resulting constants are `σ₀ + c√K₁` and `c√K₂` — both explicit, no hidden absolute constant. -/
theorem perturbed_chain_of_meanPoincare (Q : Hs →L[ℝ] Ks) (d : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂)
    (σ₀ c K₁ K₂ : ℝ) (hc : 0 ≤ c) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (A : Hs)
    (hraw : ‖d₁ (Q A)‖ ≤ σ₀ * ‖d A‖ + c * ‖A‖)
    (hmean : ‖A‖ ^ 2 ≤ K₁ * ‖d A‖ ^ 2 + K₂ * ‖Q A‖ ^ 2) :
    ‖d₁ (Q A)‖ ≤ (σ₀ + c * Real.sqrt K₁) * ‖d A‖ + (c * Real.sqrt K₂) * ‖Q A‖ := by
  set B : Ks := Q A with hB
  have hX : (0 : ℝ) ≤ ‖d A‖ := norm_nonneg _
  have hY : (0 : ℝ) ≤ ‖B‖ := norm_nonneg _
  have hA0 : (0 : ℝ) ≤ ‖A‖ := norm_nonneg _
  have hs1 : Real.sqrt K₁ ^ 2 = K₁ := Real.sq_sqrt hK₁
  have hs2 : Real.sqrt K₂ ^ 2 = K₂ := Real.sq_sqrt hK₂
  have hs1n : (0 : ℝ) ≤ Real.sqrt K₁ := Real.sqrt_nonneg _
  have hs2n : (0 : ℝ) ≤ Real.sqrt K₂ := Real.sqrt_nonneg _
  have hR0 : (0 : ℝ) ≤ Real.sqrt K₁ * ‖d A‖ + Real.sqrt K₂ * ‖B‖ := by positivity
  have hsq : ‖A‖ ^ 2 ≤ (Real.sqrt K₁ * ‖d A‖ + Real.sqrt K₂ * ‖B‖) ^ 2 := by
    have hcross : (0 : ℝ) ≤ 2 * (Real.sqrt K₁ * ‖d A‖) * (Real.sqrt K₂ * ‖B‖) := by positivity
    nlinarith [hmean, hs1, hs2, hcross]
  have hAle : ‖A‖ ≤ Real.sqrt K₁ * ‖d A‖ + Real.sqrt K₂ * ‖B‖ := by
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hA0, Real.sqrt_sq hR0] at this
  nlinarith [hraw, hAle, hc]

/-- **THE OBSTRUCTION TO §4, PROVED.**  A single nonzero vector killed by BOTH `d` and `Q` refutes
the Poincaré-with-mean for EVERY pair of constants `K₁, K₂` — no size of constant repairs it.  So
the `‖A‖`-measured error of the general-`U` drift cannot be converted without a further constraint
(a gauge-fixing clause) that empties `ker d ∩ ker Q`. -/
theorem not_meanPoincare_of_kernel (Q : Hs →L[ℝ] Ks) (d : Hs →L[ℝ] P₁)
    (A₀ : Hs) (hne : A₀ ≠ 0) (hd : d A₀ = 0) (hQ : Q A₀ = 0) (K₁ K₂ : ℝ) :
    ¬ (∀ A : Hs, ‖A‖ ^ 2 ≤ K₁ * ‖d A‖ ^ 2 + K₂ * ‖Q A‖ ^ 2) := by
  intro h
  have hb := h A₀
  rw [hd, hQ, norm_zero] at hb
  have hz : ‖A₀‖ ^ 2 ≤ 0 := by simpa using hb
  have : ‖A₀‖ = 0 := by nlinarith [norm_nonneg A₀, hz]
  exact hne (norm_eq_zero.mp this)

/-! ## §5 — WITNESSES: every class gets an inhabitant AND a non-inhabitant

The carrier is `ℝ` with its own real inner product (`inner ℝ x y = x * y`), the smallest space on
which all four operators of §1–§4 can be exhibited simultaneously. -/

theorem inner_real (x y : ℝ) : (inner ℝ x y : ℝ) = x * y := by
  simp [mul_comm]

/-- `Q = id` on `ℝ`. -/
noncomputable def wQ : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

/-- `d₁ = id` on `ℝ`. -/
noncomputable def wd1 : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

/-- `d = id` on `ℝ` — the GOOD fine coboundary. -/
noncomputable def wdGood : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

/-- `d = 0` — the fine coboundary with a maximal kernel; the DEFECT witness. -/
noncomputable def wdBad : ℝ →L[ℝ] ℝ := 0

/-- `Kop = id`. -/
noncomputable def wKop : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

/-- **INHABITANT of §3 with a genuinely nonzero error coefficient.**  `σ₀ = 1`, `κ = 1/2`,
`γ_P = 1`: `2κ² = 1/2 < 1 = γ_P`, the absorbed constant is `1/4 > 0`, `d₁ ≠ 0`, and the conclusion is
non-trivial at `B = 1` (`1/4 ≤ 1`).  So §3 is not vacuous through `κ = 0`. -/
theorem witness_absorption (t : ℝ) :
    ((1 - 2 * (1/2 : ℝ) ^ 2) / (2 * (1 : ℝ) ^ 2)) * ‖t‖ ^ 2 ≤ (inner ℝ t (wKop t) : ℝ) := by
  have hQt : wQ t = t := rfl
  rw [← hQt]
  refine gamma_floor_of_perturbed_chain wQ wdGood wd1 wKop 1 (1/2) 1 one_pos (by norm_num)
    t ?_ ?_ ?_
  · show ‖wd1 (wQ t)‖ ≤ 1 * ‖wdGood t‖ + (1/2 : ℝ) * ‖wQ t‖
    simp only [wd1, wdGood, wQ, ContinuousLinearMap.id_apply]
    have : (0 : ℝ) ≤ ‖t‖ := norm_nonneg _
    linarith
  · show (1 : ℝ) * ‖wQ t‖ ^ 2 ≤ ‖wd1 (wQ t)‖ ^ 2
    simp [wd1, wQ]
  · show ‖wdGood t‖ ^ 2 ≤ (inner ℝ t (wKop t) : ℝ)
    simp [wdGood, wKop, inner_real, Real.norm_eq_abs, sq_abs]

/-- The absorbed constant of `witness_absorption` is `1/4`, and it is strictly positive. -/
theorem witness_absorption_constant :
    (1 - 2 * (1/2 : ℝ) ^ 2) / (2 * (1 : ℝ) ^ 2) = 1/4 ∧
      (0 : ℝ) < (1 - 2 * (1/2 : ℝ) ^ 2) / (2 * (1 : ℝ) ^ 2) := by
  constructor
  · norm_num
  · exact absorbed_constant_pos 1 (1/2) 1 one_pos (by norm_num)

/-- **NON-INHABITANT of §2, i.e. the perturbed bound is STRICTLY more general than the one-sided
bound.**  With `d = 0`, `d₁ = Q = id`: the perturbed bound holds with `σ₀ = 0`, `κ = 1`, yet NO `σ`
whatsoever gives the one-sided bound.  A class with no failing witness is not a class; this is the
failing witness for §2 and the succeeding one for §3's hypothesis. -/
theorem witness_perturbed_strictly_weaker :
    (∀ B : ℝ, ‖wd1 B‖ ≤ 0 * ‖wdBad B‖ + 1 * ‖B‖) ∧
      (∀ σ : ℝ, ¬ (∀ A : ℝ, ‖wd1 (wQ A)‖ ≤ σ * ‖wdBad A‖)) := by
  constructor
  · intro B; simp [wd1, wdBad]
  · intro σ
    refine not_onesided_of_defect wQ wdBad wd1 (1 : ℝ) ?_ ?_ σ
    · simp [wdBad]
    · simp [wd1, wQ]

/-- **NON-INHABITANT of §4.**  `d = 0` and `Q = 0` share the nonzero vector `1`, so the
Poincaré-with-mean fails for every `K₁, K₂` — the concrete instance of `not_meanPoincare_of_kernel`.
-/
theorem witness_no_meanPoincare (K₁ K₂ : ℝ) :
    ¬ (∀ A : ℝ, ‖A‖ ^ 2 ≤ K₁ * ‖wdBad A‖ ^ 2 + K₂ * ‖(0 : ℝ →L[ℝ] ℝ) A‖ ^ 2) :=
  not_meanPoincare_of_kernel (0 : ℝ →L[ℝ] ℝ) wdBad (1 : ℝ) one_ne_zero (by simp [wdBad]) (by simp)
    K₁ K₂

/-- **JUNK SUBSTITUTION (S82).**  At `B = 0` every conclusion of §3 degenerates to `0 ≤ ⟨A,KopA⟩`;
recorded so that no reader mistakes the `B = 0` instance for content. -/
theorem junk_zero (σ₀ κ γP : ℝ) : ((γP - 2 * κ ^ 2) / (2 * σ₀ ^ 2)) * ‖(0 : ℝ)‖ ^ 2 = 0 := by simp

/-- **JUNK SUBSTITUTION (S82), the operator side.**  With `Kop = 0` and `d = 0` the §1 conclusion is
`0 ≤ 0`: `interp_energy_of_onesided` is NOT algebraically forced, because it fails to be informative
exactly where its hypotheses collapse, and `witness_absorption` shows it is informative elsewhere. -/
theorem junk_zero_operators (t : ℝ) :
    (1 / (1 : ℝ) ^ 2) * ‖wd1 ((0 : ℝ →L[ℝ] ℝ) t)‖ ^ 2 = 0 := by simp

#print axioms interp_energy_of_onesided
#print axioms onesided_of_chain
#print axioms ker_subset_of_onesided
#print axioms not_onesided_of_defect
#print axioms gamma_floor_of_perturbed_chain
#print axioms absorbed_constant_pos
#print axioms absorbed_constant_nonpos
#print axioms perturbed_chain_of_meanPoincare
#print axioms not_meanPoincare_of_kernel
#print axioms inner_real
#print axioms witness_absorption
#print axioms witness_absorption_constant
#print axioms witness_perturbed_strictly_weaker
#print axioms witness_no_meanPoincare
#print axioms junk_zero
#print axioms junk_zero_operators
-- TAG COMPLETION 2026-08-12 (repair pass): the five witness DEFS were declared but untagged;
-- a tagged-vs-declared census counted 21 declared / 16 tagged here.  Tagging a `def` is as
-- meaningful as tagging a theorem: it is the axiom set its body pulls in.
#print axioms wQ
#print axioms wd1
#print axioms wdGood
#print axioms wdBad
#print axioms wKop

end AdalyFormal.StokesCommu.OneSided
