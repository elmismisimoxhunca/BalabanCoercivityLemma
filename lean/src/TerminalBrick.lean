/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import CovLemma24
import ConstructCDC
import CovLemma24Witness

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

/-!
# `TerminalBrick.lean` — THE FIRST EDGE OF THE TERMINAL COMPOSITION

## What this module does, in one sentence

It carries `compute/covariant_lemma24/`'s general-`U` covariant Lemma 2.4 — a floor on the FINE
bond space — through `compute/construct_cdc/`'s printed parametrisation `C₀ : ℓ²(Λ̃) → ℓ²(bonds)`,
and lands it as an explicit coercivity of the CONSTRUCTED operator `C*Δ_kC` **on the printed
carrier `ℓ²(Λ̃)`**, for the `D_U^*D_U` part of `Δ_k`.

## Why the composition goes through — the three facts that make it mechanical

CMP99b p.428 (corpus page `corpus/pages/CMP99b_p428.md`, `verification_status: adjudicated`)
considers the form *"on the subspace `{B : B=0 on Λ^c, B=0 on ⋃_{y∈Λ'} Ax(y), Q₁B=0}`"*.
`construct_cdc` proved that the printed `C₀` lands in exactly that subspace:

* `ConstructCDC.cZero_axialGauge` — `C₀B̃ = 0` on every `Γ_{y,x}`, `y ∈ Λ'`, `x ∈ B(y)`.  That is
  **character-for-character** `CovariantLemma24.SuAdmissible`, i.e. CMP96 (2.121), which is
  covariant Lemma 2.4's own hypothesis.  So Lemma 2.4 APPLIES at `C₀B̃`, with no new admissibility
  work and no drift priced on the hypothesis.
* `ConstructCDC.cZero_mem_kerQ` — `Q₁(U)(C₀B̃)(c) = 0` at every coarse bond.  So the coarse term
  `ell·∑_c ‖(Q₁(U)A)(c)‖²` on Lemma 2.4's right-hand side **vanishes identically on the range of
  `C₀`**, and the floor falls entirely on the curl term.  This is the step that turns a
  two-term Poincaré inequality into a one-term coercivity.
* `ConstructCDC.norm_le_norm_cZero` — `‖B̃‖_{Λ̃} ≤ ‖C₀B̃‖`.  The inequality runs in the direction the
  composition needs: a floor stated in `bondEnergy (C₀B̃) = ‖C₀B̃‖²` implies one stated in `‖B̃‖²`.

## The statement that comes out

For every `ell ≥ 2`, every tiled torus (`ell < L ν + 1`, `ell ∣ L ν + 1`), every background `U`
whatsoever, every `T2` supplying `Δ_k = D_U^*D_U + T2`, and every `B̃ : ℓ²(Λ̃)`:

    ((1/360)·ell⁻⁵ − 96·α₁²) · ‖B̃‖²
      ≤ ⟪B̃, (C₀*Δ_kC₀) B̃⟫_{Λ̃} − ⟪C₀B̃, T2 (C₀B̃)⟫,      α₁ = frobSupBond U

(`cdc_covariant_floor_general`), hence unconditionally at `T2 = 0`
(`cdc_covariant_floor_dstarD`), and with the `T2` term absorbed whenever `T2`'s form is
nonnegative (`cdc_covariant_floor_of_T2_nonneg`).  Under the smallness hypothesis
`α₁ ≤ 1/(186·ell³)` — the threshold `compute/threshold_vs_printed/` converts CMP99b (3.35) into —
the coefficient is STRICTLY POSITIVE (`cdc_covariant_floor_positive`).

## ⚠ WHAT THIS IS **NOT** — read before quoting anything above

1. **IT IS NOT `γ₀ > 0` FOR THE PRINTED `Δ_k`, AND THE GAP HAS A PROVED DIRECTION.**  The operator
   whose form is bounded below here is `ConstructCDC.deltaK U T2 = dstarDCLM U + T2`.  Its
   `D_U^*D_U` half is bounded below; the `T2` half is CARRIED, not bounded.  CMP99b (3.156)'s own
   `Δ_k` has `T2 = pinnedT2` in `compute/deltak_wiring/`'s sense —
   `(QG₁Q*)⁻¹ − a·I − 2S − D_U^*D_U` — and **nothing here proves that `T2`'s form is nonnegative,
   or bounded below at all**.
   **⚠ AND THE ORDERING IS KNOWN TO RUN THE OTHER WAY.**
   `formal/…/Balaban/CStarDeltaKCCoercive.lean` proves
   `deltaJQuadFormCovFaithful_le_dstarDQuadForm`: the faithful covariant Schur complement is **≤**
   `D_U^*D_U`.  If (3.156)'s leading term `(QG₁Q*)⁻¹` is that Schur complement — an identification
   `CStarDeltaKCSuTwo.lean`'s corrected docstring asserts at `U = 1`, and which THIS MODULE DOES NOT
   ADJUDICATE — then the printed `T2`'s form is `≤ 0`, and **`cdc_covariant_floor_of_T2_nonneg`'s
   hypothesis `hT2` FAILS at the printed pinning**.  A reader must not instantiate that theorem at
   `deltak_wiring`'s `pinnedT2` without settling the ordering first.  This is gap `[CSTAR-SCHUR-GAP]`
   and it is the largest single gap between this module and p.428's sentence.
2. **`k` DOES NOT APPEAR, AND THAT IS NOT `k`-UNIFORMITY.**  No statement here mentions an RG step
   index.  The constant is `ell`-dependent and extent-free; whether the source's `Δ_k` at step `k`
   is this operator is `compute/deltak_wiring/`'s question, not settled here.
3. **THE `ell⁻⁵` IS THE CORRECTED EXPONENT, NOT THE PRINTED `ell⁻⁴`.**  Inherited from
   `Lemma24GeneralEll.lemma24_general_ell` through `CovariantLemma24.covariant_lemma24`, whose own
   docstring proves the printed (2.126)→(2.127) step false from `L = 10`.
4. **`α₁ = frobSupBond U` IS PROVED CONSERVATIVE** by the upstream lane
   (`CovLemma24Center.center_outside_certified_class`); nothing here improves it.
5. **`Λ^c = ∅` in this encoding** (torus carrier), so the printed subspace's first conjunct is
   vacuous.  Inherited from `construct_cdc`; not repairable in one module.
6. **ISLAND.**  Nothing here is installed in `formal/`; nothing is in `Spine.lean`'s import cone;
   `FULL3D.main`'s axiom set is unchanged.

## LAW-19 — the overlap with what already exists, stated rather than left for a reader to find

`formal/AdalyFormal/AdalyFormal/Balaban/CStarDeltaKCCoercive.lean` proves a statement of the same
SHAPE: `γ''·bondEnergy B̃ ≤ cStarDstarDCForm a 2 U Dinv B̃`.  Four differences, all measurable at
the two types:

| | `CStarDeltaKCCoercive` | here |
|---|---|---|
| carrier of `B̃` | the FULL bond space, with "vanishes on every dropped bond" as a HYPOTHESIS | `ℓ²(Λ̃)`, where that vanishing is a property of the INDEX TYPE and needs no hypothesis |
| block size | `ell = 2` only | every `ell ≥ 2` |
| the floor consumed | `RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU`, `γ₀ = (1/108)(1/2⁴)` | `CovariantLemma24.covariant_lemma24`, `(1/360)ell⁻⁵ − 96α₁²` |
| the object bounded | a FORM (`cStarDstarDCForm`) | the constructed OPERATOR `ConstructCDC.cdcOp`, through `inner_cdcOp_self` |

Neither statement implies the other, and this module cites nothing from that one.
-/

namespace AdalyFormal.Balaban.TerminalCompose

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice staircasePath)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy frobSupBond)
open AdalyFormal.Balaban.CovariantHj (covPlaqInner dstarDQuadForm)
open AdalyFormal.Balaban.CovariantOperators (curlValueCovariant)
open AdalyFormal.Balaban.SuTwoInner (hsInner norm_eq_sqrt_hsInner hsInner_self_nonneg)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.CStarDeltaKCOperator (dstarDCLM inner_dstarDCLM_eq_dstarDQuadForm)
open AdalyFormal.Balaban.CovariantLemma24 (SuAdmissible coarseQEnergyCov curlEnergyCov
  covariant_lemma24 covariant_floor_pos_iff threshold_of_alpha_le)
open AdalyFormal.Balaban.ConstructCDC (TildeSet TildeBond TildeFn cZero cZeroStar cdcOp deltaK
  cZero_axialGauge cZero_mem_kerQ norm_le_norm_cZero normSq_eq_sum_bond inner_cdcOp_self
  tildeSpike tildeSpike_ne_zero)

open scoped InnerProductSpace RealInnerProductSpace

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE THREE VOCABULARY TRANSPORTS

Three identifications, each between an object the covariant Lemma 2.4 speaks in and an object
`construct_cdc` speaks in.  None of them is an estimate; each is a re-indexing or a definitional
unfolding, and each is stated separately so the arithmetic of §3 can be audited without them. -/

/-- **TRANSPORT 1 — the `𝔰𝔲(2)` fibre norm and the Hilbert–Schmidt inner product.**  A FIFTH
in-tree copy of a one-liner (`Weitzenbock.norm_sq_eq_hsInner`,
`LemmaAssembly.hsInner_self_eq_norm_sq`, `SplitBaseCase.hsInner_self_eq_norm_sq`,
`CovariantLemma24.normSq_eq_hsInner` are the others).  It exists here only to keep this module's
import cone at three.  **That the tree carries the same one-liner in five places is a FINDING about
the tree, reported not remediated (LAW-4).** -/
theorem normSq_eq_hsInner (X : SuTwo) : ‖X‖ ^ 2 = hsInner X X := by
  rw [norm_eq_sqrt_hsInner, Real.sq_sqrt (hsInner_self_nonneg X)]

/-- **TRANSPORT 2 — the curl energy IS the `D_U^*D_U` quadratic form.**  `curlEnergyCov` sums
`‖·‖²` over plaquettes; `dstarDQuadForm` is `covPlaqInner` of the same covariant curl with itself,
i.e. the same sum written with `hsInner`. -/
theorem curlEnergyCov_eq_dstarDQuadForm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    curlEnergyCov U A = dstarDQuadForm U A := by
  unfold curlEnergyCov dstarDQuadForm plaqEnergy covPlaqInner
  exact Finset.sum_congr rfl fun p _ => normSq_eq_hsInner (curlValueCovariant U A p)

/-- **TRANSPORT 3 — the curl energy of a `BondFnL2` element is the form of `dstarDCLM`.**  This is
TRANSPORT 2 composed with `CStarDeltaKCOperator.inner_dstarDCLM_eq_dstarDQuadForm`, at the
`WithLp` coercion. -/
theorem curlEnergyCov_eq_inner_dstarDCLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : BondFnL2 L) :
    curlEnergyCov U (fun b => x b) = (inner ℝ x (dstarDCLM U x) : ℝ) := by
  rw [curlEnergyCov_eq_dstarDQuadForm]
  exact (inner_dstarDCLM_eq_dstarDQuadForm U (fun b => x b)).symm

/-- **TRANSPORT 4 — `bondEnergy` of the underlying function IS the `ℓ²` norm squared.** -/
theorem bondEnergy_eq_normSq (x : BondFnL2 L) :
    bondEnergy (fun b => x b) = ‖x‖ ^ 2 := by
  rw [normSq_eq_sum_bond]
  rfl

/-! ## §2 — THE RANGE OF `C₀` SITS INSIDE LEMMA 2.4'S HYPOTHESIS AND KILLS ITS COARSE TERM -/

/-- The underlying `Bond L → SuTwo` function of `C₀B̃`, at the unconditional `Dinv = dinvC U ell`
(the value at which `construct_cdc` proves the two subspace clauses without hypotheses). -/
noncomputable def cZeroFn
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (w : TildeFn L ell) : Bond L → SuTwo :=
  fun b => (cZero U ell (dinvC U ell) w : BondFnL2 L) b

/-- **`C₀B̃` SATISFIES CMP96 (2.121).**  Verbatim `construct_cdc`'s `cZero_axialGauge`, re-typed as
`CovariantLemma24.SuAdmissible`.  The two statements have the SAME quantifier prefix — `∀ y ∈ Λ'`,
`∀ x ∈ B(y)`, `∀ b ∈ Γ_{y,x}` — which is why this is `id` and not a weakening. -/
theorem cZeroFn_admissible {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (w : TildeFn L ell) :
    SuAdmissible L ell (cZeroFn U ell w) :=
  cZero_axialGauge hell hdvd U w

/-- **THE COARSE TERM VANISHES ON THE RANGE OF `C₀`.**  Every summand of `coarseQEnergyCov` is
`‖Q₁(U)(C₀B̃)(c)‖²` and `construct_cdc` proves each `Q₁(U)(C₀B̃)(c) = 0`. -/
theorem coarseQEnergyCov_cZero_eq_zero {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (w : TildeFn L ell) :
    coarseQEnergyCov U ell (cZeroFn U ell w) = 0 := by
  unfold coarseQEnergyCov cZeroFn
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [cZero_mem_kerQ hell hdvd U w c, norm_zero]
  norm_num

/-! ## §3 — THE BRICK -/

/-- **THE COVARIANT FLOOR, TRANSPORTED TO THE PRINTED CARRIER, ON THE `D_U^*D_U` LEG.**

For every `ell ≥ 2`, every tiled torus, every background `U` with NO smallness assumed, and every
`B̃ : ℓ²(Λ̃)`:

    ((1/360)·ell⁻⁵ − 96·(frobSupBond U)²) · ‖B̃‖²  ≤  ⟪C₀B̃, D_U^*D_U (C₀B̃)⟫ .

The coefficient is the same one `CovariantLemma24.covariant_lemma24` carries; the `‖B̃‖²` on the
left is the `Λ̃`-norm, i.e. the norm of the printed carrier.  The hypothesis `hcoeff` is needed
ONLY to move from `‖C₀B̃‖²` to `‖B̃‖²` (the inequality runs the right way, but multiplying an
inequality by a coefficient needs its sign); it is discharged from the smallness threshold in
`cdc_covariant_floor_positive`. -/
theorem cdc_covariant_floor_dstarD {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hcoeff : 0 ≤ (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2)
    (w : TildeFn L ell) :
    ((1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2) * ‖w‖ ^ 2
      ≤ (inner ℝ (cZero U ell (dinvC U ell) w)
          (dstarDCLM U (cZero U ell (dinvC U ell) w)) : ℝ) := by
  have hell : 0 < ell := by omega
  set x : BondFnL2 L := cZero U ell (dinvC U ell) w with hx
  set gam : ℝ := (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2 with hgam
  -- Lemma 2.4 at `C₀B̃`
  have hmain := covariant_lemma24 (L := L) hell2 hstrict hdvd U (cZeroFn U ell w)
    (cZeroFn_admissible hell hdvd U w)
  rw [coarseQEnergyCov_cZero_eq_zero hell hdvd U w, mul_zero, zero_add] at hmain
  -- `cZeroFn = fun b => x b` definitionally
  have hfn : cZeroFn U ell w = fun b => x b := rfl
  rw [hfn, bondEnergy_eq_normSq, curlEnergyCov_eq_inner_dstarDCLM] at hmain
  -- `‖w‖ ≤ ‖x‖`, so `gam * ‖w‖^2 ≤ gam * ‖x‖^2`
  have hnorm : ‖w‖ ≤ ‖x‖ := norm_le_norm_cZero U ell (dinvC U ell) w
  have hsq : ‖w‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
    exact pow_le_pow_left₀ h0 hnorm 2
  calc gam * ‖w‖ ^ 2 ≤ gam * ‖x‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsq hcoeff
    _ ≤ (inner ℝ x (dstarDCLM U x) : ℝ) := hmain

/-- **THE SAME, AGAINST THE CONSTRUCTED OPERATOR `C*Δ_kC`, WITH THE `T2` LEG CARRIED EXPLICITLY.**

`ConstructCDC.cdcOp U ell Dinv T2` is `C₀* ∘ (D_U^*D_U + T2) ∘ C₀`.  This states the floor for its
form with the `T2` contribution SUBTRACTED on the right — so nothing about `T2` is assumed and
nothing about `T2` is hidden. -/
theorem cdc_covariant_floor_general {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hcoeff : 0 ≤ (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2)
    (T2 : BondFnL2 L →L[ℝ] BondFnL2 L) (w : TildeFn L ell) :
    ((1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2) * ‖w‖ ^ 2
      ≤ (inner ℝ w (cdcOp U ell (dinvC U ell) T2 w) : ℝ)
        - (inner ℝ (cZero U ell (dinvC U ell) w)
            (T2 (cZero U ell (dinvC U ell) w)) : ℝ) := by
  have hbase := cdc_covariant_floor_dstarD hell2 hstrict hdvd U hcoeff w
  have hsplit : (inner ℝ w (cdcOp U ell (dinvC U ell) T2 w) : ℝ)
      = (inner ℝ (cZero U ell (dinvC U ell) w)
          (dstarDCLM U (cZero U ell (dinvC U ell) w)) : ℝ)
        + (inner ℝ (cZero U ell (dinvC U ell) w)
            (T2 (cZero U ell (dinvC U ell) w)) : ℝ) := by
    rw [inner_cdcOp_self]
    show (inner ℝ (cZero U ell (dinvC U ell) w)
        ((dstarDCLM U + T2) (cZero U ell (dinvC U ell) w)) : ℝ) = _
    rw [add_apply, inner_add_right]
  rw [hsplit]
  linarith

/-- **THE FLOOR FOR THE FULL `C*Δ_kC` WHENEVER `T2`'s FORM IS NONNEGATIVE.**  Stated separately
because the hypothesis `hT2` is exactly the thing this module does NOT prove about the printed
`Δ_k`: `compute/deltak_wiring/`'s `pinnedT2` carries `− a·I − 2S`, whose form has no proved sign. -/
theorem cdc_covariant_floor_of_T2_nonneg {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hcoeff : 0 ≤ (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2)
    (T2 : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hT2 : ∀ x : BondFnL2 L, 0 ≤ (inner ℝ x (T2 x) : ℝ))
    (w : TildeFn L ell) :
    ((1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2) * ‖w‖ ^ 2
      ≤ (inner ℝ w (cdcOp U ell (dinvC U ell) T2 w) : ℝ) := by
  have h := cdc_covariant_floor_general hell2 hstrict hdvd U hcoeff T2 w
  have := hT2 (cZero U ell (dinvC U ell) w)
  linarith

/-- **THE COEFFICIENT IS STRICTLY POSITIVE UNDER THE SMALLNESS THRESHOLD**, and the floor holds
there.  `α₁ ≤ 1/(186·ell³)` is the threshold `CovariantLemma24.threshold_of_alpha_le` certifies;
`compute/threshold_vs_printed/` is the lane that converts CMP99b (3.35) into a bound on `α₁`, and
this module asserts nothing about that conversion. -/
theorem cdc_covariant_floor_positive {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    (w : TildeFn L ell) :
    0 < (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2
    ∧ ((1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2) * ‖w‖ ^ 2
        ≤ (inner ℝ (cZero U ell (dinvC U ell) w)
            (dstarDCLM U (cZero U ell (dinvC U ell) w)) : ℝ) := by
  have hell : 0 < ell := by omega
  have hpos : 0 < (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2 :=
    (covariant_floor_pos_iff hell (frobSupBond U)).mpr
      (threshold_of_alpha_le hell
        (AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg U) hthr)
  exact ⟨hpos, cdc_covariant_floor_dstarD hell2 hstrict hdvd U (le_of_lt hpos) w⟩

/-! ## §4 — NON-VACUITY

A floor whose carrier is `{0}`, or whose admissible background class contains only `U = 1`, proves
nothing.  Both are excluded, at a NAMED point, with no existential over free data (S91). -/

/-- The `ell = 3` witness torus of `Lemma24GeneralEll` (`9³`): `3 < 8 + 1` and `3 ∣ 9`. -/
theorem witL3_hyps :
    (∀ ν : Fin 3, (3 : ℕ) < AdalyFormal.Balaban.Lemma24GeneralEll.witL3 ν + 1)
    ∧ (∀ ν : Fin 3, (3 : ℕ) ∣ (AdalyFormal.Balaban.Lemma24GeneralEll.witL3 ν + 1)) := by
  exact ⟨AdalyFormal.Balaban.Lemma24GeneralEll.witL3_strict,
         AdalyFormal.Balaban.Lemma24GeneralEll.witL3_dvd⟩

/-- **THE PRINTED CARRIER IS NOT THE ZERO SPACE** at the witness parameters: `Λ̃` carries a named
nonzero element.  Reuses `construct_cdc`'s `tildeSpike`; nothing is rebuilt. -/
theorem tildeSpike_witL3_ne_zero :
    (tildeSpike (L := AdalyFormal.Balaban.Lemma24GeneralEll.witL3)
      (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2) ≠ 0 :=
  tildeSpike_ne_zero _ _

/-- **THE FLOOR AT A GENUINELY CURVED BACKGROUND, ON A NONZERO ELEMENT OF THE PRINTED CARRIER.**

All four at once, at `ell = 3` on the `9³` torus:

* the background has plaquette holonomy `≠ 1` (`CovLemma24Witness.witU_curved`, CITED — it is not
  restated here, only the numeric consequences are used);
* `α₁ > 0` strictly, so the background is not the flat one;
* the coefficient is strictly positive;
* the carrier element is nonzero, so `‖B̃‖² > 0` and the LEFT-HAND SIDE IS STRICTLY POSITIVE.

The last conjunct is the one that matters: it rules out the degenerate reading in which the
inequality is `0 ≤ something`. -/
theorem cdc_covariant_floor_nonvacuous
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      AdalyFormal.Balaban.Lemma24GeneralEll.witL3)
    (hthr : frobSupBond U ≤ 1 / (186 * ((3 : ℕ) : ℝ) ^ 3)) :
    0 < ((1 / 360) * (1 / ((3 : ℕ) : ℝ) ^ 5) - 96 * frobSupBond U ^ 2)
        * ‖tildeSpike (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2‖ ^ 2
    ∧ ((1 / 360) * (1 / ((3 : ℕ) : ℝ) ^ 5) - 96 * frobSupBond U ^ 2)
        * ‖tildeSpike (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2‖ ^ 2
      ≤ (inner ℝ (cZero U 3 (dinvC U 3)
            (tildeSpike (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2))
          (dstarDCLM U (cZero U 3 (dinvC U 3)
            (tildeSpike (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2))) : ℝ) := by
  obtain ⟨hpos, hfloor⟩ := cdc_covariant_floor_positive (L := _)
    (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.1 witL3_hyps.2 U hthr
    (tildeSpike (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2)
  refine ⟨?_, hfloor⟩
  have hne := tildeSpike_witL3_ne_zero
  have hn : 0 < ‖tildeSpike (L := AdalyFormal.Balaban.Lemma24GeneralEll.witL3)
      (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2‖ := norm_pos_iff.mpr hne
  positivity

/-- **THE ADMISSIBLE BACKGROUND CLASS OF `cdc_covariant_floor_positive` IS INHABITED AT A CURVED
BACKGROUND** — `CovLemma24Witness.witU witT` on `witL3` has plaquette holonomy `≠ 1`, `α₁ > 0`,
and meets the `ell = 3` threshold.  All three are CITED from that lane, not re-proved.  Without
this row `cdc_covariant_floor_positive` could be a statement about `U = 1` in disguise. -/
theorem witness_background_curved_and_in_class :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem
        (AdalyFormal.Balaban.CovLemma24Witness.witU AdalyFormal.Balaban.CovLemma24Witness.witT)
        (AdalyFormal.Balaban.CovLemma24Witness.witBond.1,
         AdalyFormal.Balaban.CovLemma24Witness.witDir)
      ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    ∧ 0 < frobSupBond (AdalyFormal.Balaban.CovLemma24Witness.witU
            AdalyFormal.Balaban.CovLemma24Witness.witT)
    ∧ frobSupBond (AdalyFormal.Balaban.CovLemma24Witness.witU
            AdalyFormal.Balaban.CovLemma24Witness.witT)
        ≤ 1 / (186 * ((3 : ℕ) : ℝ) ^ 3) :=
  ⟨AdalyFormal.Balaban.CovLemma24Witness.witU_curved,
   AdalyFormal.Balaban.CovLemma24Witness.witU_alpha_pos,
   AdalyFormal.Balaban.CovLemma24Witness.witU_alpha_le_threshold⟩

/-- **THE COMPOSED NON-VACUITY, AT THE CURVED BACKGROUND ITSELF.**  `cdc_covariant_floor_nonvacuous`
instantiated at `CovLemma24Witness.witU witT`: a curved background, a nonzero element of the printed
carrier `ℓ²(Λ̃)`, a strictly positive left-hand side. -/
theorem cdc_covariant_floor_nonvacuous_curved :
    0 < ((1 / 360) * (1 / ((3 : ℕ) : ℝ) ^ 5)
          - 96 * frobSupBond (AdalyFormal.Balaban.CovLemma24Witness.witU
              AdalyFormal.Balaban.CovLemma24Witness.witT) ^ 2)
        * ‖tildeSpike (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2‖ ^ 2
    ∧ ((1 / 360) * (1 / ((3 : ℕ) : ℝ) ^ 5)
        - 96 * frobSupBond (AdalyFormal.Balaban.CovLemma24Witness.witU
            AdalyFormal.Balaban.CovLemma24Witness.witT) ^ 2)
        * ‖tildeSpike (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2‖ ^ 2
      ≤ (inner ℝ
          (cZero (AdalyFormal.Balaban.CovLemma24Witness.witU
              AdalyFormal.Balaban.CovLemma24Witness.witT) 3
            (dinvC (AdalyFormal.Balaban.CovLemma24Witness.witU
              AdalyFormal.Balaban.CovLemma24Witness.witT) 3)
            (tildeSpike (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2))
          (dstarDCLM (AdalyFormal.Balaban.CovLemma24Witness.witU
              AdalyFormal.Balaban.CovLemma24Witness.witT)
            (cZero (AdalyFormal.Balaban.CovLemma24Witness.witU
              AdalyFormal.Balaban.CovLemma24Witness.witT) 3
              (dinvC (AdalyFormal.Balaban.CovLemma24Witness.witU
                AdalyFormal.Balaban.CovLemma24Witness.witT) 3)
              (tildeSpike (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2))) : ℝ) :=
  cdc_covariant_floor_nonvacuous _ AdalyFormal.Balaban.CovLemma24Witness.witU_alpha_le_threshold

/-! ## §5 — CONTROLS: THE HYPOTHESES ARE LOAD-BEARING -/

/-- **THE SMALLNESS HYPOTHESIS IS NOT DECORATIVE.**  At `α₁ = 2` — the value `frobSupBond` takes at
the centre element `U ≡ −1` (`CovLemma24Center.frobSupBond_negOneU` gives `2√2 > 2`) — the
coefficient is strictly NEGATIVE at every `ell ≥ 1`, so `cdc_covariant_floor_dstarD`'s conclusion
carries no positive information there and `hcoeff` genuinely fails. -/
theorem coefficient_neg_at_alpha_two {ell : ℕ} (hell : 0 < ell) :
    (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * (2 : ℝ) ^ 2 < 0 := by
  have h1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h5 : (1 : ℝ) ≤ (ell : ℝ) ^ 5 := one_le_pow₀ h1
  have : (1 / 360 : ℝ) * (1 / (ell : ℝ) ^ 5) ≤ 1 / 360 := by
    have hp : (0 : ℝ) < (ell : ℝ) ^ 5 := by positivity
    have : (1 : ℝ) / (ell : ℝ) ^ 5 ≤ 1 := by
      rw [div_le_one hp]; exact h5
    nlinarith
  nlinarith

/-- **AT `B̃ = 0` EVERYTHING IS `0`** — stated so that no reader takes the non-vacuity of §4 off a
degenerate point (S82). -/
theorem floor_at_zero {ell : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ((1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2) * ‖(0 : TildeFn L ell)‖ ^ 2 = 0 := by
  simp

/-- **THE COARSE TERM IS NOT VACUOUSLY ZERO ON THE WHOLE FINE SPACE** — §2's cancellation is a
property of `range C₀`, not of `coarseQEnergyCov`.  Stated as: there is a field on which
`coarseQEnergyCov` is defined as a nonnegative sum, and `coarseQEnergyCov` of a general `A` is
`≥ 0` — the point being that §2 uses `cZero_mem_kerQ`, a theorem about `C₀`, and not a triviality
about the operator. -/
theorem coarseQEnergyCov_nonneg {ell : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : 0 ≤ coarseQEnergyCov U ell A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

#print axioms normSq_eq_hsInner
#print axioms curlEnergyCov_eq_dstarDQuadForm
#print axioms curlEnergyCov_eq_inner_dstarDCLM
#print axioms bondEnergy_eq_normSq
#print axioms cZeroFn
#print axioms cZeroFn_admissible
#print axioms coarseQEnergyCov_cZero_eq_zero
#print axioms cdc_covariant_floor_dstarD
#print axioms cdc_covariant_floor_general
#print axioms cdc_covariant_floor_of_T2_nonneg
#print axioms cdc_covariant_floor_positive
#print axioms witL3_hyps
#print axioms tildeSpike_witL3_ne_zero
#print axioms cdc_covariant_floor_nonvacuous
#print axioms witness_background_curved_and_in_class
#print axioms cdc_covariant_floor_nonvacuous_curved
#print axioms coefficient_neg_at_alpha_two
#print axioms floor_at_zero
#print axioms coarseQEnergyCov_nonneg

/-! ## §6 — THE `U`-FREE, `k`-FREE CONSTANT

`cdc_covariant_floor_positive`'s coefficient still mentions the background through `α₁`.  p.428
asks for a bound *"independent of `k` and `U`"*.  Over the smallness class `α₁ ≤ 1/(186·ell³)` the
coefficient is bounded below by a number depending on `ell` alone, and that number is exhibited in
closed form with its own rational lower bound. -/

/-- **THE CLASS-UNIFORM COEFFICIENT.**  `covariant_lemma24`'s coefficient at the WORST admissible
background: `α₁` replaced by its threshold value `1/(186·ell³)`.  No background appears. -/
noncomputable def gammaBrick (ell : ℕ) : ℝ :=
  (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * (1 / (186 * (ell : ℝ) ^ 3)) ^ 2

/-- **THE CONSTANT IS BOUNDED BELOW BY AN EXPLICIT RATIONAL**, `1/(345960·ell⁶)`.

Every factor is counted, not fitted: `gammaBrick ell = (34596·ell − 34560)/(12454560·ell⁶)` where
`34596 = 186²` (the threshold's denominator squared), `34560 = 96·360` (the drift constant times
the flat floor's denominator — the same `34560` `covariant_lemma24`'s own
`threshold_decomposition` carries), and `12454560 = 360·34596`.  At `ell ≥ 1` the numerator is at
least `34596 − 34560 = 36`, and `12454560/36 = 345960`.  **The margin is exactly `36`, i.e. the
class-uniform constant is positive by `186² > 34560` and by nothing else** — which is the same
inequality `covariant_lemma24`'s `186` is chosen by, so no new headroom is being spent here. -/
theorem gammaBrick_lower {ell : ℕ} (hell : 0 < ell) :
    1 / (345960 * (ell : ℝ) ^ 6) ≤ gammaBrick ell := by
  have h1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell : ℝ) := by linarith
  have hden : (0 : ℝ) < 12454560 * (ell : ℝ) ^ 6 := by positivity
  have key : gammaBrick ell - 1 / (345960 * (ell : ℝ) ^ 6)
      = 34596 * ((ell : ℝ) - 1) / (12454560 * (ell : ℝ) ^ 6) := by
    unfold gammaBrick
    field_simp
    ring
  have hnn : 0 ≤ 34596 * ((ell : ℝ) - 1) / (12454560 * (ell : ℝ) ^ 6) :=
    div_nonneg (by linarith) (le_of_lt hden)
  linarith

/-- The class-uniform constant is STRICTLY POSITIVE at every block size. -/
theorem gammaBrick_pos {ell : ℕ} (hell : 0 < ell) : 0 < gammaBrick ell := by
  have h0 : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hlow := gammaBrick_lower hell
  have : (0 : ℝ) < 1 / (345960 * (ell : ℝ) ^ 6) := by positivity
  linarith

/-- **THE CONSTANT IS THE WORST CASE OVER THE CLASS**, not a separate estimate: at any background
meeting the threshold, `covariant_lemma24`'s own coefficient is at least `gammaBrick ell`.

**`hell : 0 < ell` IS NOT USED BY THIS PROOF AND IS RETAINED DELIBERATELY** (Lean's linter flags it,
and the flag is correct).  Dropping it yields a statement that is still TRUE — but only through
Lean's junk convention `1/0 = 0`: at `ell = 0` the definition gives `gammaBrick 0 = 0`, the
hypothesis `hthr` reads `frobSupBond U ≤ 1/0 = 0` and so forces `α₁ = 0`, and both sides collapse to
`0`.  A statement whose truth at a boundary point rests on a junk value is exactly the class this
campaign keeps convicting, so the binder stays and keeps the theorem inside its intended domain.
This is a hypothesis that is decorative to the KERNEL and load-bearing for DENOTATION. -/
theorem gammaBrick_le_coefficient {ell : ℕ} (hell : 0 < ell)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3)) :
    gammaBrick ell ≤ (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2 := by
  have h0 := AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg U
  have hsq : frobSupBond U ^ 2 ≤ (1 / (186 * (ell : ℝ) ^ 3)) ^ 2 :=
    pow_le_pow_left₀ h0 hthr 2
  unfold gammaBrick
  linarith

/-- **THE FLOOR WITH A COEFFICIENT THAT DOES NOT MENTION THE BACKGROUND.**

    gammaBrick ell · ‖B̃‖²  ≤  ⟪C₀B̃, D_U^*D_U (C₀B̃)⟫    for EVERY `U` with `α₁ ≤ 1/(186·ell³)`.

`gammaBrick ell ≥ 1/(345960·ell⁶) > 0`.  This is p.428's *"independent of … `U`"* clause, for the
`D_U^*D_U` leg, over the class the threshold defines. -/
theorem cdc_floor_class_uniform {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    (w : TildeFn L ell) :
    gammaBrick ell * ‖w‖ ^ 2
      ≤ (inner ℝ (cZero U ell (dinvC U ell) w)
          (dstarDCLM U (cZero U ell (dinvC U ell) w)) : ℝ) := by
  have hell : 0 < ell := by omega
  obtain ⟨_, hfloor⟩ := cdc_covariant_floor_positive hell2 hstrict hdvd U hthr w
  have hcmp := gammaBrick_le_coefficient hell U hthr
  have hn : (0 : ℝ) ≤ ‖w‖ ^ 2 := sq_nonneg _
  nlinarith

/-- **THE `k`-FREE FORM.**  One constant, one inequality, for a WHOLE FAMILY of backgrounds indexed
by the RG step — the shape p.428's *"independent of `k`"* asks for, on the `D_U^*D_U` leg.

**What this does and does not say (read it against `deltak_wiring`).**  It says: if a family
`Ufam : ℕ → configurations` stays in the smallness class at every index, ONE constant serves every
index.  It does NOT say that Bałaban's RG produces such a family, and it does NOT say that the
tree's `deltaK` at index `k` is CMP99b's `Δ_k`.  Both are `compute/deltak_wiring/`'s and
`compute/perturbation_route/`'s questions and neither is settled here.  The constant is a
DEFINITION (`gammaBrick`), not an `∃` over free data (S91). -/
theorem cdc_floor_k_free {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (Ufam : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : ∀ k : ℕ, frobSupBond (Ufam k) ≤ 1 / (186 * (ell : ℝ) ^ 3)) :
    0 < gammaBrick ell
    ∧ ∀ (k : ℕ) (w : TildeFn L ell),
        gammaBrick ell * ‖w‖ ^ 2
          ≤ (inner ℝ (cZero (Ufam k) ell (dinvC (Ufam k) ell) w)
              (dstarDCLM (Ufam k) (cZero (Ufam k) ell (dinvC (Ufam k) ell) w)) : ℝ) :=
  ⟨gammaBrick_pos (by omega),
   fun k w => cdc_floor_class_uniform hell2 hstrict hdvd (Ufam k) (hthr k) w⟩

/-! ## §7 — POSITIVE DEFINITENESS OF THE CONSTRUCTED `C*Δ_kC`, AT `T2 = 0`

`compute/construct_cdc/` §8 residual 4 records: *"Positive definiteness itself.  `cdcOp_posDef_iff`
reduces it to `Δ_k > 0` on `range C₀` and stops there."*  At `T2 = 0` — i.e. with `Δ_k` taken to be
its `D_U^*D_U` leg alone — BOTH sides of that iff are now theorems, for every background in the
smallness class.  **This does NOT discharge the residual at the printed `Δ_k`**, whose `T2` is
`deltak_wiring`'s `pinnedT2`; it discharges it at the leg this lane bounds. -/

/-- **`C₀*(D_U^*D_U)C₀` IS POSITIVE DEFINITE ON `ℓ²(Λ̃)`** for every background meeting the
threshold.  Note `w ≠ 0` is the only hypothesis on the vector: the carrier is the printed one, so
no "vanishes on dropped bonds" side condition appears. -/
theorem cdcOp_posDef_at_zero {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    (w : TildeFn L ell) (hw : w ≠ 0) :
    (0 : ℝ) < inner ℝ w (cdcOp U ell (dinvC U ell) 0 w) := by
  have hell : 0 < ell := by omega
  have hpos := gammaBrick_pos hell
  have hn : (0 : ℝ) < ‖w‖ ^ 2 := by
    have := norm_pos_iff.mpr hw
    positivity
  have hbase := cdc_covariant_floor_general hell2 hstrict hdvd U
    (le_of_lt ((cdc_covariant_floor_positive hell2 hstrict hdvd U hthr w).1)) 0 w
  have hzero : (inner ℝ (cZero U ell (dinvC U ell) w)
      ((0 : BondFnL2 L →L[ℝ] BondFnL2 L) (cZero U ell (dinvC U ell) w)) : ℝ) = 0 := by
    simp
  rw [hzero, sub_zero] at hbase
  have hcmp := gammaBrick_le_coefficient hell U hthr
  nlinarith

/-- **THE OTHER SIDE OF `construct_cdc`'s `cdcOp_posDef_iff`, DISCHARGED AT `T2 = 0`**: the
`D_U^*D_U` form is strictly positive at every nonzero element of `range C₀`.  Obtained by running
that lane's own equivalence forwards, so the two statements cannot drift apart. -/
theorem deltaK_posDef_on_range_cZero {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3)) :
    ∀ z : BondFnL2 L, z ∈ LinearMap.range (cZero U ell (dinvC U ell)) → z ≠ 0 →
      (0 : ℝ) < inner ℝ z (deltaK U 0 z) :=
  (AdalyFormal.Balaban.ConstructCDC.cdcOp_posDef_iff U ell (dinvC U ell) 0).mp
    (fun w hw => cdcOp_posDef_at_zero hell2 hstrict hdvd U hthr w hw)

/-- **CONTROL — the positive-definiteness statement is not vacuous**: the carrier has a named
nonzero element at the witness parameters, so `cdcOp_posDef_at_zero`'s hypothesis `w ≠ 0` is
satisfiable and the conclusion is asserted somewhere. -/
theorem cdcOp_posDef_at_zero_nonvacuous
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      AdalyFormal.Balaban.Lemma24GeneralEll.witL3)
    (hthr : frobSupBond U ≤ 1 / (186 * ((3 : ℕ) : ℝ) ^ 3)) :
    (0 : ℝ) < inner ℝ (tildeSpike (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2)
      (cdcOp U 3 (dinvC U 3) 0 (tildeSpike (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2)) :=
  cdcOp_posDef_at_zero (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.1 witL3_hyps.2 U hthr _
    tildeSpike_witL3_ne_zero

#print axioms gammaBrick
#print axioms gammaBrick_lower
#print axioms gammaBrick_pos
#print axioms gammaBrick_le_coefficient
#print axioms cdc_floor_class_uniform
#print axioms cdc_floor_k_free
#print axioms cdcOp_posDef_at_zero
#print axioms deltaK_posDef_on_range_cZero
#print axioms cdcOp_posDef_at_zero_nonvacuous

end AdalyFormal.Balaban.TerminalCompose
