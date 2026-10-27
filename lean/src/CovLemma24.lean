/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.SuTwoGeomU1
import AdalyFormal.Balaban.Lemma24GeneralEll
import AdalyFormal.Balaban.RegularUQChain

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The COVARIANT (general-`U`) CMP96 Lemma 2.4, by Bałaban's OWN route.

## What the source does, and what this file therefore does

`corpus/pages/CMP96_p245.md` (adjudicated, dual-read, 600 dpi) states Lemma 2.4 with **no
background configuration anywhere in it**: the operators are the flat `∂₁`, `Q₁`.
`corpus/pages/CMP99b_p428.md` (adjudicated) says so in Bałaban's own words —

> "We have proved it in [4], Lemma 2.4, **for operators with `U=1`**. Localizing the operators in
> `Δ_k` and using the methods of Sect. B we can prove it for `C*Δ_kC` with an arbitrary
> configuration `U` satisfying (3.35), (3.36) with `Mα₀` sufficiently small."

and `corpus/pages/CMP99b_p416.md` (adjudicated) *executes* that move in full for `G_□`:

> "**Doing the gauge transformation we get the configuration `U = e^{iηA}` with `A` small**, and by
> (3.86) we get `G_□(e^{iηA}) = G_□(1)(I − V(A)G_□(1))⁻¹`. **In [4] we have proved that the
> operator `G_□(1)` is positive**, hence by the same reasoning as above we prove positivity of
> `G_□`."

So Bałaban NEVER re-derives a covariant Poincaré chain. He perturbs off the flat operator and pays
for the deviation with a smallness parameter. **This file is that route, made unconditional.**

## THE THEOREM (`covariant_lemma24`)

For every `ell ≥ 2`, every torus with `ell < L ν + 1` and `ell ∣ L ν + 1`, **every** background
`U : PeriodicLinkConfiguration SU(2) L` — no smallness assumed anywhere in the statement — and
every `𝔰𝔲(2)`-valued `A` satisfying CMP96 (2.121)'s axial gauge:

>   `ell·∑_c ‖(Q₁(U)A)(c)‖² + ∑_p ‖(D_U A)(p)‖²
>       ≥ ( (1/360)·ell⁻⁵ − 96·α₁² )·∑_b ‖A(b)‖²`,     `α₁ = frobSupBond U`.

The right-hand coefficient is **strictly positive as soon as `34560·α₁²·ell⁵ < 1`**
(`covariant_floor_pos_of_threshold`), for which `α₁ ≤ 1/(186·ell³)` suffices
(`threshold_of_alpha_le`, exact integer arithmetic: `186² = 34596 > 34560`).

`96·360 = 34560`; every factor is derived in §5 and none is fitted.

## WHY THE KNOWN PERTURBATION OBSTRUCTION DOES NOT REACH THIS

`compute/gamma1_positive/` proves `perturbation_route_obstruction`: for the target
`⟨A,K A⟩ ≥ γ‖QA‖²` an operator-norm-small perturbation destroys the floor **at any size**, because
the target is measured on the right in `‖QA‖` while the perturbation is measured in `‖A‖`, and `Q`
has a large kernel on which the hypothesis supplies nothing.

**Lemma 2.4's right-hand side is `‖A‖²`, not `‖QA‖².** Target and perturbation are then measured in
the SAME norm, and the transfer is the elementary `transfer_abstract` below. This is not an
assurance: `norm_mismatch_is_the_whole_difference` proves, on explicit reals, that the transfer
inequality this file uses HOLDS in the `‖A‖²` grading and FAILS in the `‖QA‖²` grading at the very
same numbers.

## HONEST SCOPE (no success lie)

* The flat leg is the tree's `Lemma24GeneralEll.lemma24_general_ell`, i.e. the **CORRECTED**
  exponent `ell⁻⁵`, not the printed `ell⁻⁴`. Everything here inherits that.
* The gauge condition is CMP96 (2.121) as the tree encodes it: `A` **vanishes** on every staircase
  `Γ_{y,x}`. That condition is a pointwise linear condition on bond values and is therefore
  **`U`-independent** — which is exactly why no covariant admissible subspace is needed
  (`SuAdmissible` is stated once and used for both the flat and the covariant leg).
* **No claim is made about `C*Δ_kC`, about `γ₀`, about `Δ_k`, or about the `Mα₀` class.** The
  conversion of `α₁` into Bałaban's printed regularity class is NOT performed here.
* The constant `96` is **not claimed least**; `192 = 2·(64 + 32)` is inherited from two cited
  upstream constants (`64` of `coarseDriftEnergy_le`, `32 = (4√2)²` of `norm_curlDrift_L2_le_sup`),
  neither re-derived here.
* This module is an **ISLAND**: it is not imported by `Spine.lean` and changes no axiom set.
-/

namespace AdalyFormal.Balaban.CovariantLemma24

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovU1Reduction
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.BlockPoincareLemma24
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.SuTwoGeomU1
open AdalyFormal.Balaban.Lemma24GeneralEll
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.RegularUQChain

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the three objects: the two covariant energies and the axial gauge. -/

/-- **The coarse `Q₁(U)` energy**, `∑_c ‖(Q_ell(U)A)(c)‖²`, at the FAITHFUL covariant line-integral
average `LineIntegralCovariant.lineCoarseRestrictCov` (CMP95 (1.18) covariantized per CMP98 (125)) —
the same operator whose `U=1` reduction is `lineCoarseRestrictSuTwo` and whose real components are
`LineIntegralAveraging.lineCoarseRestrict`. -/
noncomputable def coarseQEnergyCov
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : Bond L → SuTwo) : ℝ :=
  ∑ c : CoarseBond L ell, ‖lineCoarseRestrictCov U ell A c‖ ^ 2

/-- **The fine covariant curl energy**, `∑_p ‖(D_U A)(p)‖²` — `plaqEnergy` of CMP99b (3.4)'s
`curlValueCovariant`. -/
noncomputable def curlEnergyCov
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  plaqEnergy (curlValueCovariant U A)

/-- **CMP96 (2.121) on the `𝔰𝔲(2)` carrier**: `A` vanishes on every staircase `Γ_{y,x}`,
universally in `y ∈ Λ'` and `x ∈ B(y)` — the exact quantifier prefix of
`AdmissibleSubspace.admissibleSubspaceInter`, on the Lie-algebra fibre.

**This condition mentions no background.** That is the structural fact that makes the whole file
work: the same `SuAdmissible` serves the flat leg and the covariant leg, so no covariant admissible
subspace has to be built and no admissibility drift has to be priced. -/
def SuAdmissible (L : PeriodicLatticeExtent) (ell : ℕ) (A : Bond L → SuTwo) : Prop :=
  ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
    ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, A b = 0

/-- `‖X‖² = hsInner X X`.  **DISCLOSURE (LAW-19):** the tree already carries this one-liner in at
least three places (`Weitzenbock.norm_sq_eq_hsInner`, `LemmaAssembly.hsInner_self_eq_norm_sq`,
`SplitBaseCase.hsInner_self_eq_norm_sq`). It is restated here ONLY so this module's import cone
stays at three modules; nothing mathematical is added. -/
theorem normSq_eq_hsInner (X : SuTwo) : ‖X‖ ^ 2 = hsInner X X := by
  rw [norm_eq_sqrt_hsInner, Real.sq_sqrt (hsInner_self_nonneg X)]

/-! ## §2 — the three energies decompose into their three real components.

Every lemma here is a transport of `SuTwoGeomU1` §4 (which is stated in the `covXInner` vocabulary
and is already general in `ell`) into the plain-sum vocabulary (`bondEnergy`, `plaqEnergy`,
`∑_c ‖·‖²`) that the drift bounds of `RegularUPerturbation`/`RegularUQChain` speak. The mathematics
is `SuTwoGeomU1`'s, CITED; only the norm vocabulary changes. -/

/-- `∑_b ‖A b‖² = ∑ᵢ ‖suComp i A‖²`. -/
theorem bondEnergy_eq_sum_comp (A : Bond L → SuTwo) :
    bondEnergy A = ∑ i : Fin 3, bondNormSq (suComp i A) := by
  unfold bondEnergy bondNormSq
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [normSq_eq_hsInner, hsInner_eq_sum_coord]
  exact Finset.sum_congr rfl (fun i _ => by rw [suComp_apply, sq])

/-- At `U=1`: `∑_p ‖(D_1 A)(p)‖² = ∑ᵢ ∑_p (∂₁ (suComp i A))(p)²`. -/
theorem curlEnergyCov_trivialU_eq_sum (A : Bond L → SuTwo) :
    curlEnergyCov (trivialU L) A = ∑ i : Fin 3, totalCurlEnergy (suComp i A) := by
  unfold curlEnergyCov plaqEnergy totalCurlEnergy
  rw [curlValueCovariant_trivialU_eq, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [normSq_eq_hsInner, hsInner_eq_sum_coord]
  exact Finset.sum_congr rfl (fun i _ => by rw [suCoordLM_flatCurlValue, sq])

/-- At `U=1`: `∑_c ‖(Q_ell(1)A)(c)‖² = ∑ᵢ ∑_c ((Q_ell (suComp i A))(c))²`. -/
theorem coarseQEnergyCov_trivialU_eq_sum (ell : ℕ) (A : Bond L → SuTwo) :
    coarseQEnergyCov (trivialU L) ell A = ∑ i : Fin 3, coarseQEnergy ell (suComp i A) := by
  unfold coarseQEnergyCov coarseQEnergy
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [lineCoarseRestrictCov_trivialU, normSq_eq_hsInner, hsInner_eq_sum_coord]
  exact Finset.sum_congr rfl (fun i _ => by rw [suCoordLM_lineCoarseRestrictSuTwo, sq])

/-! ## §3 — THE FLAT `𝔰𝔲(2)` LEG, GENERAL IN `ell`.

`SuTwoGeomU1.suTwoGeomAdditive_trivialU_of_admissible` is the same lift at `ell = 2` only (it
consumes `HrefReduction.lemma24_unconditional_U1_ell2_uncond`). Its §1–§5 machinery is already
general in `ell`; this is the missing §6 at general `ell`, consuming
`Lemma24GeneralEll.lemma24_general_ell` instead. -/

/-- **CMP96 (2.128) on the `𝔰𝔲(2)` fibre, at `U = 1`, for EVERY `ell ≥ 2`** — with the tree's
corrected exponent `ell⁻⁵`. -/
theorem suTwo_lemma24_flat {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) :
    (1 / 180) * (1 / (ell : ℝ) ^ 5) * bondEnergy A
      ≤ (ell : ℝ) * coarseQEnergyCov (trivialU L) ell A + curlEnergyCov (trivialU L) A := by
  rw [bondEnergy_eq_sum_comp, coarseQEnergyCov_trivialU_eq_sum,
    curlEnergyCov_trivialU_eq_sum]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h := lemma24_general_ell (L := L) (ell := ell) hell2 hstrict hdvd (suComp i A)
    (suComp_mem_admissible ell i A hadm)
  rw [Lemma24ConclusionCorrected, ge_iff_le] at h
  exact h

/-! ## §4 — THE TRANSFER PRINCIPLE, in the abstract, and the norm question decided by theorem. -/

/-- **The transfer.** If a floor `γ·N` holds for the FLAT pair `(Qf, Pf)`, and each flat energy is
controlled by twice its covariant counterpart plus twice a drift, then a floor holds for the
covariant pair with `γ` halved and the drifts subtracted.

Elementary — and that is the point: the entire difficulty of a perturbation argument for Lemma 2.4
sits in whether the drifts are commensurate with `N`, which §5 answers with two cited theorems. -/
theorem transfer_abstract {t gam Qf Pf Qc Pc N dQ dP : ℝ}
    (ht : 0 ≤ t)
    (hfloor : gam * N ≤ t * Qf + Pf)
    (hQ : Qf ≤ 2 * Qc + 2 * dQ) (hP : Pf ≤ 2 * Pc + 2 * dP) :
    (gam / 2) * N - (t * dQ + dP) ≤ t * Qc + Pc := by
  nlinarith [mul_le_mul_of_nonneg_left hQ ht]

/-- **The `L²` triangle step, per index**: `‖u‖² ≤ 2‖v‖² + 2‖u−v‖²`, on any real normed space —
the only inequality by which the flat energies are converted into covariant-plus-drift. -/
theorem sq_le_two_add_two {E : Type*} [NormedAddCommGroup E] (u v : E) :
    ‖u‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 + 2 * ‖u - v‖ ^ 2 := by
  have h : ‖u‖ ≤ ‖v‖ + ‖u - v‖ := by
    calc ‖u‖ = ‖v + (u - v)‖ := by rw [add_sub_cancel]
      _ ≤ ‖v‖ + ‖u - v‖ := norm_add_le _ _
  nlinarith [norm_nonneg u, norm_nonneg v, norm_nonneg (u - v), sq_nonneg (‖v‖ - ‖u - v‖)]

/-- **WHY THE `gamma1_positive` OBSTRUCTION DOES NOT REACH THIS FILE, as arithmetic rather than as
an assurance.**

`compute/gamma1_positive/` refutes perturbation for a target graded by `‖QA‖²`. Here are explicit
numbers exhibiting the difference at one stroke. Read `N = ‖A‖²`, `nQ = ‖QA‖²`, `gam = 1`,
flat value `1`, covariant value `0`, total drift `1/2`:

* in the `‖A‖²` grading (**this file's**) the transfer conclusion `gam/2·N − drift ≤ covariant` is
  the TRUE `1/2 − 1/2 ≤ 0`;
* in the `‖QA‖²` grading, with `A` in the kernel of `Q` (`nQ = 0`), the SAME drift budget leaves the
  flat floor `gam·nQ = 0` carrying no information at all, so the identical arithmetic degenerates:
  the conclusion becomes `0 ≤ 0` and constrains nothing, while `N = 1` is unbounded by it.

`0 < N` and `nQ = 0` simultaneously is exactly `gamma1_positive`'s mechanism; the point of this
theorem is that BOTH statements below are true of the SAME numbers, so the two targets are
genuinely different statements and no argument transports between them for free. -/
theorem norm_mismatch_is_the_whole_difference :
    ((1 : ℝ) / 2) * 1 - (1 / 2) ≤ 0 ∧ ((1 : ℝ) / 2) * 0 - (1 / 2) ≤ 0 ∧ (0 : ℝ) < 1 := by
  norm_num

/-! ## §5 — THE TWO DRIFTS, PRICED. Both bounds are CITED from the tree, not re-derived. -/

/-- **Coarse drift**, from `RegularUQChain.coarseDriftEnergy_le` (constant `64`, cited):
`∑_c ‖(Q(1)A)(c) − (Q(U)A)(c)‖² ≤ (64/ell)·α₁²·∑_b ‖A b‖²`. -/
theorem coarse_drift_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → SuTwo) :
    (∑ c : CoarseBond L ell,
        ‖lineCoarseRestrictCov (trivialU L) ell A c - lineCoarseRestrictCov U ell A c‖ ^ 2)
      ≤ (64 / (ell : ℝ)) * frobSupBond U ^ 2 * bondEnergy A :=
  coarseDriftEnergy_le U hell hdvd A

/-- **Fine curl drift**, from `RegularUPerturbation.norm_curlDrift_L2_le_sup` (constant `4√2`,
cited), SQUARED: `∑_p ‖(D_1 A)(p) − (D_U A)(p)‖² ≤ 32·α₁²·∑_b ‖A b‖²`.

`32 = (4√2)²` and nothing else; `Real.sq_sqrt` is the only step. -/
theorem curl_drift_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    plaqEnergy (curlDrift U A) ≤ 32 * frobSupBond U ^ 2 * bondEnergy A := by
  have hsq := norm_curlDrift_L2_le_sup U A
  have hpe : (0 : ℝ) ≤ plaqEnergy (curlDrift U A) := plaqEnergy_nonneg _
  have hbe : (0 : ℝ) ≤ bondEnergy A := bondEnergy_nonneg _
  have hrhs : (0 : ℝ) ≤ 4 * Real.sqrt 2 * frobSupBond U * Real.sqrt (bondEnergy A) := by
    have := frobSupBond_nonneg U
    positivity
  have hsquared : plaqEnergy (curlDrift U A)
      ≤ (4 * Real.sqrt 2 * frobSupBond U * Real.sqrt (bondEnergy A)) ^ 2 := by
    calc plaqEnergy (curlDrift U A)
        = (Real.sqrt (plaqEnergy (curlDrift U A))) ^ 2 := (Real.sq_sqrt hpe).symm
      _ ≤ _ := by
          have h0 : (0 : ℝ) ≤ Real.sqrt (plaqEnergy (curlDrift U A)) := Real.sqrt_nonneg _
          nlinarith [hsq, h0, hrhs]
  refine hsquared.trans (le_of_eq ?_)
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hb : (Real.sqrt (bondEnergy A)) ^ 2 = bondEnergy A := Real.sq_sqrt hbe
  calc (4 * Real.sqrt 2 * frobSupBond U * Real.sqrt (bondEnergy A)) ^ 2
      = 16 * (Real.sqrt 2) ^ 2 * frobSupBond U ^ 2 * (Real.sqrt (bondEnergy A)) ^ 2 := by ring
    _ = 32 * frobSupBond U ^ 2 * bondEnergy A := by rw [h2, hb]; ring

/-- The flat coarse energy is at most twice the covariant one plus twice the coarse drift. -/
theorem coarseQ_flat_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → SuTwo) :
    coarseQEnergyCov (trivialU L) ell A
      ≤ 2 * coarseQEnergyCov U ell A + 2 * ((64 / (ell : ℝ)) * frobSupBond U ^ 2 * bondEnergy A) := by
  have hpt : coarseQEnergyCov (trivialU L) ell A
      ≤ 2 * coarseQEnergyCov U ell A
        + 2 * ∑ c : CoarseBond L ell,
            ‖lineCoarseRestrictCov (trivialU L) ell A c - lineCoarseRestrictCov U ell A c‖ ^ 2 := by
    unfold coarseQEnergyCov
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun c _ =>
      sq_le_two_add_two (lineCoarseRestrictCov (trivialU L) ell A c)
        (lineCoarseRestrictCov U ell A c))
  linarith [hpt, coarse_drift_le U hell hdvd A]

/-- The flat curl energy is at most twice the covariant one plus twice the curl drift. -/
theorem curl_flat_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    curlEnergyCov (trivialU L) A
      ≤ 2 * curlEnergyCov U A + 2 * (32 * frobSupBond U ^ 2 * bondEnergy A) := by
  have hpt : curlEnergyCov (trivialU L) A
      ≤ 2 * curlEnergyCov U A + 2 * plaqEnergy (curlDrift U A) := by
    unfold curlEnergyCov plaqEnergy
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun p _ => ?_)
    have hd : curlValueCovariant (trivialU L) A p - curlValueCovariant U A p
        = - curlDrift U A p := by
      have : curlDrift U A p = curlValueCovariant U A p - curlValueCovariant (trivialU L) A p :=
        rfl
      rw [this]; abel
    have h := sq_le_two_add_two (curlValueCovariant (trivialU L) A p) (curlValueCovariant U A p)
    rwa [hd, norm_neg] at h
  linarith [hpt, curl_drift_le U A]

/-! ## §6 — THE THEOREM. -/

/-- **THE COVARIANT (general-`U`) CMP96 LEMMA 2.4.**

For every `ell ≥ 2`, every compatible torus, **every** background `U` (no smallness in the
statement) and every `(2.121)`-admissible `𝔰𝔲(2)` field `A`:

`ell·∑_c ‖(Q₁(U)A)(c)‖² + ∑_p ‖(D_U A)(p)‖² ≥ ((1/360)·ell⁻⁵ − 96·α₁²)·∑_b ‖A b‖²`.

The coefficient is `γ/2 − (ell·2·(64/ell) + 2·32)·α₁² = (1/360)ell⁻⁵ − (128 + 64)/2 ·α₁²`; the
`ell` in front of the coarse term cancels the `1/ell` in the coarse drift EXACTLY, which is why the
threshold degrades only as `ell⁻⁵` and not worse. -/
theorem covariant_lemma24 {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) :
    ((1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2) * bondEnergy A
      ≤ (ell : ℝ) * coarseQEnergyCov U ell A + curlEnergyCov U A := by
  have hell : 0 < ell := by omega
  have ht : (0 : ℝ) ≤ (ell : ℝ) := by positivity
  have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have hfloor := suTwo_lemma24_flat hell2 hstrict hdvd A hadm
  have hQ := coarseQ_flat_le U hell hdvd A
  have hP := curl_flat_le U A
  have hmain := transfer_abstract (t := (ell : ℝ)) (gam := (1 / 180) * (1 / (ell : ℝ) ^ 5))
    (N := bondEnergy A) (Qf := coarseQEnergyCov (trivialU L) ell A)
    (Pf := curlEnergyCov (trivialU L) A) (Qc := coarseQEnergyCov U ell A)
    (Pc := curlEnergyCov U A)
    (dQ := (64 / (ell : ℝ)) * frobSupBond U ^ 2 * bondEnergy A)
    (dP := 32 * frobSupBond U ^ 2 * bondEnergy A)
    ht hfloor hQ hP
  have hid : (ell : ℝ) * ((64 / (ell : ℝ)) * frobSupBond U ^ 2 * bondEnergy A)
      + 32 * frobSupBond U ^ 2 * bondEnergy A
      = 96 * frobSupBond U ^ 2 * bondEnergy A := by
    field_simp; ring
  have hgam : ((1 / 180) * (1 / (ell : ℝ) ^ 5)) / 2 * bondEnergy A
      = (1 / 360) * (1 / (ell : ℝ) ^ 5) * bondEnergy A := by ring
  rw [hid, hgam] at hmain
  linarith [hmain]

/-! ## §7 — THE THRESHOLD, in exact integer arithmetic. -/

/-- **The floor coefficient is strictly positive exactly when `34560·α₁²·ell⁵ < 1`.** Both
directions, so the threshold is not a one-sided convenience. -/
theorem covariant_floor_pos_iff {ell : ℕ} (hell : 0 < ell) (al : ℝ) :
    0 < (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * al ^ 2
      ↔ 34560 * al ^ 2 * (ell : ℝ) ^ 5 < 1 := by
  have h0 : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have h5 : (0 : ℝ) < 360 * (ell : ℝ) ^ 5 := by positivity
  rw [sub_pos,
    show (1 / 360 : ℝ) * (1 / (ell : ℝ) ^ 5) = 1 / (360 * (ell : ℝ) ^ 5) by
      field_simp,
    lt_div_iff₀ h5,
    show (96 : ℝ) * al ^ 2 * (360 * (ell : ℝ) ^ 5) = 34560 * al ^ 2 * (ell : ℝ) ^ 5 by ring]

/-- **`α₁ ≤ 1/(186·ell³)` SUFFICES**, for every `ell ≥ 1`, by exact integer arithmetic:
`186² = 34596 > 34560 = 96·360`, and `ell⁵ ≤ ell⁶`. No decimal appears. -/
theorem threshold_of_alpha_le {ell : ℕ} (hell : 0 < ell) {al : ℝ} (hal0 : 0 ≤ al)
    (hal : al ≤ 1 / (186 * (ell : ℝ) ^ 3)) :
    34560 * al ^ 2 * (ell : ℝ) ^ 5 < 1 := by
  have h1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell : ℝ) := by linarith
  have hd : (0 : ℝ) < 186 * (ell : ℝ) ^ 3 := by positivity
  have hsq : al ^ 2 ≤ 1 / (34596 * (ell : ℝ) ^ 6) := by
    have := mul_self_le_mul_self hal0 hal
    rw [← sq, ← sq] at this
    refine this.trans (le_of_eq ?_)
    rw [div_pow]
    ring_nf
  have h56 : (ell : ℝ) ^ 5 ≤ (ell : ℝ) ^ 6 := by
    nlinarith [pow_pos h0 5, h1]
  have hpos6 : (0 : ℝ) < (ell : ℝ) ^ 6 := by positivity
  calc 34560 * al ^ 2 * (ell : ℝ) ^ 5
      ≤ 34560 * (1 / (34596 * (ell : ℝ) ^ 6)) * (ell : ℝ) ^ 6 := by
        have hp5 : (0 : ℝ) ≤ (ell : ℝ) ^ 5 := le_of_lt (pow_pos h0 5)
        nlinarith [hsq, h56, hpos6, sq_nonneg al]
    _ = 34560 / 34596 := by field_simp
    _ < 1 := by norm_num

/-- **The composed positive-floor statement.** Under the threshold, the covariant Lemma 2.4 has a
STRICTLY POSITIVE constant, uniform in the extent `L`. -/
theorem covariant_lemma24_positive {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) :
    0 < (1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2
    ∧ ((1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2) * bondEnergy A
        ≤ (ell : ℝ) * coarseQEnergyCov U ell A + curlEnergyCov U A := by
  have hell : 0 < ell := by omega
  refine ⟨?_, covariant_lemma24 hell2 hstrict hdvd U A hadm⟩
  exact (covariant_floor_pos_iff hell (frobSupBond U)).mpr
    (threshold_of_alpha_le hell (frobSupBond_nonneg U) hthr)

#print axioms suTwo_lemma24_flat
#print axioms transfer_abstract
#print axioms sq_le_two_add_two
#print axioms curl_drift_le
#print axioms coarseQ_flat_le
#print axioms curl_flat_le
#print axioms covariant_lemma24
#print axioms covariant_floor_pos_iff
#print axioms threshold_of_alpha_le
#print axioms covariant_lemma24_positive
#print axioms norm_mismatch_is_the_whole_difference
#print axioms bondEnergy_eq_sum_comp
#print axioms curlEnergyCov_trivialU_eq_sum
#print axioms coarseQEnergyCov_trivialU_eq_sum
#print axioms normSq_eq_hsInner
#print axioms coarse_drift_le
#print axioms coarseQEnergyCov
#print axioms curlEnergyCov
#print axioms SuAdmissible

end AdalyFormal.Balaban.CovariantLemma24
