/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Gamma1Reduction
import TerminalBrick

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

/-!
# `SchurFloor.lean` — G3 THROUGH THE VARIATIONAL IDENTITY, AND THE DENOTATION QUESTION SETTLED

## The question this module was dispatched to answer

`compute/terminal_compose/DAG.md` row **G3** `[CSTAR-SCHUR-GAP]`: the general-`U` brick
`TerminalCompose.cdc_floor_class_uniform` floors `⟪C₀B̃, D_U^*D_U (C₀B̃)⟫`, while CMP99b (3.156)'s
leading term is the Schur complement `(QG₁Q*)⁻¹`; and the FORM comparison is proved adverse
(`CStarDeltaKCCoercive.deltaJQuadFormCovFaithful_le_dstarDQuadForm`: the faithful form sits BELOW
`D*D`).  Every previous attack compared forms.  The route tried here goes through the VARIATIONAL
identity `Gamma1Reduction.deltaKQuadForm_eq` instead — `Φ_a(B) = ⟨H₁B, Kop H₁B⟩` — where no form
comparison between `Δ_j^{cov}` and `D_U^*D_U` occurs at all.

Before any of that, one question had to be settled, because getting it wrong would poison
everything downstream:

> **Is `D_U^*D_U` the engine's `Kop`?**

`Kop` is `Gamma1Reduction.IsAQuadSplit`'s `a`-free part of `G₁⁻¹`, i.e. CMP99b (3.128)'s
`Δ_π + DRD*`.  `D_U^*D_U` is `CStarDeltaKCOperator.dstarDCLM U`, whose form
(`inner_dstarDCLM_eq_dstarDQuadForm`) is the covariant curl energy.  Both are "a curl energy", so the
names collide.  **They are not the same object, and §1 settles it at the declarations.**

## §1 — THE ANSWER: THE COLLISION IS A SCALE COLLISION, AND BOTH READINGS ARE REFUTED

The engine `Gamma1Reduction` runs on `BalabanCovarianceData Hs Ks` with `Q : Hs →L Ks`.  Three
carriers occur in the printed statement, at three consecutive blocking levels:

| | printed | engine | what lives there |
|---|---|---|---|
| level 0 | `A` of (3.128) | `Hs` | `G₁`, `Kop = Δ_π + DRD*`, the FINE curl |
| level 1 | `B` of (3.156) | `Ks` | `(QG₁Q*)⁻¹`, `Δ_k`, and `Q₁B = 0` |
| level 2 | `Q₁B` | — | the target of the printed subspace's third clause |

The two candidate readings of the brick, and what happens to route (i) under each:

**READING A — the brick's `BondFnL2 L` is `Ks` (level 1).**  This is the reading FORCED by the only
existing consumer link: `Gamma1Reduction.gamma_floor_compressed_of_restricted` takes
`C₀ : W →L[ℝ] Ks` with `hC : ∀ w, ‖w‖ ≤ ‖C₀ w‖`, and the brick's
`ConstructCDC.cZero U ell (dinvC U ell) : TildeFn L ell →L[ℝ] BondFnL2 L` together with
`ConstructCDC.norm_le_norm_cZero` has EXACTLY that signature; and `ConstructCDC.cZero_mem_kerQ`
(`Q₁(U)(C₀B̃) = 0`) is character-for-character the printed subspace's third clause, which is a
condition on `B`.  Under Reading A the brick's `dstarDCLM U` is the LEVEL-1 curl energy — the engine's
`E`, not the engine's `Kop`, which lives on `Hs`.  **Route (i) is then a pun at the carrier: the
hypothesis it wants (`⟨A,KopA⟩ ≥ γ_f‖A‖²`) is a statement about `Hs`, and the brick asserts nothing
about `Hs`.**  §3 shows the brick is nonetheless exactly what the engine's OTHER input slot wants.

**READING B — the brick's `BondFnL2 L` is `Hs` (level 0).**  This is the reading the tree's own
constructed datum uses: `compute/g1_datum/stage/G1Datum.lean:318` types
`g1Data : BalabanCovarianceData ↥(admSub L ell) (CoarseBondSpace L ell)` with `Q = QH L ell`, and
`QH` is the SAME block average that `construct_cdc` calls `Q₁`.  Under Reading B `dstarDCLM U` IS
(the leading part of) `Kop`, so route (i)'s premise is at least type-correct — but the brick's floor
holds only on `range C₀`, and `range C₀ ⊆ ker Q₁ = ker Q`.  **On `ker Q` the engine's condition reads
`γ‖QA‖² = 0 ≤ ⟨A,KopA⟩`, which is free from positivity alone: the brick's constant is multiplied by
zero.**  §2 proves the sharp version — a strictly positive floor on `ker Q`, with `‖Q‖ ≤ 1` and `Kop`
positive semidefinite, does NOT extend to the engine's condition for any `γ > 0`.

**THE TWO READINGS ARE NOT INTERCHANGEABLE, AND THE MISMATCH IS TWOFOLD AT THE TYPES.**  Measured, not
described:

* `CovariantOperators.lean:655` — `abbrev BondFnL2 (L) : Type := PiLp 2 (fun _ : Bond L => SuTwo)`;
* `LatticeOperators.lean:620` — `abbrev CoarseBondSpace (L) (ell) := EuclideanSpace ℝ (CoarseBond L ell)`.

They differ in the INDEX (`Bond L` vs `CoarseBond L ell` — one blocking level) **and** in the FIBRE
(`SuTwo` vs `ℝ` — Lie algebra vs scalar).  So `g1Data` and the brick cannot be instantiated into one
and the same `BalabanCovarianceData`, and no theorem in this module pretends otherwise.

## §2–§3 — WHAT IS BUILT

* **§2** the Reading-B no-go, at named objects with no `∃` over free data (S91).  Route (i)'s ALGEBRA
  is proved SOUND first (`contraction_transfers_fine_floor`) so that the refutation lands where it
  belongs — on the domain of the available floor, not on the `‖Q‖ ≤ 1` step.
* **§3** the Reading-A re-wiring, which is where a theorem lands:
  * `gamma_floor_of_interp_and_weakPoincare` — `Gamma1Reduction.gamma_floor_from_interp_and_poincare`
    with `hpoin` WEAKENED from `γP‖C₀w‖²` to `γP‖w‖²`.  Strictly more general: the hypothesis is
    weaker (`‖w‖ ≤ ‖C₀w‖`) and the hypothesis `hC` disappears from the statement entirely.  This is
    the shape the brick actually delivers.
  * `interp_of_energy_contraction` — `hinterp` from a pure QUADRATIC-FORM contraction
    `E(QA) ≤ σ²‖dA‖²`, with no chain-map operator `S` and no coarse coboundary CLM.  Strictly more
    general than `Gamma1ChainMap.interp_energy_of_chain`, which is shown to imply it
    (`energy_contraction_of_chain`; LAW-19, that lemma is reused, not rebuilt).
  * **`schur_floor_on_printed_carrier`** — the composed statement.  For every `ell ≥ 2`, every tiled
    torus, every background `U` in the smallness class `α₁ ≤ 1/(186 ell³)`, every covariance datum
    `D` whose coarse carrier is `BondFnL2 L`, and every `B̃` in the printed carrier `ℓ²(Λ̃)`:

        ((1/σ²)·gammaBrick ell)·‖B̃‖²  ≤  ⟨C₀B̃, (QG₁Q*)⁻¹ C₀B̃⟩ − a‖C₀B̃‖²

    with `gammaBrick ell ≥ 1/(345960·ell⁶) > 0`, from exactly three carried inputs: the `(3.128)`
    split `hs`, curl-domination `hKcurl`, and the energy contraction `hcontract`.
    **NO FORM COMPARISON BETWEEN `Δ_j^{cov}` AND `D_U^*D_U` OCCURS ANYWHERE IN ITS DERIVATION**, so
    the adverse ordering `deltaJQuadFormCovFaithful_le_dstarDQuadForm` is not consumed and cannot
    block it.  The general-`U` brick enters through the `hpoin` slot, which is the slot
    `compute/gamma1_positive/` could previously fill only at `U = 1`
    (`Gamma1U1Poincare.lemma24_on_kerQ1`).

## WHAT THIS IS **NOT**

1. **It is not `γ₀ > 0`.**  `hcontract` is carried, not proved.  §4 records precisely what it says
   in the tree's own vocabulary and why it is not `stokes_flat` (wrong pair of levels).
2. **No simultaneous inhabitant of the concrete composition is exhibited**, and the reason is a
   FACT about the tree, stated in §1: the only constructed `BalabanCovarianceData`
   (`g1_datum.g1Data`) has coarse carrier `CoarseBondSpace L ell`, which is not `BondFnL2 L` in
   either index or fibre.  §5 carries the non-vacuity that IS available: the abstract composition on
   `Gamma1Reduction`'s §5 datum, and the brick leg's own curved-background non-vacuity (CITED from
   `TerminalCompose`, not rebuilt).
3. **ISLAND.**  Nothing here is installed in `formal/`; `FULL3D.main`'s axiom set is unchanged.
   `formal/` was not written by this lane (freeze verified before and after).
4. All scope of `terminal_compose`, `construct_cdc`, `covariant_lemma24` and `gamma1_positive` is
   inherited in full, including the corrected `ell⁻⁵` exponent and `Λ^c = ∅` on the torus carrier.
-/

namespace AdalyFormal.Balaban.SchurFloor

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1
open AdalyFormal.Balaban.Gamma1Positive
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.CStarDeltaKCOperator (dstarDCLM)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.TerminalCompose (gammaBrick gammaBrick_pos gammaBrick_lower
  cdc_floor_class_uniform)
open Matrix WithLp

variable {Hs Ks P₁ P₂ : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
  [NormedAddCommGroup Ks] [InnerProductSpace ℝ Ks]
  [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
  [NormedAddCommGroup P₂] [InnerProductSpace ℝ P₂]

/-! ## §2 — ROUTE (i): THE ALGEBRA IS SOUND, THE AVAILABLE DOMAIN IS NOT

The dispatch's route (i) reads: *if the covariant fine floor gives `⟨A,KopA⟩ ≥ γ_f‖A‖²` and
`‖Q‖ ≤ 1`, then `γ_f‖A‖² ≥ γ_f‖QA‖²`, so the Schur floor holds at the SAME constant.*

The first theorem proves that reasoning is correct.  Everything after it is about the premise. -/

/-- **ROUTE (i)'s ALGEBRA, PROVED SOUND.**  A fine-space floor plus a contraction `‖Q‖ ≤ 1` does give
the engine's right-hand condition `∀A, γ‖QA‖² ≤ ⟨A,KopA⟩` at the same constant.  Stated so that the
refutations below cannot be misread as an objection to this step. -/
theorem contraction_transfers_fine_floor (Q : Hs →L[ℝ] Ks) (hQ : ‖Q‖ ≤ 1) (Kop : Hs →L[ℝ] Hs)
    (γf : ℝ) (hγf : 0 ≤ γf) (hfine : ∀ A : Hs, γf * ‖A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ)) (A : Hs) :
    γf * ‖Q A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ) := by
  have hle : ‖Q A‖ ≤ ‖A‖ := by
    have h := Q.le_opNorm A
    nlinarith [h, hQ, norm_nonneg A, norm_nonneg (Q A)]
  have hsq : ‖Q A‖ ^ 2 ≤ ‖A‖ ^ 2 := by nlinarith [hle, norm_nonneg (Q A)]
  nlinarith [hfine A, hsq, hγf]

/-- **THE PREMISE IS FALSE AMBIENTLY FOR BAŁABAN'S OWN OPERATOR.**  `Kop = Δ_π + DRD*` annihilates
the constant lattice 1-forms, so no `γ_f > 0` fine floor `γ_f‖A‖² ≤ ⟨A,KopA⟩` exists at all.  This is
the `‖A‖`-measured analogue of `Gamma1Reduction.gamma_nonpos_of_null_vector`, and it is what forces
route (i) onto a RESTRICTED domain in the first place. -/
theorem no_fine_floor_of_null_vector (Kop : Hs →L[ℝ] Hs) (A₀ : Hs) (hne : A₀ ≠ 0)
    (hK0 : (inner ℝ A₀ (Kop A₀) : ℝ) ≤ 0) (γf : ℝ)
    (hfine : ∀ A : Hs, γf * ‖A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ)) : γf ≤ 0 := by
  have h := hfine A₀
  have hpos : 0 < ‖A₀‖ ^ 2 := by
    have : 0 < ‖A₀‖ := norm_pos_iff.mpr hne
    positivity
  nlinarith [h, hK0, hpos]

/-! ### §2b — THE READING-B WITNESS: a strictly positive floor on `ker Q` gives NOTHING

Reading B says the brick's floor lives on `Hs` and holds on `range C₀ ⊆ ker Q₁ = ker Q`.  The
objects below are `Gamma1Reduction` §5's, reused (LAW-19), with ONE change: the block average is
replaced by the block AVERAGE `Q(x,y,z) = ((x+y)/2, z)` rather than the block SUM, so that
`‖Q‖ ≤ 1` — the very hypothesis route (i) wants — is a THEOREM here and not an obstacle.  Every
object is a named definition; nothing is quantified existentially (S91). -/

/-- `Q(x,y,z) = ((x+y)/2, z)`: the block AVERAGE.  Normalised so that `‖Q‖ ≤ 1` holds. -/
@[reducible] noncomputable def sQ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  matCLM (!![(1/2 : ℝ), 1/2, 0; 0, 0, 1])

theorem sQ_norm_sq (A : EuclideanSpace ℝ (Fin 3)) :
    ‖sQ A‖ ^ 2
      = ((ofLp A 0 + ofLp A 1) / 2) ^ 2 + (ofLp A 2) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Fin.sum_univ_three]
  ring

theorem euclid3_norm_sq (A : EuclideanSpace ℝ (Fin 3)) :
    ‖A‖ ^ 2 = (ofLp A 0) ^ 2 + (ofLp A 1) ^ 2 + (ofLp A 2) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_three]
  ring

theorem wKop_form (A : EuclideanSpace ℝ (Fin 3)) :
    (inner ℝ A (wKop A) : ℝ)
      = (ofLp A 0 - ofLp A 1) ^ 2 + 4 * (ofLp A 2) ^ 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- **`‖Q‖ ≤ 1`** — route (i)'s contraction hypothesis, discharged as a theorem for `sQ`. -/
theorem sQ_opNorm_le_one : ‖sQ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => ?_
  have hl := sQ_norm_sq A
  have hr := euclid3_norm_sq A
  have hsq : ‖sQ A‖ ^ 2 ≤ (1 * ‖A‖) ^ 2 := by
    rw [one_mul, hl, hr]
    nlinarith [sq_nonneg (ofLp A 0 - ofLp A 1)]
  nlinarith [hsq, norm_nonneg (sQ A), norm_nonneg A]

/-- `Kop` is positive semidefinite: its form is `(x−y)² + 4z²`. -/
theorem wKop_psd (A : EuclideanSpace ℝ (Fin 3)) : (0 : ℝ) ≤ inner ℝ A (wKop A) := by
  rw [wKop_form]
  positivity

/-- **A STRICTLY POSITIVE FLOOR ON `ker Q`, WITH CONSTANT `2`.**  On `ker sQ = {(t,−t,0)}` the form
is `4t²` and `‖A‖² = 2t²`, so the floor holds with equality at `γ_f = 2`.  This is the strongest
possible form of Reading B's premise: not merely "a floor exists", but a floor with an explicit
positive constant, attained. -/
theorem wKop_floor_on_ker_sQ (A : EuclideanSpace ℝ (Fin 3)) (h : sQ A = 0) :
    (2 : ℝ) * ‖A‖ ^ 2 ≤ (inner ℝ A (wKop A) : ℝ) := by
  have h0 : ofLp (sQ A) 0 = (0 : ℝ) := by rw [h]; simp
  have h1 : ofLp (sQ A) 1 = (0 : ℝ) := by rw [h]; simp
  rw [matCLM_apply] at h0 h1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
  rw [euclid3_norm_sq, wKop_form]
  nlinarith [h0, h1]

/-- `sQ A₀ = (1,0)`, so `‖sQ A₀‖² = 1 ≠ 0`: the null vector of `Kop` is NOT in `ker sQ`. -/
theorem sQ_wA0_norm_sq : ‖sQ wA0‖ ^ 2 = 1 := by
  rw [sQ_norm_sq]
  simp [wA0, EuclideanSpace.equiv]

/-- **THE READING-B NO-GO.**  All of route (i)'s ingredients hold simultaneously — `‖Q‖ ≤ 1`, `Kop`
positive semidefinite, and a floor with strictly positive constant `2` on `ker Q` (which is where
`range C₀` sits under Reading B) — and the engine's condition still fails for EVERY `γ > 0`.

So under Reading B route (i) is not merely unproved: the brick's floor, read on the fine space and
on the domain the brick actually controls, **cannot** produce the Schur floor.  The reason is
visible in `sQ_wA0_norm_sq`: the condition `γ‖QA‖² ≤ ⟨A,KopA⟩` bites exactly where `QA ≠ 0`, which is
exactly where a `ker Q`-floor says nothing. -/
theorem reading_b_no_go :
    ‖sQ‖ ≤ 1
    ∧ (∀ A : EuclideanSpace ℝ (Fin 3), (0 : ℝ) ≤ inner ℝ A (wKop A))
    ∧ (∀ A : EuclideanSpace ℝ (Fin 3), sQ A = 0 → (2 : ℝ) * ‖A‖ ^ 2 ≤ inner ℝ A (wKop A))
    ∧ (∀ γ : ℝ, 0 < γ →
        ¬ (∀ A : EuclideanSpace ℝ (Fin 3), γ * ‖sQ A‖ ^ 2 ≤ (inner ℝ A (wKop A) : ℝ))) := by
  refine ⟨sQ_opNorm_le_one, wKop_psd, wKop_floor_on_ker_sQ, fun γ hγ hcontra => ?_⟩
  have h := hcontra wA0
  rw [sQ_wA0_norm_sq, w_kop_A0] at h
  linarith

/-- **CONTROL — the no-go is not an artefact of a trivial `ker Q`.**  `ker sQ` contains the nonzero
vector `(1,−1,0)` (`Gamma1Reduction`'s `wA1`), so `wKop_floor_on_ker_sQ` is a statement with content
and not a vacuous quantification over `{0}`. -/
theorem sQ_kernel_nontrivial : sQ wA1 = 0 ∧ wA1 ≠ (0 : EuclideanSpace ℝ (Fin 3)) := by
  refine ⟨?_, w_A1_ne_zero⟩
  apply WithLp.ofLp_injective 2
  rw [matCLM_apply]
  funext i
  fin_cases i <;>
    simp [wA1, Matrix.mulVec, dotProduct, Fin.sum_univ_three, EuclideanSpace.equiv]

/-- `Q₂ = 2·sQ`, i.e. `(x,y,z) ↦ (x+y, 2z)`: the SAME map with the contraction hypothesis broken. -/
@[reducible] noncomputable def sQ2 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  matCLM (!![(1 : ℝ), 1, 0; 0, 0, 2])

theorem sQ2_norm_sq (A : EuclideanSpace ℝ (Fin 3)) :
    ‖sQ2 A‖ ^ 2 = (ofLp A 0 + ofLp A 1) ^ 2 + (2 * ofLp A 2) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Fin.sum_univ_three]
  ring

theorem wA0_norm_sq : ‖wA0‖ ^ 2 = 2 := by
  rw [euclid3_norm_sq]
  simp [wA0, EuclideanSpace.equiv]
  norm_num

/-- **`‖Q‖ ≤ 1` IS LOAD-BEARING IN `contraction_transfers_fine_floor`, AS A NAMED REFUTATION.**

Mutation `S05` originally deleted `hQ` only from an `nlinarith` hint list, and the module still
compiled — because the hypothesis was still in the local context.  That was a defect in the
MUTATION, not in the theorem, and it is recorded rather than quietly re-rolled (`MUTATION_RESULTS`
carries the corrected row, which deletes the BINDER).  This theorem settles the question inside the
kernel instead of relying on a compile-or-not signal at all:

with `Q := sQ2` (which is `2·sQ`, so `‖Q‖ > 1`), `Kop := id` and `γ_f := 1`, the fine floor
`γ_f‖A‖² ≤ ⟨A,KopA⟩` holds with EQUALITY, and the conclusion
`∀A, γ_f‖QA‖² ≤ ⟨A,KopA⟩` is FALSE — refuted at `A₀ = (1,1,0)`, where `‖QA₀‖² = 4` and
`⟨A₀,A₀⟩ = 2`. -/
theorem contraction_needs_hQ :
    (∀ A : EuclideanSpace ℝ (Fin 3), (1 : ℝ) * ‖A‖ ^ 2
        ≤ (inner ℝ A ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))) A) : ℝ))
    ∧ ¬ (∀ A : EuclideanSpace ℝ (Fin 3), (1 : ℝ) * ‖sQ2 A‖ ^ 2
        ≤ (inner ℝ A ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))) A) : ℝ)) := by
  constructor
  · intro A
    simp only [ContinuousLinearMap.id_apply, one_mul]
    rw [real_inner_self_eq_norm_sq]
  · intro hcontra
    have h := hcontra wA0
    simp only [ContinuousLinearMap.id_apply, one_mul] at h
    rw [real_inner_self_eq_norm_sq, wA0_norm_sq, sQ2_norm_sq] at h
    simp [wA0, EuclideanSpace.equiv] at h
    norm_num at h

/-- **CONTROL — `contraction_transfers_fine_floor` is not vacuous.**  It fires on a named instance
with a strictly positive constant: `Q = sQ`, `Kop` the identity, `γ_f = 1`. -/
theorem contraction_transfers_fine_floor_fires (A : EuclideanSpace ℝ (Fin 3)) :
    (1 : ℝ) * ‖sQ A‖ ^ 2 ≤ (inner ℝ A ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))) A) : ℝ) := by
  refine contraction_transfers_fine_floor sQ sQ_opNorm_le_one _ 1 zero_le_one (fun B => ?_) A
  simp only [ContinuousLinearMap.id_apply, one_mul]
  rw [real_inner_self_eq_norm_sq]

/-! ## §3 — READING A: THE RE-WIRING THAT LANDS

Under Reading A the brick occupies the engine's `hpoin` slot.  Two adjustments are needed and both
WEAKEN hypotheses, so nothing is smuggled in. -/

/-- **THE COMPOSITION WITH `hpoin` WEAKENED.**  `Gamma1Reduction.gamma_floor_from_interp_and_poincare`
asks for `γP‖C₀w‖² ≤ E(C₀w)` and additionally carries `hC : ∀w, ‖w‖ ≤ ‖C₀w‖` and `hγP : 0 ≤ γP`.
This version asks only for `γP‖w‖² ≤ E(C₀w)` — implied by the other, since `‖w‖ ≤ ‖C₀w‖` — and
carries NEITHER `hC` NOR `hγP`.

**AND `C₀` IS A PLAIN `→ₗ[ℝ]`, NOT A `→L[ℝ]`.**  That is not cosmetic and it is not a preference:
`ConstructCDC.cZero U ell Dinv : TildeFn L ell →ₗ[ℝ] BondFnL2 L` is a LINEAR MAP, so
`Gamma1Reduction.gamma_floor_compressed_of_restricted` and
`Gamma1Reduction.gamma_floor_from_interp_and_poincare`, whose `C₀` slots are typed `W →L[ℝ] Ks`,
**cannot be instantiated at the tree's own `C₀` without a `LinearMap.toContinuousLinearMap`
wrapper**.  The `#check` at the end of this module records `cZero`'s type in the build log.
Continuity is never used in the proof, so the weakening costs nothing.  It is exactly the shape the brick delivers
(`cdc_floor_class_uniform` bounds `gammaBrick ell * ‖w‖²`, with the `Λ̃`-norm on the left). -/
theorem gamma_floor_of_interp_and_weakPoincare {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] (D : BalabanCovarianceData Hs Ks) (a γc γP : ℝ) (Kop : Hs →L[ℝ] Hs)
    (hs : IsAQuadSplit D a Kop) (C₀ : W →ₗ[ℝ] Ks) (E : Ks → ℝ) (hγc : 0 ≤ γc)
    (hinterp : ∀ w : W,
      γc * E (C₀ w) ≤ (inner ℝ (solutionOperator D (C₀ w)) (Kop (solutionOperator D (C₀ w))) : ℝ))
    (hpoin : ∀ w : W, γP * ‖w‖ ^ 2 ≤ E (C₀ w)) (w : W) :
    (γc * γP) * ‖w‖ ^ 2 ≤ deltaKQuadForm D a (C₀ w) := by
  rw [deltaKQuadForm_eq D a Kop hs (C₀ w)]
  refine le_trans ?_ (hinterp w)
  have h1 : γc * (γP * ‖w‖ ^ 2) ≤ γc * E (C₀ w) := mul_le_mul_of_nonneg_left (hpoin w) hγc
  calc (γc * γP) * ‖w‖ ^ 2 = γc * (γP * ‖w‖ ^ 2) := by ring
    _ ≤ γc * E (C₀ w) := h1

/-- **`hinterp` FROM A PURE QUADRATIC-FORM CONTRACTION.**  No chain-map operator `S`, no coarse
coboundary `d₁`, no CLM into a plaquette space: only the inequality
`E(QA) ≤ σ²‖dA‖²` — *the level-1 energy of the block average is at most `σ²` times the level-0
curl energy* — together with curl-domination of `Kop`.

Note the quantifier: `hcontract` is `∀ A : Hs`, but it is consumed at exactly ONE point,
`A := solutionOperator D B`, so the fact actually used is a bound over `range H₁` only.  (Same pivot
`compute/stokes_commu/` measures for its own chain hypothesis.) -/
theorem interp_of_energy_contraction (D : BalabanCovarianceData Hs Ks) (Kop : Hs →L[ℝ] Hs)
    (d : Hs →L[ℝ] P₁) (E : Ks → ℝ) (sigsq : ℝ) (hsig : 0 < sigsq)
    (hcontract : ∀ A : Hs, E (D.Q A) ≤ sigsq * ‖d A‖ ^ 2)
    (hKcurl : ∀ A : Hs, ‖d A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ)) (B : Ks) :
    (1 / sigsq) * E B
      ≤ (inner ℝ (solutionOperator D B) (Kop (solutionOperator D B)) : ℝ) := by
  have hQ : D.Q (solutionOperator D B) = B := interpolates D B
  have h1 : E B ≤ sigsq * ‖d (solutionOperator D B)‖ ^ 2 := by
    have := hcontract (solutionOperator D B)
    rwa [hQ] at this
  have h2 := hKcurl (solutionOperator D B)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hsig]
  nlinarith [h1, h2, hsig]

/-- **LAW-19 — THE CHAIN-MAP ROUTE IS SUBSUMED, NOT REBUILT.**
`Gamma1ChainMap.interp_energy_of_chain`'s hypotheses `(C)` `d₁ ∘ Q = S ∘ d` and `(N)` `‖S‖ ≤ σ`
IMPLY `interp_of_energy_contraction`'s `hcontract` at `E := fun B => ‖d₁ B‖²` and `σ² := σ^2`.  So
the quadratic-form hypothesis is strictly weaker, and every discharge of `(C)+(N)` is a discharge of
`hcontract`. -/
theorem energy_contraction_of_chain (D : BalabanCovarianceData Hs Ks) (d : Hs →L[ℝ] P₁)
    (d₁ : Ks →L[ℝ] P₂) (S : P₁ →L[ℝ] P₂) (σ : ℝ) (hσ : 0 ≤ σ)
    (hchain : ∀ A : Hs, d₁ (D.Q A) = S (d A)) (hS : ∀ f : P₁, ‖S f‖ ≤ σ * ‖f‖) (A : Hs) :
    ‖d₁ (D.Q A)‖ ^ 2 ≤ σ ^ 2 * ‖d A‖ ^ 2 := by
  rw [hchain A]
  have h := hS (d A)
  nlinarith [h, norm_nonneg (S (d A)), norm_nonneg (d A), hσ]

/-! ## §3b — NON-VACUITY OF THE ABSTRACT COMPOSITION

The printed-carrier instantiation lives in `SchurComposed.lean` (split off for a mechanical reason
recorded in `SCOPE.md` §5 item 5: the composed declaration is elaboration-expensive on the
`PiLp 2 (fun _ : Bond L => SuTwo)` carrier, and keeping it in its own module makes it iterable).
-/

/-- **THE WEAKENED COMPOSITION IS NON-VACUOUS, WITH A STRICTLY POSITIVE CONSTANT.**  On
`Gamma1Reduction` §5's datum, with `E(B) := B₁²` (defined independently of `Φ`), `γc = 4`, `γP = 1`:
the conclusion is `4‖w‖² ≤ Φ₁(C₀w)`, matching `witness_compressed_gamma_four`.  Note this uses the
WEAK `hpoin` (`γP‖w‖²`), so it exercises the hypothesis that was changed. -/
theorem weakPoincare_composition_instantiated (w : EuclideanSpace ℝ (Fin 1)) :
    ((4 : ℝ) * 1) * ‖w‖ ^ 2 ≤ deltaKQuadForm wData 1 (wC0 w) := by
  refine gamma_floor_of_interp_and_weakPoincare wData 1 4 1 wKop w_isAQuadSplit
    (wC0.toLinearMap) (fun B => (ofLp B 1) ^ 2) (by norm_num) ?_ ?_ w
  · intro v
    simp only [ContinuousLinearMap.coe_coe]
    have hkey := deltaKQuadForm_eq wData 1 wKop w_isAQuadSplit (wC0 v)
    have hval : deltaKQuadForm wData 1 (wC0 v) = 4 * (ofLp v 0) ^ 2 := by
      show (inner ℝ (wC0 v) (wCompInv (wC0 v)) : ℝ) - 1 * ‖wC0 v‖ ^ 2 = _
      rw [EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply, matCLM_apply,
        ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    have hE : (ofLp (wC0 v) 1) ^ 2 = (ofLp v 0) ^ 2 := by
      rw [matCLM_apply]
      simp [Matrix.mulVec, dotProduct]
    rw [← hkey, hval, hE]
  · intro v
    simp only [ContinuousLinearMap.coe_coe]
    have hE : (ofLp (wC0 v) 1) ^ 2 = (ofLp v 0) ^ 2 := by
      rw [matCLM_apply]
      simp [Matrix.mulVec, dotProduct]
    have hv : ‖v‖ ^ 2 = (ofLp v 0) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct]
      ring
    rw [hv, hE, one_mul]

#print axioms contraction_transfers_fine_floor
#print axioms no_fine_floor_of_null_vector
#print axioms sQ
#print axioms sQ_norm_sq
#print axioms euclid3_norm_sq
#print axioms wKop_form
#print axioms sQ_opNorm_le_one
#print axioms wKop_psd
#print axioms wKop_floor_on_ker_sQ
#print axioms sQ_wA0_norm_sq
#print axioms reading_b_no_go
#print axioms sQ_kernel_nontrivial
#print axioms sQ2
#print axioms sQ2_norm_sq
#print axioms wA0_norm_sq
#print axioms contraction_needs_hQ
#print axioms contraction_transfers_fine_floor_fires
#print axioms gamma_floor_of_interp_and_weakPoincare
#print axioms interp_of_energy_contraction
#print axioms energy_contraction_of_chain
#print axioms weakPoincare_composition_instantiated

-- MACHINE-CHECKED RECORD OF THE TYPE MISMATCH NAMED IN `gamma_floor_of_interp_and_weakPoincare`'s
-- docstring: the tree's own `C₀` is a LINEAR map, while the two upstream composition theorems in
-- `Gamma1Reduction` type their `C₀` slot as a CONTINUOUS linear map.
#check @AdalyFormal.Balaban.ConstructCDC.cZero
#check @AdalyFormal.Balaban.Gamma1Positive.gamma_floor_from_interp_and_poincare

end AdalyFormal.Balaban.SchurFloor
