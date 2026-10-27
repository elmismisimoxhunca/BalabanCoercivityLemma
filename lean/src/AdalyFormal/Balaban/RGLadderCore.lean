/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.Coercivity

set_option autoImplicit false

/-!
# `RGLadderCore` — what a FIXED-CARRIER, FIXED-`V` coercivity ladder forces on the RG maps

## What this file is

`Spine.coerc_u_main` asks for a `Balaban.CoercivityHypothesis H Uconfig` whose `Δ : ℕ → Uconfig →
H →L[ℝ] H` genuinely varies with the RG step `k` (`∃ U k₁ k₂, k₁ ≠ k₂ ∧ Δ k₁ U ≠ Δ k₂ U`), on a
**fixed** carrier `H = Balaban.Anchoring.AnchoredBondSpace Lat` and against a **fixed** subspace
`V = cohyp.V` with a **single** constant `γ''`.

This file proves the elementary but decisive constraint that shape imposes: **coercivity on `V`
with a positive constant forces every factorization of `Δ k U` to be INJECTIVE ON `V`.** A
renormalization-group step is a coarsening — a map that identifies distinct fine configurations —
so this is exactly the property an RG map does not have.

Nothing here is about `Bałaban`'s mathematics being wrong. Bałaban states his coercivity at each
scale on THAT scale's own space, whose dimension shrinks with `k`; there is no fixed `V`. The
constraint below is on the ENCODING: a single `V : Submodule ℝ H` shared by all `k`.

## The statements, in order

* `eq_zero_of_coercive_of_apply_eq_zero` — `v ∈ V`, `Δ v = 0`, `0 < γ`, `γ‖·‖² ≤ ⟪·, Δ ·⟫` on `V`
  ⟹ `v = 0`. (The whole file is downstream of this two-line fact.)
* `not_coercive_of_mem_ker` — the contrapositive, as a refutation tool.
* `factor_injOn_of_coercive` — if `Δ = A ∘ B` then `B` is injective on `V`.
* `finrank_le_of_coercive_factor` — hence `finrank V ≤ finrank W` for the intermediate space `W`.
* `CoercivityHypothesis.factor_injOn` / `CoercivityHypothesis.finrank_V_le_of_factor` — the same
  two facts stated directly against the structure `Spine.coerc_u_main` must inhabit, so they apply
  to the campaign's real target and not to an analogue.
* `no_uniform_ladder_of_one_small_rung` — the ladder form: ONE rung whose intermediate space is
  smaller than `V` refutes the whole family. Uniformity in `k` is not needed as a hypothesis; a
  single `k` does it, which is why this is a statement about the encoding rather than about the
  constant.

## Controls shipped in this file (§4)

* **must-not-fire (non-vacuity):** `coercive_factor_exists_witness` — a concrete `Δ`, `V ≠ ⊥`,
  `γ > 0` and factorization satisfying every hypothesis of `finrank_le_of_coercive_factor`, so the
  hypotheses are not contradictory and the conclusion is not vacuously reached.
* **must-fire:** `not_coercive_of_mem_ker_fires` — a concrete operator with a nonzero kernel vector
  inside `V`, for which the coercivity hypothesis is therefore PROVABLY unsatisfiable for every
  `γ > 0`. If the refutation tool could not fire, this theorem would not be provable.
* **degenerate points:** `bot_coercive_trivially` records that the constraint is empty when
  `V = ⊥` (which `CoercivityHypothesis.V_ne_bot` excludes) and `zero_gamma_no_constraint` records
  that it is empty when `γ = 0` (which `γ''_pos` excludes) — i.e. both structure fields are
  load-bearing for this file's conclusions, and neither is decorative.
-/

namespace AdalyFormal.Balaban.RGLadderCore

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-! ## §1 — the kernel fact -/

/-- **The load-bearing two-liner.** If `Δ` is coercive on `V` with a strictly positive constant,
then `Δ` annihilates no nonzero vector of `V`. -/
theorem eq_zero_of_coercive_of_apply_eq_zero (Δ : H →L[ℝ] H) (V : Submodule ℝ H) (γ : ℝ)
    (hγ : 0 < γ) (hc : ∀ v ∈ V, γ * ‖v‖ ^ 2 ≤ (inner ℝ v (Δ v) : ℝ))
    {v : H} (hv : v ∈ V) (h0 : Δ v = 0) : v = 0 := by
  have hle : γ * ‖v‖ ^ 2 ≤ 0 := by
    have := hc v hv
    rwa [h0, inner_zero_right] at this
  have hnn : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  have : ‖v‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  exact norm_eq_zero.mp this

/-- **The refutation form.** A nonzero vector of `V` in `ker Δ` refutes coercivity on `V` for
EVERY positive constant. -/
theorem not_coercive_of_mem_ker (Δ : H →L[ℝ] H) (V : Submodule ℝ H)
    {v : H} (hv : v ∈ V) (hvne : v ≠ 0) (h0 : Δ v = 0) :
    ¬ ∃ γ : ℝ, 0 < γ ∧ ∀ w ∈ V, γ * ‖w‖ ^ 2 ≤ (inner ℝ w (Δ w) : ℝ) := by
  rintro ⟨γ, hγ, hc⟩
  exact hvne (eq_zero_of_coercive_of_apply_eq_zero Δ V γ hγ hc hv h0)

/-! ## §2 — factorizations: what coercivity forces on the RG map -/

/-- **A factored operator inherits the factor's kernel.** -/
theorem apply_eq_zero_of_factor (A : W →L[ℝ] H) (B : H →L[ℝ] W) {v : H} (h : B v = 0) :
    (A.comp B) v = 0 := by
  simp [ContinuousLinearMap.comp_apply, h]

/-- **THE CONSTRAINT.** If `Δ` factors through `W` as `A ∘ B` and is coercive on `V` with a
positive constant, then `B` is INJECTIVE ON `V`.

An RG step is a coarsening: it identifies distinct fine configurations. This says a fixed-`V`
coercivity ladder forbids that at every rung. -/
theorem factor_injOn_of_coercive (A : W →L[ℝ] H) (B : H →L[ℝ] W) (V : Submodule ℝ H) (γ : ℝ)
    (hγ : 0 < γ) (hc : ∀ v ∈ V, γ * ‖v‖ ^ 2 ≤ (inner ℝ v ((A.comp B) v) : ℝ))
    {v : H} (hv : v ∈ V) (h0 : B v = 0) : v = 0 :=
  eq_zero_of_coercive_of_apply_eq_zero (A.comp B) V γ hγ hc hv (apply_eq_zero_of_factor A B h0)

/-- The same statement packaged as injectivity of `B` restricted to `V`. -/
theorem factor_injective_on_subtype (A : W →L[ℝ] H) (B : H →L[ℝ] W) (V : Submodule ℝ H) (γ : ℝ)
    (hγ : 0 < γ) (hc : ∀ v ∈ V, γ * ‖v‖ ^ 2 ≤ (inner ℝ v ((A.comp B) v) : ℝ)) :
    Function.Injective ((B : H →ₗ[ℝ] W).comp V.subtype) := by
  rw [← LinearMap.ker_eq_bot]
  rw [LinearMap.ker_eq_bot']
  rintro ⟨v, hv⟩ h
  have hBv : B v = 0 := h
  have := factor_injOn_of_coercive A B V γ hγ hc hv hBv
  exact Subtype.ext this

/-- **Rank consequence.** `finrank V ≤ finrank W`: the fixed subspace must FIT INSIDE the
intermediate (coarse) space of every factorization. -/
theorem finrank_le_of_coercive_factor [FiniteDimensional ℝ H] [FiniteDimensional ℝ W]
    (A : W →L[ℝ] H) (B : H →L[ℝ] W) (V : Submodule ℝ H) (γ : ℝ)
    (hγ : 0 < γ) (hc : ∀ v ∈ V, γ * ‖v‖ ^ 2 ≤ (inner ℝ v ((A.comp B) v) : ℝ)) :
    Module.finrank ℝ V ≤ Module.finrank ℝ W :=
  LinearMap.finrank_le_finrank_of_injective (f := (B : H →ₗ[ℝ] W).comp V.subtype)
    (factor_injective_on_subtype A B V γ hγ hc)

/-! ## §3 — stated directly against `Balaban.CoercivityHypothesis`

These are the forms that bear on `Spine.coerc_u_main`: they take the actual structure, not an
analogue of it, so no transport step can be disputed. -/

variable {Uconfig : Type*} [Nontrivial Uconfig]

/-- **Every rung of a `CoercivityHypothesis` ladder is injective on `V`.** For each `k` and `U`,
any factorization `Δ k U = A ∘ B` has `B` injective on `cohyp.V`. -/
theorem CoercivityHypothesis.factor_injOn (cohyp : Balaban.CoercivityHypothesis H Uconfig)
    (k : ℕ) (U : Uconfig) (A : W →L[ℝ] H) (B : H →L[ℝ] W)
    (hfac : cohyp.Δ k U = A.comp B) {v : H} (hv : v ∈ cohyp.V) (h0 : B v = 0) : v = 0 := by
  refine factor_injOn_of_coercive A B cohyp.V cohyp.γ'' cohyp.γ''_pos ?_ hv h0
  intro w hw
  have := cohyp.coercive k U w hw
  rwa [hfac] at this

/-- **`finrank cohyp.V ≤ finrank W` at every rung.** -/
theorem CoercivityHypothesis.finrank_V_le_of_factor [FiniteDimensional ℝ H]
    [FiniteDimensional ℝ W] (cohyp : Balaban.CoercivityHypothesis H Uconfig)
    (k : ℕ) (U : Uconfig) (A : W →L[ℝ] H) (B : H →L[ℝ] W)
    (hfac : cohyp.Δ k U = A.comp B) :
    Module.finrank ℝ cohyp.V ≤ Module.finrank ℝ W := by
  refine finrank_le_of_coercive_factor A B cohyp.V cohyp.γ'' cohyp.γ''_pos ?_
  intro w hw
  have := cohyp.coercive k U w hw
  rwa [hfac] at this

/-- **ONE bad rung refutes the whole ladder.** If at a single scale `k₀` the operator kills a
nonzero vector of `V`, no `CoercivityHypothesis` with that `Δ` and that `V` exists — irrespective
of how well-behaved every other rung is. This is why the obstruction is about the ENCODING (one
`V` for all `k`) rather than about the SIZE of the constant. -/
theorem no_uniform_ladder_of_one_small_rung (cohyp : Balaban.CoercivityHypothesis H Uconfig)
    (k₀ : ℕ) (U₀ : Uconfig) {v : H} (hv : v ∈ cohyp.V) (hvne : v ≠ 0)
    (h0 : cohyp.Δ k₀ U₀ v = 0) : False :=
  hvne (eq_zero_of_coercive_of_apply_eq_zero (cohyp.Δ k₀ U₀) cohyp.V cohyp.γ'' cohyp.γ''_pos
    (cohyp.coercive k₀ U₀) hv h0)

/-- **Ladder form with an explicit factorization at one scale.** -/
theorem no_uniform_ladder_of_one_coarsening_rung (cohyp : Balaban.CoercivityHypothesis H Uconfig)
    (k₀ : ℕ) (U₀ : Uconfig) (A : W →L[ℝ] H) (B : H →L[ℝ] W)
    (hfac : cohyp.Δ k₀ U₀ = A.comp B) {v : H} (hv : v ∈ cohyp.V) (hvne : v ≠ 0)
    (h0 : B v = 0) : False :=
  hvne (CoercivityHypothesis.factor_injOn cohyp k₀ U₀ A B hfac hv h0)

/-! ## §4 — controls, both directions -/

/-- **must-not-fire (non-vacuity).** The hypothesis set of `finrank_le_of_coercive_factor` is
consistent: here is a `V ≠ ⊥`, a `γ > 0`, and a factorization satisfying it. So the results above
are not reached by contradictory premises. -/
theorem coercive_factor_exists_witness :
    ∃ (V : Submodule ℝ ℝ) (γ : ℝ) (A B : ℝ →L[ℝ] ℝ),
      V ≠ ⊥ ∧ 0 < γ ∧ ∀ v ∈ V, γ * ‖v‖ ^ 2 ≤ (inner ℝ v ((A.comp B) v) : ℝ) := by
  refine ⟨⊤, 1, ContinuousLinearMap.id ℝ ℝ, ContinuousLinearMap.id ℝ ℝ, top_ne_bot, one_pos, ?_⟩
  intro v _
  simp

/-- **must-fire.** A concrete instance where the refutation tool actually refutes: the zero operator
kills `1 ∈ ⊤`, so no positive constant makes it coercive there. If `not_coercive_of_mem_ker` could
not fire, this theorem would not be provable. -/
theorem not_coercive_of_mem_ker_fires :
    ¬ ∃ γ : ℝ, 0 < γ ∧ ∀ w ∈ (⊤ : Submodule ℝ ℝ),
        γ * ‖w‖ ^ 2 ≤ (inner ℝ w ((0 : ℝ →L[ℝ] ℝ) w) : ℝ) :=
  not_coercive_of_mem_ker (0 : ℝ →L[ℝ] ℝ) ⊤ (v := (1 : ℝ)) Submodule.mem_top one_ne_zero (by simp)

/-- **Degenerate `V = ⊥`: the constraint is EMPTY.** Every operator is "coercive" on `⊥` with every
constant, so `Balaban.CoercivityHypothesis.V_ne_bot` is load-bearing for everything above — it is
not a decorative field. -/
theorem bot_coercive_trivially (Δ : H →L[ℝ] H) (γ : ℝ) :
    ∀ v ∈ (⊥ : Submodule ℝ H), γ * ‖v‖ ^ 2 ≤ (inner ℝ v (Δ v) : ℝ) := by
  intro v hv
  rw [Submodule.mem_bot] at hv
  subst hv
  simp

/-- **Degenerate `γ = 0`: the constraint is EMPTY.** The zero operator satisfies the bound on every
subspace with `γ = 0`, so `Balaban.CoercivityHypothesis.γ''_pos` is likewise load-bearing. -/
theorem zero_gamma_no_constraint (V : Submodule ℝ H) :
    ∀ v ∈ V, (0 : ℝ) * ‖v‖ ^ 2 ≤ (inner ℝ v ((0 : H →L[ℝ] H) v) : ℝ) := by
  intro v _
  simp

#print axioms apply_eq_zero_of_factor
#print axioms eq_zero_of_coercive_of_apply_eq_zero
#print axioms not_coercive_of_mem_ker
#print axioms factor_injOn_of_coercive
#print axioms factor_injective_on_subtype
#print axioms finrank_le_of_coercive_factor
#print axioms CoercivityHypothesis.factor_injOn
#print axioms CoercivityHypothesis.finrank_V_le_of_factor
#print axioms no_uniform_ladder_of_one_small_rung
#print axioms no_uniform_ladder_of_one_coarsening_rung
#print axioms coercive_factor_exists_witness
#print axioms not_coercive_of_mem_ker_fires
#print axioms bot_coercive_trivially
#print axioms zero_gamma_no_constraint

end AdalyFormal.Balaban.RGLadderCore
