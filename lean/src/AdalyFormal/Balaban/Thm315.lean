/-
# CMP99b pp.431–432: (3.185), (3.186), and the statement of Theorem 3.15.

LANE `compute/thm315_core/`.  Write scope: `compute/thm315_core/` only.  Imports Mathlib only.
Compiled with `compile.sh` (hardlink shadow + absolute `LEAN_PATH`); never `lake build`.

## Source

p.432 was image-verified at 400 dpi by the sibling lane `compute/p429_pivot/`
(`compute/p429_pivot/renders/CMP99b_p432-44.png`,
sha256 `8a93bdc77d8b8604fbb9871cd2de7595a1c1629ed34217713f19830a7af133d9`), and that lane's
verbatim transcription is reproduced in `compute/p429_pivot/FINDINGS.md`:

> "Let us denote a covariance operator of the Gaussian integral in (3.183) by `G̃₂`, then we
> obtain
>   `C^(k)(Λ) = (I + D̄μ) Q G̃₂ Q* (I + μ*D̄*).`                       (3.185)
> It is the formula we are looking for. The operator `G̃₂` can be related in a simple way to the
> operator `G₂` defined by the Gaussian integral (3.183), but with the `δ`-function `δ(Q̃A)`
> replaced by `exp[-½⟨Q̃A, aQ̃A⟩]`. We have
>   `G̃₂ = G₂ - G₂Q̃*(Q̃G₂Q̃*)⁻¹Q̃G₂.`                                  (3.186)
> The operator `G₂` differs from `G₁` only by the small and regular operators connected with the
> second term in the exponential in (3.183), and with terms containing `Dλ̃(A)`. Thus we can
> investigate the operator `G₂` perturbatively in the same way as the operator `G₁` in (3.138).
> ... This way we can express `C^(k)(Λ)` in terms of the operators of the type `G'`,
> `(Q'G'²Q'*)⁻¹`, `G`, `(QGQ*)⁻¹`. Expanding these into random walks we get a random walk
> expansion of `C^(k)(Λ)`. The formula (3.185) implies immediately bounds and an exponential
> decay. Thus we get
>
> **Theorem 3.15.** For `Mα₀` sufficiently small the propagator `C^(k)(Λ)` is given by the
> formula (3.185), and satisfies the bound
>   `|C^(k)(Λ; y, y')| ≦ B₀ e^{-δ₀|y-y'|},   y, y' ∈ Λ`             (3.187)
> with the constants `B₀, δ₀` depending on `d` and `L` only. This propagator has a convergent
> random walk expansion of the type described previously. Of course we have all the other
> consequences following from the random walk expansion."

## Carriers

`𝔄` = fine-lattice bond fields (`A`);  `𝔅` = unit-lattice bond fields (`B`, and `C^(k)(Λ)`
acts here);  `𝔅t` = the bond fields of the EXTENDED sequence, the target of `Q̃`.
`Q : 𝔄 → 𝔅`, `Qs = Q* : 𝔅 → 𝔄`;  `Db = D̄ : 𝔖' → 𝔅` and `mumap = μ(·) : 𝔅 → 𝔖'` are the objects
of CMP99b (3.169) (see `MuStep.lean`), with `Dbs = D̄*`, `mus = μ*`.
`G2t = G̃₂ : 𝔄 → 𝔄`, `G2 = G₂ : 𝔄 → 𝔄`, `Qt = Q̃ : 𝔄 → 𝔅t`.

Adjoints are supplied as SEPARATE operators together with their defining pairing identity, so
that CMP99b's printed left and right factors are represented literally and no completeness
hypothesis is needed.

## What is PROVED

* `printed_factors_are_adjoint` — CMP99b's printed RIGHT factor `Q*(I + μ*D̄*)` of (3.185) IS
  the adjoint of its printed LEFT factor `(I + D̄μ)Q`.  So (3.185) is a symmetric sandwich
  `T G̃₂ T*`.  This is a faithfulness check ON THE PRINTED DISPLAY.
* `sandwich_form` — the quadratic form of (3.185): `⟨B, C B⟩ = ⟨T*B, G̃₂ (T*B)⟩`.
* `sandwich_psd` — hence `C^(k)(Λ)` is positive semidefinite whenever `G̃₂` is.
* `sandwich_form_le` — hence a form bound on `G̃₂` plus a bound on `‖T*‖` gives a form bound on
  `C^(k)(Λ)`.  **No exponential decay is used.**
* `Qt_comp_G2tilde_eq_zero` — (3.186) does what the `δ(Q̃A)` of (3.183) demands: `Q̃ G̃₂ = 0`.
* `G2tilde_form_le_G2_form` — (3.186) is a Schur complement: `⟨A, G̃₂ A⟩ ≤ ⟨A, G₂ A⟩`.
* `G2tilde_psd` — `G̃₂ ≥ 0` when `G₂ ≥ 0` and the middle inverse is bounded above by the form
  of `G₂` on the relevant vectors (see the statement for the exact hypothesis).
* `Thm315Uniform` — Theorem 3.15's conclusion (3.187) in the shape the constants demand:
  `B₀, δ₀` quantified OUTSIDE the setup `s = (k, Λ, U)`.
* `thm315_uniform_not_free` / `thm315_uniform_satisfiable` — a must-fire and a must-not-fire
  control on that shape.  The must-fire control is the point: the tree's standing gate
  `AdalyFormal.Assumptions.finite_domain_decay_conclusion_is_free` shows that a decay
  conclusion on a FIXED finite domain is free; `thm315_uniform_not_free` exhibits a family for
  which the UNIFORM statement is FALSE, so the shape used here is not free.

## What is DEFERRED, and named

Nothing in this file proves Theorem 3.15.  The two CMP99b steps that the theorem's one-line
proof rests on are recorded as `def : Prop` (no `sorry` anywhere in this lane):
`G2PerturbativeControl` and `RandomWalkExpansionAvailable`.
-/
import Mathlib

open scoped InnerProductSpace RealInnerProductSpace

namespace Thm315Core

/-! ## Part 1 — CMP99b (3.185). -/

section Sandwich

variable {𝔄 𝔅 𝔖' : Type*}
  [NormedAddCommGroup 𝔄] [InnerProductSpace ℝ 𝔄]
  [NormedAddCommGroup 𝔅] [InnerProductSpace ℝ 𝔅]
  [NormedAddCommGroup 𝔖'] [InnerProductSpace ℝ 𝔖']

variable (Q : 𝔄 →L[ℝ] 𝔅) (Qs : 𝔅 →L[ℝ] 𝔄)
  (Db : 𝔖' →L[ℝ] 𝔅) (Dbs : 𝔅 →L[ℝ] 𝔖')
  (mumap : 𝔅 →L[ℝ] 𝔖') (mus : 𝔖' →L[ℝ] 𝔅)

/-- CMP99b (3.185)'s printed LEFT factor `(I + D̄μ)Q : 𝔄 → 𝔅`. -/
noncomputable def leftFactor : 𝔄 →L[ℝ] 𝔅 :=
  (ContinuousLinearMap.id ℝ 𝔅 + Db ∘L mumap) ∘L Q

/-- CMP99b (3.185)'s printed RIGHT factor `Q*(I + μ*D̄*) : 𝔅 → 𝔄`. -/
noncomputable def rightFactor : 𝔅 →L[ℝ] 𝔄 :=
  Qs ∘L (ContinuousLinearMap.id ℝ 𝔅 + mus ∘L Dbs)

/-- **The printed right factor of (3.185) is the adjoint of the printed left factor.**

Proved from the three constituent adjoint relations only (`Qs = Q*`, `Dbs = D̄*`, `mus = μ*`);
no completeness and no Mathlib adjoint machinery is used.  Consequence: (3.185) exhibits
`C^(k)(Λ)` as a SYMMETRIC sandwich `T G̃₂ T*`, which is what makes "the formula (3.185) implies
immediately bounds" (p.432) an operator-theoretic statement rather than a kernel estimate. -/
theorem printed_factors_are_adjoint
    (hQ : ∀ (A : 𝔄) (B : 𝔅), ⟪Qs B, A⟫_ℝ = ⟪B, Q A⟫_ℝ)
    (hDb : ∀ (m : 𝔖') (B : 𝔅), ⟪Dbs B, m⟫_ℝ = ⟪B, Db m⟫_ℝ)
    (hmu : ∀ (m : 𝔖') (B : 𝔅), ⟪mus m, B⟫_ℝ = ⟪m, mumap B⟫_ℝ)
    (A : 𝔄) (B : 𝔅) :
    ⟪rightFactor Qs Dbs mus B, A⟫_ℝ = ⟪B, leftFactor Q Db mumap A⟫_ℝ := by
  show ⟪Qs (B + mus (Dbs B)), A⟫_ℝ = ⟪B, Q A + Db (mumap (Q A))⟫_ℝ
  rw [hQ, inner_add_left, inner_add_right]
  congr 1
  rw [hmu (Dbs B) (Q A)]
  exact hDb (mumap (Q A)) B

/-- The quadratic form of CMP99b (3.185).  `C` is the operator the paper calls `C^(k)(Λ)`;
`hC` is (3.185) itself, in the form `C = (I + D̄μ)Q ∘ G̃₂ ∘ Q*(I + μ*D̄*)`. -/
theorem sandwich_form (G2t : 𝔄 →L[ℝ] 𝔄) (C : 𝔅 →L[ℝ] 𝔅)
    (hC : C = leftFactor Q Db mumap ∘L G2t ∘L rightFactor Qs Dbs mus)
    (hadj : ∀ (A : 𝔄) (B : 𝔅),
      ⟪rightFactor Qs Dbs mus B, A⟫_ℝ = ⟪B, leftFactor Q Db mumap A⟫_ℝ)
    (B : 𝔅) :
    ⟪B, C B⟫_ℝ = ⟪rightFactor Qs Dbs mus B, G2t (rightFactor Qs Dbs mus B)⟫_ℝ := by
  rw [hC]
  show ⟪B, leftFactor Q Db mumap (G2t (rightFactor Qs Dbs mus B))⟫_ℝ = _
  rw [← hadj (G2t (rightFactor Qs Dbs mus B)) B]

/-- **(3.185) ⟹ `C^(k)(Λ) ≥ 0` whenever `G̃₂ ≥ 0`.** -/
theorem sandwich_psd (G2t : 𝔄 →L[ℝ] 𝔄) (C : 𝔅 →L[ℝ] 𝔅)
    (hC : C = leftFactor Q Db mumap ∘L G2t ∘L rightFactor Qs Dbs mus)
    (hadj : ∀ (A : 𝔄) (B : 𝔅),
      ⟪rightFactor Qs Dbs mus B, A⟫_ℝ = ⟪B, leftFactor Q Db mumap A⟫_ℝ)
    (hG : ∀ A : 𝔄, 0 ≤ ⟪A, G2t A⟫_ℝ) (B : 𝔅) :
    0 ≤ ⟪B, C B⟫_ℝ := by
  rw [sandwich_form Q Qs Db Dbs mumap mus G2t C hC hadj B]
  exact hG _

/-- **(3.185) + a form bound on `G̃₂` + boundedness of the right factor ⟹ a form bound on
`C^(k)(Λ)`.**

This is the route to `γ₀` that does NOT pass through the exponential decay (3.187): it needs
only that `G̃₂` is bounded as a quadratic form and that `Q*(I + μ*D̄*)` is a bounded operator. -/
theorem sandwich_form_le (G2t : 𝔄 →L[ℝ] 𝔄) (C : 𝔅 →L[ℝ] 𝔅)
    (hC : C = leftFactor Q Db mumap ∘L G2t ∘L rightFactor Qs Dbs mus)
    (hadj : ∀ (A : 𝔄) (B : 𝔅),
      ⟪rightFactor Qs Dbs mus B, A⟫_ℝ = ⟪B, leftFactor Q Db mumap A⟫_ℝ)
    (γG : ℝ) (hγG : 0 ≤ γG) (hG : ∀ A : 𝔄, ⟪A, G2t A⟫_ℝ ≤ γG * ‖A‖ ^ 2)
    (κ : ℝ) (hκ : 0 ≤ κ) (hT : ∀ B : 𝔅, ‖rightFactor Qs Dbs mus B‖ ≤ κ * ‖B‖)
    (B : 𝔅) :
    ⟪B, C B⟫_ℝ ≤ (γG * κ ^ 2) * ‖B‖ ^ 2 := by
  rw [sandwich_form Q Qs Db Dbs mumap mus G2t C hC hadj B]
  have h1 := hG (rightFactor Qs Dbs mus B)
  have h2 := hT B
  have h3 : ‖rightFactor Qs Dbs mus B‖ ^ 2 ≤ (κ * ‖B‖) ^ 2 := by
    have := norm_nonneg (rightFactor Qs Dbs mus B)
    nlinarith [h2, this]
  nlinarith [h1, h3, hγG, sq_nonneg ‖B‖]

end Sandwich

/-! ## Part 2 — CMP99b (3.186), the Schur complement. -/

section Schur

variable {𝔄 𝔅t : Type*}
  [NormedAddCommGroup 𝔄] [InnerProductSpace ℝ 𝔄]
  [NormedAddCommGroup 𝔅t] [InnerProductSpace ℝ 𝔅t]

variable (G2 : 𝔄 →L[ℝ] 𝔄) (Qt : 𝔄 →L[ℝ] 𝔅t) (Qts : 𝔅t →L[ℝ] 𝔄) (Kt : 𝔅t →L[ℝ] 𝔅t)

/-- **CMP99b (3.186):** `G̃₂ = G₂ - G₂Q̃*(Q̃G₂Q̃*)⁻¹Q̃G₂`, with `Kt = (Q̃G₂Q̃*)⁻¹`. -/
noncomputable def G2tilde : 𝔄 →L[ℝ] 𝔄 :=
  G2 - G2 ∘L Qts ∘L Kt ∘L Qt ∘L G2

@[simp] theorem G2tilde_apply (A : 𝔄) :
    G2tilde G2 Qt Qts Kt A = G2 A - G2 (Qts (Kt (Qt (G2 A)))) := by
  simp [G2tilde]

/-- **(3.186) implements the constraint `δ(Q̃A)` of (3.183):** `Q̃ G̃₂ = 0`.

This is the check that CMP99b's printed formula does what it is introduced to do — pass from
the `a`-regularised `G₂` back to the `δ`-function-constrained `G̃₂`.  Uses only that `Kt` is a
right inverse of `Q̃G₂Q̃*`. -/
theorem Qt_comp_G2tilde_eq_zero
    (hK : ∀ f : 𝔅t, Qt (G2 (Qts (Kt f))) = f) (A : 𝔄) :
    Qt (G2tilde G2 Qt Qts Kt A) = 0 := by
  rw [G2tilde_apply, map_sub, hK (Qt (G2 A)), sub_self]

/-- **(3.186) is a Schur complement:** `⟨A, G̃₂ A⟩ ≤ ⟨A, G₂ A⟩`.

Hypotheses: `G₂` is self-adjoint (`hsa`), `Q̃*` is the adjoint of `Q̃` (`hQadj`), and the middle
operator `(Q̃G₂Q̃*)⁻¹` is positive semidefinite (`hKpos`).  The last is exactly the
positive-definiteness CMP99b's Theorem 3.11 (p.416) supplies qualitatively for operators of
this type. -/
theorem G2tilde_form_le_G2_form
    (hsa : ∀ x y : 𝔄, ⟪G2 x, y⟫_ℝ = ⟪x, G2 y⟫_ℝ)
    (hQadj : ∀ (x : 𝔄) (f : 𝔅t), ⟪Qts f, x⟫_ℝ = ⟪f, Qt x⟫_ℝ)
    (hKpos : ∀ f : 𝔅t, 0 ≤ ⟪f, Kt f⟫_ℝ) (A : 𝔄) :
    ⟪A, G2tilde G2 Qt Qts Kt A⟫_ℝ ≤ ⟪A, G2 A⟫_ℝ := by
  have hsub : ⟪A, G2 (Qts (Kt (Qt (G2 A))))⟫_ℝ = ⟪Qt (G2 A), Kt (Qt (G2 A))⟫_ℝ := by
    rw [← hsa A (Qts (Kt (Qt (G2 A)))), real_inner_comm, hQadj (G2 A) (Kt (Qt (G2 A))),
      real_inner_comm]
  have hnn : 0 ≤ ⟪A, G2 (Qts (Kt (Qt (G2 A))))⟫_ℝ := by
    rw [hsub]; exact hKpos _
  rw [G2tilde_apply, inner_sub_right]
  linarith

/-- **`G̃₂ ≥ 0`.**  With `G₂ ≥ 0` and `Q̃*` the adjoint of `Q̃`, positivity of `G̃₂` is exactly the
statement that the subtracted Schur term never exceeds `⟨A, G₂A⟩`. -/
theorem G2tilde_psd
    (hdom : ∀ A : 𝔄, ⟪Qt (G2 A), Kt (Qt (G2 A))⟫_ℝ ≤ ⟪A, G2 A⟫_ℝ)
    (hsa : ∀ x y : 𝔄, ⟪G2 x, y⟫_ℝ = ⟪x, G2 y⟫_ℝ)
    (hQadj : ∀ (x : 𝔄) (f : 𝔅t), ⟪Qts f, x⟫_ℝ = ⟪f, Qt x⟫_ℝ) (A : 𝔄) :
    0 ≤ ⟪A, G2tilde G2 Qt Qts Kt A⟫_ℝ := by
  have hsub : ⟪A, G2 (Qts (Kt (Qt (G2 A))))⟫_ℝ = ⟪Qt (G2 A), Kt (Qt (G2 A))⟫_ℝ := by
    rw [← hsa A (Qts (Kt (Qt (G2 A)))), real_inner_comm, hQadj (G2 A) (Kt (Qt (G2 A))),
      real_inner_comm]
  rw [G2tilde_apply, inner_sub_right, hsub]
  linarith [hdom A]

end Schur

/-! ## Part 3 — the deferred CMP99b steps, named as `Prop`s (never `sorry`). -/

/-- **NAMED DEFERRAL `[P429-G2-PERTURBATIVE]`.**  CMP99b p.432: "The operator `G₂` differs from
`G₁` only by the small and regular operators ... Thus we can investigate the operator `G₂`
perturbatively in the same way as the operator `G₁` in (3.138)."  The analysis is asserted by
method-transfer and is not carried out in the paper.  Formally: `G₂` admits a bound of the
`G₁` type with constants depending on `d` and `L` only. -/
def G2PerturbativeControl (Setup : Type*) (bound : Setup → ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ s : Setup, bound s ≤ γ

/-- **NAMED DEFERRAL `[P429-RANDOM-WALK]`.**  CMP99b p.432: "Expanding these into random walks
we get a random walk expansion of `C^(k)(Λ)`."  The random-walk/polymer apparatus is not
formalised anywhere in this campaign's tree. -/
def RandomWalkExpansionAvailable (Setup : Type*) (Decay : Setup → Prop) : Prop :=
  ∀ s : Setup, Decay s

/-! ## Part 4 — Theorem 3.15's conclusion (3.187), in a shape whose constants have content. -/

/-- **CMP99b Theorem 3.15, conclusion (3.187)**:
`|C^(k)(Λ; y, y')| ≦ B₀ e^{-δ₀|y-y'|}`, `y, y' ∈ Λ`, "with the constants `B₀, δ₀` depending on
`d` and `L` only".

`S` is the setup type — everything the constants must NOT depend on: the RG step `k`, the
domain `Λ`, and the background configuration `U`.  `ι s` is the index set of `Λ` at setup `s`.
The existential quantifier on `B₀, δ₀` stands OUTSIDE the universal quantifier on `s`; that
ordering IS the content of "depending on `d` and `L` only". -/
def Thm315Uniform {S : Type*} (ι : S → Type*)
    (C : (s : S) → ι s → ι s → ℝ) (dst : (s : S) → ι s → ι s → ℝ) : Prop :=
  ∃ B₀ δ₀ : ℝ, 0 < B₀ ∧ 0 < δ₀ ∧
    ∀ (s : S) (y y' : ι s), |C s y y'| ≤ B₀ * Real.exp (-δ₀ * dst s y y')

/-- **MUST-FIRE CONTROL.**  `Thm315Uniform` is not free: there is a family for which it is
FALSE.  Contrast the campaign tree's standing gate
`AdalyFormal.Assumptions.finite_domain_decay_conclusion_is_free`, which proves that for a FIXED
finite domain a decay conclusion always holds for SOME constants.  Quantifying the constants
outside the setup destroys that freeness, so the shape used here carries content. -/
theorem thm315_uniform_not_free :
    ¬ Thm315Uniform (S := ℕ) (fun _ => Fin 1)
        (fun n _ _ => (n : ℝ)) (fun _ _ _ => (0 : ℝ)) := by
  rintro ⟨B₀, δ₀, hB, hδ, h⟩
  obtain ⟨n, hn⟩ := exists_nat_gt B₀
  have := h n 0 0
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, Nat.abs_cast] at this
  linarith

/-- **MUST-NOT-FIRE CONTROL.**  `Thm315Uniform` is satisfiable, so `thm315_uniform_not_free`
above is a genuine discrimination and not a vacuous shape.  A vanishing kernel satisfies it. -/
theorem thm315_uniform_satisfiable :
    Thm315Uniform (S := ℕ) (fun _ => Fin 1)
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) := by
  refine ⟨1, 1, one_pos, one_pos, ?_⟩
  intro s y y'
  simp

end Thm315Core
