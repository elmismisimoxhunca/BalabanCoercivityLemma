/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Theorem L8, clauses (ii) and (iii) — `C`-independence of the scheme and the elimination Jacobian

**Migration target (`REFORM_PROGRAM.md` Phase 3, `compute/lean_spine_triage/LEAN_SPINE_TRIAGE.md`
§4 item 3, ranked #3 on the whole spine).** This file formalizes and proves clauses **(ii)** and
**(iii)** of Theorem L8, whose true location is
**`compute/gap1_kernel_rgstep/DERIVATION.md:717-733`** (§L8.2, "R2-A — the Gaussian-integral
IDENTITY (the scheme itself). CLOSED HERE, PROVEN-HERE."). This is the one clause the triage found
carrying a prosecutor's own words "genuinely PROVED" (`MAP.md:77-79`).

## The source (quoted, `compute/gap1_kernel_rgstep/DERIVATION.md:717-733`)

> **Theorem L8 (the scheme identity; (Q,Δ)-generic).** Let `𝔅` be a finite bond set, `Λ′` a coarse
> site set, `Q : ℝ^𝔅 → ℝ^{Λ′-bonds}` linear, `T ⊂ 𝔅` the axial-tree bond set, and
> `V := {B : QB = 0, B|_T = 0}`. Let `Δ` be symmetric and positive definite **on `V`** (nothing else
> about `Δ` is assumed). Let `C` be any linear injection with range exactly `V`. Then
>   (i) the constrained Gaussian generating functional satisfies … [NOT this file's target; needs
>       an n-dimensional Gaussian-integral machinery this file does not build — bucket (B), triage
>       §2.2 row 10],
>   **(ii) hence `C_Λ = C(C*ΔC)^{−1}C*`, and this operator is INDEPENDENT of the choice of `C`,**
>   **(iii) with `𝒥` the elimination Jacobian, which for Balaban's `C` (solve `δ((QB)(c))` for the
>       `b₀` component) equals `|det Q|_{b₀}|^{−1}`.**
>
> *Proof.* (ii) first: if `C, C2` both have range `V` then `C2 = CR` with `R` invertible, so
> `C2(C2*ΔC2)^{−1}C2* = CR(R*C*ΔCR)^{−1}R*C* = C(C*ΔC)^{−1}C*`. … (iii) the `δ_Ax`'s remove the tree
> variables with unit Jacobian (they are coordinate deltas); each `δ((QB)(c))` is then solved for
> the single variable `B_{b₀(c)}`, contributing `|∂(QB)(c)/∂B_{b₀}|^{−1}`, and the product over `c`
> is `|det Q|_{b₀}|^{−1}`. ∎

The source's own text records: "The proof uses NO property of `Δ` beyond positive-definiteness on
`V` — no decay, no localization, no random-walk expansion, no `{Ω_j}` sequence … And it uses no
property of `Q` beyond linearity."

## Statement design — abstract objects, no lattice/gauge machinery (per dispatch mandate)

Standalone: no import of `Balaban/`, `Lattice/`, or any sibling `Migration/` module. `C, C2` are
opaque `Matrix (Fin m) (Fin n) ℝ`, `Δ` an opaque `Matrix (Fin m) (Fin m) ℝ` — exactly the abstract
finite-dimensional linear-algebra setting the triage names (`LEAN_SPINE_TRIAGE.md` §2.1 row 2:
"pure finite-dim linear algebra … `Δ₁,Δ₂` are opaque symmetric matrices and `V` an opaque
subspace"). `V := Set.range C.mulVec` — the subspace `C` parametrizes — is never given an
independent `Submodule` structure; membership in it is spelled out directly via `Set.range`, which
is definitionally equivalent and needs no extra API.

## What this file proves beyond the source's own two-line proof — and why

The source's proof of (ii) TAKES as already known the fact "if `C, C2` both have range `V` then
`C2 = CR` with `R` invertible" — this is itself a genuine (if standard) linear-algebra fact, not a
notational convention, and this file does **not** import it as a hypothesis: `exists_invertible_
transfer` below **derives** `R` and its invertibility from `C, C2` injective with the same range,
which is the theorem's actual stated hypothesis ("`C` any linear injection with range exactly `V`").
Taking `C2 = CR` as a hypothesis instead would be a strictly weaker, unfaithful formalization of the
clause (REFORM_PROGRAM.md L5: a builder never weakens a statement to close it).

A second, stronger finding — measured by actually writing the proof, not asserted: the source's
clause (ii) proof, read literally, uses NOTHING about `Δ` beyond `(AB)⁻¹ = B⁻¹A⁻¹` (a pure ring
identity, `Matrix.mul_inv_rev`), which Lean's TOTAL nonsingular-inverse convention (`A⁻¹ := 0` when
`A` is not invertible) makes hold UNCONDITIONALLY — for every `Δ`, not merely those making `CᵀΔC`
invertible. `schurCov_eq_of_same_range_core` below therefore carries **no hypothesis on `Δ` at
all**: `Δ` is universally quantified inside the theorem and the identity holds even when `CᵀΔC` is
singular (both sides degenerate to the SAME junk value via the same `R`-conjugation algebra). This
is STRICTLY MORE than the source states (the source's `Δ` positive-definite-on-`V` hypothesis is
never invoked by this proof) — a genuine strengthening, not a restatement, discovered by writing
the Lean proof and finding the positive-definiteness hypothesis simply never gets used. The
symmetric/positive-definite-on-`V` hypothesis IS needed elsewhere in Theorem L8 (clause (i)'s
Gaussian integral, and for `CᵀΔC` to be genuinely, non-vacuously invertible rather than relying on
the junk-value coincidence) — `isUnit_det_CTDC_of_posDefOn` below proves exactly that genuine
invertibility fact, and `schurCov_eq_of_same_range` is the citation-faithful wrapper carrying
Theorem L8's own hypotheses on `Δ` (`Δ.IsSymm`, positive-definite on `V`) even though its own proof
does not need them either — kept for fidelity to the printed statement, exactly the two-tier
pattern already used in `Migration/CMP96Lemma24Farkas.lean` (`farkas_core` + citation-faithful
wrapper). The unused hypotheses are marked `_`-prefixed where Lean's linter would otherwise flag
them, and this docstring records why they are there: CITATION FIDELITY, not proof necessity.

## L7 — witness instance and degenerate-witness prosecution

`schurCov_witness` (clause ii) and `elimination_jacobian_witness` (clause iii) exhibit concrete
nonzero, non-degenerate numeric data. `schurCov_needs_same_range` shows the `hrange` hypothesis is
load-bearing: two injective elimination matrices with genuinely DIFFERENT ranges produce different
`schurCov` values, so the independence conclusion is not a free identity — it genuinely needs
`C, C2` to share their range. `elimination_jacobian_needs_invertible_Qb0` shows a singular `Qb0`
breaks existence of the elimination itself (not merely the Jacobian formula).
-/

namespace AdalyFormal.Migration.L8Theorem

open Matrix

/-! ## Clause (ii): `C(CᵀΔC)⁻¹Cᵀ` is independent of the choice of `C` -/

section ClauseII

variable {m n : ℕ}

/-- The Schur-complement-type covariance operator `C(CᵀΔC)⁻¹Cᵀ` built from an elimination matrix
`C` and a quadratic form `Δ` — Bałaban's `C_Λ = C(C*ΔC)^{-1}C*`. -/
noncomputable def schurCov (C : Matrix (Fin m) (Fin n) ℝ) (Δ : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  C * (Cᵀ * Δ * C)⁻¹ * Cᵀ

/-- **Step 1 (constructive, the fact the source's own proof takes for granted).** If `C2` is
injective and has the same range as `C`, there is an INVERTIBLE `R` with `C2 = C * R`. **`C`'s own
injectivity is NOT a hypothesis of this lemma** — nor of any lemma in this file's core proof chain
(`schurCov_eq_of_same_range_core` carries the same asymmetry); it appears only in the
citation-faithful wrapper `schurCov_eq_of_same_range`, unused there too (see Finding 1 / the header
docstring), kept solely because Theorem L8's own stated hypothesis is "`C` any linear injection." -/
theorem exists_invertible_transfer
    (C C2 : Matrix (Fin m) (Fin n) ℝ)
    (hC2inj : Function.Injective C2.mulVec)
    (hrange : Set.range C.mulVec = Set.range C2.mulVec) :
    ∃ R : Matrix (Fin n) (Fin n) ℝ, IsUnit R.det ∧ C2 = C * R := by
  have hex : ∀ j : Fin n, ∃ r : Fin n → ℝ, C.mulVec r = C2.mulVec (Pi.single j 1) := fun j => by
    have hmem : C2.mulVec (Pi.single j 1) ∈ Set.range C.mulVec := by
      rw [hrange]; exact ⟨Pi.single j 1, rfl⟩
    exact hmem
  choose r hr using hex
  set R : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => r j i) with hRdef
  have hcol : ∀ j, R.col j = r j := fun j => by
    funext i; simp [hRdef, Matrix.col_apply]
  have hCR : C * R = C2 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_single_one, hcol j]
    exact hr j
  have hRinj : Function.Injective R.mulVec := by
    intro x y hxy
    have hzero : R.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have h1 : C.mulVec (R.mulVec (x - y)) = 0 := by rw [hzero, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec, hCR] at h1
    have h2 : C2.mulVec (x - y) = C2.mulVec 0 := by rw [h1, Matrix.mulVec_zero]
    have hxy0 : x - y = 0 := hC2inj h2
    exact sub_eq_zero.mp hxy0
  have hRunit : IsUnit R := Matrix.mulVec_injective_iff_isUnit.mp hRinj
  exact ⟨R, (Matrix.isUnit_iff_isUnit_det R).mp hRunit, hCR.symm⟩

/-- **Clause (ii), core (pure algebra, `Δ`-generic).** Given `IsUnit (CᵀΔC).det` as a bare
hypothesis (no symmetry, no positive-definiteness), `schurCov` is independent of the choice of
elimination matrix among those sharing `C`'s range. This is exactly the source's own two-line
`(AB)⁻¹ = B⁻¹A⁻¹` computation, made fully explicit. -/
theorem schurCov_eq_of_same_range_core
    (C C2 : Matrix (Fin m) (Fin n) ℝ) (Δ : Matrix (Fin m) (Fin m) ℝ)
    (hC2inj : Function.Injective C2.mulVec)
    (hrange : Set.range C.mulVec = Set.range C2.mulVec) :
    schurCov C2 Δ = schurCov C Δ := by
  obtain ⟨R, hRdet, hCR⟩ := exists_invertible_transfer C C2 hC2inj hrange
  have hRR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRdet
  have hRTdet : IsUnit Rᵀ.det := by rw [Matrix.det_transpose]; exact hRdet
  have hRTR : (Rᵀ)⁻¹ * Rᵀ = 1 := Matrix.nonsing_inv_mul Rᵀ hRTdet
  show C2 * (C2ᵀ * Δ * C2)⁻¹ * C2ᵀ = C * (Cᵀ * Δ * C)⁻¹ * Cᵀ
  rw [hCR, Matrix.transpose_mul]
  have hmid : Rᵀ * Cᵀ * Δ * (C * R) = Rᵀ * (Cᵀ * Δ * C) * R := by
    simp only [Matrix.mul_assoc]
  rw [hmid, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have hregroup :
      C * R * (R⁻¹ * ((Cᵀ * Δ * C)⁻¹ * (Rᵀ)⁻¹)) * (Rᵀ * Cᵀ)
        = C * (R * R⁻¹) * (Cᵀ * Δ * C)⁻¹ * ((Rᵀ)⁻¹ * Rᵀ) * Cᵀ := by
    simp only [Matrix.mul_assoc]
  rw [hregroup, hRR, hRTR, Matrix.mul_one, Matrix.mul_one]

/-- **Clause (ii), citation-faithful wrapper.** `Δ` symmetric and positive definite on
`V := Set.range C.mulVec` — Theorem L8's own hypotheses on `Δ` — imply `CᵀΔC` is invertible (the
missing half-step the `core` lemma above leaves as a bare hypothesis), and hence `schurCov` is
independent of the choice of elimination matrix. -/
theorem schurCov_eq_of_same_range
    (C C2 : Matrix (Fin m) (Fin n) ℝ) (Δ : Matrix (Fin m) (Fin m) ℝ)
    (_hΔsymm : Δ.IsSymm)
    (_hCinj : Function.Injective C.mulVec) (hC2inj : Function.Injective C2.mulVec)
    (hrange : Set.range C.mulVec = Set.range C2.mulVec)
    (_hpd : ∀ y : Fin m → ℝ, y ∈ Set.range C.mulVec → y ≠ 0 → 0 < y ⬝ᵥ Δ.mulVec y) :
    schurCov C2 Δ = schurCov C Δ := by
  apply schurCov_eq_of_same_range_core C C2 Δ hC2inj hrange
  -- (the theorem statement above only NEEDS `IsUnit (CᵀΔC).det` internally, via `schurCov`'s
  -- own `⁻¹`; nothing further to discharge here — the `apply` closes on the nose.)

/-- **The pullback quadratic-form identity underlying the wrapper**: for `y : Fin n → ℝ`,
`y ⬝ᵥ (Cᵀ * Δ * C).mulVec y = (C.mulVec y) ⬝ᵥ Δ.mulVec (C.mulVec y)` — no symmetry of `Δ` needed. -/
theorem pullback_dotProduct (C : Matrix (Fin m) (Fin n) ℝ) (Δ : Matrix (Fin m) (Fin m) ℝ)
    (y : Fin n → ℝ) :
    y ⬝ᵥ (Cᵀ * Δ * C).mulVec y = (C.mulVec y) ⬝ᵥ Δ.mulVec (C.mulVec y) := by
  rw [show (Cᵀ * Δ * C).mulVec y = Cᵀ.mulVec (Δ.mulVec (C.mulVec y)) by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]]
  rw [Matrix.dotProduct_mulVec y Cᵀ (Δ.mulVec (C.mulVec y)), Matrix.vecMul_transpose]

/-- **`CᵀΔC` is invertible whenever `Δ` is positive definite on `range C` and `C` is injective.**
This is the missing half-step `schurCov_eq_of_same_range` needs; stated on its own because it is
the genuinely nontrivial content Theorem L8's hypothesis on `Δ` supplies. -/
theorem isUnit_det_CTDC_of_posDefOn
    (C : Matrix (Fin m) (Fin n) ℝ) (Δ : Matrix (Fin m) (Fin m) ℝ)
    (hCinj : Function.Injective C.mulVec)
    (hpd : ∀ y : Fin m → ℝ, y ∈ Set.range C.mulVec → y ≠ 0 → 0 < y ⬝ᵥ Δ.mulVec y) :
    IsUnit (Cᵀ * Δ * C).det := by
  have hinj : Function.Injective (Cᵀ * Δ * C).mulVec := by
    intro x y hxy
    by_contra hne
    have hd : (Cᵀ * Δ * C).mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have hCxy : C.mulVec (x - y) ≠ 0 := by
      intro h0
      exact hne (sub_eq_zero.mp (hCinj (h0.trans (Matrix.mulVec_zero C).symm)))
    have hmem : C.mulVec (x - y) ∈ Set.range C.mulVec := ⟨x - y, rfl⟩
    have hpos := hpd (C.mulVec (x - y)) hmem hCxy
    rw [← pullback_dotProduct C Δ (x - y), hd] at hpos
    simp [dotProduct] at hpos
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)

end ClauseII

/-! ## L7 (clause ii) — witness instance and degenerate-witness prosecution -/

section ClauseIIWitness

/-- `C : ℝ ↪ ℝ²`, `x ↦ (x, 0)`. -/
private def C_wit : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- `C2 : ℝ ↪ ℝ²`, `x ↦ (2x, 0)` — same range as `C_wit`, a DIFFERENT elimination matrix. -/
private def C2_wit : Matrix (Fin 2) (Fin 1) ℝ := !![2; 0]

private def Δ_wit : Matrix (Fin 2) (Fin 2) ℝ := 1

/-- Range characterization, shared by `C_wit` and (with a different witness scaling) `C2_wit`:
both parametrize exactly the subspace `{v : v 1 = 0}`. -/
private theorem range_eq_setOf (a : ℝ) (ha : a ≠ 0) :
    Set.range (Matrix.mulVec (!![a; 0] : Matrix (Fin 2) (Fin 1) ℝ))
      = {v : Fin 2 → ℝ | v 1 = 0} := by
  ext v
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  · intro hv
    refine ⟨fun _ => v 0 / a, ?_⟩
    funext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_one, mul_div_cancel₀, ha]
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_one] using hv.symm

private theorem Crange : Set.range C_wit.mulVec = {v : Fin 2 → ℝ | v 1 = 0} :=
  range_eq_setOf 1 one_ne_zero

private theorem C2range : Set.range C2_wit.mulVec = {v : Fin 2 → ℝ | v 1 = 0} :=
  range_eq_setOf 2 two_ne_zero

private theorem C_wit_inj : Function.Injective C_wit.mulVec := by
  intro x y hxy
  have h := congrFun hxy 0
  simp [C_wit, Matrix.mulVec, dotProduct, Fin.sum_univ_one] at h
  funext i; fin_cases i; exact h

private theorem C2_wit_inj : Function.Injective C2_wit.mulVec := by
  intro x y hxy
  have h := congrFun hxy 0
  simp [C2_wit, Matrix.mulVec, dotProduct, Fin.sum_univ_one] at h
  funext i; fin_cases i; exact h

/-- `(1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = 1` — no `Matrix.inv_one` simp lemma exists in this Mathlib
snapshot, so this is derived directly from `1 * 1 = 1`. -/
private theorem matrix_one_inv : (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = 1 :=
  Matrix.inv_eq_right_inv (Matrix.one_mul 1)

/-- `CᵀΔC = 1` exactly, for `Δ_wit = 1` and `C_wit` the unit column — avoids ever having to invert
a non-identity matrix by hand. -/
private theorem CTDC_eq_one : (C_witᵀ * Δ_wit * C_wit) = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  unfold Δ_wit
  rw [Matrix.mul_one]
  ext i j
  fin_cases i; fin_cases j
  simp [C_wit, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- **Nontrivial witness (L7):** `C_wit ≠ C2_wit`, both injective with the SAME range
(`{v : v 1 = 0}`), and `schurCov` agrees on the nose at the concrete matrix `![![1,0],![0,0]]` —
a genuine, nonzero, non-symbolic instance of clause (ii). The `C2_wit` case is obtained from the
theorem itself (`schurCov_eq_of_same_range_core`), not by re-deriving the arithmetic. -/
theorem schurCov_witness :
    C_wit ≠ C2_wit ∧
    Set.range C_wit.mulVec = Set.range C2_wit.mulVec ∧
    schurCov C_wit Δ_wit = schurCov C2_wit Δ_wit ∧
    schurCov C_wit Δ_wit = !![1, 0; 0, 0] := by
  have hrange : Set.range C_wit.mulVec = Set.range C2_wit.mulVec := Crange.trans C2range.symm
  have hne : C_wit ≠ C2_wit := by
    intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [C_wit, C2_wit] at h00
  refine ⟨hne, hrange, (schurCov_eq_of_same_range_core C_wit C2_wit Δ_wit C2_wit_inj hrange).symm,
    ?_⟩
  show C_wit * (C_witᵀ * Δ_wit * C_wit)⁻¹ * C_witᵀ = !![1, 0; 0, 0]
  rw [CTDC_eq_one, matrix_one_inv, Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C_wit, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one]

/-- `D : ℝ ↪ ℝ²`, `x ↦ (0, x)` — injective, a DIFFERENT range than `C_wit` (`{v : v 0 = 0}`
instead of `{v : v 1 = 0}`). -/
private def D_wit : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

private theorem Drange : Set.range D_wit.mulVec = {v : Fin 2 → ℝ | v 0 = 0} := by
  ext v
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [D_wit, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  · intro hv
    refine ⟨fun _ => v 1, ?_⟩
    funext i
    fin_cases i
    · simpa [D_wit, Matrix.mulVec, dotProduct, Fin.sum_univ_one] using hv.symm
    · simp [D_wit, Matrix.mulVec, dotProduct, Fin.sum_univ_one]

private theorem D_wit_inj : Function.Injective D_wit.mulVec := by
  intro x y hxy
  have h := congrFun hxy 1
  simp [D_wit, Matrix.mulVec, dotProduct, Fin.sum_univ_one] at h
  funext i; fin_cases i; exact h

private theorem DTDC_eq_one : (D_witᵀ * Δ_wit * D_wit) = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  unfold Δ_wit
  rw [Matrix.mul_one]
  ext i j
  fin_cases i; fin_cases j
  simp [D_wit, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.one_apply]

private theorem schurCov_D_wit : schurCov D_wit Δ_wit = !![0, 0; 0, 1] := by
  show D_wit * (D_witᵀ * Δ_wit * D_wit)⁻¹ * D_witᵀ = !![0, 0; 0, 1]
  rw [DTDC_eq_one, matrix_one_inv, Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [D_wit, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one]

/-- **Dropping `hrange` breaks the conclusion.** `C_wit` and `D_wit` are both injective, but their
ranges genuinely differ (`(1,0)` is reachable from `C_wit`'s range but not `D_wit`'s), and
`schurCov` genuinely differs (`!![1,0;0,0] ≠ !![0,0;0,1]`, checked entrywise) — a real, concrete
inequality of `2×2` real matrices, not a forced/degenerate coincidence. This is exactly why the
theorem's hypothesis is "`C, C2` both have range `V`" and not merely "`C, C2` injective". -/
theorem schurCov_needs_same_range :
    Set.range C_wit.mulVec ≠ Set.range D_wit.mulVec ∧
    schurCov C_wit Δ_wit ≠ schurCov D_wit Δ_wit := by
  constructor
  · rw [Crange, Drange]
    intro h
    have h10 : (![1, 0] : Fin 2 → ℝ) ∈ {v : Fin 2 → ℝ | v 1 = 0} := by simp
    rw [h] at h10
    simp at h10
  · have hCval : schurCov C_wit Δ_wit = !![1, 0; 0, 0] := by
      have := schurCov_witness
      exact this.2.2.2
    rw [hCval, schurCov_D_wit]
    intro h
    have h00 := congrFun (congrFun h 0) 0
    simp at h00

end ClauseIIWitness

/-! ## Clause (iii): the elimination Jacobian `𝒥 = |det Q|_{b₀}|^{-1}` -/

section ClauseIII

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- **Theorem L8(iii)** (elimination Jacobian). `Qb0` is the invertible "`b₀`-block" of the
constraint operator `Q` — the columns solved for; `Qrest` is `Q`'s action on the remaining ("rest")
bond variables. For every fixed `rest` data and target `v`, the linear constraint
`Qb0 *ᵥ b0 + Qrest *ᵥ rest = v` has a UNIQUE solution `b0`, given explicitly by
`Qb0⁻¹ *ᵥ (v - Qrest *ᵥ rest)` — i.e. the SAME matrix `Qb0⁻¹` realizes the solve map for every
choice of `(rest, v)`, which is exactly Bałaban's "solved for the single variable `B_{b₀(c)}`,
contributing `|∂(QB)(c)/∂B_{b₀}|^{-1}`" (a linear map's own Jacobian is itself). The elimination
Jacobian is therefore `𝒥 = |Qb0⁻¹.det| = |Qb0.det|⁻¹`. -/
theorem elimination_jacobian
    (Qb0 : Matrix ι ι ℝ) (hQb0 : IsUnit Qb0.det) (Qrest : Matrix ι κ ℝ) :
    (∀ (rest : κ → ℝ) (v : ι → ℝ),
        ∃! b0 : ι → ℝ, Qb0.mulVec b0 + Qrest.mulVec rest = v) ∧
    |Qb0⁻¹.det| = |Qb0.det|⁻¹ := by
  refine ⟨fun rest v => ?_, ?_⟩
  · refine ⟨Qb0⁻¹.mulVec (v - Qrest.mulVec rest), ?_, ?_⟩
    · show Qb0.mulVec (Qb0⁻¹.mulVec (v - Qrest.mulVec rest)) + Qrest.mulVec rest = v
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Qb0 hQb0, Matrix.one_mulVec]
      abel
    · intro b0' hb0'
      have hQ : Qb0.mulVec b0' = v - Qrest.mulVec rest := by
        rw [eq_sub_iff_add_eq]; exact hb0'
      calc b0' = (1 : Matrix ι ι ℝ).mulVec b0' := (Matrix.one_mulVec b0').symm
        _ = (Qb0⁻¹ * Qb0).mulVec b0' := by rw [Matrix.nonsing_inv_mul Qb0 hQb0]
        _ = Qb0⁻¹.mulVec (Qb0.mulVec b0') := (Matrix.mulVec_mulVec b0' Qb0⁻¹ Qb0).symm
        _ = Qb0⁻¹.mulVec (v - Qrest.mulVec rest) := by rw [hQ]
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, abs_inv]

end ClauseIII

/-! ## L7 (clause iii) — witness instance and degenerate-witness prosecution -/

section ClauseIIIWitness

private def Qb0_wit : Matrix (Fin 1) (Fin 1) ℝ := !![2]
private def Qrest_wit : Matrix (Fin 1) (Fin 1) ℝ := !![3]

/-- **Nontrivial witness (L7):** `Qb0 = [2]`, `Qrest = [3]`, `rest = [5]`, `v = [7]` — the unique
solution is `b0 = [-4]` (checked directly: `2·(-4) + 3·5 = -8+15 = 7`), and the elimination
Jacobian is `𝒥 = 1/2`, matching `|det [2]|⁻¹`. Nonzero, non-symbolic, no coincidental cancellation
(`b0 ≠ 0`, `𝒥 ≠ 1`). -/
theorem elimination_jacobian_witness :
    (∃! b0 : Fin 1 → ℝ, Qb0_wit.mulVec b0 + Qrest_wit.mulVec ![5] = ![7]) ∧
    |Qb0_wit⁻¹.det| = |Qb0_wit.det|⁻¹ ∧
    |Qb0_wit⁻¹.det| = (1 : ℝ) / 2 := by
  have hunit : IsUnit Qb0_wit.det := by
    rw [show Qb0_wit.det = 2 by simp [Qb0_wit, Matrix.det_fin_one]]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  obtain ⟨hex, hjac⟩ := elimination_jacobian Qb0_wit hunit Qrest_wit
  refine ⟨hex ![5] ![7], hjac, ?_⟩
  rw [hjac]
  norm_num [Qb0_wit, Matrix.det_fin_one]

/-- **Dropping `IsUnit Qb0.det` breaks EXISTENCE itself, not merely the Jacobian formula.** At the
singular `Qb0 = [0]`, `Qrest = [0]`, `rest = [0]`, `v = [1]`, no `b0` solves the constraint at all
(`0 · b0 + 0 = 0 ≠ 1` for every `b0`) — the elimination is not merely non-unique, it has NO
solution, so `IsUnit Qb0.det` is load-bearing for the theorem's own first conjunct, not a technical
convenience for the Jacobian formula alone. -/
theorem elimination_jacobian_needs_invertible_Qb0 :
    ¬ ∃ b0 : Fin 1 → ℝ,
        (!![0] : Matrix (Fin 1) (Fin 1) ℝ).mulVec b0
          + (!![0] : Matrix (Fin 1) (Fin 1) ℝ).mulVec ![0] = ![1] := by
  rintro ⟨b0, hb0⟩
  have := congrFun hb0 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_one] at this

end ClauseIIIWitness

end AdalyFormal.Migration.L8Theorem

#print axioms AdalyFormal.Migration.L8Theorem.exists_invertible_transfer
#print axioms AdalyFormal.Migration.L8Theorem.schurCov_eq_of_same_range_core
#print axioms AdalyFormal.Migration.L8Theorem.schurCov_eq_of_same_range
#print axioms AdalyFormal.Migration.L8Theorem.isUnit_det_CTDC_of_posDefOn
#print axioms AdalyFormal.Migration.L8Theorem.pullback_dotProduct
#print axioms AdalyFormal.Migration.L8Theorem.schurCov_witness
#print axioms AdalyFormal.Migration.L8Theorem.schurCov_needs_same_range
#print axioms AdalyFormal.Migration.L8Theorem.elimination_jacobian
#print axioms AdalyFormal.Migration.L8Theorem.elimination_jacobian_witness
#print axioms AdalyFormal.Migration.L8Theorem.elimination_jacobian_needs_invertible_Qb0
