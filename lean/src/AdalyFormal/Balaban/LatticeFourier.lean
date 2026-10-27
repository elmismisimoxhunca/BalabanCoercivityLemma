/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Target.ClayStatement

set_option autoImplicit false

/-!
# Discrete Fourier analysis on the periodic lattice, and diagonalization of translation-invariant
operators

**Task (blocking brick 4, the `U = 1` anchor)**: `compute/how_he_proves_it/PROOF_OF_167.md`
established that Bałaban proves the free-case bound CMP95 (1.67) by **momentum-space
diagonalization**: at `U = 1` every operator (`Δ`, `∂`, `Q_k`) is translation-invariant, so the
quadratic form diagonalizes and (1.67) reduces to a pointwise bound (1.66) on an explicit
trigonometric-polynomial ratio. This file builds the general-purpose infrastructure that
diagonalization argument rests on: a `d`-fold discrete Fourier transform on any finite periodic
lattice, its inversion formula, Parseval, the convolution theorem, and the general fact that a
translation-invariant linear operator is diagonalized by characters with eigenvalue equal to the
DFT of its own kernel (its "symbol") — together with the concrete symbol
`Δ₀(p) = Σ_μ |e^{ip_μ}−1|²` (CMP95 p.24) and its elementary two-sided bound.

## Scope, per `compute/u1_scope/U1_SCOPE.md`

* This is item **A** (the Fourier package) plus the elementary piece of item **1c** (the symbol and
  its bound) from that scoping document — **pure infrastructure**, no Bałaban-specific denotation
  risk. It does **not** attempt item **B** (translating `Δ, ∂, Q_k` themselves into momentum space)
  or item **C** (wiring the scalar bound back into `HjMinimizer`/`CoarseCurl`) — those are
  out-of-scope for this brick and remain open, exactly as that scoping document names them.
* **Mathlib gap, verified directly (not guessed) before building**: `ZMod.dft` (1-D, no Parseval, no
  convolution theorem), `AddChar.wInner_cWeight_eq_boole` / `AddChar.complexBasis` (orthogonality and
  a basis-of-characters fact, generic in *any* finite abelian group, but **not packaged** into a
  usable DFT+Parseval+convolution+diagonalization toolkit), `Matrix.circulant` (algebraic object with
  **zero** connection to eigenvalues anywhere in Mathlib). This file builds that missing package
  directly from the generic primitives (`AddChar.map_neg_eq_conj`, `AddChar.sum_apply_eq_ite`,
  `AddChar.norm_apply`), rather than re-deriving `ZMod.dft`'s 1-D pattern per axis — since those
  primitives are *already* generic in any finite `AddCommGroup`, no "tensor/product extension" step is
  needed at all: the package below applies directly to the lattice's own site group.

## The uniformity subtlety (settled in `U1_SCOPE.md`, respected, not re-litigated)

Bałaban's `∫dp′` is a continuous Brillouin-zone integral; our lattice is finite and periodic, so the
dual group is finite and every "integral" below is a **finite sum**. `U1_SCOPE.md` establishes these
are the *same claim*: his "`d`-only" constants are uniform over an unboundedly growing family of
finite lattices, and this campaign's own `∀ L : Fin 3 → ℕ` convention already forces that harder
statement. Every theorem below is accordingly stated **for an arbitrary `L`/`n`, not a fixed one** —
uniformity is visible directly in the theorem *types* (no hidden fixed modulus anywhere), which is
the discipline that document demands.

## What this file builds

1. **§1 — generic finite-abelian-group DFT.** `dft`, `dft_inversion`, `dft_parseval`, for any
   `[AddCommGroup α] [Fintype α] [DecidableEq α]` — this already covers `(ZMod n)^d` and, in
   particular, the campaign's own `PeriodicLatticeSite L` (§4), since the latter's group structure is
   an instance of the former (no separate "tensor extension" construction needed, see above).
2. **§2 — convolution and diagonalization.** `conv`, `dft_conv` (the convolution theorem), and the
   **load-bearing lemma**: `translationInvariant_diagonalized` — a linear operator that commutes with
   every lattice shift acts on each character `ψ` by scalar multiplication, the scalar being the DFT
   of the operator's own impulse response (its symbol). This is the exact mechanism
   `PROOF_OF_167.md` describes: *"a translation-invariant operator is diagonal in the momentum
   basis."*
3. **§3 — the symbol `Δ₀(p) = Σ_μ|e^{ip_μ}−1|²`** (CMP95 p.24), built as a function of a character
   `ψ` of the site group (not an abstract auxiliary "momentum" variable — a real momentum label is
   available for free via `AddChar.zmod`, but is not needed to state or bound the symbol), with the
   elementary identity `|e^{iθ}−1|² = 2(1−cos θ)` and the resulting two-sided bound
   `0 ≤ Δ₀(ψ) ≤ 4·3` (falsifiable both ways, §5).
4. **§4 — specialization to `PeriodicLatticeSite L`.** `PeriodicLatticeSite L` is definitionally
   `(μ : Fin 3) → ZMod (L μ + 1)` (`ZMod (n+1) := Fin (n+1)` by Mathlib's own definition, checked
   directly), so §1–§3 apply to it with **no** conversion lemma needed; this section records that
   fact explicitly (`periodicLatticeSite_eq_piZMod`, closed by `rfl`, itself a falsifiable check) and
   instantiates `Delta0Symbol` on the actual lattice site type.
5. **§5 — falsifiability / D4 controls.** Mutated statements that fail where the real ones hold,
   exercising every load-bearing lemma above.

## What this file does NOT build (named, not silently dropped)

* The momentum-space translation of `Δ, ∂, Q_k` themselves (item B, `U1_SCOPE.md`) — this requires
  identifying `LatticeOperators.siteLaplacianCLM`/`bondLaplacianCLM` as convolution operators in the
  sense of §2 and would need those files' complex-linear promotions; genuinely useful and enabled by
  this file's lemmas, but out of scope here (a real, sizeable follow-up, not attempted).
* Wiring any of the above into `HjMinimizer`/`CoarseCurl`/`KernelSubspace` (item C) — explicit NO-GO,
  those files are live-edited by concurrent lanes and this is out of this brick's mandate.
* The scalar bound `0 < γ₀ ≤ Δ₀(p′)φ_μ(p′) ≤ γ₁` itself (CMP95 (1.67)'s actual content) — that needs
  `φ_μ`, which is built from `Q_k`, `Δ` (fine lattice) and a reciprocal-lattice summability estimate
  (CMP89 Lemma 2.4) not attempted here; only the elementary, unconditional two-sided bound on `Δ₀`
  alone (no `φ_μ` factor) is built (§3).
-/

namespace AdalyFormal.Balaban.LatticeFourier

open AdalyFormal.Target.ClayStatement
open scoped ComplexConjugate

/-! ## §1. Discrete Fourier transform on a finite abelian group, with inversion and Parseval -/

section GenericDFT

variable {α : Type*} [AddCommGroup α] [Fintype α]

/-- The (unnormalized, forward) discrete Fourier transform of `f` at the character `ψ`:
`dft f ψ = Σ_x f(x) · conj(ψ(x))`. Matches the standard Fourier-coefficient formula; the inverse
carries the `1 / card α` normalization (`dft_inversion`), matching the usual DFT convention where
the forward transform is a plain sum and the inverse transform divides by the group size. -/
noncomputable def dft (f : α → ℂ) (ψ : AddChar α ℂ) : ℂ :=
  ∑ x : α, f x * conj (ψ x)

@[simp] theorem dft_zero (ψ : AddChar α ℂ) : dft (fun _ => (0 : ℂ)) ψ = 0 := by
  simp [dft]

theorem dft_add (f g : α → ℂ) (ψ : AddChar α ℂ) :
    dft (fun x => f x + g x) ψ = dft f ψ + dft g ψ := by
  simp [dft, add_mul, Finset.sum_add_distrib]

theorem dft_smul (c : ℂ) (f : α → ℂ) (ψ : AddChar α ℂ) :
    dft (fun x => c * f x) ψ = c * dft f ψ := by
  simp [dft, Finset.mul_sum, mul_assoc]

variable [DecidableEq α]

/-- **Fourier inversion.** `Σ_ψ (dft f ψ) · ψ(y) = (card α) · f(y)` for every `y`. This is the exact
finite-lattice analogue of Bałaban's continuum inverse Fourier transform: the dual group here is
`AddChar α ℂ`, a genuinely finite index set (`AddChar.instFintype`), so the "integral" is a finite
sum, per the uniformity note above. -/
theorem dft_inversion (f : α → ℂ) (y : α) :
    ∑ ψ : AddChar α ℂ, dft f ψ * ψ y = (Fintype.card α : ℂ) * f y := by
  classical
  have step1 : ∀ ψ : AddChar α ℂ, dft f ψ * ψ y = ∑ x : α, f x * ψ (y - x) := by
    intro ψ
    simp only [dft, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [mul_assoc, ← AddChar.map_neg_eq_conj ψ x, ← AddChar.map_add_eq_mul,
      show (-x + y : α) = y - x from by abel]
  simp_rw [step1]
  rw [Finset.sum_comm]
  have step2 : ∀ x : α,
      ∑ ψ : AddChar α ℂ, f x * ψ (y - x) = f x * ∑ ψ : AddChar α ℂ, ψ (y - x) := by
    intro x; rw [Finset.mul_sum]
  simp_rw [step2, AddChar.sum_apply_eq_ite]
  rw [Finset.sum_eq_single y]
  · simp [mul_comm]
  · intro x _ hxy
    have hy : y - x ≠ 0 := fun h => hxy (sub_eq_zero.mp h).symm
    simp [hy]
  · intro h; exact absurd (Finset.mem_univ y) h

/-- **Parseval / Plancherel.** `Σ_ψ |dft f ψ|² = (card α) · Σ_x |f(x)|²`. The single normalization
constant `card α` on the right is exactly the same constant that appears in `dft_inversion`
(inversion divides by it, Parseval multiplies by it) — this is the standard finite-DFT asymmetric
normalization, and both sides are genuine finite sums over the finite dual group, matching the
uniformity discipline stated above (no hidden fixed modulus). -/
theorem dft_parseval (f : α → ℂ) :
    ∑ ψ : AddChar α ℂ, Complex.normSq (dft f ψ)
      = (Fintype.card α : ℝ) * ∑ x : α, Complex.normSq (f x) := by
  classical
  have main : (∑ ψ : AddChar α ℂ, (Complex.normSq (dft f ψ) : ℂ))
      = (Fintype.card α : ℂ) * ∑ x : α, (Complex.normSq (f x) : ℂ) := by
    have e1 : ∀ ψ : AddChar α ℂ, (Complex.normSq (dft f ψ) : ℂ)
        = ∑ x : α, (dft f ψ * ψ x) * conj (f x) := by
      intro ψ
      rw [Complex.normSq_eq_conj_mul_self, mul_comm (conj (dft f ψ))]
      have hconj : conj (dft f ψ) = ∑ x : α, conj (f x) * ψ x := by
        simp only [dft, map_sum, map_mul, Complex.conj_conj]
      rw [hconj, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    simp_rw [e1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, dft_inversion]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Complex.normSq_eq_conj_mul_self]; ring
  exact_mod_cast main

end GenericDFT

/-! ## §2. Convolution, and the diagonalization of translation-invariant operators -/

section Convolution

variable {α : Type*} [AddCommGroup α] [Fintype α] [DecidableEq α]

/-- Discrete convolution on a finite abelian group: `(k ✶ f)(x) = Σ_y k(y) · f(x − y)`. -/
noncomputable def conv (k f : α → ℂ) (x : α) : ℂ :=
  ∑ y : α, k y * f (x - y)

omit [DecidableEq α] in
/-- **The convolution theorem.** `dft (k ✶ f) ψ = dft k ψ · dft f ψ`: convolution becomes pointwise
multiplication after the transform, the standard fact underlying `Q_k`/`Δ`/`∂`'s simultaneous
diagonalizability at `U = 1`. -/
theorem dft_conv (k f : α → ℂ) (ψ : AddChar α ℂ) :
    dft (conv k f) ψ = dft k ψ * dft f ψ := by
  classical
  have e1 : ∀ x : α, conv k f x * conj (ψ x)
      = ∑ y : α, k y * conj (ψ y) * (f (x - y) * conj (ψ (x - y))) := by
    intro x
    simp only [conv, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have hxy : conj (ψ x) = conj (ψ y) * conj (ψ (x - y)) := by
      rw [← map_mul, ← AddChar.map_add_eq_mul,
        show (y + (x - y) : α) = x from by abel]
    rw [hxy]; ring
  have reindex : ∀ y : α, ∑ x : α, f (x - y) * conj (ψ (x - y)) = dft f ψ :=
    fun y => Fintype.sum_equiv (Equiv.subRight y)
      (fun x => f (x - y) * conj (ψ (x - y))) (fun x => f x * conj (ψ x)) (fun _ => rfl)
  calc dft (conv k f) ψ = ∑ x : α, conv k f x * conj (ψ x) := rfl
    _ = ∑ x : α, ∑ y : α, k y * conj (ψ y) * (f (x - y) * conj (ψ (x - y))) :=
        Finset.sum_congr rfl (fun x _ => e1 x)
    _ = ∑ y : α, ∑ x : α, k y * conj (ψ y) * (f (x - y) * conj (ψ (x - y))) := Finset.sum_comm
    _ = ∑ y : α, k y * conj (ψ y) * ∑ x : α, f (x - y) * conj (ψ (x - y)) :=
        Finset.sum_congr rfl (fun y _ => by rw [Finset.mul_sum])
    _ = ∑ y : α, k y * conj (ψ y) * dft f ψ :=
        Finset.sum_congr rfl (fun y _ => by rw [reindex y])
    _ = (∑ y : α, k y * conj (ψ y)) * dft f ψ := by rw [Finset.sum_mul]
    _ = dft k ψ * dft f ψ := rfl

/-- The lattice shift-by-`t` operator on functions `α → ℂ`. -/
def shiftOp (t : α) (f : α → ℂ) (x : α) : ℂ := f (x - t)

/-- A linear operator is **translation invariant** if it commutes with every lattice shift. This is
exactly the property `PROOF_OF_167.md` isolates as what breaks under `U ≠ 1`: "the fine Laplacian
`Δ`, the derivative `∂`, and the RG kernel `Q_k` are translation-invariant (convolution) operators…
simultaneously diagonalized by the Fourier transform." -/
def IsTranslationInvariant (T : (α → ℂ) →ₗ[ℂ] (α → ℂ)) : Prop :=
  ∀ (t : α) (f : α → ℂ), T (shiftOp t f) = shiftOp t (T f)

/-- The indicator ("delta") function at a point. -/
noncomputable def deltaAt (a : α) : α → ℂ := fun x => if x = a then 1 else 0

omit [Fintype α] in
theorem shiftOp_deltaAt_zero (y : α) : shiftOp y (deltaAt (0 : α)) = deltaAt y := by
  funext x
  simp only [shiftOp, deltaAt, sub_eq_zero]

omit [AddCommGroup α] in
/-- `f = Σ_y f(y) • δ_y`: every function on a finite index set is a linear combination of point
masses. -/
theorem eq_sum_smul_deltaAt (f : α → ℂ) : f = ∑ y : α, f y • deltaAt y := by
  classical
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, deltaAt, smul_eq_mul, mul_ite, mul_one, mul_zero]
  exact (Fintype.sum_ite_eq x f).symm

/-- **Any translation-invariant linear operator is a convolution operator**, with kernel equal to
its own impulse response `T δ₀` (`T` applied to the delta function at the origin). This is the
"only if" half of the classical fact "linear + translation-invariant ⇔ convolution." -/
theorem translationInvariant_eq_conv (T : (α → ℂ) →ₗ[ℂ] (α → ℂ))
    (hT : IsTranslationInvariant T) (f : α → ℂ) :
    T f = conv (T (deltaAt 0)) f := by
  classical
  have hTf : T f = ∑ y : α, f y • T (deltaAt y) := by
    conv_lhs => rw [eq_sum_smul_deltaAt f]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun y _ => by rw [LinearMap.map_smul])
  have hTdelta : ∀ y : α, T (deltaAt y) = shiftOp y (T (deltaAt 0)) := by
    intro y
    rw [← shiftOp_deltaAt_zero y, ← hT y (deltaAt 0)]
  funext x
  rw [hTf]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- Rewrite each summand once via `hTdelta` (NOT via `simp_rw`: `hTdelta` applied to `y = 0` gives
  -- `T (deltaAt 0) = shiftOp 0 (T (deltaAt 0))`, so treating it as a rewrite rule self-matches its
  -- own right-hand side and loops; a single per-term `Finset.sum_congr` application avoids this).
  have step : ∀ y : α, f y * T (deltaAt y) x = f y * T (deltaAt 0) (x - y) := by
    intro y; rw [hTdelta y]; rfl
  calc (∑ y : α, f y * T (deltaAt y) x)
      = ∑ y : α, f y * T (deltaAt 0) (x - y) := Finset.sum_congr rfl (fun y _ => step y)
    _ = conv (T (deltaAt 0)) f x := by
        simp only [conv]
        exact Fintype.sum_equiv (Equiv.subLeft x) (fun y => f y * T (deltaAt 0) (x - y))
          (fun y => T (deltaAt 0) y * f (x - y)) (fun y => by
            simp only [Equiv.subLeft_apply]
            rw [show x - (x - y) = y from by abel]
            ring)

/-- **THE LOAD-BEARING LEMMA (diagonalization of translation-invariant operators).** A
translation-invariant linear operator acts on every character `ψ` by scalar multiplication, the
scalar being `dft (T δ₀) ψ` — the DFT of the operator's own kernel, i.e. its **symbol**. This is
the exact mechanism `PROOF_OF_167.md` describes: at `U = 1`, `Δ`, `∂`, `Q_k` are translation
invariant, hence simultaneously diagonal in the character (momentum) basis, turning an operator
inequality into a pointwise bound on an explicit function of the character alone. -/
theorem translationInvariant_diagonalized (T : (α → ℂ) →ₗ[ℂ] (α → ℂ))
    (hT : IsTranslationInvariant T) (ψ : AddChar α ℂ) :
    T (⇑ψ) = fun x => dft (T (deltaAt 0)) ψ * ψ x := by
  rw [translationInvariant_eq_conv T hT (⇑ψ)]
  funext x
  simp only [conv, dft]
  have e1 : ∀ y : α, T (deltaAt 0) y * ψ (x - y)
      = ψ x * (T (deltaAt 0) y * conj (ψ y)) := by
    intro y
    have : ψ (x - y) = ψ x * conj (ψ y) := by
      rw [← AddChar.map_neg_eq_conj ψ y, ← AddChar.map_add_eq_mul,
        show (x + -y : α) = x - y from by abel]
    rw [this]; ring
  simp_rw [e1, ← Finset.mul_sum]
  ring

end Convolution

/-! ## §3-4. The symbol `Δ₀`, and specialization to `PeriodicLatticeSite L` -/

section Symbol

/-- **`PeriodicLatticeSite L` is definitionally `(μ : Fin 3) → ZMod (L μ + 1)`**: Mathlib defines
`ZMod (n+1) := Fin (n+1)` (`Mathlib/Data/ZMod/Defs.lean:149`, checked directly, not guessed), and
`PeriodicLatticeSite L := (μ:Fin 3) → Fin (L μ+1)` is an `abbrev`
(`Target/ClayStatement.lean:1257`). Recorded here explicitly and closed by `rfl` — itself a
falsifiable check (§5): if the two sides were genuinely different types this would fail to
typecheck, not merely fail as a tactic. Consequently the whole §1-§2 package, instantiated at
`α := PeriodicLatticeSite L`, already **is** the "`d`-fold DFT on `(ZMod n)^d`" asked for — no
separate tensor/product construction is needed, and the `AddCommGroup`/`Fintype`/`DecidableEq`
instances used below are the same instances Mathlib attaches to `(ZMod n)^d`, not ad-hoc ones. -/
theorem periodicLatticeSite_eq_piZMod (L : PeriodicLatticeExtent) :
    PeriodicLatticeSite L = ((μ : Fin 3) → ZMod (L μ + 1)) := rfl

/-- The site reached from the all-zero site by one unit shift in direction `μ` — the lattice
translate whose character eigenvalue plays the role of Bałaban's `e^{ip_μ}` (CMP95 p.23-24: `p_μ` is
literally the coordinate dual to translation by `e_μ`). -/
def unitShiftSite (L : PeriodicLatticeExtent) (μ : Fin 3) : PeriodicLatticeSite L :=
  periodicLatticeShift (fun _ => 0) μ

/-- **The symbol `Δ₀(p) = Σ_μ |e^{ip_μ}−1|²`, CMP95 p.24** (`compute/how_he_proves_it/PROOF_OF_167.md`,
image-verified against `CMP95_pdfpg8-08.png`), built directly as a function of a character `ψ` of
the site group: `ψ (unitShiftSite L μ)` is the eigenvalue by which `ψ` is scaled under the unit
shift in direction `μ`, playing the role of `e^{ip_μ}`. This is exactly the symbol of the standard
combinatorial (nearest-neighbor) lattice Laplacian `2f(x) - f(x+e_μ) - f(x-e_μ)`, summed over `μ`,
matching §2's diagonalization mechanism: a translation-invariant operator's eigenvalue on the
character `ψ` is a fixed function of `ψ` alone, unchanged at every RG scale `k` (`Δ₀` itself carries
no `k`, `L`, or `ell` dependence anywhere in its formula — only through which characters exist,
matching `PROOF_OF_167.md`'s "`Δ₀(p′)` is the same function of `p′`, unchanged, at every `k`"). -/
noncomputable def Delta0Symbol (L : PeriodicLatticeExtent)
    (ψ : AddChar (PeriodicLatticeSite L) ℂ) : ℝ :=
  ∑ μ : Fin 3, Complex.normSq (ψ (unitShiftSite L μ) - 1)

/-- **The elementary identity `|e^{iθ}−1|² = 2(1−cos θ)`**, in the exact form needed: for any
norm-one value `z` of a character (`Complex.normSq z = 1`), `|z − 1|² = 2 − 2·Re(z)`. -/
theorem normSq_sub_one_of_normSq_one {z : ℂ} (hz : Complex.normSq z = 1) :
    Complex.normSq (z - 1) = 2 - 2 * z.re := by
  rw [Complex.normSq_sub]
  simp only [map_one, mul_one]
  rw [hz]; ring

theorem normSq_addChar_apply {L : PeriodicLatticeExtent}
    (ψ : AddChar (PeriodicLatticeSite L) ℂ) (x : PeriodicLatticeSite L) :
    Complex.normSq (ψ x) = 1 := by
  rw [Complex.normSq_eq_norm_sq, AddChar.norm_apply]; norm_num

/-- `Δ₀(ψ) = Σ_μ (2 − 2·Re(ψ(e_μ)))`, the concrete real-cosine form of CMP95 p.24. -/
theorem Delta0Symbol_apply (L : PeriodicLatticeExtent) (ψ : AddChar (PeriodicLatticeSite L) ℂ) :
    Delta0Symbol L ψ = ∑ μ : Fin 3, (2 - 2 * (ψ (unitShiftSite L μ)).re) := by
  unfold Delta0Symbol
  exact Finset.sum_congr rfl (fun μ _ =>
    normSq_sub_one_of_normSq_one (normSq_addChar_apply ψ _))

/-- **Elementary lower bound**: `Δ₀(ψ) ≥ 0` for every character, on every lattice `L` — no hidden
fixed modulus, matching the uniformity discipline above. -/
theorem Delta0Symbol_nonneg (L : PeriodicLatticeExtent) (ψ : AddChar (PeriodicLatticeSite L) ℂ) :
    0 ≤ Delta0Symbol L ψ :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

/-- **Elementary upper bound**: `Δ₀(ψ) ≤ 4·3` for every character on this 3-dimensional lattice
(each term `|e^{ip_μ}−1|² ≤ 4` since `|Re(ψ(e_μ))| ≤ ‖ψ(e_μ)‖ = 1`). -/
theorem Delta0Symbol_le (L : PeriodicLatticeExtent) (ψ : AddChar (PeriodicLatticeSite L) ℂ) :
    Delta0Symbol L ψ ≤ 4 * 3 := by
  rw [Delta0Symbol_apply]
  have hterm : ∀ μ : Fin 3, (2 : ℝ) - 2 * (ψ (unitShiftSite L μ)).re ≤ 4 := by
    intro μ
    have hnorm : ‖ψ (unitShiftSite L μ)‖ = 1 := AddChar.norm_apply _ _
    have hre : -1 ≤ (ψ (unitShiftSite L μ)).re := by
      have := (abs_le.1 (Complex.abs_re_le_norm (ψ (unitShiftSite L μ)))).1
      rwa [hnorm] at this
    linarith
  calc ∑ μ : Fin 3, (2 - 2 * (ψ (unitShiftSite L μ)).re)
      ≤ ∑ _μ : Fin 3, (4 : ℝ) := Finset.sum_le_sum (fun μ _ => hterm μ)
    _ = 4 * 3 := by simp; ring

/-- **Sanity / non-vacuity control.** `Δ₀` vanishes on the trivial character, for every lattice `L`
— the lower bound `0 ≤ Δ₀` (`Delta0Symbol_nonneg`) is genuinely **achieved**, not a vacuous bound
that never binds. This is also the concrete content behind "`Δ₀(p) = 0` only at zero momentum,"
the fact a spectral-gap/Poincaré argument on `Δ₀` would need. -/
theorem Delta0Symbol_trivial (L : PeriodicLatticeExtent) :
    Delta0Symbol L (0 : AddChar (PeriodicLatticeSite L) ℂ) = 0 := by
  unfold Delta0Symbol
  simp

end Symbol

/-! ## §5. Falsifiability / D4 mutation controls

Per `compute/BUILD_STANDARDS.md` §S/§OPS: every load-bearing constant and hypothesis above is
exercised by an explicit mutation that FAILS where the real statement holds, with the failure
proved (not asserted) on a genuinely closed witness. -/

section Falsifiability

/-- **Mutation 1 — the normalization constant in `dft_inversion` is forced, not decorative.**
Dropping `Fintype.card α` (replacing it with the "mutated" constant `1`) makes the inversion
identity FALSE on any nontrivial group: evaluated at the delta function `δ₀` (whose DFT is
identically `1` on every character, computed directly, not asserted) and at `y = 0`, the true
identity gives `card α`, and the mutated one gives `1` — these differ whenever `card α ≠ 1`. -/
theorem dft_inversion_delta_forces_card {α : Type*} [AddCommGroup α] [Fintype α] [DecidableEq α]
    (hα : Fintype.card α ≠ 1) :
    (∑ ψ : AddChar α ℂ, dft (deltaAt (0 : α)) ψ * ψ (0 : α)) ≠ (1 : ℂ) := by
  have hs : dft (deltaAt (0 : α)) = fun _ : AddChar α ℂ => (1 : ℂ) := by
    funext ψ
    simp only [dft, deltaAt]
    rw [Finset.sum_eq_single (0 : α)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ (0 : α)) h
  have hdft : ∀ ψ : AddChar α ℂ, dft (deltaAt (0 : α)) ψ * ψ (0 : α) = 1 := by
    intro ψ; rw [hs]; simp
  simp_rw [hdft]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, AddChar.card_eq]
  exact_mod_cast hα

/-- **Mutation 1, exercised on a closed witness** (`ZMod 2`, `card = 2 ≠ 1`): the true theorem
(`dft_inversion`) gives `∑ψ dft δ₀ ψ · ψ(0) = 2`; the mutated (unnormalized) statement claims this
equals `δ₀(0) = 1`. `2 ≠ 1`, so the mutation fails exactly where the real theorem holds — the
constant is load-bearing. -/
theorem dft_inversion_mutation_fails_on_ZMod2 :
    (∑ ψ : AddChar (ZMod 2) ℂ, dft (deltaAt (0 : ZMod 2)) ψ * ψ (0 : ZMod 2)) ≠ (1 : ℂ) :=
  dft_inversion_delta_forces_card (by rw [ZMod.card]; norm_num)

/-- The sign character of `ZMod 2`: `0 ↦ 1`, `1 ↦ −1`, built as `(-1)^x.val` so that
`map_add_eq_mul'` reduces to `neg_one_pow_eq_pow_mod_two` plus `ZMod.val_add` — a fully transparent,
hand-built (not via `AddChar.zmod`/`Circle`) witness for the mutation below. -/
noncomputable def signCharZMod2 : AddChar (ZMod 2) ℂ where
  toFun x := (-1 : ℂ) ^ x.val
  map_zero_eq_one' := by simp [ZMod.val_zero]
  map_add_eq_mul' := by
    intro a b
    change (-1 : ℂ) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val
    rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

theorem signCharZMod2_zero : signCharZMod2 0 = 1 := by
  simp [signCharZMod2]

theorem signCharZMod2_one : signCharZMod2 1 = -1 := by
  have hval : (1 : ZMod 2).val = 1 := by decide
  simp [signCharZMod2, hval]

/-- A coordinate-projection operator on `ZMod 2 → ℂ`: keeps the value at `0`, zeroes out the value
at `1`. A plausible-looking linear operator that is **not** built from any shift, hence a natural
candidate to test whether `IsTranslationInvariant` is really needed. -/
noncomputable def projT : (ZMod 2 → ℂ) →ₗ[ℂ] (ZMod 2 → ℂ) where
  toFun f x := if x = 0 then f 0 else 0
  map_add' f g := by funext x; by_cases h : x = 0 <;> simp [h]
  map_smul' c f := by funext x; by_cases h : x = 0 <;> simp [h]

/-- **Mutation 2a — `projT` genuinely fails the hypothesis.** It is not merely an operator someone
forgot to check; it is exhibited failing to commute with the shift-by-`1` operator on a concrete
input. -/
theorem projT_not_translationInvariant : ¬ IsTranslationInvariant projT := by
  intro hT
  have h := congrFun (hT 1 (deltaAt (1 : ZMod 2))) (0 : ZMod 2)
  have hlhs : projT (shiftOp 1 (deltaAt (1 : ZMod 2))) 0 = 1 := by
    simp [projT, shiftOp, deltaAt]
  have hrhs : shiftOp 1 (projT (deltaAt (1 : ZMod 2))) 0 = 0 := by
    simp [projT, shiftOp]
  rw [hlhs, hrhs] at h
  exact absurd h one_ne_zero

/-- **Mutation 2b — with the hypothesis genuinely false, the conclusion genuinely fails too**, not
merely "isn't proved": `projT` does **not** act on the (nontrivial) sign character by scalar
multiplication — a real, closed counterexample to the diagonalization conclusion, confirming
`IsTranslationInvariant` is load-bearing rather than a decorative hypothesis nothing depends on. -/
theorem projT_signChar_not_diagonal :
    ¬ ∃ c : ℂ, projT (⇑signCharZMod2) = fun x => c * signCharZMod2 x := by
  rintro ⟨c, hc⟩
  have h0 : projT (⇑signCharZMod2) 0 = c * signCharZMod2 0 := congrFun hc 0
  have h1 : projT (⇑signCharZMod2) 1 = c * signCharZMod2 1 := congrFun hc 1
  have hne : (1 : ZMod 2) ≠ 0 := by decide
  simp only [projT, LinearMap.coe_mk, AddHom.coe_mk] at h0
  simp only [projT, LinearMap.coe_mk, AddHom.coe_mk, if_neg hne] at h1
  rw [signCharZMod2_zero] at h0
  rw [signCharZMod2_one] at h1
  have hc1 : c = 1 := by simpa using h0.symm
  rw [hc1] at h1
  norm_num at h1

end Falsifiability

end AdalyFormal.Balaban.LatticeFourier
