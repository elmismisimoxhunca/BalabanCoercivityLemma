/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.VariationalProjectorH1
import AdalyFormal.Balaban.ConstantA

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `γ₁ > 0` — THE EXACT REDUCTION, AND WHY THE AMBIENT FORM OF THE CLAIM IS FALSE

CMP99b p.428 (`corpus/pages/CMP99b_p428.md`, `verification_status: adjudicated`) prints

> `⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ − 2⟨H₁D̃⁽²⁾(B),J⟩ = ⟨B,Δ_kB⟩.` (3.156)

and then, VERBATIM:

> "This form is considered on the subspace `{B : B=0 on Λ^c, B=0 on ⋃_{y∈Λ'} Ax(y), Q₁B=0}`."

and, four paragraphs later, VERBATIM:

> "It is more convenient to work with the operator `C̃⁽ᵏ⁾(Λ)`, because it is defined by a positive
> definite operator `C*Δ_kC` with a lower bound `γ₀ > 0` independent of `k` and `U`. We have proved
> it in [4], Lemma 2.4, for operators with `U=1`. Localizing the operators in `Δ_k` and using the
> methods of Sect. B we can prove it for `C*Δ_kC` with an arbitrary configuration `U` satisfying
> (3.35), (3.36) with `Mα₀` sufficiently small."

The claim carries **`C*` … `C`** on both sides. This module establishes, in the kernel, exactly
what that compression is doing, and it is not decoration: **the ambient (uncompressed) statement is
FALSE**, by a proved obstruction, and a concrete instance where it fails is exhibited (§5).

## THE ONE INPUT, AND WHERE IT IS PRINTED

CMP99b p.421, (3.128) (`corpus/pages/CMP99b_p421.md`):
`⟨A, G₁⁻¹A⟩ = ⟨A,Δ_πA⟩ − 2⟨HC_π^{(2)}(A),J⟩ + ‖RD*A‖² + a‖QA‖²`.

The **last summand is `a‖QA‖²` — the SAME constant `a` that (3.156) subtracts**, and it is the same
`a` of (3.16)/(3.26) (`ConstantA.lean`: one bare, unsubscripted, `k`-independent positive real).
`IsAQuadSplit D a Kop` below is exactly this: `⟨A,G₁⁻¹A⟩ = ⟨A,KopA⟩ + a‖QA‖²`, with
`Kop := Δ_π + DRD*` (`− 2⟨HC^{(2)}(A),J⟩` if the source term inside `G₁` is retained) the
**`a`-free remainder**. Nothing else about `G₁` is used anywhere in §1–§4.

## THE RESULTS

Write `Φ_a(B) := ⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩` (`deltaKQuadForm`), the source-free part of (3.156).

* **§1 `inner_solutionOperator_Ginv`** — `⟨H₁B, G₁⁻¹H₁B⟩ = ⟨B,(QG₁Q*)⁻¹B⟩`. This is the algebraic
  identity CMP99b uses, unstated, to pass from (3.155)'s integrand to (3.156).
  **NOT NEW: `Balaban/GatedRouteEmptiness.lean`'s `compInv_quadForm_eq_Ginv_at_solution` is the same
  statement with the same proof, and this module rebuilt it** (disclosed; this module deliberately
  imports nothing beyond `VariationalProjectorH1`/`ConstantA`, so it is retained here, but it is not
  billed as a result). See `SCOPE.md` §1b.
* **§1 `compInv_isLeast`** — hence `⟨B,(QG₁Q*)⁻¹B⟩ = min{⟨A,G₁⁻¹A⟩ : QA = B}`, attained.
* **§2 `deltaKQuadForm_eq`** — **THE KEY IDENTITY**: `Φ_a(B) = ⟨H₁B, Kop H₁B⟩`.
  The right-hand side **does not contain `a`**. This is the exact answer to "could a free `a` make
  the statement vacuous or false at will": *no* — `a` cancels identically, because the source puts
  the same `a` in (3.128) and (3.156).
* **§3 `gamma_floor_iff`** — **THE REDUCTION, AN IFF, UNIFORM IN `k` AND `U`**:
  `(∀B, γ‖B‖² ≤ Φ_a(B))  ↔  (∀A, γ‖QA‖² ≤ ⟨A,KopA⟩)`.
  A statement about the INVERSE of a compression becomes a forward quadratic-form inequality
  `Kop ≥ γ·Q*Q` on the fine space. No estimate, no smallness, no hypothesis on `k` or `U`.
* **§4 `gamma_nonpos_of_kernel`** — **THE OBSTRUCTION**: if `Kop` has ANY null vector `A₀` with
  `QA₀ ≠ 0`, then no `γ > 0` satisfies the ambient floor. At `U=1` the constant lattice 1-forms are
  exactly such an `A₀` (`Δ_π` is a covariant-curl energy and `RD*` a divergence: both annihilate
  constants; block averages of a constant do not vanish).
* **§4 `gamma_floor_compressed_of_restricted`** — the compressed statement, with `‖w‖ ≤ ‖C₀w‖`:
  it needs `Kop ≥ γQ*Q` **only on `{A : QA ∈ range C₀}`**, and `range C₀ ⊆ ker Q₁` is exactly the
  printed subspace. This is the route that survives §4's obstruction.
* **§5** — a CONCRETE 3-fine/2-coarse instance where `Φ_a` is `4B₂²`: not identically zero, yet zero
  on `B = QA₀ ≠ 0`, so the ambient `γ₁ > 0` fails while the compressed one holds with `γ = 4`.

## WHAT THIS MODULE DOES **NOT** DO — named, and NOT elected

It does not prove `Kop ≥ γQ*Q` on the printed subspace for Bałaban's own `Δ_π + DRD*` and `Q(U)`.
That is the deferred claim itself. What §1–§4 do is establish, unconditionally, that this fine-space
inequality is **equivalent** to the printed one, and that the ambient version of the printed one is
**unprovable** (§4). See `SCOPE.md` for the measurement of the three candidate routes.

## CONSUMER NOTE (S75 / LAW-19)

`compute/source_wired/stage/SourceWiredComposed.lean` takes `γ₁` through
`hfloor : ∀ B : BondFnL2 L, γ₁ * ‖B‖^2 ≤ ⟪B, deltaKQuadOp D bc B⟫` — an **AMBIENT** binder, over
the whole bond carrier. `deltaKQuadOp D bc` is `D.CompInv − (usedAt bc 0)•id`
(`compute/deltak_wiring/stage/DeltaKWiring.lean` §2), and `inner_deltaKQuadOp` gives
`⟪B, deltaKQuadOp D bc B⟫ = ⟪B, D.CompInv B⟫ − usedAt bc 0 * ⟪B,B⟫`, which is
`deltaKQuadForm D (usedAt bc 0) B` here (`deltaKQuadForm_eq_deltaKWiring_form`, §2).
By §4 that binder is **not satisfiable with `γ₁ > 0`** for any covariance datum whose `a`-free part
has a null vector outside `ker Q` — which is the `U=1` case of Bałaban's own operator. The
statement `source_wired` needs is the COMPRESSED one.
-/

namespace AdalyFormal.Balaban.Gamma1Positive

open AdalyFormal.Balaban.VariationalProjectorH1
open AdalyFormal.Balaban.ConstantA

variable {Hs Ks : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
  [NormedAddCommGroup Ks] [InnerProductSpace ℝ Ks]

/-! ## §1 — the value of the minimum IS the coarse form (CMP99b's own (3.155)→(3.156) step) -/

/-- **`⟨H₁B, G₁⁻¹H₁B⟩ = ⟨B,(QG₁Q*)⁻¹B⟩`.**  The identity CMP99b passes over silently between
(3.155) (whose integrand carries `−½⟨H₁B, G₁⁻¹H₁B⟩ + ½a⟨B,B⟩`) and (3.156) (whose left-hand side
carries `⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩`).  Two lines: `G₁⁻¹H₁B = Q*ω` with `ω = (QG₁Q*)⁻¹B`
(`Ginv_solutionOperator`), then move `Q*` across the pairing and use `Q H₁B = B`
(`interpolates`). -/
theorem inner_solutionOperator_Ginv (D : BalabanCovarianceData Hs Ks) (B : Ks) :
    (inner ℝ (solutionOperator D B) (D.Ginv (solutionOperator D B)) : ℝ)
      = inner ℝ B (D.CompInv B) := by
  rw [Ginv_solutionOperator D B, ← D.Q_Qstar_adjoint, interpolates D B]

/-- **`⟨B,(QG₁Q*)⁻¹B⟩ = min{⟨A,G₁⁻¹A⟩ : QA = B}`, attained at `A = H₁B`.**  `isMinimal` supplies
the lower-bound half; §1's identity supplies membership. -/
theorem compInv_isLeast (D : BalabanCovarianceData Hs Ks) (B : Ks) :
    IsLeast {r : ℝ | ∃ A : Hs, D.Q A = B ∧ r = inner ℝ A (D.Ginv A)}
      (inner ℝ B (D.CompInv B)) := by
  constructor
  · exact ⟨solutionOperator D B, interpolates D B, (inner_solutionOperator_Ginv D B).symm⟩
  · rintro r ⟨A, hA, rfl⟩
    rw [← inner_solutionOperator_Ginv D B]
    exact isMinimal D B A hA

/-! ## §2 — the `a`-free split of `G₁⁻¹`, and the key identity -/

/-- **CMP99b (3.128)'s split.**  `⟨A,G₁⁻¹A⟩ = ⟨A,KopA⟩ + a‖QA‖²`: `Kop` is the `a`-FREE remainder
`Δ_π + DRD*` (plus the `−2⟨HC^{(2)}(A),J⟩` term if it is kept inside `G₁`), and the last summand is
literally (3.128)'s `+ a‖QA‖²` with the SAME `a` that (3.156) subtracts. -/
def IsAQuadSplit (D : BalabanCovarianceData Hs Ks) (a : ℝ) (Kop : Hs →L[ℝ] Hs) : Prop :=
  ∀ A : Hs, (inner ℝ A (D.Ginv A) : ℝ) = inner ℝ A (Kop A) + a * ‖D.Q A‖ ^ 2

/-- **`Φ_a(B) := ⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩`** — the source-free part of (3.156), i.e. the object whose
positive lower bound is `γ₁`. -/
noncomputable def deltaKQuadForm (D : BalabanCovarianceData Hs Ks) (a : ℝ) (B : Ks) : ℝ :=
  (inner ℝ B (D.CompInv B) : ℝ) - a * ‖B‖ ^ 2

/-- The bridge to `compute/deltak_wiring/stage/DeltaKWiring.lean`'s `inner_deltaKQuadOp`, whose
right-hand side is `⟪B, D.CompInv B⟫ - usedAt bc 0 * ⟪B,B⟫`: the two are the same real number
(`⟪B,B⟫ = ‖B‖²`), so every theorem below applies verbatim to `deltaKQuadOp`. -/
theorem deltaKQuadForm_eq_deltaKWiring_form (D : BalabanCovarianceData Hs Ks) (bc : BaseConstant)
    (B : Ks) :
    deltaKQuadForm D (usedAt bc 0) B
      = (inner ℝ B (D.CompInv B) : ℝ) - usedAt bc 0 * (inner ℝ B B : ℝ) := by
  rw [deltaKQuadForm, real_inner_self_eq_norm_sq]

/-- **THE KEY IDENTITY.**  `Φ_a(B) = ⟨H₁B, Kop H₁B⟩` — the source-free part of (3.156) is the
`a`-FREE energy of the minimizer.  `a` cancels exactly, because `QH₁B = B`, so (3.128)'s
`+a‖QH₁B‖²` is literally the `a⟨B,B⟩` that (3.156) subtracts.

**This is the answer to "is `a` a free constant that could make the claim vacuous or false".**  It
is free (`a > 0`, no numerical value anywhere in CMP95/CMP99b), and it is also IRRELEVANT: the
right-hand side does not mention it.

**NO DISCHARGE IS CLAIMED FROM THIS.**  `GatedRouteEmptiness.lean`'s own §2 banner records a
CONVICTION (Sol second-family gate, 2026-07-29) of exactly that overclaim about the same
cancellation: *"the claim that it DISCHARGES anything is false… It is not obtained; it is renamed."*
The claim here is only that the free parameter `a` cannot be tuned to make the statement true or
false, because it does not occur in the reduced statement.  The whole content is the STRICT excess,
and §3/§4/§7 are about that. -/
theorem deltaKQuadForm_eq (D : BalabanCovarianceData Hs Ks) (a : ℝ) (Kop : Hs →L[ℝ] Hs)
    (hs : IsAQuadSplit D a Kop) (B : Ks) :
    deltaKQuadForm D a B
      = (inner ℝ (solutionOperator D B) (Kop (solutionOperator D B)) : ℝ) := by
  have h := hs (solutionOperator D B)
  rw [inner_solutionOperator_Ginv D B, interpolates D B] at h
  rw [deltaKQuadForm, h]
  ring

/-! ## §3 — THE REDUCTION: an IFF, uniform in `k` and `U` -/

/-- **Sufficiency.**  `Kop ≥ γ·Q*Q` on the fine space gives the coarse floor `γ` for `Φ_a`. -/
theorem gamma_floor_of_kinetic (D : BalabanCovarianceData Hs Ks) (a γ : ℝ) (Kop : Hs →L[ℝ] Hs)
    (hs : IsAQuadSplit D a Kop)
    (hK : ∀ A : Hs, γ * ‖D.Q A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ)) (B : Ks) :
    γ * ‖B‖ ^ 2 ≤ deltaKQuadForm D a B := by
  have h := hK (solutionOperator D B)
  rw [interpolates D B] at h
  rw [deltaKQuadForm_eq D a Kop hs B]
  exact h

/-- **Necessity.**  The coarse floor `γ` for `Φ_a` forces `Kop ≥ γ·Q*Q` on the WHOLE fine space.
The `a`-terms cancel against each other (`QH₁B = B = QA`), so no sign condition on `a` is used. -/
theorem kinetic_of_gamma_floor (D : BalabanCovarianceData Hs Ks) (a γ : ℝ) (Kop : Hs →L[ℝ] Hs)
    (hs : IsAQuadSplit D a Kop)
    (hfloor : ∀ B : Ks, γ * ‖B‖ ^ 2 ≤ deltaKQuadForm D a B) (A : Hs) :
    γ * ‖D.Q A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ) := by
  have hmin := isMinimal D (D.Q A) A rfl
  rw [inner_solutionOperator_Ginv D (D.Q A), hs A] at hmin
  have hstep : γ * ‖D.Q A‖ ^ 2 ≤ (inner ℝ (D.Q A) (D.CompInv (D.Q A)) : ℝ) - a * ‖D.Q A‖ ^ 2 :=
    hfloor (D.Q A)
  linarith

/-- **THE REDUCTION, AS AN IFF.**  Uniform in `k` and `U`: neither side mentions either. -/
theorem gamma_floor_iff (D : BalabanCovarianceData Hs Ks) (a γ : ℝ) (Kop : Hs →L[ℝ] Hs)
    (hs : IsAQuadSplit D a Kop) :
    (∀ B : Ks, γ * ‖B‖ ^ 2 ≤ deltaKQuadForm D a B)
      ↔ (∀ A : Hs, γ * ‖D.Q A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ)) :=
  ⟨fun h A => kinetic_of_gamma_floor D a γ Kop hs h A,
   fun h B => gamma_floor_of_kinetic D a γ Kop hs h B⟩

/-! ## §4 — THE OBSTRUCTION, and the compressed statement that survives it -/

/-- **THE AMBIENT CLAIM IS FALSE whenever `Kop` has a null vector outside `ker Q`.**

At `U = 1` this hypothesis is met by Bałaban's own operator: `Kop = Δ_π + DRD*` is a sum of a
covariant-curl energy and a divergence penalty, both of which annihilate the constant lattice
1-forms, whose block averages `QA₀` do not vanish.  Hence **no `γ₁ > 0` can satisfy the ambient
floor** — the compression `C` in `C*Δ_kC` is load-bearing, not decoration. -/
theorem gamma_nonpos_of_kernel (D : BalabanCovarianceData Hs Ks) (a γ : ℝ) (Kop : Hs →L[ℝ] Hs)
    (hs : IsAQuadSplit D a Kop) (A₀ : Hs) (hK0 : (inner ℝ A₀ (Kop A₀) : ℝ) ≤ 0)
    (hQ0 : D.Q A₀ ≠ 0) (hfloor : ∀ B : Ks, γ * ‖B‖ ^ 2 ≤ deltaKQuadForm D a B) :
    γ ≤ 0 := by
  have h := kinetic_of_gamma_floor D a γ Kop hs hfloor A₀
  have hpos : 0 < ‖D.Q A₀‖ ^ 2 := by
    have : 0 < ‖D.Q A₀‖ := norm_pos_iff.mpr hQ0
    positivity
  nlinarith [h, hK0, hpos]

/-- **`hQ0` IS AUTOMATIC.**  A `BalabanCovarianceData` carries `Ginv` positive SEMI-definite AND
two-sidedly invertible, which together force positive DEFINITENESS.  So a nonzero `A₀` with
`⟨A₀,KopA₀⟩ ≤ 0` cannot have `QA₀ = 0`: it would make `⟨A₀,GinvA₀⟩ = 0`, hence `GinvA₀ = 0` (by the
discriminant argument for the PSD form), hence `A₀ = Gstar(GinvA₀) = 0`. -/
theorem Q_ne_zero_of_null (D : BalabanCovarianceData Hs Ks) (a : ℝ) (Kop : Hs →L[ℝ] Hs)
    (hs : IsAQuadSplit D a Kop) (A₀ : Hs) (hne : A₀ ≠ 0)
    (hK0 : (inner ℝ A₀ (Kop A₀) : ℝ) ≤ 0) : D.Q A₀ ≠ 0 := by
  intro hQ
  have hG0 : (inner ℝ A₀ (D.Ginv A₀) : ℝ) = 0 := by
    have h := hs A₀
    rw [hQ] at h
    have hpos := D.Ginv_posSemidef A₀
    simp only [norm_zero] at h
    nlinarith [h, hK0, hpos]
  -- discriminant argument: the PSD symmetric form vanishes at A₀, so `Ginv A₀ = 0`
  have hzero : ∀ v : Hs, (inner ℝ v (D.Ginv A₀) : ℝ) = 0 := by
    intro v
    by_contra hv
    have key : ∀ t : ℝ, (0 : ℝ) ≤ inner ℝ v (D.Ginv v) + 2 * t * (inner ℝ v (D.Ginv A₀) : ℝ) := by
      intro t
      have hexp : (inner ℝ (v + t • A₀) (D.Ginv (v + t • A₀)) : ℝ)
          = inner ℝ v (D.Ginv v) + 2 * t * (inner ℝ v (D.Ginv A₀) : ℝ)
            + t ^ 2 * (inner ℝ A₀ (D.Ginv A₀) : ℝ) := by
        rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
          real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
          real_inner_smul_right]
        have hsym : (inner ℝ A₀ (D.Ginv v) : ℝ) = inner ℝ v (D.Ginv A₀) := by
          rw [← D.Ginv_selfAdjoint A₀ v, real_inner_comm]
        rw [hsym]; ring
      have := D.Ginv_posSemidef (v + t • A₀)
      rw [hexp, hG0] at this
      linarith
    set b : ℝ := (inner ℝ v (D.Ginv A₀) : ℝ) with hb
    set q : ℝ := (inner ℝ v (D.Ginv v) : ℝ) with hq
    have hb0 : b ≠ 0 := hv
    have hspec := key (-(q + 1) / (2 * b))
    have harith : 2 * (-(q + 1) / (2 * b)) * b = -(q + 1) := by field_simp
    rw [harith] at hspec
    linarith
  have hGA : D.Ginv A₀ = 0 := by
    have hnn := hzero (D.Ginv A₀)
    rw [real_inner_self_eq_norm_sq] at hnn
    have : ‖D.Ginv A₀‖ = 0 := by nlinarith [norm_nonneg (D.Ginv A₀), hnn]
    exact norm_eq_zero.mp this
  exact hne (by rw [← D.Gstar_Ginv A₀, hGA, map_zero])

/-- **THE OBSTRUCTION, IN ITS STRONGEST FORM.**  Only a NONZERO null vector of `Kop` is needed:
`QA₀ ≠ 0` comes for free (`Q_ne_zero_of_null`).  At `U=1` the constant lattice 1-forms are such an
`A₀`, so **no `γ₁ > 0` satisfies the ambient floor for Bałaban's own operator**. -/
theorem gamma_nonpos_of_null_vector (D : BalabanCovarianceData Hs Ks) (a γ : ℝ)
    (Kop : Hs →L[ℝ] Hs) (hs : IsAQuadSplit D a Kop) (A₀ : Hs) (hne : A₀ ≠ 0)
    (hK0 : (inner ℝ A₀ (Kop A₀) : ℝ) ≤ 0)
    (hfloor : ∀ B : Ks, γ * ‖B‖ ^ 2 ≤ deltaKQuadForm D a B) : γ ≤ 0 :=
  gamma_nonpos_of_kernel D a γ Kop hs A₀ hK0 (Q_ne_zero_of_null D a Kop hs A₀ hne hK0) hfloor

/-- **THE COMPRESSED STATEMENT.**  `C₀` is CMP99b p.428's `C` (the parametrization `B = CB̃` of the
printed subspace `{B = 0 on Λ^c, B = 0 on ⋃Ax(y), Q₁B = 0}`); `hC` is
`compute/item2_mechanical/`'s `‖w‖ ≤ ‖C₀w‖`.  The fine-space inequality is now needed **only on
`{A : QA ∈ range C₀}`** — which is where §4's null vectors are excluded, since `QA₀ ∉ ker Q₁`. -/
theorem gamma_floor_compressed_of_restricted {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] (D : BalabanCovarianceData Hs Ks) (a γ : ℝ) (Kop : Hs →L[ℝ] Hs)
    (hs : IsAQuadSplit D a Kop) (C₀ : W →L[ℝ] Ks) (hC : ∀ w : W, ‖w‖ ≤ ‖C₀ w‖) (hγ : 0 ≤ γ)
    (hKres : ∀ A : Hs, (∃ w : W, D.Q A = C₀ w) → γ * ‖D.Q A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ))
    (w : W) :
    γ * ‖w‖ ^ 2 ≤ deltaKQuadForm D a (C₀ w) := by
  have hmem : ∃ v : W, D.Q (solutionOperator D (C₀ w)) = C₀ v := ⟨w, interpolates D (C₀ w)⟩
  have h := hKres (solutionOperator D (C₀ w)) hmem
  rw [interpolates D (C₀ w)] at h
  rw [deltaKQuadForm_eq D a Kop hs (C₀ w)]
  refine le_trans ?_ h
  have hw := hC w
  have h0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  have hsq : ‖w‖ ^ 2 ≤ ‖C₀ w‖ ^ 2 := by nlinarith [hw, h0]
  exact mul_le_mul_of_nonneg_left hsq hγ


/-! ## §5 — A CONCRETE INSTANCE OF THE OBSTRUCTION (L7 / S82 non-vacuity)

Everything above is an implication; §4's obstruction would be worthless if its hypothesis could
never be met by a genuine `BalabanCovarianceData`. It can. This is a **3-fine / 2-coarse** instance,
deliberately NOT the degenerate `dim K = 1` case (where `Φ_a` would vanish identically and prove
nothing):

* fine `Hs = EuclideanSpace ℝ (Fin 3)`, coarse `Ks = EuclideanSpace ℝ (Fin 2)`;
* `Q(x,y,z) = (x+y, z)` — a genuine block average (two fine sites into one coarse), rank-deficient;
* `Kop = ` the form `(x−y)² + 4z²` — a miniature "curl energy": it annihilates the CONSTANT
  configuration `(1,1,0)`, exactly as `Δ_π + DRD*` annihilates constant lattice 1-forms;
* `a = 1`, and `Ginv = Kop + Q*Q = diag(2,2,5)` — so `IsAQuadSplit` holds BY COMPUTATION, not by
  fiat, and `Ginv` is genuinely positive definite and invertible;
* `Comp = QGQ* = diag(1, 1/5)`, `CompInv = diag(1,5)`, hence

      `Φ₁(B) = (B₀² + 5B₁²) − (B₀² + B₁²) = 4B₁²`.

`Φ₁` is **not identically zero** (it is `4B₁²`), yet it **vanishes on `B = QA₀ = (2,0) ≠ 0`**. So
the ambient floor forces `γ ≤ 0` (`witness_ambient_gamma_nonpos`) while the compressed floor holds
with `γ = 4` on `C₀ : w ↦ (0,w)` (`witness_compressed_gamma_four`). This is the whole phenomenon of
CMP99b p.428 in three dimensions. -/

open Matrix WithLp

/-- `Q(x,y,z) = (x+y, z)`: the miniature block average. -/
@[reducible] noncomputable def wQ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  matCLM (!![(1:ℝ), 1, 0; 0, 0, 1])

/-- `Q*(s,t) = (s,s,t)`. -/
@[reducible] noncomputable def wQstar : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  matCLM (!![(1:ℝ), 0; 1, 0; 0, 1])

/-- `Kop`: the quadratic form `(x−y)² + 4z²`. Annihilates the "constant" configuration `(1,1,0)`. -/
@[reducible] noncomputable def wKop : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  matCLM (!![(1:ℝ), -1, 0; -1, 1, 0; 0, 0, 4])

/-- `Ginv = Kop + 1·Q*Q = diag(2,2,5)`. -/
@[reducible] noncomputable def wGinv : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  matCLM (!![(2:ℝ), 0, 0; 0, 2, 0; 0, 0, 5])

/-- `G = diag(1/2,1/2,1/5)`. -/
@[reducible] noncomputable def wGstar : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  matCLM (!![(1/2:ℝ), 0, 0; 0, 1/2, 0; 0, 0, 1/5])

/-- `QGQ* = diag(1, 1/5)`. -/
@[reducible] noncomputable def wComp : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  matCLM (!![(1:ℝ), 0; 0, 1/5])

/-- `(QGQ*)⁻¹ = diag(1, 5)`. -/
@[reducible] noncomputable def wCompInv : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  matCLM (!![(1:ℝ), 0; 0, 5])

theorem w_Ginv_Gstar (x : EuclideanSpace ℝ (Fin 3)) : wGinv (wGstar x) = x := by
  apply WithLp.ofLp_injective 2
  rw [matCLM_apply, matCLM_apply]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem w_Gstar_Ginv (x : EuclideanSpace ℝ (Fin 3)) : wGstar (wGinv x) = x := by
  apply WithLp.ofLp_injective 2
  rw [matCLM_apply, matCLM_apply]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem w_Ginv_selfAdjoint (x y : EuclideanSpace ℝ (Fin 3)) :
    (inner ℝ (wGinv x) y : ℝ) = inner ℝ x (wGinv y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    matCLM_apply, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

theorem w_Ginv_posSemidef (x : EuclideanSpace ℝ (Fin 3)) : (0 : ℝ) ≤ inner ℝ x (wGinv x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  nlinarith [sq_nonneg (WithLp.ofLp x 0), sq_nonneg (WithLp.ofLp x 1), sq_nonneg (WithLp.ofLp x 2)]

theorem w_Q_Qstar_adjoint (x : EuclideanSpace ℝ (Fin 3)) (y : EuclideanSpace ℝ (Fin 2)) :
    (inner ℝ (wQ x) y : ℝ) = inner ℝ x (wQstar y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    matCLM_apply, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

theorem w_Comp_eq (x : EuclideanSpace ℝ (Fin 2)) : wComp x = wQ (wGstar (wQstar x)) := by
  apply WithLp.ofLp_injective 2
  rw [matCLM_apply, matCLM_apply, matCLM_apply, matCLM_apply]
  funext i
  fin_cases i <;>
    (simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]; try ring)

theorem w_Comp_CompInv (x : EuclideanSpace ℝ (Fin 2)) : wComp (wCompInv x) = x := by
  apply WithLp.ofLp_injective 2
  rw [matCLM_apply, matCLM_apply]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem w_CompInv_Comp (x : EuclideanSpace ℝ (Fin 2)) : wCompInv (wComp x) = x := by
  apply WithLp.ofLp_injective 2
  rw [matCLM_apply, matCLM_apply]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **The §5 instance.** Every field discharged by computation. -/
noncomputable def wData : BalabanCovarianceData
    (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 2)) where
  Ginv := wGinv
  Gstar := wGstar
  Ginv_Gstar := w_Ginv_Gstar
  Gstar_Ginv := w_Gstar_Ginv
  Ginv_selfAdjoint := w_Ginv_selfAdjoint
  Ginv_posSemidef := w_Ginv_posSemidef
  Q := wQ
  Qstar := wQstar
  Q_Qstar_adjoint := w_Q_Qstar_adjoint
  Comp := wComp
  Comp_eq := w_Comp_eq
  CompInv := wCompInv
  Comp_CompInv := w_Comp_CompInv
  CompInv_Comp := w_CompInv_Comp

/-- **`IsAQuadSplit wData 1 wKop` — CMP99b (3.128)'s split, verified by computation.**
`⟨A,GinvA⟩ = 2x²+2y²+5z²` and `⟨A,KopA⟩ + ‖QA‖² = ((x−y)²+4z²) + ((x+y)²+z²)`, equal by `ring`. -/
theorem w_isAQuadSplit : IsAQuadSplit wData 1 wKop := by
  intro A
  show (inner ℝ A (wGinv A) : ℝ) = inner ℝ A (wKop A) + 1 * ‖wQ A‖ ^ 2
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    matCLM_apply, matCLM_apply, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

/-- The "constant configuration" `A₀ = (1,1,0)`. -/
noncomputable def wA0 : EuclideanSpace ℝ (Fin 3) := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![1, 1, 0]

/-- `⟨A₀, Kop A₀⟩ = 0`: the miniature curl energy annihilates the constant configuration. -/
theorem w_kop_A0 : (inner ℝ wA0 (wKop wA0) : ℝ) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
  simp [wA0, dotProduct, Matrix.mulVec, Fin.sum_univ_three, EuclideanSpace.equiv]

/-- `Q A₀ = (2,0) ≠ 0`: the block average of the constant configuration does NOT vanish. -/
theorem w_Q_A0_ne_zero : wQ wA0 ≠ 0 := by
  intro h
  have h0 : WithLp.ofLp (wQ wA0) 0 = (0 : ℝ) := by rw [h]; simp
  rw [matCLM_apply] at h0
  simp [wA0, Matrix.mulVec, dotProduct, Fin.sum_univ_three, EuclideanSpace.equiv] at h0

/-- **THE AMBIENT CLAIM FAILS ON A GENUINE INSTANCE.**  No `γ > 0` satisfies the ambient floor for
`wData` — `γ ≤ 0` is forced.  This is `source_wired`'s `hfloor` binder, refuted on a covariance
datum whose every structure field is discharged by computation. -/
theorem witness_ambient_gamma_nonpos (γ : ℝ)
    (hfloor : ∀ B : EuclideanSpace ℝ (Fin 2), γ * ‖B‖ ^ 2 ≤ deltaKQuadForm wData 1 B) : γ ≤ 0 :=
  gamma_nonpos_of_kernel wData 1 γ wKop w_isAQuadSplit wA0 (le_of_eq w_kop_A0) w_Q_A0_ne_zero hfloor

/-- **THE AMBIENT CLAIM, REFUTED OUTRIGHT ON A GENUINE INSTANCE.**  For EVERY `γ > 0`, the ambient
floor is IMPOSSIBLE for `wData`.  This is the exact shape of `source_wired`'s `hfloor` binder, and
it is not merely unproved here: it is false. -/
theorem witness_ambient_impossible (γ : ℝ) (hγ : 0 < γ) :
    ¬ (∀ B : EuclideanSpace ℝ (Fin 2), γ * ‖B‖ ^ 2 ≤ deltaKQuadForm wData 1 B) := by
  intro h
  have := witness_ambient_gamma_nonpos γ h
  linarith

/-- **`Φ₁` IS NOT IDENTICALLY ZERO** — it is `4B₁²`, so §5 is not the degenerate `dim K = 1`
situation where the obstruction would be vacuous.  Exhibited at `B = (0,1)`: `Φ₁ = 4`. -/
theorem w_deltaKQuadForm_ne_zero :
    deltaKQuadForm wData 1 ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 1]) = 4 := by
  show (inner ℝ ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 1])
      (wCompInv ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 1])) : ℝ)
    - 1 * ‖((EuclideanSpace.equiv (Fin 2) ℝ).symm ![(0:ℝ), 1])‖ ^ 2 = 4
  rw [EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, EuclideanSpace.equiv]
  norm_num

/-- The compression `C₀ : w ↦ (0,w)` — the §5 analogue of CMP99b p.428's `C` (its range is the
subspace on which the obstruction's null direction has been removed). -/
@[reducible] noncomputable def wC0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  matCLM (!![(0:ℝ); 1])

/-- `‖w‖ ≤ ‖C₀w‖` — `item2_mechanical`'s compression hypothesis, here an equality. -/
theorem w_C0_norm (w : EuclideanSpace ℝ (Fin 1)) : ‖w‖ ≤ ‖wC0 w‖ := by
  have h : ‖wC0 w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
      matCLM_apply]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  nlinarith [h, norm_nonneg w, norm_nonneg (wC0 w)]

/-- **THE COMPRESSED CLAIM HOLDS ON THE SAME INSTANCE, WITH `γ = 4`.**  Same datum, same `a`, same
`Kop`: only the carrier changed, from the ambient coarse space to the range of `C₀`.  Together with
`witness_ambient_gamma_nonpos` this is the whole content of CMP99b p.428's `C*Δ_kC`, exhibited. -/
theorem witness_compressed_gamma_four (w : EuclideanSpace ℝ (Fin 1)) :
    (4 : ℝ) * ‖w‖ ^ 2 ≤ deltaKQuadForm wData 1 (wC0 w) := by
  have hform : deltaKQuadForm wData 1 (wC0 w)
      = 4 * (WithLp.ofLp w 0) ^ 2 := by
    show (inner ℝ (wC0 w) (wCompInv (wC0 w)) : ℝ) - 1 * ‖wC0 w‖ ^ 2 = _
    rw [EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply, matCLM_apply,
      ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  have hn : ‖w‖ ^ 2 = (WithLp.ofLp w 0) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct]
    ring
  rw [hform, hn]

/-! ## §6 — ROUTE (a), PERTURBATION FROM `U=1`: MEASURED, AND WHERE IT BREAKS

The obvious route to the general-`U` claim is to perturb off `U=1`: the printed class (3.35)/(3.36)
makes `U` close to `1`, so `Kop(U)` is close to `Kop(1)` in operator norm, so — the argument would
go — the coercivity constant degrades only slightly.

**It does not survive contact.**  The target inequality `⟨A,KopA⟩ ≥ γ‖QA‖²` is measured on the
right in `‖QA‖`, while an operator-norm perturbation is measured in `‖A‖`.  `Q` is a block average
with a huge kernel, so there is NO bound `‖A‖ ≲ ‖QA‖` to convert one into the other, and the
hypothesis `Kop ≥ γQ*Q` supplies **no lower bound at all** on `⟨A,KopA⟩` for `A ∈ ker Q` beyond `0`
(`kinetic_nonneg_on_kernel`).  §6 makes that sharp: there is a `Kop` meeting the target with `γ=1`
which an **arbitrarily small** quadratic-form perturbation drives strictly negative on `ker Q`, so
after perturbation NO `γ ≥ 0` survives.

This is the exact reason CMP99b p.428 says *"Localizing the operators in `Δ_k` and using the methods
of Sect. B"* rather than "by perturbation": the transfer needs the deviation to be dominated by
`Q*Q` (or by `Kop` itself), not by the identity. -/

/-- The target hypothesis gives **nothing but non-negativity** on `ker Q`. -/
theorem kinetic_nonneg_on_kernel (D : BalabanCovarianceData Hs Ks) (γ : ℝ) (Kop : Hs →L[ℝ] Hs)
    (hK : ∀ A : Hs, γ * ‖D.Q A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ)) (A₁ : Hs) (h : D.Q A₁ = 0) :
    (0 : ℝ) ≤ inner ℝ A₁ (Kop A₁) := by
  have := hK A₁
  rw [h] at this
  simpa using this

/-- `K₁ = Q*Q` on the §5 fine space — the extremal operator meeting the target with `γ = 1`. -/
@[reducible] noncomputable def wK1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  matCLM (!![(1:ℝ), 1, 0; 1, 1, 0; 0, 0, 1])

/-- `K₂(ε) = Q*Q − ε·P`, `P` the orthogonal projection onto `(1,−1,0) ∈ ker Q`. -/
@[reducible] noncomputable def wK2 (ε : ℝ) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  matCLM (!![1 - ε/2, 1 + ε/2, 0; 1 + ε/2, 1 - ε/2, 0; 0, 0, 1])

/-- `⟨A, K₁A⟩ = ‖QA‖²` exactly: `K₁` meets the target with `γ = 1`, with equality. -/
theorem w_K1_eq (A : EuclideanSpace ℝ (Fin 3)) :
    (inner ℝ A (wK1 A) : ℝ) = ‖wQ A‖ ^ 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

/-- **`K₂(ε)` is an `ε`-perturbation of `K₁` in the quadratic-form norm.** -/
theorem w_K2_close (ε : ℝ) (hε : 0 ≤ ε) (A : EuclideanSpace ℝ (Fin 3)) :
    |(inner ℝ A (wK2 ε A) : ℝ) - inner ℝ A (wK1 A)| ≤ ε * ‖A‖ ^ 2 := by
  have hdiff : (inner ℝ A (wK2 ε A) : ℝ) - inner ℝ A (wK1 A)
      = -(ε / 2) * (WithLp.ofLp A 0 - WithLp.ofLp A 1) ^ 2 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
      matCLM_apply, matCLM_apply]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    ring
  have hnorm : ‖A‖ ^ 2 = (WithLp.ofLp A 0) ^ 2 + (WithLp.ofLp A 1) ^ 2 + (WithLp.ofLp A 2) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, Fin.sum_univ_three]
    ring
  rw [hdiff, abs_of_nonpos (by nlinarith [sq_nonneg (WithLp.ofLp A 0 - WithLp.ofLp A 1), hε]), hnorm]
  nlinarith [sq_nonneg (WithLp.ofLp A 0 + WithLp.ofLp A 1), sq_nonneg (WithLp.ofLp A 2), hε]

/-- `A₁ = (1,−1,0)`, a nonzero element of `ker Q`. -/
noncomputable def wA1 : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![1, -1, 0]

theorem w_Q_A1 : wQ wA1 = 0 := by
  apply WithLp.ofLp_injective 2
  rw [matCLM_apply]
  funext i
  fin_cases i <;>
    simp [wA1, Matrix.mulVec, dotProduct, Fin.sum_univ_three, EuclideanSpace.equiv]

theorem w_A1_ne_zero : wA1 ≠ 0 := by
  intro h
  have h0 : WithLp.ofLp wA1 0 = (0 : ℝ) := by rw [h]; simp
  simp [wA1, EuclideanSpace.equiv] at h0

/-- **THE MEASUREMENT.**  For every `ε > 0`: `K₁` satisfies the target with `γ = 1`, `K₂(ε)` differs
from it by at most `ε` in quadratic-form norm, and `⟨A₁,K₂(ε)A₁⟩ = −2ε < 0` at a NONZERO `A₁` with
`QA₁ = 0`.  Hence `K₂(ε)` satisfies `⟨A,K₂A⟩ ≥ γ‖QA‖²` for NO `γ ≥ 0` whatsoever
(`kinetic_nonneg_on_kernel` is already violated).  Operator-norm smallness of the `U`-deviation is
therefore **insufficient** to transfer `γ₁ > 0` from `U=1`, at any size of deviation. -/
theorem perturbation_route_obstruction (ε : ℝ) (hε : 0 < ε) :
    ((∀ A : EuclideanSpace ℝ (Fin 3), (1 : ℝ) * ‖wQ A‖ ^ 2 ≤ inner ℝ A (wK1 A))
      ∧ (∀ A : EuclideanSpace ℝ (Fin 3),
          |(inner ℝ A (wK2 ε A) : ℝ) - inner ℝ A (wK1 A)| ≤ ε * ‖A‖ ^ 2))
    ∧ ((inner ℝ wA1 (wK2 ε wA1) : ℝ) = -2 * ε ∧ wA1 ≠ 0 ∧ wQ wA1 = 0) := by
  refine ⟨⟨fun A => by rw [w_K1_eq A]; ring_nf; exact le_refl _,
    fun A => w_K2_close ε hε.le A⟩, ?_, w_A1_ne_zero, w_Q_A1⟩
  rw [EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
  simp [wA1, dotProduct, Matrix.mulVec, Fin.sum_univ_three, EuclideanSpace.equiv]
  ring

/-! ## §7 — THE DECOMPOSITION: what is left after §3–§4, in exactly two named inputs

`§4`'s compressed statement needs `⟨H₁B, Kop H₁B⟩ ≥ γ‖B‖²` for `B` in the printed subspace.  Split
it at the coarse curl energy `E(B) := ⟨B, Δ₁B⟩` (CMP96 (2.128)'s `Σ_p|(∂₁B)(p)|²`):

* **(I) `hinterp` — THE INTERPOLATION-ENERGY COMPARISON** (the genuinely new input):
  `γ_c · E(B) ≤ ⟨H₁B, Kop H₁B⟩`, i.e. the fine kinetic energy of the CHEAPEST interpolation of `B`
  dominates the coarse curl energy of `B`.  By `deltaKQuadForm_eq` the left side of `§4` IS this
  minimum, so this is exactly "averaging does not create curl energy" for Bałaban's `Q(U)`.
* **(II) `hpoin` — CMP96 LEMMA 2.4 ON `ker Q₁`**: `γ_P‖B‖² ≤ E(B)` for `B` with `Q₁B = 0`.
  **This one is IN THIS TREE at `U=1`**: `Balaban/Lemma24GeneralEll.lean`'s `lemma24_general_ell`
  proves `ell·coarseQEnergy ell B + totalCurlEnergy B ≥ (1/180)·ell⁻⁵·‖B‖²` for every `ell ≥ 2`,
  and `coarseQEnergy` is CMP96's `Σ_c|(Q₁B)(c)|²`, which VANISHES on the printed subspace — so on
  `ker Q₁` it reads `totalCurlEnergy B ≥ (1/180)ell⁻⁵‖B‖²`, i.e. `γ_P = (1/180)ell⁻⁵`.

`gamma_floor_from_interp_and_poincare` composes them: `γ = γ_c·γ_P`. -/

/-- **THE COMPOSITION.**  Two inputs, one conclusion: the compressed floor with `γ = γ_c·γ_P`. -/
theorem gamma_floor_from_interp_and_poincare {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] (D : BalabanCovarianceData Hs Ks) (a γc γP : ℝ)
    (Kop : Hs →L[ℝ] Hs) (hs : IsAQuadSplit D a Kop) (C₀ : W →L[ℝ] Ks)
    (hC : ∀ w : W, ‖w‖ ≤ ‖C₀ w‖) (E : Ks → ℝ) (hγc : 0 ≤ γc) (hγP : 0 ≤ γP)
    (hinterp : ∀ w : W,
      γc * E (C₀ w) ≤ (inner ℝ (solutionOperator D (C₀ w)) (Kop (solutionOperator D (C₀ w))) : ℝ))
    (hpoin : ∀ w : W, γP * ‖C₀ w‖ ^ 2 ≤ E (C₀ w)) (w : W) :
    (γc * γP) * ‖w‖ ^ 2 ≤ deltaKQuadForm D a (C₀ w) := by
  rw [deltaKQuadForm_eq D a Kop hs (C₀ w)]
  refine le_trans ?_ (hinterp w)
  have h1 : γc * (γP * ‖C₀ w‖ ^ 2) ≤ γc * E (C₀ w) :=
    mul_le_mul_of_nonneg_left (hpoin w) hγc
  have hsq : ‖w‖ ^ 2 ≤ ‖C₀ w‖ ^ 2 := by
    have := hC w; nlinarith [this, norm_nonneg w]
  have h2 : (γc * γP) * ‖w‖ ^ 2 ≤ (γc * γP) * ‖C₀ w‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (mul_nonneg hγc hγP)
  nlinarith [h1, h2]

/-- **THE COMPOSITION IS NOT VACUOUS** — instantiated on §5's datum with an `E` that is defined
independently of `Φ` (it is the plain quadratic `E(B) = B₁²`, vanishing exactly on the null
direction `QA₀`): `γ_c = 4`, `γ_P = 1`, product `4`, matching `witness_compressed_gamma_four`. -/
theorem w_composition_instantiated (w : EuclideanSpace ℝ (Fin 1)) :
    ((4 : ℝ) * 1) * ‖w‖ ^ 2 ≤ deltaKQuadForm wData 1 (wC0 w) := by
  refine gamma_floor_from_interp_and_poincare wData 1 4 1 wKop w_isAQuadSplit wC0 w_C0_norm
    (fun B => (WithLp.ofLp B 1) ^ 2) (by norm_num) (by norm_num) ?_ ?_ w
  · intro v
    have hkey := deltaKQuadForm_eq wData 1 wKop w_isAQuadSplit (wC0 v)
    have hval : deltaKQuadForm wData 1 (wC0 v) = 4 * (WithLp.ofLp v 0) ^ 2 := by
      show (inner ℝ (wC0 v) (wCompInv (wC0 v)) : ℝ) - 1 * ‖wC0 v‖ ^ 2 = _
      rw [EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply, matCLM_apply,
        ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    have hE : (WithLp.ofLp (wC0 v) 1) ^ 2 = (WithLp.ofLp v 0) ^ 2 := by
      rw [matCLM_apply]
      simp [Matrix.mulVec, dotProduct]
    rw [← hkey, hval, hE]
  · intro v
    have hn : ‖wC0 v‖ ^ 2 = (WithLp.ofLp v 0) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    have hE : (WithLp.ofLp (wC0 v) 1) ^ 2 = (WithLp.ofLp v 0) ^ 2 := by
      rw [matCLM_apply]
      simp [Matrix.mulVec, dotProduct]
    rw [hn, hE, one_mul]

/-! ## §8 — `hG2` AND `γ₁` ARE OPPOSITE-DIRECTION BOUNDS ON THE SAME COMPOSITE

`compute/sigma_finish/SCOPE.md` §5 item 1 names `hG2` as "the σ-chain's own `G₂` coercivity input
(the source's `γ₀ > 0`)", and carries it as
`∀ x : BondFnL2 L, g₀(η³‖x‖²) ≤ η³⟪x, G₂x⟫`, consumed through the composite
`⟪F, Q_U(G₂(ℓ³·Q*_U F))⟫` (`SCOPE.md` §3a).  That is a **LOWER** bound on `Q G₂ Q*`.

`γ₁` is a **LOWER** bound on `(Q G₁ Q*)⁻¹ − a`.  §8 proves these are bounds on the same composite
in OPPOSITE directions:

* `compInv_upper_of_comp_lower` — a lower bound `c` on `QGQ*` yields an **UPPER** bound `1/c` on
  `(QGQ*)⁻¹`.  It gives no positive lower bound at all, so it cannot deliver `γ₁ > 0`.
* `comp_upper_of_gamma_floor` — conversely `γ₁ > 0` yields an **UPPER** bound `1/(a+γ₁)` on `QGQ*`.
* `comp_lower_holds_while_gamma_fails` — on the §5 datum BOTH facts are exhibited at once: the
  `hG2`-shaped lower bound HOLDS with `c = 1/5`, and `γ₁ > 0` is IMPOSSIBLE.

**Verdict: they are not the same fact, and neither implies the other.**  Closing `hG2` leaves `γ₁`
untouched, and vice versa.  (`sigma_finish` is a live sibling lane; this is a FINDING about the
parenthetical identification in its `SCOPE.md`, not an edit to it — LAW-4.) -/

/-- A lower bound on `QGQ*` gives an UPPER bound on `(QGQ*)⁻¹` — the wrong direction for `γ₁`. -/
theorem compInv_upper_of_comp_lower (D : BalabanCovarianceData Hs Ks) (c : ℝ) (hc : 0 < c)
    (hlow : ∀ y : Ks, c * ‖y‖ ^ 2 ≤ (inner ℝ y (D.Comp y) : ℝ)) (y : Ks) :
    (inner ℝ y (D.CompInv y) : ℝ) ≤ (1 / c) * ‖y‖ ^ 2 := by
  set z : Ks := D.CompInv y with hz
  have hCz : D.Comp z = y := D.Comp_CompInv y
  have hval : (inner ℝ y (D.CompInv y) : ℝ) = inner ℝ z (D.Comp z) := by
    rw [hCz, real_inner_comm]
  have hlow' : c * ‖z‖ ^ 2 ≤ (inner ℝ z (D.Comp z) : ℝ) := hlow z
  have hCS : (inner ℝ z (D.Comp z) : ℝ) ≤ ‖z‖ * ‖y‖ := by
    rw [hCz]
    exact real_inner_le_norm z y
  have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  have hyn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
  have hbound : c * ‖z‖ ≤ ‖y‖ ∨ ‖z‖ = 0 := by
    rcases eq_or_lt_of_le hzn with h | h
    · exact Or.inr h.symm
    · left
      have := le_trans hlow' hCS
      nlinarith [this, h]
  rw [hval]
  rcases hbound with h | h
  · have : ‖z‖ * ‖y‖ ≤ (1 / c) * ‖y‖ ^ 2 := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
      nlinarith [h, hyn]
    linarith [le_trans hlow' hCS, hCS, this]
  · have hz0 : z = 0 := norm_eq_zero.mp h
    rw [hz0]
    simp
    positivity

/-- Conversely, `γ₁ > 0` gives an UPPER bound on `QGQ*` — again the opposite direction. -/
theorem comp_upper_of_gamma_floor (D : BalabanCovarianceData Hs Ks) (a γ : ℝ) (hpos : 0 < a + γ)
    (hfloor : ∀ B : Ks, γ * ‖B‖ ^ 2 ≤ deltaKQuadForm D a B) (y : Ks) :
    (inner ℝ y (D.Comp y) : ℝ) ≤ (1 / (a + γ)) * ‖y‖ ^ 2 := by
  have hCI : ∀ B : Ks, (a + γ) * ‖B‖ ^ 2 ≤ (inner ℝ B (D.CompInv B) : ℝ) := by
    intro B
    have := hfloor B
    rw [deltaKQuadForm] at this
    linarith
  set z : Ks := D.Comp y with hz
  have hIz : D.CompInv z = y := D.CompInv_Comp y
  have hval : (inner ℝ y (D.Comp y) : ℝ) = inner ℝ z (D.CompInv z) := by
    rw [hIz, real_inner_comm]
  have hCS : (inner ℝ z (D.CompInv z) : ℝ) ≤ ‖z‖ * ‖y‖ := by
    rw [hIz]; exact real_inner_le_norm z y
  have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  have hyn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
  have hlow' : (a + γ) * ‖z‖ ^ 2 ≤ (inner ℝ z (D.CompInv z) : ℝ) := hCI z
  rw [hval]
  rcases eq_or_lt_of_le hzn with h | h
  · have hz0 : z = 0 := norm_eq_zero.mp h.symm
    rw [hz0]; simp; positivity
  · have hb : (a + γ) * ‖z‖ ≤ ‖y‖ := by nlinarith [le_trans hlow' hCS, h]
    have : ‖z‖ * ‖y‖ ≤ (1 / (a + γ)) * ‖y‖ ^ 2 := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
      nlinarith [hb, hyn]
    linarith [hCS, this]

/-- **THE INDEPENDENCE, EXHIBITED.**  On the §5 datum the `hG2`-shaped lower bound on `QGQ*` holds
with `c = 1/5`, while `γ₁ > 0` is impossible.  So `hG2` and `γ₁ > 0` are NOT the same fact and
`hG2` does not imply `γ₁ > 0`. -/
theorem comp_lower_holds_while_gamma_fails :
    (∀ y : EuclideanSpace ℝ (Fin 2), (1 / 5 : ℝ) * ‖y‖ ^ 2 ≤ (inner ℝ y (wData.Comp y) : ℝ))
    ∧ (∀ γ : ℝ, 0 < γ →
        ¬ (∀ B : EuclideanSpace ℝ (Fin 2), γ * ‖B‖ ^ 2 ≤ deltaKQuadForm wData 1 B)) := by
  refine ⟨fun y => ?_, fun γ hγ => witness_ambient_impossible γ hγ⟩
  show (1 / 5 : ℝ) * ‖y‖ ^ 2 ≤ (inner ℝ y (wComp y) : ℝ)
  rw [EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  nlinarith [sq_nonneg (WithLp.ofLp y 0), sq_nonneg (WithLp.ofLp y 1)]

#print axioms compInv_upper_of_comp_lower
#print axioms comp_upper_of_gamma_floor
#print axioms comp_lower_holds_while_gamma_fails
#print axioms inner_solutionOperator_Ginv
#print axioms compInv_isLeast
#print axioms deltaKQuadForm_eq_deltaKWiring_form
#print axioms deltaKQuadForm_eq
#print axioms gamma_floor_of_kinetic
#print axioms kinetic_of_gamma_floor
#print axioms gamma_floor_iff
#print axioms gamma_nonpos_of_kernel
#print axioms Q_ne_zero_of_null
#print axioms gamma_nonpos_of_null_vector
#print axioms gamma_floor_compressed_of_restricted
#print axioms wData
#print axioms w_isAQuadSplit
#print axioms w_kop_A0
#print axioms w_Q_A0_ne_zero
#print axioms witness_ambient_gamma_nonpos
#print axioms witness_ambient_impossible
#print axioms w_deltaKQuadForm_ne_zero
#print axioms w_C0_norm
#print axioms witness_compressed_gamma_four

#print axioms kinetic_nonneg_on_kernel
#print axioms w_K1_eq
#print axioms w_K2_close
#print axioms w_Q_A1
#print axioms w_A1_ne_zero
#print axioms perturbation_route_obstruction
#print axioms gamma_floor_from_interp_and_poincare
#print axioms w_composition_instantiated

end AdalyFormal.Balaban.Gamma1Positive
