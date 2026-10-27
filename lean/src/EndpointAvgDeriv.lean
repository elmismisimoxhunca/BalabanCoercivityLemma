/-
Owned SI1-long file (compute/m1_si1_long/endpoint/). Imports the frozen `AdalyFormal` package,
the read-only compiled `ModifiedAverageDeriv` tranche (copied byte-identically into this directory
only for `LEAN_PATH` visibility, hash-checked against `compute/m1_si1_deriv/COORDINATOR_REVIEW.md`'s
`767f9f97…` source / `b65760da…` olean), and the wrap stage's already-compiled
`SI1AssembleDeriv`/`SI1Assemble`/`IngredientDeriv` (read from `compute/m1_si1_long/wrap/`, not
copied since that directory already sits inside this workflow's own `compute/m1_si1_long`
LEAN_PATH root). Neither dependency is edited.

## Scope

Differentiates CMP98 (63)/(89)'s `endpointAvg` (the block-averaged endpoint factor
`exp[Σ_{x∈B(y)} ℓ⁻³ log(R_{0,y}V₁)(Γ_{y,x})]`) at `V₁ = 1` along an arbitrary direction
`fun e => su2Exp (t • A e)`, for arbitrary traceless anti-Hermitian per-bond `A` and arbitrary
background `V0`/block size `ell`/base site `y`.

`endpointAvg` (`ModifiedAverageDeriv.lean`) is built from a LOCAL `rZeroPath`/`rZeroPathStep`
definition, independent of the one `hasDerivAt_su2Log_rZeroPath_forward` (wrap's
`SI1AssembleDeriv.lean`) is stated about (`IngredientDeriv.rZeroPath`) — both encode the SAME
tree-frame transport, but are different Lean declarations. §1 below proves the two agree
pointwise on any forward-only path (their step functions coincide exactly on the `step.2 = true`
branch), and that `GammaPath` is always forward-only, so every term `endpointAvg` sums over is
eligible for the already-compiled `su2Log ∘ rZeroPath` derivative untouched.

§2 differentiates one bracket term, §3 sums over the block with the `ℓ⁻³` weight
(`HasDerivAt.fun_sum`, a rational-to-real scalar bridge for `HasDerivAt.const_smul`), and §4
composes with `su2Exp`'s own unconditional chart-domain identity (`endpointChartDomain_always`,
already compiled) via `hasFDerivAt_exp_zero` to land the genuine `HasDerivAt` of the coerced
`endpointAvg` itself.

## What this file does NOT reach

It does not touch `ubarSU2`, `modifiedAverage`'s 4-factor product rule, the outer `log_skew`
derivative, or any CMP98 (121)–(124) vs `q124Principal` comparison. Only `endpointAvg` (one of the
two endpoint factors `modifiedAverage` needs, CMP98's own (63)) is differentiated here.
-/
import ModifiedAverageDeriv
import SI1AssembleDeriv

set_option autoImplicit false

open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing
attribute [local instance 10000] Matrix.linftyOpNormedAlgebra

namespace AdalySI1.EndpointAvgDeriv

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.Q1Real (GammaPath straightSegment)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2Exp_zero su2Log_one)
open AdalySI1.ModifiedAverageDeriv (endpointAvg rZeroPath rZeroPathStep
  EndpointChartDomain endpointAvg_coe_eq_of_chartDomain endpointChartDomain_always)
open AdalySI1.IngredientDeriv (dirDeriv)
open AdalySI1.SI1AssembleDeriv (hasDerivAt_su2Log_rZeroPath_forward rZeroPath_zero_smul_eq_one)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the forward-only bridge: `ModifiedAverageDeriv.rZeroPath` = `IngredientDeriv.rZeroPath`

Both `rZeroPathStep` definitions compute the SAME tuple on the `step.2 = true` (forward) branch
(`bondFactor := V1 (x, step.1)`, `bgFactor := V0 (x, step.1)`) — they differ only in the reverse
branch (`ModifiedAverageDeriv`'s carries the `[b,-b]`-fold fix, `IngredientDeriv`'s does not), which
`GammaPath` never uses. -/

theorem rZeroPathStep_eq_ingredient (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (st : PeriodicLatticeSite L × SU2 × SU2) (μ : Fin 3) :
    rZeroPathStep V0 V1 st (μ, true)
      = AdalySI1.IngredientDeriv.rZeroPathStep V0 V1 st (μ, true) := by
  unfold rZeroPathStep AdalySI1.IngredientDeriv.rZeroPathStep
  rfl

/-- **Generic forward-only fold congruence** (mirrors wrap's own `foldl_snd_snd_of_inv`): induction
over ABSTRACT step functions `f g`, never the concrete `rZeroPathStep`s themselves. Casing on
`steps` while the goal mentions the CONCRETE, `let`/`if`-heavy `rZeroPathStep V0 V1` applications
directly (rather than through an opaque `f`/`g`) forces Lean's motive/defeq machinery to unfold
those bodies during `cases`/`induction`, which is what actually pushed this file's compile past the
8 GiB owned-RSS ceiling in an earlier attempt (isolated by probe, not guessed) — this generic
version is the fix, not a rewording. -/
theorem foldl_congr_forward {f g : (PeriodicLatticeSite L × SU2 × SU2) → (Fin 3 × Bool) →
      (PeriodicLatticeSite L × SU2 × SU2)}
    (hfg : ∀ st (μ : Fin 3), f st (μ, true) = g st (μ, true)) :
    ∀ (steps : List (Fin 3 × Bool)) (st : PeriodicLatticeSite L × SU2 × SU2),
      (∀ s ∈ steps, s.2 = true) → steps.foldl f st = steps.foldl g st
  | [], _, _ => rfl
  | (μ, b) :: rest, st, hfwd => by
      have hb : b = true := hfwd (μ, b) List.mem_cons_self
      subst hb
      rw [List.foldl_cons, List.foldl_cons, hfg st μ,
        foldl_congr_forward hfg rest _ (fun s hs => hfwd s (List.mem_cons_of_mem _ hs))]

theorem rZeroPath_eq_ingredient_of_forward (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (base : PeriodicLatticeSite L) (steps : List (Fin 3 × Bool))
    (hfwd : ∀ s ∈ steps, s.2 = true) :
    rZeroPath V0 V1 base steps = AdalySI1.IngredientDeriv.rZeroPath V0 V1 base steps := by
  unfold rZeroPath AdalySI1.IngredientDeriv.rZeroPath
  rw [foldl_congr_forward (rZeroPathStep_eq_ingredient V0 V1) steps (base, 1, 1) hfwd]

/-- **`GammaPath` is always forward-only.** Every segment `straightSegment` emits is
`List.replicate _ (μ, true)` — the direction bit is never `false`, for ANY endpoints `y x`
(not merely those in a common block). -/
theorem GammaPath_forward (y x : PeriodicLatticeSite L) :
    ∀ s ∈ GammaPath y x, s.2 = true := by
  intro s hs
  unfold GammaPath straightSegment at hs
  simp only [List.mem_append] at hs
  rcases hs with (h | h) | h <;> rw [List.eq_of_mem_replicate h]

/-- **The shared gap, transported to `endpointAvg`'s own local `rZeroPath`.** Reuses
`hasDerivAt_su2Log_rZeroPath_forward` (wrap's already-compiled quadratic-remainder packaging)
verbatim via the §1 bridge; no new BCH/remainder analysis. -/
theorem hasDerivAt_su2Log_rZeroPath_ModifiedAverage (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (base x : PeriodicLatticeSite L) :
    HasDerivAt (fun t : ℝ =>
        su2Log (rZeroPath V0 (fun e => su2Exp (t • A e)) base (GammaPath base x)))
      (dirDeriv V0 A base (GammaPath base x) 1) 0 := by
  have hfwd : ∀ s ∈ GammaPath base x, s.2 = true := GammaPath_forward base x
  have hfun : (fun t : ℝ =>
        su2Log (rZeroPath V0 (fun e => su2Exp (t • A e)) base (GammaPath base x)))
      = (fun t : ℝ => su2Log (AdalySI1.IngredientDeriv.rZeroPath V0
          (fun e => su2Exp (t • A e)) base (GammaPath base x))) :=
    funext (fun t => congrArg su2Log
      (rZeroPath_eq_ingredient_of_forward V0 (fun e => su2Exp (t • A e)) base
        (GammaPath base x) hfwd))
  rw [hfun]
  exact hasDerivAt_su2Log_rZeroPath_forward V0 A hah htr base (GammaPath base x) hfwd

/-! ## §2 — a `ℚ`-to-`ℝ` smul bridge, mirroring the project's own `qsmul_eq_csmul`

`endpointAvg`'s bracket weights each term by `((ell:ℚ)^3)⁻¹`; `HasDerivAt.const_smul` is applied
below with the SAME scalar field `ℝ` as the derivative's own domain (`SMulCommClass ℝ ℝ M2` is the
generic `smulCommClass_self` instance, no cross-field `SMulCommClass` risk). -/

theorem qsmul_eq_rsmul (ell : ℕ) (X : M2) :
    ((ell : ℚ) ^ 3)⁻¹ • X = ((ell : ℝ) ^ 3)⁻¹ • X := by
  rw [← Rat.cast_smul_eq_qsmul ℝ (((ell : ℚ) ^ 3)⁻¹) X]
  congr 1
  push_cast
  ring

/-! ## §3 — the bracket sum, differentiated term-by-term and summed over the block -/

noncomputable def endpointAvgBracket (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : PeriodicLatticeEdge L → M2) (y : PeriodicLatticeSite L) (t : ℝ) : M2 :=
  ∑ x ∈ blockOf y ell,
    ((ell : ℚ) ^ 3)⁻¹ • su2Log (rZeroPath V0 (fun e => su2Exp (t • A e)) y (GammaPath y x))

theorem endpointAvg_eq_exp_bracket (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : PeriodicLatticeEdge L → M2) (y : PeriodicLatticeSite L) (t : ℝ) :
    ((endpointAvg V0 (fun e => su2Exp (t • A e)) ell y : SU2) : M2)
      = NormedSpace.exp (endpointAvgBracket V0 ell A y t) :=
  endpointAvg_coe_eq_of_chartDomain V0 (fun e => su2Exp (t • A e)) ell y
    (endpointChartDomain_always V0 (fun e => su2Exp (t • A e)) ell y)

theorem hasDerivAt_endpointAvgBracket_term (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (y x : PeriodicLatticeSite L) :
    HasDerivAt (fun t : ℝ => ((ell : ℚ) ^ 3)⁻¹ •
        su2Log (rZeroPath V0 (fun e => su2Exp (t • A e)) y (GammaPath y x)))
      (((ell : ℚ) ^ 3)⁻¹ • dirDeriv V0 A y (GammaPath y x) 1) 0 := by
  have hb := hasDerivAt_su2Log_rZeroPath_ModifiedAverage V0 A hah htr y x
  have heq : (fun t : ℝ => ((ell : ℚ) ^ 3)⁻¹ •
      su2Log (rZeroPath V0 (fun e => su2Exp (t • A e)) y (GammaPath y x)))
      = (fun t : ℝ => ((ell : ℝ) ^ 3)⁻¹ •
      su2Log (rZeroPath V0 (fun e => su2Exp (t • A e)) y (GammaPath y x))) :=
    funext (fun t => qsmul_eq_rsmul ell _)
  rw [heq, qsmul_eq_rsmul ell (dirDeriv V0 A y (GammaPath y x) 1)]
  exact hb.const_smul (((ell : ℝ) ^ 3)⁻¹)

theorem hasDerivAt_endpointAvgBracket (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (y : PeriodicLatticeSite L) :
    HasDerivAt (endpointAvgBracket V0 ell A y)
      (∑ x ∈ blockOf y ell, ((ell : ℚ) ^ 3)⁻¹ • dirDeriv V0 A y (GammaPath y x) 1) 0 := by
  show HasDerivAt (fun t : ℝ => ∑ x ∈ blockOf y ell, ((ell : ℚ) ^ 3)⁻¹ •
      su2Log (rZeroPath V0 (fun e => su2Exp (t • A e)) y (GammaPath y x))) _ 0
  exact HasDerivAt.fun_sum (fun x _ => hasDerivAt_endpointAvgBracket_term V0 ell A hah htr y x)

theorem endpointAvgBracket_zero (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : PeriodicLatticeEdge L → M2) (y : PeriodicLatticeSite L) :
    endpointAvgBracket V0 ell A y 0 = 0 := by
  show (∑ x ∈ blockOf y ell, ((ell : ℚ) ^ 3)⁻¹ •
      su2Log (rZeroPath V0 (fun e => su2Exp ((0 : ℝ) • A e)) y (GammaPath y x))) = 0
  apply Finset.sum_eq_zero
  intro x _
  have h1 : rZeroPath V0 (fun e => su2Exp ((0 : ℝ) • A e)) y (GammaPath y x) = 1 := by
    rw [rZeroPath_eq_ingredient_of_forward V0 _ y (GammaPath y x) (GammaPath_forward y x)]
    exact rZeroPath_zero_smul_eq_one V0 A y (GammaPath y x)
  rw [h1, su2Log_one, smul_zero]

/-! ## §4 — the target: a genuine `HasDerivAt` of `endpointAvg` itself, arbitrary `A`, `V0`, `ell`,
`y`

`endpointAvg`'s chart-domain identity holds UNCONDITIONALLY (`endpointChartDomain_always`, already
compiled — no smallness hypothesis anywhere), so `endpointAvg`'s coercion is literally
`NormedSpace.exp ∘ endpointAvgBracket` at EVERY `t`, not merely near `0`; composing `hasFDerivAt_exp_zero`
(the ambient exponential's own Fréchet derivative at `0`, the identity map) with §3's bracket
derivative via the standard chain rule gives the result directly, with no `su2Exp`-branch case
split needed. -/

theorem hasDerivAt_endpointAvg_coe (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (y : PeriodicLatticeSite L) :
    HasDerivAt (fun t : ℝ => ((endpointAvg V0 (fun e => su2Exp (t • A e)) ell y : SU2) : M2))
      (∑ x ∈ blockOf y ell, ((ell : ℚ) ^ 3)⁻¹ • dirDeriv V0 A y (GammaPath y x) 1) 0 := by
  have hfun : (fun t : ℝ => ((endpointAvg V0 (fun e => su2Exp (t • A e)) ell y : SU2) : M2))
      = (NormedSpace.exp ∘ endpointAvgBracket V0 ell A y) :=
    funext (endpointAvg_eq_exp_bracket V0 ell A y)
  rw [hfun]
  have hl : HasFDerivAt NormedSpace.exp (1 : M2 →L[ℝ] M2) (endpointAvgBracket V0 ell A y 0) := by
    rw [endpointAvgBracket_zero]
    exact hasFDerivAt_exp_zero
  have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hl
    (hasDerivAt_endpointAvgBracket V0 ell A hah htr y) rfl
  exact hcomp

#print axioms rZeroPathStep_eq_ingredient
#print axioms foldl_congr_forward
#print axioms rZeroPath_eq_ingredient_of_forward
#print axioms GammaPath_forward
#print axioms hasDerivAt_su2Log_rZeroPath_ModifiedAverage
#print axioms qsmul_eq_rsmul
#print axioms hasDerivAt_endpointAvgBracket_term
#print axioms hasDerivAt_endpointAvgBracket
#print axioms endpointAvgBracket_zero
#print axioms hasDerivAt_endpointAvg_coe

end AdalySI1.EndpointAvgDeriv
