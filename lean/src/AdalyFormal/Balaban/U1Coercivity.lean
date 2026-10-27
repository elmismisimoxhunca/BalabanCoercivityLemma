/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo

# U1 COERCIVITY — the `U = 1` case, PROVED `sorry`-free, ON `Δ^η` — **NOT** on CMP99b p.428's `Δ_k`

⚠ **QUALIFIER, HERE AT THE HEADLINE AND NOT ONLY IN `THE_LEMMA.md` ROW 4** (Sol gate,
`compute/sol_u1_gate/SOL_U1_GATE.md`, convicted the earlier title for dropping it at the payoff —
an S76 qualifier drop): `deltaKQuadFormCorrected` is the **unsubscripted, NON-RECURSIVE `Δ^η(U)`
of CMP99b p.392 (3.10)**, **NOT** the recursive `Δ_k(U)` of p.428 (3.156). No bridge between them
is built or attempted anywhere in this tree.

⚠ **AND WHAT THE PROOF ACTUALLY CONTAINS** (Sol's scoping, adopted verbatim because it is right):
once `Δ′` is deleted at `trivialU`, this is exactly *"an injective linear map on a
finite-dimensional space has a positive lower singular-value bound."* It uses **no** momentum
diagonalisation, **no** CMP95 (1.66), **no** CMP89 Lemma 2.4, **no** scale recursion, and **no**
nontrivial regular-background estimate. It is a real theorem and a much smaller one than an
unqualified reading of "Bałaban's `U = 1` case". `IsBalabanReparam` is likewise a proxy, not a
proof that Bałaban's actual reparametrization satisfies it.

## Why this file exists

Two de-correlated prosecution families (Sol, `compute/sol_stmt_gate/SOL_STMT_GATE.md`, and Kimi K3,
`compute/kimi_stmt_gate/KIMI_STMT_GATE.md`) independently CONVICTED the general-`U` statement
`TheLemma.theLemma_C_star_Delta_k_C_uniform` (repair `3976c753`): at a proxy-regular but non-flat
`U` (their `witnessU`/`centralU`), `deltaKQuadFormCorrected` goes to `-4`, so no positive `γ₀` can
work. **Both explicitly reported the `U = 1` companion,
`TheLemma.theLemma_U1_known_case`, is UNTOUCHED by that refutation** — at `trivialU` the transported
`Δ′` term vanishes identically (already banked, `DeltaPrime.deltaPrimeQuadFormTransported_
vanishes_at_trivial`), so the attack's entire mechanism (a negative `Δ′` overwhelming a nonnegative
`D*D`) cannot fire. Kimi: *"a proof looks reachable with existing machinery
(compactness/injectivity-below of a continuous linear map into a finite-dimensional codomain)."*

~~**This file builds that proof, standalone, without editing `TheLemma.lean`** (write-scope
discipline — other lanes own that file). The statement below is IDENTICAL in shape to
`TheLemma.theLemma_U1_known_case` ... a drop-in candidate to close that `sorry` once a maintainer of
that file chooses to.~~
⚠ **SUPERSEDED 2026-07-28 (`compute/sorry_triage/`): THE PROOF HAS MOVED INTO `TheLemma.lean` AND
THAT
`sorry` IS CLOSED.** The `Prop`-identity was machine-checked first
(`@theLemma_U1_known_case = @u1_coercivity := rfl` elaborated, two must-fail controls fired), and
the
move was possible with no new mathematics because this module's ONLY `import` is `TheLemma`, so
every
lemma the proof used was already in scope there; the proof sat downstream solely because the
target was
a `sorry` and consuming it there would have cycled. `u1_coercivity` below is now a ONE-LINE
RE-EXPORT of
`TheLemma.theLemma_U1_known_case`, and §1's three bridge lemmas are re-exports of `TheLemma.lean`
§2b.
Everything this header says about the MATHEMATICS and its scope (`Δ^η` not `Δ_k`, etc.) is
unchanged and
still governs — the caveat travels with the proof to its new home.

## The proof, in one paragraph

At `U = trivialU`, `deltaKQuadFormCorrected trivialU A = dstarDQuadForm trivialU A` for EVERY `A`
(the `Δ′` summand is killed identically — `deltaPrimeQuadFormTransported_vanishes_at_trivial`, a
fact about `Δ′` alone, no reference to `C` or `A`'s shape). `dstarDQuadForm trivialU A = ‖D_U^1 ·‖²`
on the `BondFnL2`/`PlaqFnL2` carrier (`norm_sq_curlCovariantCLM_L2_eq_dstarDQuadForm`, already
banked) — a manifest SQUARE, hence trivially `≥ 0`, and STRICTLY positive on any nonzero-curl input.
`IsBalabanReparam`'s own defining law says exactly this: for `Bt ≠ 0`, the covariant curl of `C Bt`
is nonzero at every regular `U`, in particular at `U = trivialU` (regular at `Mα₀ = 0` for ANY
positive threshold — `trivialU_isRegular`, the single most uncontroversial instance of the proxy:
`U = 1` displaces nothing, under any sane reading of "regular"). So the composed linear map
`Bt ↦ curlCovariantCLM_L2 trivialU (C Bt)` is INJECTIVE. Its domain `Btilde` is automatically
finite-dimensional — NOT assumed, DERIVED: `C` itself is injective (`hC.1`) into `BondFnL2 Lat`,
which is finite-dimensional (`SuTwo` is finite-dim, `Bond Lat` is a `Fintype`, Mathlib's
`WithLp.instModuleFinite` transports this through the `PiLp` carrier), and an injective linear map
into a finite-dimensional space forces its domain finite-dimensional too
(`FiniteDimensional.of_injective`). An injective linear map OUT OF a finite-dimensional normed space
is anti-Lipschitz (Mathlib `LinearMap.exists_antilipschitzWith`) — i.e. bounded below in norm by
some `K⁻¹ > 0` — which is exactly the compactness-of-the-unit-sphere argument the dispatch
anticipated, already packaged in Mathlib rather than hand-rolled. Squaring the bound and setting
`γ₀ := K⁻¹²` closes the goal.

## What this file does NOT need, and why that matters

* **No positivity/coercivity argument for `Δ′` anywhere** — it is not merely bounded, it is
  IDENTICALLY ZERO at `trivialU`, so the entire mechanism that killed the general-`U` statement
  (an indefinite `Δ′` overwhelming `D*D` at a proxy-regular non-flat background) cannot occur here
  by construction. This is stated once, precisely, rather than argued informally.
* **No use of `IsRegular`'s disputed content.** `IsRegular` is invoked at EXACTLY one point:
  `U = trivialU`, `Mα₀ = 0` (`trivialU_isRegular`). Every documented gap between the `IsRegular`
  proxy and CMP99b (3.35)/(3.36) — the missing cube/gauge-transformation geometry, the fixed-vector
  blind spot exhibited by `TheLemma.lean` §1d's `diagGroupElem`/`diagConfig` — concerns configurations
  OTHER than `U = 1`. At `U = 1` every reasonable regularity proxy agrees (displacement is exactly
  `0`, the minimum possible), so this proof does NOT inherit the proxy's rot: it would go through
  verbatim under any faithful formalization of (3.35)/(3.36) that classifies `U = 1` as regular
  (every one does — Bałaban's own class is a NEIGHBORHOOD of the identity).
* **No hand-rolled compactness argument.** Mathlib's `LinearMap.exists_antilipschitzWith` is exactly
  "injective + finite-dimensional domain ⇒ bounded below," which is the compactness-of-the-unit-
  sphere fact stated abstractly; using it directly avoids re-deriving a Bolzano–Weierstrass argument.

## Degeneracies, checked explicitly (per dispatch, not asserted)

* **`U = 1` is the class-5 degenerate test point** (every "wrong alternative" for the general
  statement's fatal channel coincides here: `Δ′ ≡ 0` regardless of which reading of `IsRegular` one
  takes, because `trivialU` is regular at threshold `0` under ANY sane proxy). Consequently this
  proof would still catch: (i) `IsBalabanReparam`'s curl-nonvanishing clause being VACUOUS or
  mis-stated (the injectivity-of-`Lmap` step fails immediately — demonstrated below,
  `u1_conclusion_fails_for_windC`, an S82 mutation using the tree's own `windC` witness, which
  violates `IsBalabanReparam` and for which the SAME-SHAPED conclusion is PROVABLY FALSE); (ii)
  `BondFnL2 Lat` failing to be finite-dimensional (the whole antilipschitz route is unavailable —
  this is a genuine, checked fact about `SuTwo`/`Bond Lat`, not assumed); (iii) `dstarDQuadForm`
  failing to be a norm-square (the Gram identity `norm_sq_curlCovariantCLM_L2_eq_dstarDQuadForm` is
  reused, not re-derived, and is itself a separately banked, `sorry`-free theorem).
* **`ell = 1`**: `deltaKQuadFormCorrected` as built in this tree carries no explicit `ell`/scale
  parameter (unchanged disclosure from `TheLemma.lean` §6); does not apply here either.
* **`γ₀` does not depend on `Bt`**: checked from the ELABORATED type (not source order) — see
  `#check @u1_coercivity` below; the `∃ γ₀` binder prints strictly before `∀ (Bt : Btilde)`,
  matching Bałaban's own quantifier order (`γ₀` chosen once, independent of `k` and `U` in his text;
  here additionally independent of `Bt`, which his text does not even mention as a possible
  dependence — the correct, strongest reading).
* **Not vacuous**: `u1_coercivity_spikeC_instance` below instantiates the theorem at the tree's own
  concrete `IsBalabanReparam`-satisfying witness (`TheLemma.spikeC`), producing a genuine
  `∃ γ₀ > 0, …` — the hypotheses are jointly satisfiable, this is not a vacuous implication.

## What this file does NOT claim (unchanged residuals, inherited from `TheLemma.lean`, not silently
bridged)

* `IsBalabanReparam`/`IsRegular` remain the SAME disclosed proxies as `TheLemma.lean` builds them —
  this file does not touch, strengthen, or weaken either definition (imported unchanged).
* This is NOT a re-derivation of CMP96 Lemma 2.4's actual geometric content (Bałaban's own
  `U = 1` case, over the true `Λ̃`/gauge-fixing machinery) — it is a proof of the SAME LEAN
  STATEMENT `theLemma_U1_known_case` already carries, on the SAME (disclosed, simplified) carrier.
  `Migration.CMP96Lemma24Farkas`'s five-opaque-real-number arithmetic re-derivation is a SEPARATE,
  disjoint piece of evidence for the same underlying mathematical fact; this file does not depend on
  it and does not claim to unify with it (a residual `TheLemma.lean` itself already names).
* `k`-uniformity: not represented, same as `TheLemma.lean` (this tree's `Δ_k(U)` has no `k`-index).

## Result

`u1_coercivity` below is proved, `sorry`-free, axiom footprint `[propext, Classical.choice,
Quot.sound]`. It is BINDER-IDENTICAL to `TheLemma.theLemma_U1_known_case`'s statement — in fact
DEFINITIONALLY EQUAL, measured by `rfl` (`compute/sorry_triage/probe_pass.log`).
~~a maintainer of `TheLemma.lean` can close that `sorry` with this file's proof term directly ...
which this file deliberately does NOT do itself (write-scope).~~ **DONE 2026-07-28: the proof was
moved into `TheLemma.lean` §3 and `u1_coercivity` is now a re-export of it.**
-/

import AdalyFormal.Balaban.TheLemma

set_option autoImplicit false

namespace AdalyFormal.Balaban.U1Coercivity

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.TheLemma
  AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.DeltaKFull AdalyFormal.Balaban.DeltaPrime
  AdalyFormal.Balaban.BondSU2Space AdalyFormal.Balaban.CovariantHj
  AdalyFormal.Balaban.HarmonicModes

/-! ## §1 — bridge lemmas: `WithLp.toLp 2 ∘ bondFnL2Equiv Lat = id`, and `WithLp.toLp 2` injective

⚠ **MOVED 2026-07-28, retained as re-exports.** These three lemmas' proofs now live in
`TheLemma.lean` §2b, because `theLemma_U1_known_case`'s proof (see the §2 note below) was moved
there.
The names and statements here are UNCHANGED so nothing referring to them breaks; each is now a
one-line re-export. There is exactly ONE proof text, in `TheLemma.lean`.

`bondFnL2Equiv Lat := WithLp.linearEquiv 2 ℝ (Bond Lat → SuTwo)` (`BondSU2Space.lean`), so its
`.symm` IS `WithLp.toLp 2` (Mathlib `WithLp.coe_symm_linearEquiv`) — these three facts package that
cancellation and its injectivity/zero behavior once, generically, for reuse below. -/

/-- `WithLp.toLp 2 (bondFnL2Equiv Lat X) = X` — `bondFnL2Equiv` and `WithLp.toLp 2` are mutually
inverse on `BondFnL2 Lat`, by definition of `bondFnL2Equiv` (`BondSU2Space.lean`). -/
theorem toLp_bondFnL2Equiv_eq {Lat : PeriodicLatticeExtent} (X : BondFnL2 Lat) :
    WithLp.toLp 2 (bondFnL2Equiv Lat X) = X :=
  AdalyFormal.Balaban.TheLemma.toLp_bondFnL2Equiv_eq X

/-- `WithLp.toLp 2 : V → WithLp 2 V` is injective, for ANY `V` (generic, reused at both the bond
and plaquette carriers below) — it is literally `(WithLp.linearEquiv 2 ℝ V).symm`, an equiv. -/
theorem toLp_injective {V : Type*} [AddCommGroup V] [Module ℝ V] :
    Function.Injective (WithLp.toLp 2 : V → WithLp 2 V) :=
  AdalyFormal.Balaban.TheLemma.toLp_injective

/-- `WithLp.toLp 2 0 = 0` — the same equiv preserves zero. -/
theorem toLp_zero {V : Type*} [AddCommGroup V] [Module ℝ V] :
    (WithLp.toLp 2 (0 : V) : WithLp 2 V) = 0 :=
  AdalyFormal.Balaban.TheLemma.toLp_zero

/-! ## §2 — THE THEOREM

Binder-identical to `TheLemma.theLemma_U1_known_case`: same `Btilde`/`C`/`Mα₀thresh` hypotheses,
`IsBalabanReparam`, `U` fixed at `trivialU`, `∃ γ₀ > 0, ∀ Bt, …` with `γ₀` bound ONCE before `∀ Bt`
(verified from the elaborated type below, not source order — S92 discipline). -/

/-- **THE `U = 1` COERCIVITY BOUND — PROVED, ON `Δ^η` NOT `Δ_k`.** ⚠ This discharges the exact
proposition `TheLemma.theLemma_U1_known_case` states — which is stated on `deltaKQuadFormCorrected`,
i.e. CMP99b p.392's **unsubscripted, non-recursive `Δ^η`**, **NOT** p.428's recursive `Δ_k` of
(3.156). At `U = 1` these are genuinely different operators (local `D*D` vs the nonlocal
inverse-covariance `(QG₁Q*)⁻¹ − a`); see the module header and `THE_LEMMA.md` row 4. So this closes
the tree's internal `sorry` and is **not** evidence about Bałaban's `C*Δ_kC` bound. See the module docstring for
the full proof sketch; in Lean: `Δ′` vanishes identically at `trivialU`
(`deltaPrimeQuadFormTransported_vanishes_at_trivial`), so the goal reduces to a norm-square lower
bound on the injective, finite-domain composed map `Bt ↦ curlCovariantCLM_L2 trivialU (C Bt)`,
supplied by Mathlib's `LinearMap.exists_antilipschitzWith`.

⚠ **2026-07-28: the proof text now lives in `TheLemma.lean` §3** (`theLemma_U1_known_case`, whose
`sorry` it closed); this declaration is a re-export, kept so its name and its 7-module reverse
closure
are unaffected. One proof text, not two. -/
theorem u1_coercivity
    {Lat : PeriodicLatticeExtent}
    {Btilde : Type*} [NormedAddCommGroup Btilde] [InnerProductSpace ℝ Btilde]
    (C : Btilde →L[ℝ] BondFnL2 Lat)
    (Mα₀thresh : ℝ) (hMα₀thresh_pos : 0 < Mα₀thresh)
    (hC : IsBalabanReparam Mα₀thresh C) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ Bt : Btilde,
        γ₀ * ‖Bt‖ ^ 2 ≤ deltaKQuadFormCorrected (trivialU (L := Lat)) (bondFnL2Equiv Lat (C Bt)) :=
  AdalyFormal.Balaban.TheLemma.theLemma_U1_known_case C Mα₀thresh hMα₀thresh_pos hC

#print axioms u1_coercivity

/-! ## §3 — NON-VACUITY: instantiate at the tree's own `spikeC` witness -/

/-- **Non-vacuity, checked not assumed.** `spikeC` (`TheLemma.lean` §5b) genuinely satisfies
`IsBalabanReparam` at every threshold, so `u1_coercivity` is not vacuously true from an
unsatisfiable hypothesis — this specializes it to a concrete, already-banked witness. -/
theorem u1_coercivity_spikeC_instance (Mα₀thresh : ℝ) (hpos : 0 < Mα₀thresh) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ Bt : ℝ,
      γ₀ * ‖Bt‖ ^ 2 ≤
        deltaKQuadFormCorrected (trivialU (L := AdalyFormal.Balaban.AdmissibleSubspace.witnessL))
          (bondFnL2Equiv AdalyFormal.Balaban.AdmissibleSubspace.witnessL (spikeC Bt)) :=
  u1_coercivity spikeC Mα₀thresh hpos (spikeC_satisfies_isBalabanReparam Mα₀thresh)

#print axioms u1_coercivity_spikeC_instance

/-! ## §4 — S82 MUTATION: drop `IsBalabanReparam` (use `windC`) and the SAME-SHAPED conclusion
becomes PROVABLY FALSE — `hC` is load-bearing, not decorative. -/

/-- **`hC` is load-bearing.** `windC` (`TheLemma.lean` §5) does NOT satisfy `IsBalabanReparam`
(`windC_fails_isBalabanReparam`, already banked) — its image is the winding mode, whose covariant
curl vanishes identically at `trivialU`. Consequently the SAME-SHAPED conclusion (same `deltaKQuad
FormCorrected trivialU (bondFnL2Equiv Lat (· Bt))` bound) is FALSE for `windC`: `deltaKQuadForm
Corrected trivialU (windingModeCov …) = 0` (already banked), so no `γ₀ > 0` can satisfy it at
`Bt = 1`. This is the S82 garbage substitution demonstrating `u1_coercivity`'s hypothesis is
substantive: the theorem is not "true for any `C`" — dropping `IsBalabanReparam` makes it false. -/
theorem u1_conclusion_fails_for_windC {Lat : PeriodicLatticeExtent} (μ0 : Fin 3) :
    ¬ (∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ Bt : ℝ,
        γ₀ * ‖Bt‖ ^ 2 ≤
          deltaKQuadFormCorrected (trivialU (L := Lat)) (bondFnL2Equiv Lat (windC Lat μ0 Bt))) := by
  rintro ⟨γ₀, hγ₀, hBt⟩
  have h1 := hBt 1
  have hbeq : bondFnL2Equiv Lat (windC Lat μ0 1) = windingModeCov Lat μ0 := by
    rw [windC_apply]; simp
  rw [hbeq, deltaKQuadFormCorrected_trivialU_windingModeCov_eq_zero] at h1
  simp at h1
  linarith

#print axioms u1_conclusion_fails_for_windC

/-! ## §5 — S92 elaborated-type check: `γ₀` bound strictly before `∀ Bt` -/

#check @u1_coercivity
-- Elaborated (reproduced verbatim in `U1_COERCIVITY.md`):
-- ∀ {Lat} {Btilde} [NormedAddCommGroup Btilde] [InnerProductSpace ℝ Btilde]
--   (C : Btilde →L[ℝ] BondFnL2 Lat) (Mα₀thresh : ℝ),
--   0 < Mα₀thresh → IsBalabanReparam Mα₀thresh C →
--     ∃ γ₀, 0 < γ₀ ∧ ∀ (Bt : Btilde), γ₀ * ‖Bt‖ ^ 2 ≤ deltaKQuadFormCorrected trivialU (bondFnL2Equiv Lat (C Bt))
-- `∃ γ₀` prints strictly before `∀ (Bt : Btilde)` — S92 satisfied.

end AdalyFormal.Balaban.U1Coercivity
