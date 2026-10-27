/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import SchurFloor

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

/-!
# `SchurComposed.lean` — THE READING-A RE-WIRING, INSTANTIATED ON THE PRINTED CARRIER

`SchurFloor.lean` settles the denotation question (§1 there) and proves the two abstract lemmas.
This module does the one thing that needs the concrete carrier: it plugs
`TerminalCompose.cdc_floor_class_uniform` — the general-`U` covariant Lemma 2.4 brick, on the printed
carrier `ℓ²(Λ̃)` — into the engine's `hpoin` slot, and lands the Schur floor

    ((1/σ²)·gammaBrick ell)·‖B̃‖²  ≤  ⟨C₀B̃, (QG₁Q*)⁻¹ C₀B̃⟩ − a·‖C₀B̃‖²

with NO form comparison between `Δ_j^{cov}` and `D_U^*D_U` anywhere in the derivation, so the proved
adverse ordering `CStarDeltaKCCoercive.deltaJQuadFormCovFaithful_le_dstarDQuadForm` is not consumed.

It is a SEPARATE module for a mechanical reason, disclosed because it changed the file layout: the
composed declaration is elaboration-expensive on `PiLp 2 (fun _ : Bond L => SuTwo)`, and isolating it
keeps the abstract half cheap to re-check.  See `SCOPE.md` §5 item 5.

Read `SchurFloor.lean`'s header for the full scope; all of it is inherited, in particular that
`hcontract` and `hKcurl` are CARRIED and that this is NOT `γ₀ > 0`.
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

variable {Hs P₁ P₂ : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
  [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
  [NormedAddCommGroup P₂] [InnerProductSpace ℝ P₂]

/-! ### §3b — THE COMPOSED STATEMENT ON THE PRINTED CARRIER -/

variable {L : PeriodicLatticeExtent}

/-- **THE LEVEL-1 CURL ENERGY AS A NAMED FUNCTION.**  `curlForm U x = ⟪x, D_U^*D_U x⟫`, which by
`CStarDeltaKCOperator.inner_dstarDCLM_eq_dstarDQuadForm` is the covariant curl energy of `x`.

~~It is a NAMED definition rather than a lambda for a mechanical reason worth recording: passing
the anonymous `fun x => ⟪x, dstarDCLM U x⟫` as the composition's `E` forces HIGHER-ORDER unification
against `E (C₀ w)`, and the elaborator does not terminate on it inside `4·10⁶` heartbeats.~~
**STRUCK 2026-08-12 (S75, retained struck).  THAT DIAGNOSIS WAS WRONG AND IS RECORDED BECAUSE IT WAS
ACTED ON.**  The measured cause of the `whnf`/`isDefEq` non-termination was NOT the anonymous
lambda: it was that `ConstructCDC.cZero U ell Dinv` is a **`→ₗ[ℝ]`**, while the composition's `C₀`
slot was typed **`→L[ℝ]`**, so the elaborator was hunting a coercion between a linear map and a
continuous linear map on the `PiLp 2 (fun _ : Bond L => SuTwo)` carrier.  Naming `E` did not fix it
(two runs at `4·10⁶` heartbeats, both timed out at `whnf`: `logs/SchurFloor.log`,
`logs/SchurComposed.log` of those runs); weakening `C₀` to `→ₗ[ℝ]` fixed it immediately.
The named definition is RETAINED because it is harmless, not because it was the fix.  Nothing
mathematical changes; `curlForm_eq` is `rfl`. -/
noncomputable def curlForm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : BondFnL2 L) : ℝ := (inner ℝ x (dstarDCLM U x) : ℝ)

theorem curlForm_eq (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : BondFnL2 L) : curlForm U x = (inner ℝ x (dstarDCLM U x) : ℝ) := rfl

/-- **THE SCHUR FLOOR ON THE PRINTED CARRIER, GENERAL `U`, WITH NO FORM COMPARISON.**

For every `ell ≥ 2`, every tiled torus, every background `U` with `α₁ ≤ 1/(186·ell³)`, every
covariance datum `D` whose coarse carrier is `BondFnL2 L`, and every `B̃ : ℓ²(Λ̃)`:

    ((1/σ²)·gammaBrick ell) · ‖B̃‖²  ≤  ⟨C₀B̃, (QG₁Q*)⁻¹ C₀B̃⟩ − a·‖C₀B̃‖² .

The right-hand side is `Gamma1Reduction.deltaKQuadForm`, i.e. the source-free part of CMP99b (3.156)
evaluated on the printed subspace's parametrisation.  The general-`U` covariant Lemma 2.4 brick
enters through `hpoin`; `cdc_floor_class_uniform` is applied verbatim.

**THE ADVERSE ORDERING IS NOT CONSUMED.**  `deltaJQuadFormCovFaithful_le_dstarDQuadForm` compares
two forms on the same space; nothing in this derivation compares `Δ_j^{cov}` with `D_U^*D_U`, or
assumes any sign for `deltak_wiring`'s `pinnedT2`.  `TerminalBrick.cdc_covariant_floor_of_T2_nonneg`
— the theorem whose hypothesis G3 shows fails at the printed pinning — is NOT used here; the brick
enters through `cdc_floor_class_uniform`, whose statement mentions no `T2` at all.

**THE THREE CARRIED INPUTS**, none of them proved here:
`hs` (CMP99b (3.128)'s split), `hKcurl` (`Kop = Δ_π + DRD*` dominates the level-0 curl energy),
and `hcontract` (§4). -/
theorem schur_floor_on_printed_carrier {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (a : ℝ) (Kop : Hs →L[ℝ] Hs)
    (hs : IsAQuadSplit D a Kop) (d : Hs →L[ℝ] P₁) (sigsq : ℝ) (hsig : 0 < sigsq)
    (hKcurl : ∀ A : Hs, ‖d A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ))
    (hcontract : ∀ A : Hs, curlForm U (D.Q A) ≤ sigsq * ‖d A‖ ^ 2)
    (w : TildeFn L ell) :
    ((1 / sigsq) * gammaBrick ell) * ‖w‖ ^ 2
      ≤ deltaKQuadForm D a (cZero U ell (dinvC U ell) w) := by
  have hγc : (0 : ℝ) ≤ 1 / sigsq := by positivity
  have hinterp : ∀ v : TildeFn L ell,
      (1 / sigsq) * curlForm U (cZero U ell (dinvC U ell) v)
        ≤ (inner ℝ (solutionOperator D (cZero U ell (dinvC U ell) v))
            (Kop (solutionOperator D (cZero U ell (dinvC U ell) v))) : ℝ) := fun v =>
    interp_of_energy_contraction D Kop d (curlForm U) sigsq hsig
      hcontract hKcurl (cZero U ell (dinvC U ell) v)
  have hpoin : ∀ v : TildeFn L ell, gammaBrick ell * ‖v‖ ^ 2
      ≤ curlForm U (cZero U ell (dinvC U ell) v) :=
    fun v => cdc_floor_class_uniform hell2 hstrict hdvd U hthr v
  exact gamma_floor_of_interp_and_weakPoincare (W := TildeFn L ell) D a (1 / sigsq)
    (gammaBrick ell) Kop hs (cZero U ell (dinvC U ell)) (curlForm U) hγc hinterp hpoin w

/-- **THE COMPOSED CONSTANT IS STRICTLY POSITIVE**, and bounded below by an explicit rational once
`σ²` is: `gammaBrick ell ≥ 1/(345960·ell⁶)` (`TerminalCompose.gammaBrick_lower`, cited). -/
theorem schur_floor_constant_pos {ell : ℕ} (hell : 0 < ell) (sigsq : ℝ) (hsig : 0 < sigsq) :
    0 < (1 / sigsq) * gammaBrick ell
    ∧ (1 / sigsq) * (1 / (345960 * (ell : ℝ) ^ 6)) ≤ (1 / sigsq) * gammaBrick ell := by
  refine ⟨by have := gammaBrick_pos hell; positivity, ?_⟩
  exact mul_le_mul_of_nonneg_left (gammaBrick_lower hell) (by positivity)

/-- **THE SAME, WITH THE CHAIN-MAP HYPOTHESES IN PLACE OF `hcontract`** — so a reader holding
`(C)`+`(N)` for Bałaban's `Q_j(U)` can enter directly, without restating anything.  `E` is pinned to
`fun B => ‖d₁ B‖²`, so this version additionally requires the coarse coboundary as a CLM. -/
theorem schur_floor_on_printed_carrier_of_chain {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (a : ℝ) (Kop : Hs →L[ℝ] Hs)
    (hs : IsAQuadSplit D a Kop) (d : Hs →L[ℝ] P₁) (d₁ : BondFnL2 L →L[ℝ] P₂) (S : P₁ →L[ℝ] P₂)
    (σ : ℝ) (hσ : 0 < σ)
    (hchain : ∀ A : Hs, d₁ (D.Q A) = S (d A)) (hS : ∀ f : P₁, ‖S f‖ ≤ σ * ‖f‖)
    (hKcurl : ∀ A : Hs, ‖d A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ))
    (hcurlEq : ∀ x : BondFnL2 L, curlForm U x = ‖d₁ x‖ ^ 2)
    (w : TildeFn L ell) :
    ((1 / σ ^ 2) * gammaBrick ell) * ‖w‖ ^ 2
      ≤ deltaKQuadForm D a (cZero U ell (dinvC U ell) w) := by
  refine schur_floor_on_printed_carrier hell2 hstrict hdvd U hthr D a Kop hs d (σ ^ 2)
    (by positivity) hKcurl (fun A => ?_) w
  rw [hcurlEq (D.Q A)]
  exact energy_contraction_of_chain D d d₁ S σ hσ.le hchain hS A

/-! ## §4 — WHAT `hcontract` SAYS, IN THE TREE'S OWN VOCABULARY, AND WHY `stokes_flat` IS NOT IT

Instantiated at the composed theorem, `hcontract` reads

    ⟪Q A, (D_U^*D_U) (Q A)⟫_{level 1}  ≤  σ² · ‖d A‖²_{level 0}         for all `A : Hs`,

i.e. **the covariant curl energy of the block average is at most `σ²` times the covariant curl energy
of the fine field**.  That is the mathematics of `[STOKES-COMM-U]`, in quadratic-form shape.

`Balaban/ThirdLevelStokes.lean`'s `stokes_flat` proves the exact chain identity — but between
`Bond L` and `CoarseBond L ell`, i.e. between LEVEL 1 and LEVEL 2, whereas `hcontract` is between
LEVEL 0 and LEVEL 1.  To move it one level down one needs the rescaling identification
`CoarseBond L ell ≃ Bond L'` for the rescaled extent, which is the tree's `Ū^j`/`Q_j(U)` gap
(`compute/terminal_compose/DAG.md` row G14).  **`stokes_flat` is therefore not `hcontract`, and this
module does not cite it as if it were.**

`compute/schur_floor/stage/CoarseCurlContraction.lean` builds the level-1→level-2 statement — the
same inequality at the pair of levels the tree can express — so that what `hcontract` asserts is a
proved theorem somewhere and not an unexamined room (LAW-14).

The other two carried inputs, for the record:

* `hKcurl` — `‖dA‖² ≤ ⟨A,KopA⟩` for `Kop = Δ_π + DRD*`.  Immediate once `d` is `Δ_π`'s coboundary,
  since `⟨A,KopA⟩ = ‖dA‖² + ‖RD*A‖²`; it is carried rather than proved because `Kop` is abstract
  here, exactly as in `Gamma1ChainMap`.
* `hs` — CMP99b (3.128)'s split.  `Gamma1Reduction` §2 records that the `a` in it is the SAME `a`
  (3.156) subtracts, which is why no free constant can tune this statement. -/

/-! ## §5 — NON-VACUITY, AND WHAT IS NOT AVAILABLE

Three separate facts.  The third is a negative one and is stated with the same force as the first
two. -/

/-- **THE `hpoin` LEG IS NON-VACUOUS AT A CURVED BACKGROUND**, with a STRICTLY POSITIVE left-hand
side on a NAMED nonzero element of the printed carrier.  CITED from
`TerminalCompose.cdc_covariant_floor_nonvacuous_curved`, not rebuilt: this theorem only re-exposes
its first conjunct, which is the one that rules out the degenerate reading `0 ≤ something`. -/
theorem brick_leg_nonvacuous_curved :
    0 < ((1 / 360) * (1 / ((3 : ℕ) : ℝ) ^ 5)
          - 96 * frobSupBond (AdalyFormal.Balaban.CovLemma24Witness.witU
              AdalyFormal.Balaban.CovLemma24Witness.witT) ^ 2)
        * ‖AdalyFormal.Balaban.ConstructCDC.tildeSpike (by norm_num : (2 : ℕ) ≤ 3)
            (AdalyFormal.Balaban.TerminalCompose.witL3_hyps).2‖ ^ 2 :=
  AdalyFormal.Balaban.TerminalCompose.cdc_covariant_floor_nonvacuous_curved.1

/-- **JUNK SUBSTITUTION (S82) ON THE COMPOSED STATEMENT.**  At `B̃ = 0` both sides vanish, so the
`w = 0` instance of `schur_floor_on_printed_carrier` carries no information and must never be quoted
as content.  `brick_leg_nonvacuous_curved` supplies the non-degenerate point on the `hpoin` leg. -/
theorem schur_floor_junk_at_zero {ell : ℕ} (sigsq : ℝ) :
    ((1 / sigsq) * gammaBrick ell) * ‖(0 : TildeFn L ell)‖ ^ 2 = 0 := by
  simp

/-- **CONTROL — the composed constant is DESTROYED by a bad `σ²`, so `hsig` is load-bearing.**  At
`σ² = 0` Lean's junk convention gives `1/0 = 0` and the whole constant collapses to `0`, making the
conclusion the empty `0 ≤ Φ_a`.  Recorded as a theorem so no reader takes the composed floor as
positive without a positive `σ²` in hand. -/
theorem schur_floor_constant_vanishes_at_sigsq_zero {ell : ℕ} :
    (1 / (0 : ℝ)) * gammaBrick ell = 0 := by simp

#print axioms curlForm
#print axioms curlForm_eq
#print axioms schur_floor_on_printed_carrier
#print axioms schur_floor_constant_pos
#print axioms schur_floor_on_printed_carrier_of_chain
#print axioms brick_leg_nonvacuous_curved
#print axioms schur_floor_junk_at_zero
#print axioms schur_floor_constant_vanishes_at_sigsq_zero

end AdalyFormal.Balaban.SchurFloor
