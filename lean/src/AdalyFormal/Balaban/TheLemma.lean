/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DeltaKFull
import AdalyFormal.Balaban.HarmonicModes
import AdalyFormal.Migration.CMP96Lemma24Farkas

set_option autoImplicit false

/-!
# THE LEMMA — CMP99b p.428, verbatim: `C*Δ_kC` positive definite with `γ₀` independent of `k`, `U`

## ⚠⚠ BANNER (2026-07-28) — `theLemma_C_star_Delta_k_C_uniform` (§2) IS FALSE AS WRITTEN, AND ITS
## `sorry` IS UNFILLABLE. IT HAS **TWO** INDEPENDENT DEFECTS. DO NOT BUILD ON IT.

**DEFECT 1 — the caller-supplied threshold** (kernel-checked,
`compute/sorry_triage/probe_lemma_refutation.lean`, `sorry`-free refutation + a typechecking `False`
same-`Prop` check that applies §2 BY NAME). `Mα₀thresh` is an ARGUMENT constrained only by
`0 < Mα₀thresh`, so a consumer may choose it above `2‖suTwoWitness‖`, where `IsRegular U Mα₀` holds
for EVERY `U` (`RMap` is an isometry) — the regularity hypothesis is vacuous and banked spike facts
refute the conclusion. Bałaban's *"`Mα₀` sufficiently small"* is never encoded. See §2's own
docstring for the precise scope.

**DEFECT 2 — `IsRegular` ITSELF, and it SURVIVES the repair of Defect 1** (kernel-checked,
`Balaban/TheLemmaRepaired.lean`, `coercThresholdBoundAtSpikeC_false`, `sorry`-free). Binding the
threshold inside the theorem is NOT sufficient. `NormalizedCounterexampleSearch.centralHolonomyU`
(`negOneElem = -1` on one bond) is `IsRegular` at `Mα₀ = 0` because `Ad(-1) = id`, so it is admitted
at EVERY positive threshold however the theorem chooses it, and
`deltaKQuadFormCorrected centralHolonomyU deltaWitnessConfig = -12`
(`TheLemmaRepaired.deltaKQuadFormCorrected_centralHolonomyU_eq`). **⚠ That numeral is the RAW object's;
on the source-faithful `deltaKQuadFormNormalizedCorrected` it is `-4`
(`NormalizedCounterexampleSearch.central_counterexample_value`) — the refutation survives, only the
magnitude moves. See the S75 note at §11 below.** The refutation there is aimed at
the WEAKEST threshold-bound reading (one lattice, one `C := spikeC`, prover picks both constants)
and the uniform form follows. `IsRegular`'s conviction on this exact `Ad(-1)=id` mechanism is not
new — `Balaban/RegularityHolonomy.lean`'s own header records it from two de-correlated prosecution
families (`compute/kimi_stmt_gate/`, `compute/sol_stmt_gate/`) and builds `IsRegularHolonomy` as the
named fix; what is new is that the conviction is now stated and proved against the THRESHOLD-BOUND
form, so the two defects are independent and both must be repaired.

**DEFECT 2 IS SHARPER STILL: `IsRegular` IS UNUSABLE AT EVERY THRESHOLD, IN BOTH DIRECTIONS AT ONCE.**
`Balaban/LemmaAssembly.isRegular_dichotomy` proves that at `t ≥ 2‖w‖` the predicate is satisfied by
EVERY configuration, and at `t < 2‖w‖` it REJECTS `spikedIdentity` — the identity moved by a one-site
gauge spike, which is `GaugeRegular 0`, i.e. regular by CMP99b (3.35)'s own `∃u` clause at every
`α₀ ≥ 0`. So it is over-STRONG on pure gauges below the ceiling; and by the `centralHolonomyU` result
above it is simultaneously over-WEAK on curvature at those same thresholds. There is no value of the
threshold at which a coercivity statement over `IsRegular` can be both restrictive and true.

**Where to go instead.** `Balaban/TheLemmaRepaired.CoercUniformThresholdBound_gaugeRegular` — the
threshold bound by the statement AND `AlphaAnalyticity.GaugeRegular` (the source's own
existential-gauge clause, gauge-invariant, and the hypothesis the tree's PROVED assembly consumes).
`Balaban/LemmaAssembly.deltaK_gaugeRegular_coercive` already proves the `bondEnergy` form of the
conclusion (`(1/2000)·bondEnergy A ≤ deltaKQuadFormCorrected U A` for every `GaugeRegular 10⁻⁷`
background on `axial ∩ ker Q₂(U)`), and `TheLemmaRepaired.gaugeRegular_hypothesis_is_load_bearing`
proves that hypothesis excludes the counterexample above — so the refutation and the assembly are
consistent and the hypothesis is doing the work. The `IsRegularHolonomy` variant
(`TheLemmaRepaired.CoercUniformThresholdBound_holonomy`, with a proved family-restricted instance
`family_instance_of_repaired_shape`, explicit constant `4 - 2M`, sharp threshold `2`) is a
gauge-INVARIANT alternative that survives the dichotomy's second horn
(`TheLemmaRepaired.pureGauge_isRegularHolonomy_zero`) but is not the source's clause.

⚠ **AND THE GAP NONE OF THIS CLOSES:** every result named above is about
`DeltaKFull.deltaKQuadFormCorrected` = CMP99b p.392 **(3.10)**'s non-recursive `Δ^η`, NOT p.428
**(3.156)**'s recursive `Δ_k`. No bridge exists in this tree. `GOAL_LEMMA.md` §1's lemma is NOT
proved.

**§2 is RETAINED UNREPAIRED here, deliberately (L5: a false statement is never quietly weakened).**
Its `sorry` stays. `theLemma_U1_known_case` (§3) is unaffected: `U` is fixed at `trivialU` there, so
neither defect applies to it.

## ⚠ REPAIR PASS (2026-07-22) — READ THIS FIRST

The prior version of this file (commit `ed2976a3`) stated `theLemma_C_star_Delta_k_C_uniform` and
`theLemma_U1_known_case` with `IsRegular : Config Lat → ℝ → Prop` and `IsBalabanReparam :
(Btilde →L[ℝ] BondFnL2 Lat) → Prop` as **universally-quantified free predicate parameters**. A
theorem `∀ (P : X → Prop), … → Q` must hold for EVERY substitution of `P` — including
`IsRegular := fun _ _ => True`, `IsBalabanReparam := fun _ => True`. Under exactly that
substitution, `compute/pros_thelemma/RefutationWitness.lean`'s `main_hypothesis_alone_gives_false`
derives `False` from the resulting Prop alone, with a clean axiom footprint
(`[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**) — the statement, as typed, was
provably false, using `C := windC` (a rank-`1` map landing on `HarmonicModes.windingModeCov`, a
curl-free-at-`U=1` field this tree already proves is killed by `Δ_k`).

**THE REPAIR, applied here: both predicates are now DEFINITIONS (`IsRegular`, `IsBalabanReparam`
below, §1b/§1c), not theorem parameters.** An adversary can no longer substitute `fun _ _ => True`
for either — they are fixed, named, and their content is proved (not merely asserted) to EXCLUDE
the exact witness that broke the prior version (§5, the adversarial self-check, re-run and now
FAILING to produce a refutation — see `windC_fails_isBalabanReparam`).

* **`IsRegular` (§1b)**: CMP99b p.396 (3.35)/(3.36) is a per-cube, existential
  local-gauge-transformation condition (`corpus/pages/CMP99b_p396.md`, adjudicated) — building the
  cube-class/gauge-transformation geometry itself is out of this file's write-scope and reach (this
  tree's own `Assumptions.lean` already declined to axiomatize this exact sentence, for the same
  reason: "axiomatizing the sentence as printed would silently axiomatize an open research
  problem"). What IS built here, honestly disclosed as a SIMPLIFICATION, is a genuine, non-trivial,
  DEFINED coarse proxy for the same qualitative content ("the gauge field is small"): the adjoint
  displacement `‖R(U(b))·suTwoWitness − suTwoWitness‖` of one FIXED test direction, at every bond
  `b`, bounded by `Mα₀`. This is built ENTIRELY from already-canonical, non-scoped instances
  (`CovariantOperators.RMap`, `SuTwoInner`'s top-level `InnerProductSpace ℝ SuTwo`) — no new norm
  instance, no diamond risk (§0 below explains why the OBVIOUS alternative, a raw `Matrix`-norm
  bound on `U(b) − 1`, was rejected). A genuine positive consequence, checked not assumed: because
  this proxy measures the ADJOINT ACTION rather than distance-from-`1` as a GROUP element, it is
  automatically NOT center-blind (`DeltaKFull.RMap_witnessMElem_ne_id`'s own correction, "a
  background far from the identity is insufficient, the right criterion is `Ad(U)≠id`", is honored
  by construction here, not merely avoided by luck): `U(b) = -1` (central, `Ad(-1)=id`) registers as
  PERFECTLY REGULAR under this definition, correctly.
* **`IsBalabanReparam` (§1c)**: CMP99b p.428 (3.156)/(3.157) defines `C` by "`B = CB̃`... an
  identity operator on almost all bonds, except the bonds `b₀` for which a value `(CB̃)(b₀)` is
  equal to a solution of the equation `(QB)(c)=0`" — i.e. `C`'s image is constructed, bond by bond,
  to solve a gauge-fixing-style constraint, precisely so that the resulting `B` is NOT redundant
  gauge/harmonic content. Building the full `Λ̃`/`Ax(y)`/`B(c)` bond-partition geometry needed to
  construct THE actual `C` is out of this file's write-scope (documented, unchanged from the prior
  version — none of that geometry is built in this tree). What IS built here is the EXACT
  **necessary** consequence of the theorem's own conclusion, extracted honestly rather than
  invented to dodge the counterexample: if `γ₀‖B̃‖² ≤ ⟨CB̃,Δ_k(U)CB̃⟩` for `B̃≠0` at every regular
  `U`, then in particular `Δ_k(U)(CB̃) ≠ 0` for `B̃ ≠ 0` at every regular `U` — and (§5, already
  banked before this repair) `Δ_k(U)` vanishes on a nonzero vector EXACTLY WHEN its covariant curl
  vanishes there (`dstarDQuadForm_vanishes_of_curl_zero` + `deltaPrimeQuadFormTransported`'s
  vanishing at `U=trivialU`), so "the image of `C` contains no nonzero curl-free-at-regular-`U`
  mode" is a genuine, provable-necessary, non-trivial LAW — option (b) of the repair mandate
  ("a structure field with laws ruling out the degenerate instantiations"), not an arbitrary patch.

**What this does NOT claim.** `IsBalabanReparam`'s law is proved NECESSARY (from the theorem's own
conclusion) and proved to correctly EXCLUDE the one witness that is proved to break it
(`windingModeCov` at `U=trivialU`). It is NOT proved SUFFICIENT (i.e. that satisfying this law is
enough to guarantee the positivity bound — that remains the theorem's own `sorry`), and it is NOT
proved to be the actual content of "`B=CB̃`, `(QB)(c)=0`" from source (that full geometric
equivalence needs the unbuilt `Λ̃`/`Ax(y)`/`B(c)` machinery). Both are named residuals, not silently
bridged — unchanged in spirit from the prior version's own disclosure style.

**Non-vacuity, checked (§5b).** The opposite failure mode — repairing a universally-quantified
predicate into an UNSATISFIABLE one, making the theorem vacuously true for a different reason (the
same category of defect as the OLD "`IsRegular := fun _ _ => False`" observation) — is checked
directly: `Btilde := ℝ`, `C := ` a single-bond-spike embedding is exhibited (§5b) satisfying
`IsBalabanReparam` at every threshold, for EVERY `U` (not merely regular ones) — so the repaired
hypothesis is genuinely satisfiable, not vacuous from this direction either.

## THE TARGET, sourced verbatim, dual-adjudicated corpus page

`corpus/pages/CMP99b_p428.md` (adjudicated 2026-07-20, render hash
`128b1172e7090661d2c2ead70d9514244567c17a43c709ff87b18603b3012d54`), the sentence immediately after
eq. (3.158):

> *"It is more convenient to work with the operator `C̃^(k)(Λ)`, because it is defined by a positive
> definite operator `C*Δ_kC` with a lower bound `γ₀ > 0` independent of `k` and `U`. We have proved
> it in [4], Lemma 2.4, for operators with `U=1`. Localizing the operators in `Δ_k` and using the
> methods of Sect. B we can prove it for `C*Δ_kC` with an arbitrary configuration `U` satisfying
> (3.35), (3.36) with `Mα₀` sufficiently small."*

`[4] = CMP96` (`compute/CITATION_AUDIT_CONFIRM.md` B1/B2). CMP96 Lemma 2.4/(2.128) is itself
**ASSERTED NOT DERIVED on CMP96's own page** (`CITATION_AUDIT_CONFIRM.md` B1) — this campaign's own
re-derivation of its missing ARITHMETIC step (not its geometric hypotheses) is
`AdalyFormal.Migration.CMP96Lemma24Farkas.cmp96_lemma24_farkas_torus`, imported here (LAW-19,
consumed, not rebuilt).

`C`, p.428/p.427 (3.155)-(3.157), verbatim: *"Variables `B` depend linearly on `B̃` and we have
`B = CB̃`, where `C` is a linear operator. It is an identity operator on almost all bonds, except the
bonds `b₀` for which a value `(CB̃)(b₀)` is equal to a solution of the equation `(QB)(c)=0`... This
implies that the operator `C` is almost local."* `B̃` ranges over bonds in `Λ̃ = Λ \ (⋃_{y∈Λ'}Ax(y) ∪
⋃_{c∈Λ'}B(c)∩c)` — none of this bond-partition geometry (`Λ̃`, `Ax(y)`, `B(c)`) is built in this
tree; `C` is introduced below as an explicit parameter, its DEFINING LAW now the necessary
consequence described above (§1c), not silently assumed to be anything more specific.

(3.35)/(3.36), `corpus/pages/CMP99b_p396.md` (adjudicated): a per-cube, per-scale existential
gauge-transformation regularity condition parametrized by a number `α₀ > 0` ("`Mα₀` sufficiently
small" is a SEPARATE smallness demand on top of the class itself).

## §0 — WHY NOT A RAW MATRIX NORM ON `U(b) − 1`

The most literal reading of "`|A|` small" would bound `‖(U(b) : Matrix (Fin 2) (Fin 2) ℂ) − 1‖`
directly. This was tried and REJECTED for this file: `Norm (Matrix (Fin 2) (Fin 2) ℂ)` is only
resolvable under `open scoped Matrix.Norms.L2Operator` (`CovariantOperators.lean` §6's own
docstring: Mathlib withholds a default matrix norm, several candidates compete). Re-opening that
scope HERE, in a file that also (transitively, via `SuTwoInner`) has the CANONICAL, non-scoped
`InnerProductSpace ℝ SuTwo` in play, risks exactly the instance-diamond class `CovariantOperators.
lean` §7/`SUTWO_DIAMOND.md` spent an entire repair pass isolating and naming (P3, "a hypothetical
second `NormedAddCommGroup` sourced differently would be a REAL top-level-instance collision").
`IsRegular` below needs NO norm on `SuTwo` itself beyond the one that is ALREADY canonical and
already safely in scope (`SuTwoInner.instNormedAddCommGroupSuTwo`) — it measures the ADJOINT ACTION
`RMap (U b)` applied to a fixed `SuTwo` vector, never a raw `Matrix` norm. This sidesteps the
diamond entirely, at the honestly-disclosed cost of measuring a coarser quantity than `|A|` itself.

## THE QUANTIFIER ORDER — the single most important thing about this file, UNCHANGED by the repair

Bałaban's *"independent of `k` and `U`"* means `γ₀` is bound OUTSIDE `∀k, ∀U`:

    ∃ γ₀ > 0, ∀ (Mα₀ < threshold), ∀ U (IsRegular U Mα₀), ∀ B̃, γ₀‖B̃‖² ≤ ⟨CB̃, Δ_k(U)(CB̃)⟩

**Every theorem below is written with `∃ γ₀` FIRST, exactly once, before any `∀ U`/`∀ B̃`** — this
was re-derived directly from the COMPILED type below (not merely carried over from the prior
docstring), per the dispatch's own mandated self-check. §4 proves, as a genuinely separate PROVED
theorem, that moving `∃ γ₀` to AFTER the quantifiers collapses the claim to bare pointwise
positivity.

## `k`, disclosed as NOT represented — UNCHANGED

This tree's `Δ_k(U)` object (`DeltaKFull.deltaKQuadFormCorrected`) is built at a single,
undifferentiated scale — no `k`-indexed family exists yet. **A concurrent lane
(`DeltaKRecursive.lean`, Sol-graded) additionally found that this tree's `k`-recursion shape does
NOT match CMP99b (3.138)** — so a faithful `k`-uniformity statement is currently unreachable for a
DIFFERENT, independent reason beyond this file's own scope disclosure. The `∀k` quantifier in
Bałaban's sentence is therefore **not represented** below — disclosed, not silently dropped.

## What this file builds

* §1 — `Config`, notation.
* §1b — **`IsRegular`**, a genuine DEFINITION (repair).
* §1c — **`IsBalabanReparam`**, a genuine DEFINITION (repair).
* §1d — **PROXY vs REAL** (this dispatch): CMP99b p.396 (3.35)/(3.36) verbatim + printed page cite;
  the three missing primitives named precisely (gauge-transformation action on `Config Lat`, cube/
  domain geometry, both absent — confirmed by grep, not assumed); Fact I (`exists_gauge_bond_
  vanishes`, a per-bond reading of "exists a gauge" is PROVABLY VACUOUS); Fact II (`diagGroupElem`/
  `diagConfig`, the fixed-vector proxy's zero-locus strictly exceeds the center, quantified against a
  MAXIMAL orthogonal-direction displacement, `diagGroupElem_pauliE2_displacement`). Conclusion:
  PROXY and REAL are, on present earned evidence, INDEPENDENT — `IsRegular`'s definition (§1b) is
  LEFT UNCHANGED, the gap is quantified rather than silently bridged.
* §2 — **THE MAIN LEMMA** (`theLemma_C_star_Delta_k_C_uniform`), the general-`U` target. ~~One
  `sorry`.~~ **One `sorry`, and it is UNFILLABLE: the statement is FALSE AS WRITTEN, kernel-checked
  2026-07-28 (`compute/sorry_triage/probe_lemma_refutation.lean`, `sorry`-free refutation + a
  typechecking `False` same-`Prop` check). See §2's docstring for the precise scope — the defect is
  that "`Mα₀` sufficiently small" is never encoded, so the CALLER picks the threshold and a large
  one
  empties `IsRegular`. The statement is RETAINED unrepaired (L5) and routed to
  statement-prosecution. AND a SECOND, INDEPENDENT defect: `IsRegular` itself, which SURVIVES
  binding the threshold — see the 2026-07-28 banner at the top of this file and
  `Balaban/TheLemmaRepaired.lean`.**
* §2b — `WithLp.toLp 2` bridge lemmas, moved here from `U1Coercivity.lean` §1 for §3's proof.
* §3 — **THE KNOWN `U=1` CASE** (`theLemma_U1_known_case`), CMP96 Lemma 2.4, side-by-side with §2.
  ~~One `sorry`.~~ **PROVED 2026-07-28, `sorry`-free**, by moving `U1Coercivity.u1_coercivity`'s
  proof
  here (statement UNCHANGED, `Prop`-identity machine-checked by `rfl` before the move). ⚠ This is
  BOOKKEEPING, NOT PROGRESS ON THE LEMMA: it bounds p.392's non-recursive `Δ^η`, not p.428's
  recursive
  `Δ_k`, and at `U = 1` reduces to "an injective map on a finite-dimensional space is bounded
  below".
* §4 — S92 CONTRAST: the inner-bound (γ₀-after-the-quantifiers) version, PROVED trivial.
* §5 — S91 FALSIFIABILITY, re-run against the REPAIRED statement: the exact witness that broke the
  prior version (`ContinuousLinearMap.id`, landing on the winding mode) is now PROVED to violate
  `IsBalabanReparam` — the attack no longer succeeds.
* §5b — NON-VACUITY: a genuine, U-INDEPENDENT witness satisfying `IsBalabanReparam` at every
  threshold, confirming the repaired hypothesis is satisfiable, not vacuous from the other
  direction.
* §6 — degeneracy census, updated for the repair.
-/

namespace AdalyFormal.Balaban.TheLemma

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.BondSU2Space
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.DeltaPrime
  AdalyFormal.Balaban.DeltaKFull AdalyFormal.Balaban.HarmonicModes
  AdalyFormal.Balaban.AdmissibleSubspace

/-! ## §1 — `Config`, notation -/

/-- The `SU(2)` link-configuration type this whole chain is built on (`CovariantOperators`'s own
carrier), abbreviated so every theorem signature below reads at the level of Bałaban's own prose. -/
abbrev Config (Lat : PeriodicLatticeExtent) : Type :=
  PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Lat

/-! ## §1b — `IsRegular`, CMP99b p.396 (3.35)/(3.36), NOW A DEFINITION (repair, §0 explains the
proxy chosen and why). -/

/-- **`IsRegular U Mα₀`**: at every bond `b`, the adjoint action `R(U(b))` moves the FIXED test
vector `suTwoWitness` (`CovariantOperators.suTwoWitness`, already proved nonzero) by at most `Mα₀`.
A genuine, checkable, non-trivial DEFINITION — no longer a free parameter an adversary can set to
`fun _ _ => True`. Disclosed SIMPLIFICATION of (3.35)/(3.36): drops the per-cube existential
gauge-transformation structure and the second-derivative bound (3.36) entirely, measuring only a
coarse "how far the adjoint action is from trivial" proxy. `trivialU_isRegular` below confirms the
base case (`U=1`) satisfies this for every `Mα₀ ≥ 0`, consistent with source. -/
def IsRegular {Lat : PeriodicLatticeExtent} (U : Config Lat) (Mα₀ : ℝ) : Prop :=
  ∀ b : Bond Lat, ‖RMap (U b) suTwoWitness - suTwoWitness‖ ≤ Mα₀

/-- **Sanity check: `U = 1` is regular at every nonnegative threshold** — consistent with CMP96
Lemma 2.4's `U=1` case being the base instance this whole apparatus specializes to (§3). -/
theorem trivialU_isRegular {Lat : PeriodicLatticeExtent} {Mα₀ : ℝ} (h : 0 ≤ Mα₀) :
    IsRegular (trivialU (L := Lat)) Mα₀ := by
  intro b
  have h1 : trivialU (L := Lat) b = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := rfl
  rw [h1, RMap_one, LinearMap.id_apply, sub_self, norm_zero]
  exact h

#print axioms trivialU_isRegular

/-! ## §1c — `IsBalabanReparam`, CMP99b p.428 (3.155)-(3.157), NOW A DEFINITION (repair). -/

/-- **`IsBalabanReparam Mα₀thresh C`**: `C` is injective, AND its image contains no nonzero vector
whose covariant curl vanishes at ANY regular `U` (at any sufficiently small threshold `Mα₀thresh`).
This is the exact NECESSARY consequence of the theorem's own conclusion (§0/module docstring): if
`γ₀‖B̃‖² ≤ Δ_k(U)(CB̃)` held for `B̃≠0` at regular `U`, then a fortiori `Δ_k(U)(CB̃) ≠ 0` there, and
(§5's own already-banked facts) `Δ_k(U)` vanishes on a curl-free field. A genuine, checkable
DEFINITION — no longer a free parameter. `windC_fails_isBalabanReparam` (§5) proves the exact
prior counterexample (`C := id`, landing on `windingModeCov`) now VIOLATES this law. -/
def IsBalabanReparam {Lat : PeriodicLatticeExtent}
    {Btilde : Type*} [NormedAddCommGroup Btilde] [InnerProductSpace ℝ Btilde]
    (Mα₀thresh : ℝ) (C : Btilde →L[ℝ] BondFnL2 Lat) : Prop :=
  Function.Injective C ∧
    ∀ Bt : Btilde, Bt ≠ 0 →
      ∀ Mα₀ : ℝ, Mα₀ < Mα₀thresh →
      ∀ U : Config Lat, IsRegular U Mα₀ →
        curlValueCovariant U (bondFnL2Equiv Lat (C Bt)) ≠ 0

/-! ## §1d — PROXY vs REAL: `IsRegular` against CMP99b (3.35)/(3.36) itself, EARNED not elected

**Verbatim source, dual-adjudicated corpus page.** `corpus/pages/CMP99b_p396.md` (adjudicated
2026-07-20, render hash `d0f0d665232fc871e005f2e721ea338e96c1a52763e151c3966bf7fcb47568ec`, printed
page 396, `pdf_page: 8`):

> *"for an arbitrary cube □ of the described above class, and for a configuration U there exists a
> gauge transformation u on □ such that U^u = e^{iηA}, and if the index of □ is j, then*
>
> *|A| < O(1)Mα₀(L^jη)⁻¹, |∇^ηA| < O(1)Mα₀(L^jη)⁻² on □ ... (3.35)*
>
> *|∂^{η*}∂^ηA| < O(1)Mα₀(L^jη)⁻³ on □. (3.36)"*

So (3.35)/(3.36) is: **∃ a gauge transformation `u` defined on the WHOLE cube `□`** (one `u`,
correlating every bond inside `□` simultaneously) such that, in that gauge, the local vector
potential `A` (`U^u = e^{iηA}`, the Lie-algebra exponential parametrization) is small in size
(3.35), first covariant derivative (3.35's second clause), and second covariant derivative (3.36) —
matching the plain-language content CMP109 p.261 gives independently (render
`compute/sol_lemma_gate/renders/CMP109_p261-13.png`, directly image-verified in THIS dispatch, not
merely inherited from a prior claim: *"The regularity means that at least the conditions
(3.35)-(3.38) [13] ... are satisfied, i.e. first order derivatives and the special second order
derivative of a configuration are small"* — `[13] = CMP99b`, confirmed by the same page's reference
list convention used elsewhere in this tree's citation audit).

**Three primitives this needs, their status here checked directly, not assumed:**

1. **`e^{iηA} : 𝔰𝔲(2) → SU(2)`.** AVAILABLE: `NormedSpace.exp`, confirmed by direct `#check`
   (`{𝔸} → [Ring 𝔸] → [TopologicalSpace 𝔸] → [IsTopologicalRing 𝔸] → 𝔸 → 𝔸`), applicable to
   `Matrix (Fin 2) (Fin 2) ℂ` — a genuinely available, not-yet-wired building block.
2. **A gauge-transformation ACTION on `Config Lat`** (`u : PeriodicLatticeSite Lat → SU(2)` acting by
   `(u • U)(b) := u(x)·U(b)·u(y)⁻¹` for `b=(x,y)`). MISSING: `grep -rln "GaugeTransform\|
   gaugeTransform" AdalyFormal/` finds the WORD only in docstring PROSE (`Averaging.lean`,
   `DeltaPrime.lean`, `Lattice/Witness.lean`, `Target/ClayStatement.lean`, others) — never an actual
   Lean `def`/action anywhere in this tree.
3. **The cube-class/domain geometry** (`Ω_j`, `□`, `B^j(Λ_j)`) CMP99b p.396 itself defines. MISSING,
   unchanged from this module's own prior disclosure (§1b/§1c above).

**A literal Lean statement of (3.35)/(3.36) cannot be TYPED in this tree, so no checked `↔`/`→`
against `IsRegular` is directly available.** This is not a bare label: the two results below are the
EARNED evidence (OPS-1) of exactly where and why the two CHEAP shortcuts one might reach for both
fail, using ONLY primitives already in this tree (no new geometry invented, no diamond risked).

### Fact I — a PER-BOND reading of "exists a gauge" is PROVABLY VACUOUS

If "exists a gauge transformation" is (mis)read as one INDEPENDENT pair `(u₁,u₂)` per bond — rather
than Bałaban's actual "one `u` on the WHOLE cube □", tying every bond together — the resulting
existential is content-free: -/

/-- **Every bond value gauges to the identity, always.** Take `u₁ := 1`, `u₂ := U`: `1·U·U⁻¹ = 1`.
So a PER-BOND, uncorrelated reading of "exists a gauge transformation making `A` small" is satisfied
by EVERY `U`, at EVERY threshold — vacuous. -/
theorem exists_gauge_bond_vanishes (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ u1 u2 : Matrix.specialUnitaryGroup (Fin 2) ℂ, u1 * U * u2⁻¹ = 1 :=
  ⟨1, U, by group⟩

#print axioms exists_gauge_bond_vanishes

/-! This is the rigorous reason the module's own disclosed scope limit ("building the cube-class/
gauge-transformation geometry ... is out of this file's reach", §1b/§1c) is a genuine MATHEMATICAL
necessity of the source's own structure, not merely an engineering gap: the CORRELATION of `u` across
many bonds via a single site-indexed map is exactly what supplies (3.35) its content, and that
correlating structure (primitive 2 above) is precisely what is missing. No cheaper, per-bond
substitute is available — `exists_gauge_bond_vanishes` proves any such substitute collapses.

### Fact II — the FIXED-VECTOR proxy does not bound the FULL Lie-algebra element

`IsRegular` tests displacement of ONE fixed direction (`suTwoWitness = SuTwoInner.pauliE3`, CMP99b's
own `E₃ = iσ₃`). (3.35)'s `|A|` bounds the WHOLE Lie-algebra element `A`, in every direction. Below:
a concrete `SU(2)` witness, `diagGroupElem`, for which the proxy gives EXACTLY ZERO displacement
(perfectly regular, at ANY threshold, including `Mα₀ = 0`) while an ORTHOGONAL Pauli direction
(`SuTwoInner.pauliE2 = CovariantOperators.witnessM`, `hsInner`-orthogonal to `pauliE3` via
`SuTwoInner.hsInner_e2_e3`) is displaced by the MAXIMUM a norm-preserving map can produce. -/

theorem suTwoWitnessVal_mem_unitaryGroup : suTwoWitnessVal ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suTwoWitnessVal, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem suTwoWitnessVal_det : suTwoWitnessVal.det = 1 := by
  simp [suTwoWitnessVal, Matrix.det_fin_two_of]

theorem suTwoWitnessVal_mem_specialUnitaryGroup :
    suTwoWitnessVal ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  Matrix.mem_specialUnitaryGroup_iff.mpr ⟨suTwoWitnessVal_mem_unitaryGroup, suTwoWitnessVal_det⟩

/-- **`diagGroupElem`**: the very matrix `suTwoWitnessVal = diag(i,-i)` (already a Lie-algebra
element, §1 above), packaged as a GROUP element (special unitary) — a genuine element of `SU(2)`,
distinct from `1` and from `negOneElem` (below), whose adjoint action fixes `suTwoWitness` EXACTLY
(self-conjugation: any invertible matrix commutes with itself). -/
def diagGroupElem : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨suTwoWitnessVal, suTwoWitnessVal_mem_specialUnitaryGroup⟩

theorem diagGroupElem_ne_one : diagGroupElem ≠ 1 := by
  intro hcontra
  have h : (diagGroupElem : Matrix (Fin 2) (Fin 2) ℂ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    congrArg Subtype.val hcontra
  have h00 := congrFun (congrFun h 0) 0
  simp [diagGroupElem, suTwoWitnessVal] at h00
  norm_num [Complex.ext_iff] at h00

theorem diagGroupElem_ne_negOneElem : diagGroupElem ≠ negOneElem := by
  intro hcontra
  have h : (diagGroupElem : Matrix (Fin 2) (Fin 2) ℂ) = (negOneElem : Matrix (Fin 2) (Fin 2) ℂ) :=
    congrArg Subtype.val hcontra
  have h00 := congrFun (congrFun h 0) 0
  simp [diagGroupElem, suTwoWitnessVal, negOneElem] at h00
  norm_num [Complex.ext_iff] at h00

/-- **`R(diagGroupElem)` fixes `suTwoWitness` EXACTLY** — self-conjugation of `suTwoWitnessVal` by
itself (`X·X·Xᴴ = X` since `Xᴴ = X⁻¹` for unitary `X`, and `X·X·X⁻¹ = X` for any invertible `X`),
verified by direct entrywise matrix computation, matching this file's existing concrete-computation
discipline (never "by linearity"/"by symmetry" alone). -/
theorem RMap_diagGroupElem_suTwoWitness :
    RMap diagGroupElem suTwoWitness = suTwoWitness := by
  apply Subtype.ext
  rw [RMap_coe_apply]
  change suTwoWitnessVal * suTwoWitnessVal * Matrix.conjTranspose suTwoWitnessVal =
    suTwoWitnessVal
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suTwoWitnessVal, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]

/-- **`R(diagGroupElem)` sends the ORTHOGONAL generator `pauliE2` to `-pauliE2`** — the maximal
displacement a norm-preserving involution-like map can produce, by direct entrywise computation. -/
theorem RMap_diagGroupElem_pauliE2 :
    RMap diagGroupElem pauliE2 = -pauliE2 := by
  apply Subtype.ext
  rw [RMap_coe_apply]
  change suTwoWitnessVal * witnessM * Matrix.conjTranspose suTwoWitnessVal = -witnessM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suTwoWitnessVal, witnessM, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_two]

#print axioms suTwoWitnessVal_mem_unitaryGroup
#print axioms suTwoWitnessVal_det
#print axioms suTwoWitnessVal_mem_specialUnitaryGroup
#print axioms diagGroupElem
#print axioms diagGroupElem_ne_one
#print axioms diagGroupElem_ne_negOneElem
#print axioms RMap_diagGroupElem_suTwoWitness
#print axioms RMap_diagGroupElem_pauliE2

/-- The CONSTANT configuration equal to `diagGroupElem` at every bond — "perfectly regular" per the
proxy at threshold `0` (below), a genuinely non-trivial, non-central third witness beyond the
`{trivialU, negOneElem-constant}` pair the §6 census previously discussed. -/
def diagConfig (Lat : PeriodicLatticeExtent) : Config Lat := fun _ => diagGroupElem

/-- **`diagConfig` is `IsRegular`-perfect at threshold `0`.** -/
theorem diagConfig_isRegular {Lat : PeriodicLatticeExtent} {Mα₀ : ℝ} (h : 0 ≤ Mα₀) :
    IsRegular (diagConfig Lat) Mα₀ := by
  intro b
  show ‖RMap diagGroupElem suTwoWitness - suTwoWitness‖ ≤ Mα₀
  rw [RMap_diagGroupElem_suTwoWitness, sub_self, norm_zero]
  exact h

/-- **`diagConfig` is genuinely a DIFFERENT configuration from `trivialU`** (not a relabelling of the
already-known `U=1` case). -/
theorem diagConfig_ne_trivialU {Lat : PeriodicLatticeExtent} (b : Bond Lat) :
    diagConfig Lat b ≠ trivialU (L := Lat) b :=
  diagGroupElem_ne_one

/-- `pauliE2`'s underlying matrix is `witnessM` (`SuTwoInner.pauliE2`'s own definition), which is
nonzero at entry `(0,1)` — proved by direct entry inspection rather than via `hsInner_zero_left`
(defined later in this file, §5, so unavailable to a declaration placed here at §1d). -/
theorem pauliE2_ne_zero : pauliE2 ≠ 0 := by
  intro h
  have hv : (pauliE2 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := congrArg Subtype.val h
  have h01 := congrFun (congrFun hv 0) 1
  simp [pauliE2, witnessM] at h01

/-- **THE HEADLINE GAP, quantified.** On `diagConfig`: the proxy's own test direction is displaced by
EXACTLY `0` (`IsRegular` holds at threshold `0`, `diagConfig_isRegular`), while the ORTHOGONAL
direction `pauliE2` is displaced by `2‖pauliE2‖ ≠ 0` — the FULL swing a norm-preserving involution-
like map can produce. `IsRegular` (the proxy) therefore does NOT bound the adjoint action's effect on
`SuTwo` as a WHOLE (only its projection onto one fixed axis), while (3.35)'s `|A|` bounds the WHOLE
Lie-algebra element. This bound holds REGARDLESS of how the missing cube/gauge-transformation
geometry (Fact I) is eventually built — it is a fact about `RMap`/`SuTwo` alone, already fully in
scope, not contingent on any unbuilt machinery. -/
theorem diagGroupElem_pauliE2_displacement :
    ‖RMap diagGroupElem pauliE2 - pauliE2‖ = 2 * ‖pauliE2‖ := by
  have hval : RMap diagGroupElem pauliE2 - pauliE2 = (-2 : ℝ) • pauliE2 := by
    rw [RMap_diagGroupElem_pauliE2, neg_smul, two_smul]
    abel
  rw [hval, norm_smul]
  simp

theorem diagGroupElem_pauliE2_displacement_ne_zero :
    ‖RMap diagGroupElem pauliE2 - pauliE2‖ ≠ 0 := by
  rw [diagGroupElem_pauliE2_displacement]
  intro h
  apply pauliE2_ne_zero
  have hn : ‖pauliE2‖ = 0 := by linarith [norm_nonneg pauliE2]
  exact norm_eq_zero.mp hn

#print axioms diagConfig
#print axioms diagConfig_isRegular
#print axioms diagConfig_ne_trivialU
#print axioms pauliE2_ne_zero
#print axioms diagGroupElem_pauliE2_displacement
#print axioms diagGroupElem_pauliE2_displacement_ne_zero

/-! ### CONCLUSION: on present, EARNED evidence, PROXY and (3.35)/(3.36) are INDEPENDENT

Neither direction survives:

* **REAL ⇏ PROXY.** Fact I shows the only per-bond content available is vacuous: ANY `U(b)` gauges to
  `A=0` this way, so a per-bond real-condition reading certifies EVERY configuration, including ones
  the proxy correctly flags as irregular (e.g. `CovariantOperators.witnessMElem`, displacement
  `2‖pauliE3‖ ≠ 0`, already banked as `RMap_witnessMElem`/`RMap_witnessMElem`-adjacent facts in
  `CovariantOperators.lean`). The genuine, multi-bond real condition cannot even be TYPED here
  (primitives 2/3 above are absent), so no implication against IT is mechanically checkable; what IS
  checkable — the vacuous per-bond stand-in — does not imply the proxy.
* **PROXY ⇏ REAL.** Fact II shows the proxy's zero-locus is not confined to `{1, negOneElem}` but
  contains at least the whole family commuting with `suTwoWitnessVal` (`diagGroupElem` is one
  genuinely non-trivial, non-central member: `diagGroupElem_ne_one`, `diagGroupElem_ne_negOneElem`),
  while on that SAME configuration the orthogonal Lie-algebra direction is displaced MAXIMALLY. Any
  faithful reading of "`|A|` small" (bounding the WHOLE Lie-algebra element, as (3.35) literally
  states) would correctly flag `diagConfig` as NOT small in the `pauliE2` direction; `IsRegular` does
  not detect this.

**Named residual, precisely** (earned, not elected — Facts I/II are the evidence, not a bare label).
Closing this gap for real needs (i) the gauge-transformation action on `Config Lat` (absent, primitive
2), (ii) the cube/domain geometry `Ω_j`/`□` (absent, primitive 3) — both out of this file's
write-scope and reach, as §1b/§1c already disclosed — PLUS, now shown by Fact I, the recognition that
even a much CHEAPER per-bond stand-in for the gauge-existential collapses to vacuous truth, so no
"cheap" substitute closes the gap either: the full multi-bond apparatus is not an optional
simplification, it is what gives (3.35) its content at all. The proxy is LEFT IN PLACE
(`IsRegular`'s definition, §1b, is UNCHANGED by this section) — replacing it with either of the cheap
shortcuts examined here would either make the theorem vacuous (Fact I direction) or silently drop the
multi-directional content (3.35) demands (Fact II direction), which would be a WORSE defect than the
disclosed proxy gap this section quantifies. -/

/-! ## §2 — THE MAIN LEMMA -/

/-- **THE LEMMA — CMP99b p.428, general `U`.**

`Btilde`/`C` model Bałaban's reparametrization `B = CB̃` (p.428/(3.155)-(3.157)): `Btilde` is the
(unbuilt) `Λ̃`-bond coordinate space, `C : Btilde →L[ℝ] BondFnL2 Lat` the (unbuilt) reparametrization
map. `IsBalabanReparam`/`IsRegular` are now genuine DEFINITIONS (§1b/§1c), not free parameters.

**The quantifier order is the content**: `γ₀` is chosen ONCE, before `Mα₀`, `U`, and `B̃` are
quantified — so the SAME `γ₀` must work at every sufficiently-small `Mα₀`, every regular `U`, and
every `B̃`. Moving `γ₀` after these quantifiers is a DIFFERENT, TRIVIAL claim (§4).

⚠ **THIS `sorry` IS UNFILLABLE: THE STATEMENT BELOW IS FALSE AS WRITTEN, KERNEL-CHECKED
2026-07-28.**
Recorded here as a FACT; the statement is NOT repaired or weakened (L5) and the `sorry` is RETAINED.
Prior to this the tree asserted the falsity only in PROSE
(`NormalizedCounterexampleSearch.lean:45-52`,
"ALREADY known false"), with no `sorry`-free declaration anywhere refuting it, and
`compute/FINISH_LIST.md` listed it as plain open mathematics.

The refutation is `compute/sorry_triage/probe_lemma_refutation.lean` (`probe_refut4.log`, `EXIT=0`;
`theLemma_conclusion_false_at_spikeC : [propext, Classical.choice, Quot.sound]`, i.e. `sorry`-free),
assembled entirely from already-banked facts:
* `spikeC` + `spikeC_satisfies_isBalabanReparam` (§5b, this file) supply `hC` at EVERY threshold;
* `spikeSite = witnessY` (proved by `rfl` on the coordinate function), hence
  `singleBondSpike = DeltaPrime.deltaWitnessConfig`, hence
  `bondFnL2Equiv witnessL (spikeC 1) = deltaWitnessConfig`;
* `NormalizationAudit.deltaKQuadFormCorrected_witnessU_deltaWitnessConfig_eq_neg_four` gives the
value
  `-4 < 0`, so no `γ₀ > 0` survives at `B̃ = 1`;
* `IsRegular witnessU Mα₀` is available because `RMap` is an isometry (`SuTwoInner.RIsometry`), so
  `IsRegular U (2‖suTwoWitness‖)` holds for **EVERY** `U` whatsoever — the regularity hypothesis is
  VACUOUS at any threshold above `2‖suTwoWitness‖`.
The decisive same-`Prop` check (`ForcedIntersection` pattern) is in that probe: applying THIS
declaration by name at `C := spikeC`, `Mα₀thresh := 2‖suTwoWitness‖ + 1` to the refutation yields
`False`, and it TYPECHECKS — so the refuted `Prop` is this declaration's own, not a look-alike.

**PRECISE SCOPE — what is and is NOT refuted** (two must-fail controls fire,
`probe_refut_control.log`): FALSE is the LEAN STATEMENT, in which `Mα₀thresh` is a caller-supplied
ARGUMENT constrained only by `0 < Mα₀thresh`; it fails for every `Mα₀thresh > 2‖suTwoWitness‖`. NOT
refuted is Bałaban's intended claim, which is EXISTENTIAL in the threshold ("`Mα₀` sufficiently
small") — `witnessU_not_isRegular_of_lt` proves this witness is unavailable below
`2‖suTwoWitness‖`. **The defect is therefore that "sufficiently small" is never encoded**: the
caller
picks the threshold, and a large one empties `IsRegular`. Routed to statement-prosecution.

⚠ **SECOND, INDEPENDENT DEFECT (2026-07-28) — `IsRegular` ITSELF. Binding the threshold does NOT
rescue this statement.** `Balaban/TheLemmaRepaired.lean` states the threshold-bound form (`∃
Mα₀thresh > 0, ∃ γ₀ > 0, ∀ …`, both constants outside `Lat`, `C`, `Mα₀`, `U`, `B̃`) and refutes it
`sorry`-free (`coercThresholdBoundAtSpikeC_false`, and `thresholdBound_isRegular_false` for the
`∀C`-uniform form): `centralHolonomyU` is `IsRegular` at `Mα₀ = 0` (`Ad(-1) = id`), so it is
admitted at EVERY threshold the theorem could pick, and
`deltaKQuadFormCorrected centralHolonomyU deltaWitnessConfig = -12`.

**⚠ NUMERAL IS THE RAW OBJECT'S — MAIN-LOOP NOTE 2026-07-28 (S75; the VERDICT is unaffected).** `-12`
is the value on `deltaKQuadFormCorrected`, which a grade-3 finding (blind Sol + blind Kimi + verified)
established is **not** CMP99b (3.10): it adds a `tr 1 = 1`-normalized `D*D` leg to an unnormalized
`Δ′` leg, so its `Δ′` is exactly TWICE the source's. On the faithful
`NormalizationAudit.deltaKQuadFormNormalizedCorrected` the value is **`-4`**
(`NormalizedCounterexampleSearch.central_counterexample_value`). **The refutation SURVIVES** — it lives
at a sign, not a magnitude — so only the numeral moves, never the verdict. Do not quote `-12` as the
size of the defect on the source's operator.

The scope note above ("NOT
refuted: Bałaban's intended claim, which is EXISTENTIAL in the threshold") is therefore CORRECT
ONLY about Bałaban's (3.35)/(3.36) class — it is NOT correct about the existential-threshold form of
THIS statement with THIS `IsRegular`, which is now refuted. `IsRegularHolonomy`
(`Balaban/RegularityHolonomy.lean`) rejects `centralHolonomyU` at every threshold `< 8` and the same
route becomes PROVABLE on the single-bond family under it
(`TheLemmaRepaired.holonomy_thresholdBound_holds_on_family`).

The refutation could not be placed in this file: `NormalizationAudit` is NOT in this module's
17-module import closure (measured), so it needs a module importing both — e.g.
`NormalizedCounterexampleSearch.lean`, which already imports `NormalizationAudit` + `TheLemma`. -/
theorem theLemma_C_star_Delta_k_C_uniform
    {Lat : PeriodicLatticeExtent}
    {Btilde : Type*} [NormedAddCommGroup Btilde] [InnerProductSpace ℝ Btilde]
    (C : Btilde →L[ℝ] BondFnL2 Lat)
    (Mα₀thresh : ℝ) (hMα₀thresh_pos : 0 < Mα₀thresh)
    (hC : IsBalabanReparam Mα₀thresh C) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ Mα₀ : ℝ, Mα₀ < Mα₀thresh →
      ∀ U : Config Lat, IsRegular U Mα₀ →
      ∀ Bt : Btilde,
        γ₀ * ‖Bt‖ ^ 2 ≤ deltaKQuadFormCorrected U (bondFnL2Equiv Lat (C Bt)) := by
  sorry

#print axioms theLemma_C_star_Delta_k_C_uniform

/-! ## §2b — `WithLp.toLp 2` bridge lemmas, needed by §3's proof.

MOVED HERE, not rebuilt (LAW-19): these three are `U1Coercivity.lean` §1's lemmas verbatim. They had
to live there only because §3 below used to be a `sorry` and the proof was written in a downstream
module; now that §3 is proved here, this is their home and `U1Coercivity.lean` re-exports them.
`bondFnL2Equiv Lat := WithLp.linearEquiv 2 ℝ (Bond Lat → SuTwo)` (`BondSU2Space.lean`), so its
`.symm`
IS `WithLp.toLp 2` (Mathlib `WithLp.coe_symm_linearEquiv`). -/

/-- `WithLp.toLp 2 (bondFnL2Equiv Lat X) = X` — `bondFnL2Equiv` and `WithLp.toLp 2` are mutually
inverse on `BondFnL2 Lat`, by definition of `bondFnL2Equiv` (`BondSU2Space.lean`). -/
theorem toLp_bondFnL2Equiv_eq {Lat : PeriodicLatticeExtent} (X : BondFnL2 Lat) :
    WithLp.toLp 2 (bondFnL2Equiv Lat X) = X := by
  show WithLp.toLp 2
    ((WithLp.linearEquiv 2 ℝ (AdalyFormal.Balaban.AdmissibleSubspace.Bond Lat → SuTwo)) X) = X
  rw [← WithLp.coe_symm_linearEquiv (p := 2) (K := ℝ)
    (V := AdalyFormal.Balaban.AdmissibleSubspace.Bond Lat → SuTwo)]
  exact LinearEquiv.symm_apply_apply _ X

/-- `WithLp.toLp 2 : V → WithLp 2 V` is injective, for ANY `V` — it is literally
`(WithLp.linearEquiv 2 ℝ V).symm`, an equiv. -/
theorem toLp_injective {V : Type*} [AddCommGroup V] [Module ℝ V] :
    Function.Injective (WithLp.toLp 2 : V → WithLp 2 V) := by
  have heq : (WithLp.toLp 2 : V → WithLp 2 V) = ⇑(WithLp.linearEquiv 2 ℝ V).symm := by
    rw [WithLp.coe_symm_linearEquiv]
  rw [heq]
  exact (WithLp.linearEquiv 2 ℝ V).symm.injective

/-- `WithLp.toLp 2 0 = 0` — the same equiv preserves zero. -/
theorem toLp_zero {V : Type*} [AddCommGroup V] [Module ℝ V] :
    (WithLp.toLp 2 (0 : V) : WithLp 2 V) = 0 := by
  have heq : (WithLp.toLp 2 : V → WithLp 2 V) = ⇑(WithLp.linearEquiv 2 ℝ V).symm := by
    rw [WithLp.coe_symm_linearEquiv]
  rw [heq]
  exact map_zero _

#print axioms toLp_bondFnL2Equiv_eq
#print axioms toLp_injective
#print axioms toLp_zero

/-! ## §3 — THE KNOWN `U=1` CASE, CMP96 Lemma 2.4/(2.128), side by side -/

/-- **THE KNOWN CASE — CMP96 Lemma 2.4, `U = 1` (`DeltaPrime.trivialU`).**

Exactly `theLemma_C_star_Delta_k_C_uniform`'s statement with `U` FIXED at `trivialU` (so `∀Mα₀,
∀U, IsRegular U Mα₀ →` is gone entirely) — visibly "the same statement" as §2, differing only in
whether `U` is fixed or universally quantified over the regular class. Bałaban's own text: *"We
have proved it in [4], Lemma 2.4, for operators with `U=1`."* Reuses the SAME `IsBalabanReparam`
definition as §2 (the same `C` should satisfy the same reparametrization law regardless of which
`U` the conclusion is specialized to).

**Disclosed type-level gap.** `Migration.CMP96Lemma24Farkas.cmp96_lemma24_farkas_torus` is this
campaign's own re-derivation of CMP96 Lemma 2.4/(2.128)'s missing ARITHMETIC step — but it is
stated over FIVE OPAQUE REAL NUMBERS with no lattice/bond/gauge-field type anywhere in its
signature. It is therefore NOT literally an instance of the theorem below; this is a named
residual, not silently bridged, unchanged from the prior version.

**PROVED 2026-07-28 (`compute/sorry_triage/`). ~~`sorry`~~ — the statement below is UNCHANGED,
not one
character of it was edited; only the `by sorry` was replaced by the proof.** The proof is
`U1Coercivity.u1_coercivity`'s, MOVED here (that module's only `import` is this file, so every lemma
it used was already in scope here; it kept the proof downstream solely because this declaration
was a
`sorry` and consuming it here would have cycled). `U1Coercivity.u1_coercivity` is now a re-export of
this theorem. The `Prop`-identity was machine-checked BEFORE the move:
`@theLemma_U1_known_case = @U1Coercivity.u1_coercivity := rfl` elaborated
(`compute/sorry_triage/probe_pass.log`), with two must-fail controls firing
(`probe_mustfail.log`): a purpose-built near-miss carrying the SAME conclusion plus ONE extra
hypothesis, and the general-`U` §2 statement.

⚠ **THE CAVEAT THAT TRAVELS WITH THE PROOF — this closure is BOOKKEEPING, NOT PROGRESS ON THE
LEMMA.**
`deltaKQuadFormCorrected` is CMP99b p.392 (3.10)'s **unsubscripted, non-recursive `Δ^η`**, NOT
p.428 (3.156)'s recursive `Δ_k`; at `U = 1` these are genuinely different operators and no bridge
between them exists anywhere in this tree. And once `Δ′` is deleted at `trivialU` the content is
exactly *"an injective linear map on a finite-dimensional space has a positive lower singular-value
bound"* — no momentum diagonalisation, no CMP95 (1.66), no CMP89 Lemma 2.4, no scale recursion, no
regular-background estimate. `IsBalabanReparam` is likewise a proxy, not a proof that Bałaban's
actual
reparametrization satisfies it. See `U1Coercivity.lean`'s header for the full Sol-gate scoping. -/
theorem theLemma_U1_known_case
    {Lat : PeriodicLatticeExtent}
    {Btilde : Type*} [NormedAddCommGroup Btilde] [InnerProductSpace ℝ Btilde]
    (C : Btilde →L[ℝ] BondFnL2 Lat)
    (Mα₀thresh : ℝ) (hMα₀thresh_pos : 0 < Mα₀thresh)
    (hC : IsBalabanReparam Mα₀thresh C) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ Bt : Btilde,
        γ₀ * ‖Bt‖ ^ 2 ≤
          deltaKQuadFormCorrected (trivialU (L := Lat)) (bondFnL2Equiv Lat (C Bt)) := by
  -- `Btilde` is automatically finite-dimensional: `C` is injective into the finite-dim `BondFnL2
  -- Lat`.
  haveI : FiniteDimensional ℝ Btilde := FiniteDimensional.of_injective C.toLinearMap hC.1
  -- The composed map `Bt ↦ curlCovariantCLM_L2 trivialU (C Bt)`.
  set Lmap : Btilde →ₗ[ℝ] AdalyFormal.Balaban.CovariantHjMinimizer.PlaqFnL2 Lat :=
    (curlCovariantCLM_L2 (trivialU (L := Lat))).toLinearMap ∘ₗ C.toLinearMap with hLdef
  have hLapply : ∀ Bt : Btilde, Lmap Bt = curlCovariantCLM_L2 (trivialU (L := Lat)) (C Bt) :=
    fun _ => rfl
  -- `Lmap` is injective: `IsBalabanReparam`'s curl-nonvanishing clause, at `U = trivialU`, `Mα₀
  -- = 0`.
  have hLinj : Function.Injective Lmap := by
    intro x y hxy
    by_contra hne
    have hne' : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hcurl := hC.2 (x - y) hne' 0 hMα₀thresh_pos (trivialU (L := Lat))
      (trivialU_isRegular (le_refl (0 : ℝ)))
    apply hcurl
    have hLsub : Lmap (x - y) = 0 := by
      have hz : Lmap x - Lmap y = 0 := sub_eq_zero.mpr hxy
      rwa [← map_sub] at hz
    rw [hLapply] at hLsub
    have hCeq : C (x - y) = WithLp.toLp 2 (bondFnL2Equiv Lat (C (x - y))) :=
      (toLp_bondFnL2Equiv_eq (C (x - y))).symm
    rw [hCeq, curlCovariantCLM_L2_toLp] at hLsub
    exact toLp_injective (hLsub.trans toLp_zero.symm)
  have hker : LinearMap.ker Lmap = ⊥ := LinearMap.ker_eq_bot.mpr hLinj
  -- Injective + finite-dimensional domain ⇒ anti-Lipschitz (Mathlib, no hand-rolled compactness).
  obtain ⟨K, hKpos, hAnti⟩ := LinearMap.exists_antilipschitzWith Lmap hker
  refine ⟨(K : ℝ)⁻¹ ^ 2, by positivity, ?_⟩
  intro Bt
  have hbound : ‖Bt‖ ≤ (K : ℝ) * ‖Lmap Bt‖ := ZeroHomClass.bound_of_antilipschitz Lmap hAnti Bt
  have hKrealpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hKne : (K : ℝ) ≠ 0 := hKrealpos.ne'
  have hnn : (0 : ℝ) ≤ ‖Bt‖ := norm_nonneg _
  have hsq : ‖Bt‖ ^ 2 ≤ (K : ℝ) ^ 2 * ‖Lmap Bt‖ ^ 2 := by
    have hmm := mul_le_mul hbound hbound hnn (by positivity)
    calc ‖Bt‖ ^ 2 = ‖Bt‖ * ‖Bt‖ := sq ‖Bt‖
      _ ≤ (K : ℝ) * ‖Lmap Bt‖ * ((K : ℝ) * ‖Lmap Bt‖) := hmm
      _ = (K : ℝ) ^ 2 * ‖Lmap Bt‖ ^ 2 := by ring
  have hstep : (K : ℝ)⁻¹ ^ 2 * ‖Bt‖ ^ 2 ≤ ‖Lmap Bt‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ (K : ℝ)⁻¹ ^ 2)
    have hcalc : (K : ℝ)⁻¹ ^ 2 * ((K : ℝ) ^ 2 * ‖Lmap Bt‖ ^ 2) = ‖Lmap Bt‖ ^ 2 := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hKne, one_pow, one_mul]
    rwa [hcalc] at hmul
  have h1 : Lmap Bt =
      curlCovariantCLM_L2 (trivialU (L := Lat)) (WithLp.toLp 2 (bondFnL2Equiv Lat (C Bt))) := by
    rw [hLapply, toLp_bondFnL2Equiv_eq]
  have hLnorm : ‖Lmap Bt‖ ^ 2
      = dstarDQuadForm (trivialU (L := Lat)) (bondFnL2Equiv Lat (C Bt)) := by
    rw [h1]
    exact norm_sq_curlCovariantCLM_L2_eq_dstarDQuadForm (trivialU (L := Lat))
      (bondFnL2Equiv Lat (C Bt))
  rw [hLnorm] at hstep
  unfold deltaKQuadFormCorrected
  rw [deltaPrimeQuadFormTransported_vanishes_at_trivial]
  linarith

#print axioms theLemma_U1_known_case

/-! ## §4 — S92 CONTRAST: the inner-bound (`γ₀` moved after the quantifiers) version is TRIVIAL,
PROVED, not merely asserted. UNCHANGED by the repair (no reference to `IsRegular`/`IsBalabanReparam`). -/

/-- **The trivial alternative reading, made precise and PROVED.** If `γ₀` were bound AFTER `U`/`B̃`
(`∀ U, ∀ B̃ ≠ 0, ∃ γ₀ > 0, ...`) the claim would reduce to bare POINTWISE positivity of the
quadratic form — true for ANY nonzero-valued point of ANY positive functional whatsoever, with NO
reference to `Δ_k`, `C`, `U`-uniformity, or regularity of any kind. -/
theorem inner_bound_trivial_given_pointwise_positive
    {V : Type*} [NormedAddCommGroup V] (Q : V → ℝ) (v : V) (hv : v ≠ 0) (hQ : 0 < Q v) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ * ‖v‖ ^ 2 ≤ Q v := by
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hns : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
  refine ⟨Q v / (2 * ‖v‖ ^ 2), by positivity, ?_⟩
  have heq : Q v / (2 * ‖v‖ ^ 2) * ‖v‖ ^ 2 = Q v / 2 := by
    field_simp
  rw [heq]
  linarith

#print axioms inner_bound_trivial_given_pointwise_positive

/-! ## §5 — S91 FALSIFIABILITY, re-run against the REPAIRED statement: the exact witness that broke
the prior version is now PROVED to violate `IsBalabanReparam` -- the attack no longer succeeds.

The first several lemmas below (`hsInner_zero_left` through `contLinId_injective`) are UNCHANGED
facts about the underlying tree objects, carried forward because §5's new headline theorem
(`windC_fails_isBalabanReparam`) is built directly from them. -/

/-- **`hsInner` is zero in its left slot at `0`, for ANY right argument** — the one small
bilinearity fact `dstarDQuadForm_vanishes_on_curl_free` needs, derived (not merely asserted) from
`hsInner_smul_left` at the scalar `0` (`0 • X = 0`, `0 * t = 0`). -/
theorem hsInner_zero_left (Y : SuTwo) : hsInner (0 : SuTwo) Y = 0 := by
  have h := hsInner_smul_left (0 : SuTwo) Y 0
  simpa using h

#print axioms hsInner_zero_left

/-- **`covPlaqInner 0 0 = 0`** — the zero function paired with itself vanishes, directly from
`hsInner_zero_left` applied pointwise, summed over the (possibly empty) plaquette `Fintype`. -/
theorem covPlaqInner_zero_zero {Lat : PeriodicLatticeExtent} :
    covPlaqInner (L := Lat) 0 0 = 0 := by
  unfold covPlaqInner
  apply Finset.sum_eq_zero
  intro p _
  simpa using hsInner_zero_left (0 : SuTwo)

#print axioms covPlaqInner_zero_zero

/-- **`dstarDQuadForm` vanishes on any curl-free field.** -/
theorem dstarDQuadForm_vanishes_of_curl_zero {Lat : PeriodicLatticeExtent} (U : Config Lat)
    (A : Bond Lat → SuTwo) (hcurl : curlValueCovariant U A = 0) :
    dstarDQuadForm U A = 0 := by
  unfold dstarDQuadForm
  rw [hcurl]
  exact covPlaqInner_zero_zero

#print axioms dstarDQuadForm_vanishes_of_curl_zero

/-- **The winding mode's covariant curl is the ZERO FUNCTION at `U = trivialU`** (not merely zero
pointwise at one plaquette) — `funext` over `HarmonicModes.curlValueCovariant_trivialU_
windingModeCov_eq_zero`, which already proves this at EVERY plaquette. -/
theorem curlValueCovariant_trivialU_windingModeCov_eq_zero_fun {Lat : PeriodicLatticeExtent}
    (μ0 : Fin 3) :
    curlValueCovariant (trivialU (L := Lat)) (windingModeCov Lat μ0) = 0 :=
  funext (curlValueCovariant_trivialU_windingModeCov_eq_zero Lat μ0)

#print axioms curlValueCovariant_trivialU_windingModeCov_eq_zero_fun

/-- **`deltaKQuadFormCorrected` (the whole `Δ_k(U)` object this file's lemma is about) vanishes
IDENTICALLY at `U = trivialU` on the winding/harmonic mode.** Both summands vanish: the `D*D` term
via curl-freeness (above), the `Δ′` term via the ALREADY-BANKED general fact
`deltaPrimeQuadFormTransported_vanishes_at_trivial` (holds for ANY field `A`, not merely this one). -/
theorem deltaKQuadFormCorrected_trivialU_windingModeCov_eq_zero {Lat : PeriodicLatticeExtent}
    (μ0 : Fin 3) :
    deltaKQuadFormCorrected (trivialU (L := Lat)) (windingModeCov Lat μ0) = 0 := by
  unfold deltaKQuadFormCorrected
  rw [dstarDQuadForm_vanishes_of_curl_zero (trivialU (L := Lat)) (windingModeCov Lat μ0)
      (curlValueCovariant_trivialU_windingModeCov_eq_zero_fun μ0),
    deltaPrimeQuadFormTransported_vanishes_at_trivial]
  ring

#print axioms deltaKQuadFormCorrected_trivialU_windingModeCov_eq_zero

/-- **`ContinuousLinearMap.id` is injective** — the trivial instantiation of injectivity this
section's counterexample uses for `C`. -/
theorem contLinId_injective (Lat : PeriodicLatticeExtent) :
    Function.Injective (ContinuousLinearMap.id ℝ (BondFnL2 Lat)) := by
  intro a b h
  simpa using h

#print axioms contLinId_injective

/-- **`windC`, RE-BUILT here (LAW-19: same construction technique as
`compute/pros_thelemma/RefutationWitness.lean`'s own `windC`, that file is scratch/not importable
from this package) — `Btilde := ℝ`, a rank-`1` embedding onto the winding mode.** Deliberately NOT
`Btilde := BondFnL2 Lat` with `C := ContinuousLinearMap.id`: that instantiation hits a REAL, purely
Lean-instance-level diamond (`ContinuousLinearMap.id ℝ (BondFnL2 Lat)`'s own baked topology,
resolved via `NormedSpace`'s class hierarchy, is not SYNTACTICALLY the term `IsBalabanReparam`'s
generic `Btilde`-side instance search independently produces for the SAME type used on both sides
of one arrow at once — the exact `PILP_BRIDGE.md`-class quirk this tree has hit and bridged
elsewhere, e.g. `DeltaKFull.lean` §4/§6). `RefutationWitness.lean`'s own docstring already recorded
exactly this reason for choosing `Btilde := ℝ` over `Btilde := BondFnL2 Lat`; reused here, not
reinvented. -/
noncomputable def windC (Lat : PeriodicLatticeExtent) (μ0 : Fin 3) : ℝ →L[ℝ] BondFnL2 Lat :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
    ((bondFnL2Equiv Lat).symm (windingModeCov Lat μ0))

theorem windC_apply {Lat : PeriodicLatticeExtent} (μ0 : Fin 3) (t : ℝ) :
    windC Lat μ0 t = t • (bondFnL2Equiv Lat).symm (windingModeCov Lat μ0) := by
  simp [windC]

theorem windC_injective (Lat : PeriodicLatticeExtent) (μ0 : Fin 3) :
    Function.Injective (windC Lat μ0) := by
  have hw : (bondFnL2Equiv Lat).symm (windingModeCov Lat μ0) ≠ 0 := by
    intro h
    apply windingModeCov_ne_zero Lat μ0
    have := congrArg (bondFnL2Equiv Lat) h
    simpa using this
  intro a b hab
  rw [windC_apply, windC_apply] at hab
  have hz := sub_eq_zero.mpr hab
  rw [← sub_smul] at hz
  rcases smul_eq_zero.mp hz with h1 | h1
  · linarith [sub_eq_zero.mp h1]
  · exact absurd h1 hw

#print axioms windC_apply
#print axioms windC_injective

/-- **THE ADVERSARIAL SELF-CHECK, discharged: `windC` no longer satisfies `IsBalabanReparam`.**

The exact attack the dispatch mandates re-running: `C := windC`, landing on the winding mode.
Under the PRIOR (universally-quantified) statement this was a LEGAL instantiation (the free
`IsBalabanReparam`/`IsRegular` parameters could be set to `fun _ => True`/`fun _ _ => True`,
discharged by `trivial`, exactly `compute/pros_thelemma/RefutationWitness.lean`'s
`instantiation_is_legal`). Under the REPAIRED, fixed `IsBalabanReparam` (§1c), `windC`'s image is
EXACTLY the winding mode `windingModeCov Lat μ0` (up to scalar), whose covariant curl vanishes
identically at `U = trivialU` (`curlValueCovariant_trivialU_windingModeCov_eq_zero_fun`, already
banked above) — and `trivialU` is regular at `Mα₀ := 0` (`trivialU_isRegular`), which is `<
Mα₀thresh` for any positive threshold. So the SECOND (curl-nonvanishing) clause of
`IsBalabanReparam` FAILS at this instantiation: `windC` is NOT a legal `C` any more. An attacker
can no longer discharge `hC` with `trivial` — they would have to prove a statement that is
provably FALSE, exactly as this theorem shows. **This is the re-run of the dispatch's own mandated
self-check ("try C := windC and the winding mode … if either attack succeeds, you have not
repaired it"); it fails, as required.** -/
theorem windC_fails_isBalabanReparam {Lat : PeriodicLatticeExtent} (μ0 : Fin 3)
    (Mα₀thresh : ℝ) (hpos : 0 < Mα₀thresh) :
    ¬ IsBalabanReparam (Lat := Lat) Mα₀thresh (windC Lat μ0) := by
  rintro ⟨-, hcurl⟩
  have hspec := hcurl (1 : ℝ) one_ne_zero 0 hpos (trivialU (L := Lat))
    (trivialU_isRegular (le_refl 0))
  apply hspec
  rw [windC_apply]
  simp only [one_smul]
  have hcancel : bondFnL2Equiv Lat ((bondFnL2Equiv Lat).symm (windingModeCov Lat μ0)) =
      windingModeCov Lat μ0 := by simp
  rw [hcancel]
  exact curlValueCovariant_trivialU_windingModeCov_eq_zero_fun μ0

#print axioms windC_fails_isBalabanReparam

/-! ## §5b — NON-VACUITY: a genuine, `U`-INDEPENDENT witness satisfying `IsBalabanReparam` at every
threshold — confirming the REPAIRED hypothesis is satisfiable, not vacuous (the OTHER known failure
mode, "`IsRegular := fun _ _ => False`"-style vacuity, checked directly rather than assumed absent).

Built on the concrete `AdmissibleSubspace.witnessL` lattice (matching this tree's existing
convention for concrete witnesses, e.g. `CovariantOperators.witnessPlaquette`), a SINGLE-BOND spike
config: nonzero at exactly one bond, zero everywhere else. Its curl at the plaquette containing
that bond, in the "direct" (non-conjugated) slot, equals the spike's own value REGARDLESS of `U` —
the other three bond-slots of that plaquette's curl formula evaluate the spike at DIFFERENT bonds
(zero, by construction), so no `RMap`/`U`-dependence survives at all. -/

/-- The site with every coordinate `0`, on the concrete witness lattice (reuse of
`HarmonicModes.anySite`, LAW-19). Genuinely computable (`anySite`/`witnessL` both are) — NOT
marked `noncomputable`, so downstream `def`s built from it stay computable too. -/
def spikeSite : PeriodicLatticeSite AdmissibleSubspace.witnessL :=
  anySite AdmissibleSubspace.witnessL

/-- **A single-bond spike**: `suTwoWitness` at EXACTLY the bond `(spikeSite, 0)`, zero elsewhere. -/
noncomputable def singleBondSpike : Bond AdmissibleSubspace.witnessL → SuTwo :=
  fun b => if b = (spikeSite, (0 : Fin 3)) then suTwoWitness else 0

theorem singleBondSpike_ne_zero : singleBondSpike ≠ 0 := by
  intro h
  have hc := congrFun h (spikeSite, (0 : Fin 3))
  simp only [singleBondSpike, Pi.zero_apply] at hc
  exact suTwoWitness_ne_zero hc

/-- The concrete plaquette based at `spikeSite`, directions `(0,1)`. -/
def spikePlaquette : PeriodicLatticePlaquette AdmissibleSubspace.witnessL :=
  (spikeSite, ⟨(0, 1), by decide⟩)

/-- **The site-shift-by-`1` fact this witness needs**: shifting `spikeSite` in direction `1` on the
witness lattice (side length `3`, i.e. coordinates in `Fin 4`) genuinely changes it — `0+1=1≠0` in
`Fin 4`. Needed so the spike's OTHER three curl-slots at `spikePlaquette` evaluate at bonds
genuinely distinct from `(spikeSite, 0)`. Fully concrete (`witnessL`, `spikeSite`, `Fin`-arithmetic
all reduce), so `decide` settles it directly rather than a hand-built `Fin` computation. -/
theorem shift1_spikeSite_ne_spikeSite :
    periodicLatticeShift spikeSite (1 : Fin 3) ≠ spikeSite := by decide

/-- The spike's value AT its own bond, factored out so both the `c=1` and general-`c` computations
below reuse it (LAW-19-style internal reuse, not a fresh invention each time). -/
theorem singleBondSpike_at_zero : singleBondSpike (spikeSite, (0 : Fin 3)) = suTwoWitness := by
  simp [singleBondSpike]

theorem singleBondSpike_at_term2 :
    singleBondSpike (periodicLatticeShift spikeSite (0 : Fin 3), (1 : Fin 3)) = 0 := by
  simp only [singleBondSpike, ite_eq_right_iff]
  intro hcontra
  exact absurd (congrArg Prod.snd hcontra) (by decide)

theorem singleBondSpike_at_term3 :
    singleBondSpike (periodicLatticeShift spikeSite (1 : Fin 3), (0 : Fin 3)) = 0 := by
  simp only [singleBondSpike, ite_eq_right_iff]
  intro hcontra
  exact absurd (congrArg Prod.fst hcontra) shift1_spikeSite_ne_spikeSite

theorem singleBondSpike_at_term4 : singleBondSpike (spikeSite, (1 : Fin 3)) = 0 := by
  simp only [singleBondSpike, ite_eq_right_iff]
  intro hcontra
  exact absurd (congrArg Prod.snd hcontra) (by decide)

#print axioms singleBondSpike_ne_zero
#print axioms shift1_spikeSite_ne_spikeSite
#print axioms singleBondSpike_at_zero
#print axioms singleBondSpike_at_term2
#print axioms singleBondSpike_at_term3
#print axioms singleBondSpike_at_term4

/-- **THE HEADLINE COMPUTATION, scaled by an arbitrary real `c`: the spike's curl at
`spikePlaquette` equals `c • suTwoWitness`, at EVERY `U`.** The two conjugated (`RMap`) slots
evaluate the spike at bonds with direction `≠ 0` (direct component mismatch, no lattice fact
needed); the direct minus-slot evaluates at direction `1 ≠ 0`; only the leading direct slot
matches, contributing `c • suTwoWitness` unconjugated (`RMap`'s own linearity kills the two
conjugated slots regardless of `U`, since they are applied to `0`). -/
theorem curlValueCovariant_smul_singleBondSpike (U : Config AdmissibleSubspace.witnessL) (c : ℝ) :
    curlValueCovariant U (c • singleBondSpike) spikePlaquette = c • suTwoWitness := by
  show (c • singleBondSpike) (spikeSite, (0 : Fin 3)) +
      RMap (U (spikeSite, (0 : Fin 3)))
        ((c • singleBondSpike) (periodicLatticeShift spikeSite (0 : Fin 3), (1 : Fin 3))) -
      RMap (U (spikeSite, (1 : Fin 3)))
        ((c • singleBondSpike) (periodicLatticeShift spikeSite (1 : Fin 3), (0 : Fin 3))) -
      (c • singleBondSpike) (spikeSite, (1 : Fin 3)) = c • suTwoWitness
  have e1 : (c • singleBondSpike) (spikeSite, (0 : Fin 3)) = c • suTwoWitness := by
    rw [Pi.smul_apply, singleBondSpike_at_zero]
  have e2 : (c • singleBondSpike)
      (periodicLatticeShift spikeSite (0 : Fin 3), (1 : Fin 3)) = 0 := by
    rw [Pi.smul_apply, singleBondSpike_at_term2, smul_zero]
  have e3 : (c • singleBondSpike)
      (periodicLatticeShift spikeSite (1 : Fin 3), (0 : Fin 3)) = 0 := by
    rw [Pi.smul_apply, singleBondSpike_at_term3, smul_zero]
  have e4 : (c • singleBondSpike) (spikeSite, (1 : Fin 3)) = 0 := by
    rw [Pi.smul_apply, singleBondSpike_at_term4, smul_zero]
  rw [e1, e2, e3, e4]
  simp [map_zero]

/-- **`c • singleBondSpike`'s curl is never the zero function, at ANY `U`, whenever `c ≠ 0`.** -/
theorem curlValueCovariant_smul_singleBondSpike_ne_zero (U : Config AdmissibleSubspace.witnessL)
    (c : ℝ) (hc : c ≠ 0) :
    curlValueCovariant U (c • singleBondSpike) ≠ 0 := by
  intro h
  have hp := congrFun h spikePlaquette
  rw [curlValueCovariant_smul_singleBondSpike U c] at hp
  rcases smul_eq_zero.mp hp with h1 | h1
  · exact hc h1
  · exact suTwoWitness_ne_zero h1

#print axioms curlValueCovariant_smul_singleBondSpike
#print axioms curlValueCovariant_smul_singleBondSpike_ne_zero

/-- **`singleBondSpike`, embedded into `BondFnL2 witnessL` via a rank-`1` map from `ℝ`** — the
`Btilde := ℝ` reparametrization witness. -/
noncomputable def spikeC : ℝ →L[ℝ] BondFnL2 AdmissibleSubspace.witnessL :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
    ((bondFnL2Equiv AdmissibleSubspace.witnessL).symm singleBondSpike)

theorem spikeC_apply (t : ℝ) :
    spikeC t = t • (bondFnL2Equiv AdmissibleSubspace.witnessL).symm singleBondSpike := by
  simp [spikeC]

theorem spikeC_injective : Function.Injective spikeC := by
  have hne : (bondFnL2Equiv AdmissibleSubspace.witnessL).symm singleBondSpike ≠ 0 := by
    intro h
    apply singleBondSpike_ne_zero
    have := congrArg (bondFnL2Equiv AdmissibleSubspace.witnessL) h
    simpa using this
  intro a b hab
  rw [spikeC_apply, spikeC_apply] at hab
  have hz := sub_eq_zero.mpr hab
  rw [← sub_smul] at hz
  rcases smul_eq_zero.mp hz with h1 | h1
  · linarith [sub_eq_zero.mp h1]
  · exact absurd h1 hne

#print axioms spikeC_apply
#print axioms spikeC_injective

/-- **THE NON-VACUITY THEOREM: `spikeC` satisfies `IsBalabanReparam` at EVERY threshold.**
Injective (`spikeC_injective`), and its image's curl is nonzero at EVERY `U` whatsoever
(`curlValueCovariant_smul_singleBondSpike_ne_zero`, no regularity hypothesis even needed) — so in
particular at every regular `U`. Confirms the repaired hypothesis `IsBalabanReparam` is genuinely
SATISFIABLE, not vacuous — the theorem `theLemma_C_star_Delta_k_C_uniform` can be legally
instantiated. -/
theorem spikeC_satisfies_isBalabanReparam (Mα₀thresh : ℝ) :
    IsBalabanReparam (Lat := AdmissibleSubspace.witnessL) Mα₀thresh spikeC := by
  refine ⟨spikeC_injective, ?_⟩
  intro Bt hBt Mα₀ _ U _
  have heq : bondFnL2Equiv AdmissibleSubspace.witnessL (spikeC Bt) = Bt • singleBondSpike := by
    rw [spikeC_apply, map_smul]
    simp
  rw [heq]
  exact curlValueCovariant_smul_singleBondSpike_ne_zero U Bt hBt

#print axioms spikeC_satisfies_isBalabanReparam

/-! ## §6 — degeneracy census, updated for the repair (LAW-19, not rebuilt) -/

/-!
* **`U ≡ 1`**: exercised directly, `§5` — the theorem the whole falsifiability argument turns on.
  `trivialU_isRegular` (§1b) confirms it is genuinely regular at every nonnegative threshold.
* **Central `U` (`Ad(±I) = id`)**: `IsRegular`'s adjoint-action-based definition (§1b) is, BY
  CONSTRUCTION, immune to the center-blindness bug this tree's own `DeltaKFull.
  RMap_witnessMElem_ne_id` correction names ("a background far from the identity is INSUFFICIENT,
  the correct criterion is `Ad(U)≠id`") — `U(b) = -1` registers as PERFECTLY REGULAR under this
  definition (since `RMap(-1) = id`, so the displacement is exactly `0`), which is the CORRECT
  behavior (a central group element genuinely acts trivially on every gauge-covariant quantity),
  not a bug to guard against.
* **Constant gauge functions**: `DeltaPrime.trivialU` (`U ≡ 1` on every bond) is the extreme
  constant case and is EXACTLY where §5's disproof (`windC_fails_isBalabanReparam`) is
  exhibited — the harmonic/winding mode is killed at precisely this point, confirming a constant
  (trivial) background is not sufficient to avoid the degenerate kernel even though `U ≡ 1`
  trivially satisfies `IsRegular`.
* **`ell = 1`**: `KernelSubspace.coarseRestrictSite_one_eq_self` (already banked) proves the
  coarse-restriction operator is the IDENTITY at `ell=1`. `Δ_k(U)` as built here
  (`deltaKQuadFormCorrected`) does not itself carry an explicit `ell`/scale parameter, so this
  degeneracy does not directly apply to this file's own statements; recorded here as before.
* **`§1d` UPDATE (this dispatch): the perfectly-regular locus is STRICTLY LARGER than `{1, -1}`.**
  Not merely the center: `diagGroupElem` (`§1d`, the matrix `suTwoWitnessVal` itself, re-packaged as
  a group element) is `≠ 1` and `≠ negOneElem` (`diagGroupElem_ne_one`,
  `diagGroupElem_ne_negOneElem`) yet fixes `suTwoWitness` EXACTLY
  (`RMap_diagGroupElem_suTwoWitness`), so `diagConfig` (the constant configuration at `diagGroupElem`)
  is `IsRegular`-perfect at threshold `0` (`diagConfig_isRegular`) while being neither the trivial nor
  the central configuration. The proxy's zero-locus is (at least) the whole stabilizer subgroup of the
  fixed test direction `suTwoWitness` under the adjoint action — a `U(1)` worth of "trivially
  regular" configurations, not merely the two-element center `{1,-1}`. On the SAME witness, the
  orthogonal direction `pauliE2` is displaced MAXIMALLY (`diagGroupElem_pauliE2_displacement`,
  `= 2‖pauliE2‖`), quantifying exactly how much of CMP99b (3.35)'s full-direction content this proxy
  cannot see. `§1d`'s own conclusion: PROXY and (3.35)/(3.36) are, on present EARNED evidence,
  INDEPENDENT — neither implies the other, and the residual (the missing gauge-transformation action
  on `Config Lat` and the cube/domain geometry `Ω_j`/`□`) is named precisely there, not silently
  bridged.
-/

end AdalyFormal.Balaban.TheLemma
