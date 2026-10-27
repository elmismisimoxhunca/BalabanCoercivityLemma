/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CoercivityCov

set_option autoImplicit false

/-!
# One-scale coercivity for the covariant `𝔰𝔲(2)`-valued carrier, at unrestricted `U`

**RETARGETED DISPATCH (2026-07-22).** The owner's retarget explicitly WITHDRAWS the original
brief's item 3/4 (a full `SpineCovariant` parallel to `Spine.lean`, plus a dirty/clean
mutation-test pair for "reachable is not consumed") — "a parallel top-level spine is FULL3D-shaped
work and is not what we
need." What replaces it, and is this file's entire content, is **stating** — precisely, with `Δ`
TIED to an already-built operator and `U` genuinely unrestricted — the campaign's first
intermediate deliverable: a single-scale coercivity bound for the covariant carrier. **The statement
is the deliverable; getting it right outranks proving it** (owner's own words). This file is
therefore deliberately SMALL: one `Prop`, its docstring, and an honest account of why the natural
proof attempt is suspect before it is even tried.

## STATUS, 2026-07-28: **THIS STATEMENT IS FALSE AND ITS `sorry` CAN NEVER BE FILLED.**

### THE REPLACEMENT EXISTS, AND THE FIRST THING IT PROVES IS THAT THE OBVIOUS FIX IS NOT ENOUGH

`Balaban/OneScaleVolumeV.lean` (zero `sorry`, every declaration `#print axioms`-clean) carries the
repaired statement. Read the following two facts together, because taking the first without the
second is exactly the error this file is a monument to.

1. **Swapping the SUBSPACE alone does NOT repair it.** The diagnosed cause below is a growth-rate
   mismatch: `anchoredVCov`'s codimension is `finrank ℝ SuTwo · |Γ_{y,x}| = O(ell)`, volume-free,
   and `Balaban/VolumeScalingV.lean` supplies the source-faithful replacement whose codimension is
   `(1 - ell⁻³)·|Sites|`, i.e. `Ω(|Sites|)`. That replacement was substituted into THIS statement,
   with the operator left unchanged, and the refuting witness STILL LANDS:
   `OneScaleVolumeV.bondLaplacian_coercivity_on_axUnion_false` derives `False` from it — at EVERY
   extent and every `ell ≥ 1` dividing it, not merely at the witness lattice. The reason is a
   counting ceiling proved there (`card_axUnionBonds_le_card_site`,
   `finrank_siteFnL2_lt_finrank_axUnionVCov`): the axial clause constrains at most `|Sites|` of the
   `3·|Sites|` bonds — at most a THIRD — while `ker (D⁰_U)^*` occupies at least TWO THIRDS of the
   ambient space for every `U`. `Ω(|Sites|)` with the constant `(1 - ell⁻³) < 1` is still too
   small, and no choice of `ell` changes that. **The operator below, not only the subspace, is what
   must change.**
2. **The repaired statement is over BOTH Hodge components and the union subspace.** With
   `hodgeForm U B = ‖D¹_U B‖² + ‖(D⁰_U)^* B‖²` in place of `⟨B, D⁰_U(D⁰_U)^* B⟩` and
   `VolumeScalingV.axUnionVCov (CoarseLattice L ell) ell` in place of `anchoredVCov y x ell`, the
   rank-nullity mechanism that kills this file's statement is provably UNAVAILABLE
   (`OneScaleVolumeV.not_forced_intersection_hodge`: the two targets together have finrank
   `4·|Sites|·finrank SuTwo`, strictly above the ambient `3·|Sites|·finrank SuTwo`), the winding
   mode that kills the `hdiag`-free anchored form is EXCLUDED by the union clause at every
   `ell ≥ 2` (`OneScaleVolumeV.windingModeCov_notMem_axUnionLocusG`), and the forced
   `ker (D⁰_U)^*` witness of item 1 has nonzero curl at the flat background
   (`OneScaleVolumeV.forced_witness_curl_ne_zero_at_trivialU`).

**What is PROVED of the replacement, stated without overreach.** At the FLAT background only, and
for every `ell ≥ 2`, `OneScaleVolumeV.volumeUniformCoercivity_general` proves
`VolumeScalingV.volumeUniformCoercivity ell` with the explicit constant `γ = 1/(9·ell⁸)` bound
BEFORE the lattice extent — one constant for every volume. Its route is quantitative (the exact
discrete Weitzenböck identity `Weitzenbock.weitzenbock_flat` plus a pointwise Poincaré from the
Dirichlet datum `A(c,μ) = 0` at every coarse centre) and never touches
`LinearMap.exists_antilipschitzWith`, which is why the constant survives the quantifier move.
**Not proved, and named there rather than implied away:** general `U` (`γ` at unrestricted `U` —
and measured evidence says the flat background is NOT the worst case), and `ell`-uniformity (the
constant degrades like `ell⁻⁸`). So the `∀ U` shape of the statement below — the one part of it
that was never the defect — is still open in the replacement, and is not claimed here.

S75 propagation, in place; superseded sentences below are retained STRUCK, not deleted. The
dimension-count "FLAGGED SUSPICION" recorded further down is no longer a suspicion — it is a
kernel-checked refutation. `Balaban/ForcedIntersection.lean` (zero `sorry`) proves
`oneScaleCoercivity_su2_false_at_witness`, and its §7
`sorry_in_oneScaleCoercivity_su2_is_unfillable_at_witness : False` applies THIS declaration BY NAME
at the witness arguments, so an honest proof term for the `sorry` below at that instantiation would
make the ambient theory inconsistent. `Balaban/OneScaleRepaired.lean` §A re-derives the refuting
arithmetic independently, with the exact witness cardinalities.

Three further facts, all kernel-checked in `Balaban/OneScaleRepaired.lean`:

1. **The bare-curl repair is ALSO false.**
   `OneScaleCorrected.oneScaleCoercivity_curl_corrected` (which swaps this operator for the curl
   and adds a diagonal-pair hypothesis) is refuted by the PURE-GAUGE/coboundary mode:
   `curl_corrected_false_at_diag_witness`, and
   `sorry_in_curl_corrected_is_unfillable_at_diag_witness` applies that declaration by name. The
   `sorry` at `OneScaleCorrected.lean:278` is therefore unfillable too.
2. **The diagnosis is a GROWTH-RATE mismatch, not a wrong constant.** `anchoredVCov`'s codimension
   is `3·|Γ_{y,x}| = O(ell)` — one pair's staircase, diameter-bounded — while EVERY
   single Hodge component of the covariant bond Laplacian has a kernel of dimension
   `Ω(|Sites|)`. No choice of `(y,x)` fixes that on a large enough lattice: the operator or the
   subspace must change.
3. **What IS true, and proved:** with BOTH Hodge components
   (`‖curl_U B‖² + ‖(D⁰_U)^*B‖²`) and the diagonal-pair hypothesis, one-scale coercivity
   holds at the flat background —
   `OneScaleRepaired.hodgeCoercivity_at_trivialU`, no `sorry`, axioms
   `[propext, Classical.choice, Quot.sound]`. General `U`, and `U`-uniformity of `γ`, are NOT
   established there; both are named precisely in that file's §F.

## The lemma
-/

namespace AdalyFormal.Balaban.SpineCovariant

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantOperators AdalyFormal.Balaban.CoercivityCov

/-- **ONE-SCALE COERCIVITY FOR THE COVARIANT `𝔰𝔲(2)`-VALUED CARRIER, AT UNRESTRICTED `U`.** A
lower bound on `⟨B, Δ(U)B⟩` for `B` in the `𝔰𝔲(2)`-valued anchored admissible subspace, holding for
the ENTIRE gauge configuration space (not a neighbourhood of the identity), at a SINGLE fixed scale
— no `k`-uniformity is claimed or attempted (a separate, harder crux, explicitly out of scope here
per the owner's retarget).

**`Δ` is TIED, not existentially quantified.** The bound is stated directly against
`BondSU2Space.bondLaplacianCovCLM_L2 U` — the ALREADY-BUILT, kernel-checked `ContinuousLinearMap`
(`BondSU2Space.lean` §3, `#print axioms bondLaplacianCovCLM_L2` clean) — not a free structure field a
prover could instantiate however convenient. This is the exact repair the retarget demands relative
to `Spine.lean`'s `coerc_u_main`, whose own docstring concedes "nothing prevents a transport family
from acting as the identity on the whole admissible subspace `V` while varying arbitrarily off it":
here there is no such freedom, because the operator symbol appearing in the conclusion literally IS
the already-constructed operator, not a variable ranging over operators. For the SAME reason this
statement does **not** route through `CoercivityCov.CoercivityHypothesisCov` (whose `Δ` field, if
instantiated with `bondLaplacianCovCLM_L2`, would additionally require reconciling two DIFFERENT,
non-`rfl`-equal `NormedAddCommGroup (BondFnL2 Lat)` instances — `CoercivityCov.lean` §4's own named,
not-yet-closed finding; verified directly, not assumed, in this dispatch's own scratch tests). The
bare `‖B‖`/`inner ℝ B (...)` route below uses the SAME ambient instances `bondLaplacianCovCLM_L2`
itself was built under (checked directly: `(inferInstance : NormedAddCommGroup (BondFnL2 Lat)) =
CovariantOperators.instNormedAddCommGroupBondFnL2 := rfl` succeeds with NO separate `InnerProductSpace`
bracket forced first — the diamond named in `CoercivityCov.lean` §4 is specific to structures that
demand BOTH brackets as independently-resolved sibling instance arguments, which this bare
`∃ γ, ... ∀ U B, ...` statement does not).

**`U` is genuinely unrestricted.** `∀ U : Uconfig` sits OUTSIDE `∃ γ` — `γ` is fixed once, before `U`
is quantified, so it cannot secretly depend on `U`. The single degenerate point `U = 1`, where
(per this campaign's own recorded trap) every wrong alternative coincides, is just ONE case among
all of `Uconfig`, not a hidden restriction to a neighbourhood of it. `γ` MAY depend on the fixed
geometric data (`Lat`, `y`, `x`, `ell`) — that dependence is written into the statement explicitly,
by being fixed as arguments before `γ` is introduced — but on NOTHING else.

**Named gap, disclosed precisely, not merely called "a simplification."** `bondLaplacianCovCLM_L2 U`
is `D^0_U ∘ (D^0_U)^*` — built from `gradValueCovariant`/`gradCovariantAdjointLM`, CMP99b's
DEGREE-0 covariant gradient (p.390's unnumbered display / eq. (3.3), site→bond) composed with its
own explicit combinatorial adjoint (bond→site→bond). **Checked directly against the source, and
against `CovariantHj.lean`'s own code (not merely its prose): this is NOT CMP99b (3.10)'s own
`Δ = D*D + Δ'` term.** (3.10)'s own `D` is the DEGREE-1 covariant CURL (`D^1_U`, bond→plaquette,
eq. (3.4)) — `CovariantHj.dstarDQuadForm`'s own quadratic form (`covPlaqInner (curlValueCovariant U
A) (curlValueCovariant U A)`, confirmed by reading `CovariantHj.lean:163-166` directly), matching
`HjMinimizer.lean`'s flat `deltaJQuadForm := ‖curlCLM(...)‖²` "one level up the construction" per
`CovariantHj.lean`'s own docstring — NOT yet promoted to an operator anywhere in this tree
(`BondSU2Space.lean`'s own §6 residual note 2). `bondLaplacianCovCLM_L2` and `dstarDQuadForm`'s
eventual operator promotion are therefore TWO DIFFERENT pieces of a Hodge-type decomposition of a
bond Laplacian — built from two DIFFERENT differentials (degree 0 vs. degree 1), not the same map
`D` composed in two orders. **This is a sharper disclosure than `BondSU2Space.lean`'s own docstring
makes** ("the `D*D`/`DD*` piece alone, not the full operator" — phrasing that does not distinguish
which `D`); this docstring draws the distinction explicitly so the gap is not understated. `Δ'`
(CMP99b's curvature/commutator correction, `DeltaPrime.lean`) is also entirely absent from the bound
below. So this lemma is honestly a bound on ONE Hodge-Laplacian-shaped piece (`D^0_U(D^0_U)^*`) of
the covariant carrier — not on `Δ_j(U)`/`Δ_k(U)` itself — a disclosed, NAMED simplification, exactly
the same discipline `Coercivity.lean`'s own `coercive` field docstring already applies to CMP96
`(2.122)`'s three-term bound. As instructed: if a full `Δ_k(U)` (via `Balaban/DeltaKFull.lean`,
read-only, a concurrent lane's deliverable) exists by the time this is picked up, THIS lemma's
target operator should be reconsidered against it, not silently kept.

**THE SUSPECT-STATEMENT WARNING — SUPERSEDED 2026-07-28: now a PROVED REFUTATION**
(`ForcedIntersection.lean`; `OneScaleRepaired.lean` §A). Retained verbatim because its dimension
count is exactly the mechanism that was confirmed; only its epistemic status changed.
~~(read before attempting a proof) — a dimension count, not a hedge.~~
The subspace `anchoredVCov y x ell hy hx` is cut out by a SMALL, axis-anchored condition: `B` must
vanish on `staircasePath y x`, a bond set whose cardinality is tied to `ell`/the diameter of `(y,x)`
(the WITNESS lattice's own computed value, `AdmissibleSubspace.witness_staircasePath`, is exactly
`2` bonds out of `192`). Meanwhile `bondLaplacianCovCLM_L2 U = D^0_U ∘ (D^0_U)^*` has its RANK
bounded above by the dimension of its intermediate SITE-indexed space
(`gradCovariantAdjointLM U : (Bond L → SuTwo) →ₗ[ℝ] (PeriodicLatticeSite L → SuTwo)`, codomain
dimension `3·|Sites|`), so `dim(ker (D^0_U)^*) ≥ dim(Bond L → SuTwo) − 3·|Sites| = 3·(|Bonds| −
|Sites|)` — for a 3D periodic lattice `|Bonds| = 3·|Sites|`, so this is `6·|Sites|`, a quantity that
GROWS with lattice size while `codim(V) = 3·|staircasePath y x|` stays essentially fixed (tied to the
diameter of one pair `(y,x)`, not to the lattice volume). By the exact linear-algebra inequality
`dim(A ⊓ B) ≥ dim A + dim B − dim(ambient)` (an identity, not a genericity assumption — Mathlib:
`Submodule.finrank_sup_add_finrank_inf_eq` combined with `finrank(A⊔B) ≤ finrank(ambient)`), on the
concrete WITNESS lattice this gives `dim(V ⊓ ker (D^0_U)^*) ≥ (576 − 6) + 384 − 576 = 378 > 0`
(ambient `= 192 bonds × 3 = 576`; `dim(ker) ≥ 576 − 3·64 = 384` since `|Sites| = 64` on the witness
lattice), **for EVERY `U`, since the `≥384` bound needs no fact about `U` beyond `rank ≤ codomain
dim`, which is unconditional**. If this holds, there is a nonzero `B ∈ V` with `(D^0_U)^*B = 0` for
EVERY `U`, hence (by the Gram identity `BondSU2Space.covBondInner_bondLaplacianCovLM_eq_covSiteInner`)
`⟨B, bondLaplacianCovLM(U)(B)⟩ = ‖(D^0_U)^*B‖² = 0` while `‖B‖² > 0` — REFUTING any `γ > 0` bound on
THIS `B`, for every `U` simultaneously. **This is arithmetic reasoning from already-proved Lean facts
(the cardinality `2`, from `witness_staircasePath`; rank-nullity is standard Mathlib) — it is NOT
itself a machine-checked Lean proof in this file** (per the reform charter, prose proves nothing;
this paragraph is a FLAGGED SUSPICION, not a certificate). It is also consistent with, and sharpens,
`Coercivity.lean`'s own R3 disclosure that Balaban's actual CMP96 bound is on the FULL three-term
`(2.122)` sum, with `⟨B,Δ_jB⟩` itself ABSORBED AWAY via bound `(2.118)` before the coercivity step —
i.e. Balaban himself never bounds a bare `⟨B,ΔB⟩` on the bare axis-anchored subspace alone either.
**Recommendation, stated plainly: before attempting ANY proof of the `sorry` below, first settle this
refutation in Lean** (§ "what remains to prove," `LEMMA_STATEMENT.md`). If confirmed, this exact
statement SHAPE should be replaced, not repaired — either by further restricting the subspace to
match CMP99b `(3.156)`'s full three-condition form (`B=0` on `Λᶜ`, `B=0` on `⋃_{y∈Λ'}Ax(y)`,
`Q_1B=0`), or by bounding the FULL multi-term `(2.122)`-analogue rather than the bare bilinear form.

**The lone `sorry` — SUPERSEDED 2026-07-28.** ~~Exactly one, on the coercivity bound itself
— the crux `[LEM-COERC-U]` is exactly the content of this existential, and per the retarget's own
instruction ("the STATEMENT is the deliverable... getting it right outranks proving anything") it is
expected and honest that it remains open. Given the dimension-count warning immediately above, the
correct next step is very likely to REFUTE this exact statement in Lean before attempting to prove
it — see `LEMMA_STATEMENT.md`.~~ **Corrected status: the `sorry` below is NOT "open" — it is
UNFILLABLE, because the statement is false at the witness lattice
(`ForcedIntersection.lean` §7). It is retained, unproved and unremoved, because
`ForcedIntersection.lean` CONSUMES this declaration by
name to exhibit the inconsistency; deleting or weakening it would destroy that evidence. Do not
attempt to prove it. The live successor is `OneScaleRepaired.hodgeCoercivity_at_trivialU`.** -/
theorem oneScaleCoercivity_su2 {Lat : PeriodicLatticeExtent}
    (y x : PeriodicLatticeSite Lat) (ell : ℕ)
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Lat)
        (B : BondFnL2 Lat), B ∈ CoercivityCov.anchoredVCov y x ell hy hx →
        γ * ‖B‖ ^ 2 ≤ inner ℝ B (BondSU2Space.bondLaplacianCovCLM_L2 U B) := by
  sorry

#print axioms oneScaleCoercivity_su2

end AdalyFormal.Balaban.SpineCovariant
