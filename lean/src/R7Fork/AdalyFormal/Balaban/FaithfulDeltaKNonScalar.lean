/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import R7Fork.AdalyFormal.Balaban.FaithfulCoercivitySU2
import AdalyFormal.Balaban.BondSU2Space

set_option autoImplicit false
set_option maxRecDepth 4000

/-!
# UN-SCALARIZING `Δ_k(U)`: a genuinely non-scalar `su(2)`-carrier operator, `deltaK_not_scalar`

**Dispatch target** (owner, "un-scalarize `Δ_k(U)` to its fullest extent"): two de-correlated
prosecutions (`compute/prosecute_su2_build/VERDICT.md`, `compute/sol_su2_gate/SOL_VERDICT.md`)
proved that `FaithfulCoercivitySU2.lean`'s `deltaKC_su2` GLOBALLY COLLAPSES to `scalar(U) • id` on
its domain: `Q := Qstar := 1` and `H₁ := id` (both inherited from `DeltaKUnified.lean`) leave the
entire operator's action as ONE real number `κ(U)` — not merely restricted-to-`V` scalar, but
literally `deltaKC_su2(U) v = s(U) • RD.Cadj(RD.C v)` for EVERY `v`, EVERY `U` (Sol's
`operator_globally_collapses`). This file builds a REPLACEMENT `Δ_k(U)` whose operator content is
PROVABLY NOT of this form: `deltaK_not_scalar` below exhibits two vectors in `BFL2 witnessL` with
different images under a common scalar hypothesis, a kernel-checked refutation of `T = c • id` for
EVERY real `c` simultaneously (stronger than "two different Rayleigh quotients at one `U`" — this
is "not scalar" in the strongest available sense: no `c` works, not just no `c` matching one ratio).

## ROUTE TAKEN: Route A, the curl/gradient-squared form (CMP95 (1.65)/(1.66), CMP99b (3.10))

`⟨B,Δ_kB⟩ = ⟨∂H_kB,∂H_kB⟩` (CMP95 (1.65)) is, at the level CMP99b (3.9)/(3.10) makes covariant, a
GRAM operator built from the covariant lattice gradient `D_U` (CMP99b p.390, unnumbered display /
eq (3.3): `(D_Uλ)(b) = R(U(b))λ(b_+) - λ(b_-)`, `R := Ad`) and its EXPLICIT combinatorial adjoint
`D_U^*` (CMP99b p.391's own name for the object, first written out explicitly in
`CovariantHjMinimizer.lean` §5, `#print axioms`-clean, no `sorry`). **This file does NOT build
`D_U`/`D_U^*` from scratch** — `Balaban.BondSU2Space.lean` ALREADY built the genuine
`ContinuousLinearMap`-promotable Gram operator `D_U ∘ D_U^*` on the bare carrier `Bond witnessL →
SuTwo` (`bondLaplacianCovLM`), proved it PSD and `covBondInner`-self-adjoint (§4 there), and proved
it is genuinely `U`-dependent at a NON-degenerate witness pair (§5 there,
`bondLaplacianCovLM_genuinely_U_dependent`). LAW-19 reuse, not a rebuild: this file's §1-§2 transport
that already-proved object onto `BFL2 witnessL` (the SAME `su(2)` carrier `FaithfulCoercivitySU2.lean`
uses, via `DeltaKUnified.bfl2Equiv`) and prove the ONE thing neither prior file established — genuine
NON-SCALARITY (`T ≠ c • id` for every `c`, not merely `T ≠ 0`).

**ROUTE B, named not built** (`[LEM-Q1REAL-ADJOINT]`, unchanged from `FaithfulCoercivitySU2.lean`'s
own naming): promoting `Q1Real(U)` itself into the `Q`/`Qstar` slots of `BalabanCovarianceData`
(rather than routing its variation through the scalar `κ(U)`, as `FaithfulCoercivitySU2.lean` does)
needs `Q1Real`'s adjoint — a genuine gather/scatter Fubini argument over `q1RealMain`'s nested
`(x,i)`-indexed sum, comparable in scope to `Q1Real.lean` itself. Still not built; Route A achieves
the mandate's actual goal (a provably non-scalar, `U`-dependent operator, DERIVED not assumed)
without it.

## WHY THE CURL TERM (NOT `κ(U)`) CARRIES THE NON-SCALARITY

`FaithfulCoercivitySU2.kappa(U)` is a real NUMBER — pairing `Q1Real U`'s output against one FIXED
direction `suTwoWitness`. No matter how genuinely it varies with `U`, `κ(U) • id` is, BY
CONSTRUCTION, a scalar multiple of the identity: it can never fail to be `c • id` for `c := κ(U)`.
This is exactly the mechanism the prosecutions exploited. `bondLaplacianCovLM U`, by contrast, is a
GENUINE differential/gradient-adjoint operator — `D_U D_U^*` — whose kernel and range are
determined by the lattice's own incidence structure, not a single scalar channel. §3 below proves
its kernel is nontrivial (a translation-invariant, single-direction bond field is annihilated by the
covariant divergence `D_U^*` at `U = 1`, by a clean, general — not case-by-case — cancellation) while
its VALUE at a different, explicit witness (`BondSU2Space.bondWitnessConfig`) is nonzero — two
DISTINCT behaviors on the same space that no single scalar `c` can reproduce simultaneously.

## `bc.a` FIX (carried from the conviction)

Both prosecutions' counterexamples used `bc.a := 2` against `deltaKC_su2`'s FREE `bc : BaseConstant`
argument — the OLD `GinvSU2`/`sourceCorrection` pieces bound `usedAt bc 0` by nothing but `bc.a > 0`,
while `(baseG+κ(U))⁻¹ ≤ 1` is uniformly bounded, so `bc.a > 1` makes the assembled scalar negative
for EVERY `U` at once. **FIX**: `gamma_exists_su2_nonscalar` below takes an EXPLICIT hypothesis
`hbc : usedAt bc 0 ≤ 1/2` (this file's own honest smallness bound, matching CMP99b's own qualitative
"`a` a small fixed constant" — no page claims a SPECIFIC numeric bound, so `1/2` is THIS file's
choice, tied to the already-established `(baseG+κ(U))⁻¹ ≤ 1` uniform bound with margin) — this
BLOCKS both published counterexamples (`bc.a := 2 > 1/2`) at the type level: no caller can even
STATE the theorem with the old exploit value. A second smallness hypothesis `hvJ` bounds the source
term the same way, closing the analogous attack on `v0`,`J` (S82: a mutation making `⟪v0,J⟫`
unboundedly large would defeat ANY fixed `bc` bound if left unguarded).

## WHAT THIS FILE DOES NOT CLOSE (named, not silently dropped)

1. **Non-scalarity of the `C`-SANDWICHED, admissible-subspace-restricted operator** — this file
   proves `deltaKBaseSU2NonScalar` (the UNSANDWICHED `Δ_k(U)`, CMP99b (3.156)'s own base term, BEFORE
   the `C^*(\cdot)C` reparametrization of (3.157)) is non-scalar on the FULL carrier `BFL2 witnessL`.
   Proving the SANDWICHED `RD.Cadj ∘ Base ∘ RD.C`, restricted to `v ∈ subspace156BFL2`, is ALSO
   non-scalar would need witnesses that are SIMULTANEOUSLY (a) admissible (`∈ Q1Real.q1RealKernel U`)
   and (b) distinguish the curl term's action — a fresh construction problem this file does not
   attempt (the natural curl witnesses, `constDirConfig`/`bondWitnessConfig`, are not shown, and are
   not expected in general, to lie in `q1RealKernel`). ~~Also, proving genuine non-scalarity ON `V`
   would first need `dim V ≥ 2` (`subspace156BFL2_ne_bot` only gives `dim V ≥ 1` — on a 1-dimensional
   space EVERY operator is trivially "scalar" in the single-ratio sense, so a 2-independent-vector
   witness in `V` is a PREREQUISITE this tree has not established). Named precisely, not attempted.~~

   ⚠ **CORRECTED 2026-07-27 (S75 propagation; the struck text above is retained verbatim, not
   deleted). BOTH named prerequisites are now ESTABLISHED**, in `Balaban/NonDegenerateInstances.lean`
   (a separate module — this file is NOT edited beyond this note, and does not import it):

   * **`dim V ≥ 2` is PROVED, and for EVERY `U`, not just `trivialU`** —
     `NonDegenerateInstances.two_le_finrank_subspace156BFL2` (with the far stronger
     `finrank_subspace156BFL2_univ_empty`: `168 · dim 𝔰𝔲(2) ≤ dim V` at `Λ := univ`, `S' := ∅`, and
     `finrank_subspace156BFL2_nondegenerate`: `158 · dim 𝔰𝔲(2) ≤ dim V` at a PROPER `Λ` and a
     NONEMPTY `S'`). The route is rank–nullity on the assembled clause map, so it needs no witness
     and inherits no flat-background restriction. Explicit named members are also supplied
     (`checkerDirSuTwo μ`, `checkerDir_linearIndependent`), those at `trivialU` only.
   * **The missing piece (b) — an admissible field distinguishing the curl term — is SUPPLIED**:
     `NonDegenerateInstances.signDir01SuTwo` lies in `q1RealKernel (trivialU)`
     (`signDir01_mem_kernel`) and `D_1 D_1^*` maps it to `4 • suTwoWitness` at the direction-`1` bond
     `(witnessY, 1)` where the field itself vanishes (`bondLaplacian_signDir01_at_witnessY_dir1`), so
     it is not an eigenvector (`signDir01_not_scalar`). Hence
     `bondLaplacianCov_not_scalar_on_subspace156G_trivialU`: `D_U D_U^*` is not `c · id` on the
     admissible subspace for ANY `c`, at `trivialU`; and
     `bondLaplacianCov_not_nonzero_scalar_on_subspace156G`: not `c · id` for any `c ≠ 0`, at EVERY
     `U`, by dimension alone.

   **Still NOT closed, and this note does not claim it is:** (i) the `C`-SANDWICHED form
   `RD.Cadj ∘ Base ∘ RD.C` — everything above is about the curl/Gram term `D_U D_U^*` itself, which is
   where this file's own analysis locates the non-scalarity, not about the sandwiched composite
   [⚠ **UPDATED 2026-07-28: §13 REDUCES (i) IN LEAN.** `ReparamDataSU2.retraction` makes the sandwich
   drop out on `V` (`inner_deltaKC_su2NonScalar_on_admissible`), so residual #1 follows from any two
   admissible vectors with different `⟪v,D_UD_U^*v⟫/‖v‖²`
   (`deltaKC_su2NonScalar_not_scalar_of_two_rayleigh`), for every `RD`, `U`, `Λ`, `S'`, `ell`. §13's
   banner prices the remaining two mechanical steps and confirms every ingredient exists. The claim
   that this "needs admissible witnesses this tree does not have" is now false: the kernel witness
   exists BY COUNTING, `168+128−192 = 104` times `dim 𝔰𝔲(2)`];
   ~~(ii) the case `c = 0` at a NON-FLAT `U`. For (ii) the reduction is proved and the two candidate
   missing primitives are priced in `NonDegenerateInstances.lean` §7's header (definiteness of
   `covSiteInner`, which the tree lacks; and `rank D_U^* > 24 · dim 𝔰𝔲(2)`, reachable by a
   32-bond scatter argument).~~

   ⚠ **(ii) IS NOW CLOSED — SECOND S75 PROPAGATION, 2026-07-27 (struck text retained, not deleted).**
   Two things in it were wrong. First, *"definiteness of `covSiteInner`, which the tree lacks"* was
   FALSE: `SuTwoInner.hsInner_self_eq_zero` was already in the tree and already consumed at
   `CovU1Reduction.lean:180`; `NonDegenerateInstances` §7d's own banner records that correction and
   builds `covSiteInner_self_eq_zero` from it. Second, `c = 0` at a NON-FLAT `U` is proved:
   `NonDegenerateInstances.bondLaplacianCov_not_scalar_on_subspace156G_univ_empty` (every `c`, every
   `U`, at `Λ := univ`, `S' := ∅`) and `…_not_scalar_nondegenerate` (every `c`, every `U`, at a PROPER
   `Λ` and a NONEMPTY `S'`), with the general forms
   `…_not_scalar_of_card_union` and `…_not_scalar_general_union` covering arbitrary `Λ`, `S'`, `ell`
   under an explicit decidable hypothesis. Also note the `158` quoted above is not sharp — the two
   locus clauses OVERLAP at that parameter point and the deduplicated bound is `161 · dim 𝔰𝔲(2)`
   (`NonDegenerateInstances.finrank_subspace156G_nondegenerate_sharp`); the `158` statement remains
   true and remains in that file.

   **What (ii)'s closure is NOT.** It is a statement about `bondLaplacianCovLM U` on `subspace156G`
   at the fixed lattice `witnessL`. It is NOT `Spine.coerc_u_main`'s non-scalarity conjunct and must
   not be cited as it: the two differ in carrier (`Bond witnessL → SuTwo` vs `AnchoredBondSpace Lat`),
   lattice (hard-coded `witnessL` vs arbitrary `Lat`), operator (`D_U D_U^*` vs the `C`-sandwiched
   `C^* Δ_k C`), scale (no `k` occurs at all), and the domain of the equality (a pointwise condition
   on members of `q1RealKernel U` vs an identity of continuous linear maps). Item (i) above is
   therefore untouched by any of this.
2. **`Δ_nonconstant`'s witness pair is NOT `IsRegularHolonomy _ 0`-regular.** `trivialU`/`adWitnessU`
   (this file's pair, chosen because their `bondLaplacianCovLM` VALUES are already fully computed in
   `BondSU2Space.lean`) has the SAME single-non-trivial-link shape as `RegularityHolonomy
   .centralHolonomyU`/`witnessU`, both PROVED NOT `Mα₀ = 0`-regular there (defect `8`/`4`
   respectively). So this file's `Uconfig` restriction uses a GENERIC, DISCLOSED-VACUOUS threshold
   `Mα₀ := 8` (`holonomyDefectSq_le_eight` below: EVERY `U` satisfies this bound, proved directly from
   `SU(2)`-unitarity, not asserted) ~~rather than `FaithfulCoercivitySU2.UconfigReg`'s genuine
   `Mα₀ = 0` filter. This is a REAL, DISCLOSED weakening of scope relative to
   `FaithfulCoercivitySU2.lean` (whose `Uconfig` restriction is a genuine, non-vacuous filter) —
   building a fresh `Mα₀ = 0`-regular pair with COMPUTED curl-operator difference (needs
   `pureGaugeU`'s own bond values pushed through `bondLaplacianCovLM`, not attempted anywhere yet)
   is a comparable-size task, named, not attempted.~~
   ⚠ **CORRECTED 2026-07-26, see §7's banner** (the struck text above is retained verbatim, not
   deleted): `FaithfulCoercivitySU2.UconfigReg`'s `Mα₀ = 0` is NOT a "genuine, non-vacuous filter";
   it is the FLAT SET (`NonFlatBackground.isRegularHolonomy_zero_iff_flat`), i.e. degenerate in the
   opposite direction. `Mα₀ := 8`'s vacuity was disclosed; `Mα₀ := 0`'s degeneracy was not. And the
   named task is not merely "not attempted": a fresh `Mα₀ = 0`-regular pair CANNOT be built in the
   sense that matters, because any such pair is FLAT (`uconfigReg_vs_uconfigReg8`, §7b) — a
   curl-operator difference between two flat backgrounds is a gauge-representative difference. The
   target to build against is `FaithfulCoercivitySU2.UconfigRegPos α` with `α > 0`.
3. ~~**Coercivity itself** (`gamma_exists_su2_nonscalar`) is left as ONE honest `sorry`, now over a
   GENUINE, non-scalar, PSD, self-adjoint operator — CMP99b p.428's actual deferred claim ("using the
   methods of Sect. B we can prove it"), never carried out anywhere in this corpus.~~

   ⚠ **CORRECTED 2026-07-28 (already_exists lane; struck text retained).** That `sorry` is not an
   honest open claim: **the statement is FALSE**, refuted in the kernel by
   `gamma_exists_su2_nonscalar_refuted` (§12) at data satisfying both of its own smallness
   hypotheses. §12b proves the REPAIRED statement
   (`gamma_exists_su2_nonscalar_repaired`, `faithfulCoercivityHypothesisSU2NonScalarRepaired`) with a
   single joint bound against the explicit uniform floor `m₀ := (2‖suTwoWitness‖²+1)⁻¹`. CMP99b
   p.428's deferred claim remains uncarried-out — the repaired theorem's coercivity is carried
   entirely by the scalar `(baseG+κ(U))⁻¹` term, not by any spectral property of `D_UD_U^*`.
-/

namespace AdalyFormal.Balaban.FaithfulDeltaKNonScalar

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLatticePlaquette PeriodicLinkConfiguration)
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL witnessY Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwoWitness suTwoWitness_ne_zero RMap RMap_one
  witnessZPoint)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU adWitnessU adWitnessInternalSite
  gradCovariantAdjointValue periodicLatticeShiftBack)
open AdalyFormal.Balaban.DeltaKUnified (BFL2 bfl2Equiv subspace156BFL2 subspace156BFL2_ne_bot)
open AdalyFormal.Balaban.BondSU2Space (bondLaplacianCovLM bondLaplacianCovLM_nonneg
  bondWitnessConfig bondWitnessConfig_at_target bondWitnessConfig_elsewhere
  bondLaplacianCovLM_trivialU_value bondLaplacianCovLM_adWitnessU_value
  bondLaplacianCovLM_genuinely_U_dependent)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.FaithfulCoercivitySU2 (kappa GinvSU2 GstarSU2 baseG sourceCorrectionSU2
  ReparamDataSU2 reparamDataSU2Witness reparamDataSU2_blocks_id reparamDataSU2_blocks_zero
  subspace156BFL2_ne_top)
open AdalyFormal.Balaban.RegularityHolonomy (IsRegularHolonomy holonomyDefectSq)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem)

/-! ## §1 — the kernel witness `constDirConfig`: a nonzero, TRANSLATION-INVARIANT (one-direction)
bond field, annihilated by the covariant divergence `D_U^*` at `U = trivialU`, by a general
(not case-by-case) cancellation. -/

/-- **`constDirConfig(b) := suTwoWitness` if `b`'s direction is `0`, else `0`** — depends ONLY on
the DIRECTION component of the bond, not the site. This single property is what forces the
covariant-divergence sum to cancel termwise at `U = 1` (§1's headline theorem below): the "inflow"
and "outflow" values agree because they read the SAME direction, regardless of which site. -/
noncomputable def constDirConfig : Bond witnessL → SuTwo :=
  fun b => if b.2 = (0 : Fin 3) then suTwoWitness else 0

/-- **`constDirConfig ≠ 0`** — nonzero at, e.g., the direction-`0` bond based at `witnessY`. -/
theorem constDirConfig_ne_zero : constDirConfig ≠ 0 := by
  intro h
  have h0 : constDirConfig (witnessY, (0 : Fin 3)) = 0 := by rw [h]; rfl
  simp only [constDirConfig] at h0
  exact suTwoWitness_ne_zero h0

/-- **THE CANCELLATION, general in `y`**: at `U = trivialU` (`RMap 1 = id`), the covariant
divergence's defining sum `Σ_μ [A(shiftBack y μ,μ) - A(y,μ)]` vanishes termwise because
`constDirConfig` reads the SAME value at `(shiftBack y μ, μ)` and `(y, μ)` — both depend only on
`μ`, never on the site coordinate. No lattice combinatorics beyond `rfl`/`sub_eq_zero` needed. -/
theorem constDirConfig_adjoint_zero (y : PeriodicLatticeSite witnessL) :
    gradCovariantAdjointValue (trivialU witnessL) constDirConfig y = 0 := by
  unfold gradCovariantAdjointValue
  apply Finset.sum_eq_zero
  intro mu _
  have hU : (trivialU witnessL) (periodicLatticeShiftBack y mu, mu) = 1 := rfl
  rw [hU, inv_one, RMap_one]
  simp only [LinearMap.id_coe, id_eq]
  unfold constDirConfig
  simp only [sub_eq_zero]

/-- **`constDirConfig` is genuinely in the kernel of `bondLaplacianCovLM (trivialU witnessL)`**:
the WHOLE function (every bond, not just one component) vanishes, since the outer `gradValueCovariant`
application of a function that is already `0` everywhere is `0`. -/
theorem bondLaplacianCovLM_constDirConfig_zero :
    bondLaplacianCovLM (trivialU witnessL) constDirConfig = 0 := by
  funext b
  show AdalyFormal.Balaban.CovariantOperators.gradValueCovariant (trivialU witnessL)
    (gradCovariantAdjointValue (trivialU witnessL) constDirConfig) b = 0
  unfold AdalyFormal.Balaban.CovariantOperators.gradValueCovariant
  rw [constDirConfig_adjoint_zero, constDirConfig_adjoint_zero, map_zero, sub_zero]

#print axioms constDirConfig_ne_zero
#print axioms constDirConfig_adjoint_zero
#print axioms bondLaplacianCovLM_constDirConfig_zero

/-! ## §2 — a general "not scalar" lemma, and the headline non-scalarity of `bondLaplacianCovLM`
on the BARE carrier, at `U = trivialU` -/

/-- **General fact**: if `T v1 = a • v1` for some nonzero `v1`, and `T v2 ≠ a • v2` for some `v2`,
then `T` is not a scalar multiple of the identity, for ANY scalar `c` — not merely for `c ≠ a`. -/
theorem not_scalar_of_two_ratios {E : Type*} [AddCommGroup E] [Module ℝ E]
    (T : E →ₗ[ℝ] E) (v1 v2 : E) (a : ℝ)
    (hv1 : T v1 = a • v1) (hv1ne : v1 ≠ 0) (hv2 : T v2 ≠ a • v2) (c : ℝ) :
    T ≠ c • (LinearMap.id : E →ₗ[ℝ] E) := by
  intro hcontra
  have h1 : (c • v1 : E) = a • v1 := by
    have hx := congrArg (fun f : E →ₗ[ℝ] E => f v1) hcontra
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hx
    rw [← hx, hv1]
  have hac : a = c := by
    have hsub : (a - c) • v1 = (0 : E) := by
      rw [sub_smul, h1]; abel
    rcases smul_eq_zero.mp hsub with h' | h'
    · linarith [sub_eq_zero.mp h']
    · exact absurd h' hv1ne
  apply hv2
  have hx2 := congrArg (fun f : E →ₗ[ℝ] E => f v2) hcontra
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hx2
  rw [hx2, ← hac]

/-- **THE HEADLINE: `bondLaplacianCovLM (trivialU witnessL)` IS NOT `c • id`, for EVERY `c : ℝ`
SIMULTANEOUSLY.** Take `a := 0`: `constDirConfig` is a nonzero kernel vector
(`bondLaplacianCovLM_constDirConfig_zero`, so `T v1 = 0 = 0 • v1`), while `bondWitnessConfig`'s
image is nonzero (`bondLaplacianCovLM_trivialU_value`: value `-suTwoWitness ≠ 0` at the bond
`(witnessZPoint,0)`, so `T v2 ≠ 0 = 0 • v2`). This is the pure curl operator's own non-scalarity,
BEFORE transport to `BFL2`/before any assembly with `κ(U)`/source terms. -/
theorem bondLaplacianCovLM_not_scalar (c : ℝ) :
    bondLaplacianCovLM (trivialU witnessL) ≠
      c • (LinearMap.id : (Bond witnessL → SuTwo) →ₗ[ℝ] (Bond witnessL → SuTwo)) := by
  apply not_scalar_of_two_ratios (bondLaplacianCovLM (trivialU witnessL)) constDirConfig
    bondWitnessConfig 0
  · rw [bondLaplacianCovLM_constDirConfig_zero, zero_smul]
  · exact constDirConfig_ne_zero
  · rw [zero_smul]
    intro hzero
    have h3 := congrFun hzero (witnessZPoint, (0 : Fin 3))
    rw [bondLaplacianCovLM_trivialU_value] at h3
    exact suTwoWitness_ne_zero (neg_eq_zero.mp h3)

#print axioms bondLaplacianCovLM_not_scalar

/-! ## §3 — transport to `BFL2 witnessL`, the SAME `su(2)` carrier `FaithfulCoercivitySU2.lean`
uses, via `DeltaKUnified.bfl2Equiv` (LAW-19: the identical "promote a bare-Pi-type construction
onto the `WithLp`-wrapped carrier" move `BondSU2Space.bondLaplacianCovLM_L2` already uses for the
DIFFERENT carrier `CovariantOperators.BondFnL2`, applied here to `BFL2`). -/

/-- `D_U D_U^*`, carried to `BFL2 witnessL` as a plain `LinearMap`. -/
noncomputable def curlLM_BFL2
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    BFL2 witnessL →ₗ[ℝ] BFL2 witnessL :=
  (bfl2Equiv (Lat := witnessL)).symm.toLinearMap ∘ₗ
    (bondLaplacianCovLM U) ∘ₗ (bfl2Equiv (Lat := witnessL)).toLinearMap

/-- **`curlCLM_BFL2`, the genuine `ContinuousLinearMap`** — typechecks directly against `BFL2`'s
own standing `NormedAddCommGroup`/`InnerProductSpace`/`FiniteDimensional` instances
(`DeltaKUnified.lean` §1), with no further instance work needed (measured: `LinearMap
.toContinuousLinearMap` on `BFL2 witnessL` compiles with zero additional instances, unlike the
`BondFnL2`/`SiteFnL2` carriers `BondSU2Space.lean`/`CovariantHjMinimizer.lean` needed a dedicated
§1 to unblock). -/
noncomputable def curlCLM_BFL2
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    BFL2 witnessL →L[ℝ] BFL2 witnessL :=
  LinearMap.toContinuousLinearMap (curlLM_BFL2 U)

theorem curlCLM_BFL2_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (v : BFL2 witnessL) :
    bfl2Equiv (Lat := witnessL) (curlCLM_BFL2 U v) =
      bondLaplacianCovLM U (bfl2Equiv (Lat := witnessL) v) := by
  show (bfl2Equiv (Lat := witnessL)) ((bfl2Equiv (Lat := witnessL)).symm
    (bondLaplacianCovLM U ((bfl2Equiv (Lat := witnessL)) v))) = _
  rw [LinearEquiv.apply_symm_apply]

#print axioms curlLM_BFL2
#print axioms curlCLM_BFL2
#print axioms curlCLM_BFL2_apply

/-! ## §4 — `curlCLM_BFL2` is genuinely PSD and self-adjoint w.r.t. `inner ℝ` (not merely
w.r.t. the bare `covBondInner`) -/

open AdalyFormal.Balaban.CovariantHj (covBondInner)
open AdalyFormal.Balaban.SuTwoInner (inner_eq_hsInner)

/-- **The `BFL2 witnessL` inner-product bridge**: `inner ℝ` on `BFL2` reduces to `covBondInner` on
the bare type — the SAME bridge `BondSU2Space.inner_bondFnL2_eq_covBondInner` proves for the
DIFFERENT carrier `BondFnL2`, re-derived here for `BFL2` (its `PiLp.innerProductSpace` instance is
the identical Mathlib family, `DeltaKUnified.lean` §1a). -/
theorem inner_bfl2_eq_covBondInner (A B : Bond witnessL → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A : BFL2 witnessL) (WithLp.toLp 2 B) : ℝ) = covBondInner A B := by
  unfold covBondInner
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun b _ => inner_eq_hsInner (A b) (B b))

#print axioms inner_bfl2_eq_covBondInner

/-- **PSD**: `0 ≤ ⟪v,curlCLM_BFL2(U)v⟫`, transported from `bondLaplacianCovLM_nonneg` (proved
w.r.t. the bare `covBondInner`) via the bridge above and `bfl2Equiv`'s round trip. -/
theorem curlCLM_BFL2_nonneg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (v : BFL2 witnessL) : (0 : ℝ) ≤ (inner ℝ v (curlCLM_BFL2 U v) : ℝ) := by
  have hrw : (inner ℝ v (curlCLM_BFL2 U v) : ℝ) =
      covBondInner (bfl2Equiv (Lat := witnessL) v)
        (bondLaplacianCovLM U (bfl2Equiv (Lat := witnessL) v)) := by
    conv_lhs => rw [← (bfl2Equiv (Lat := witnessL)).symm_apply_apply v]
    show (inner ℝ (WithLp.toLp 2 (bfl2Equiv (Lat := witnessL) v) : BFL2 witnessL)
      (curlCLM_BFL2 U ((bfl2Equiv (Lat := witnessL)).symm
        (bfl2Equiv (Lat := witnessL) v))) : ℝ) = _
    have hc : curlCLM_BFL2 U ((bfl2Equiv (Lat := witnessL)).symm
        (bfl2Equiv (Lat := witnessL) v)) =
        (WithLp.toLp 2 (bondLaplacianCovLM U (bfl2Equiv (Lat := witnessL) v)) : BFL2 witnessL) := by
      show (bfl2Equiv (Lat := witnessL)).symm
        (bondLaplacianCovLM U ((bfl2Equiv (Lat := witnessL))
          ((bfl2Equiv (Lat := witnessL)).symm (bfl2Equiv (Lat := witnessL) v)))) = _
      rw [LinearEquiv.apply_symm_apply]
      rfl
    rw [hc, inner_bfl2_eq_covBondInner]
  rw [hrw]
  exact bondLaplacianCovLM_nonneg U _

#print axioms curlCLM_BFL2_nonneg

/-! ## §5 — `deltaKBaseSU2NonScalar`: the assembled `Δ_k(U)` — `κ(U)`'s genuine (but scalar)
`Q1Real`-driven `U`-dependence PLUS `curlCLM_BFL2`'s genuine (and NON-scalar) `U`-dependence,
`a•id`, and the source correction, exactly mirroring `FaithfulCoercivitySU2.deltaKBaseOfSU2`'s
shape with ONE new summand. `bc.a`/source-term FIX: explicit smallness hypotheses replace the
prosecuted free parameters. -/

/-- **`Δ_k(U)`'s BASE part, UN-SCALARIZED**: `curlCLM_BFL2(U) + (QG₁Q*)⁻¹(U) − a·id +
sourceCorrection`. The first term is the genuine, non-scalar Route-A content (§2-§4); the remaining
three terms are `FaithfulCoercivitySU2`'s own machinery, UNCHANGED (LAW-19 reuse, not rebuilt). -/
noncomputable def deltaKBaseSU2NonScalar (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    BFL2 witnessL →L[ℝ] BFL2 witnessL :=
  curlCLM_BFL2 U + GinvSU2 U - usedAt bc 0 • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) +
    sourceCorrectionSU2 U v0 J

#print axioms deltaKBaseSU2NonScalar

/-! ## §6 — `deltaK_not_scalar`: THE MANDATED PROOF, on the FULL assembled operator, on the FULL
carrier `BFL2 witnessL` (CMP99b (3.156)'s own domain, before the (3.157) `C`-reparametrization) -/

/-- **A CLM-level version of `not_scalar_of_two_ratios`** — same argument, restated for
`ContinuousLinearMap`s (needed since `deltaKBaseSU2NonScalar` lands in `→L[ℝ]`, not `→ₗ[ℝ]`). -/
theorem not_scalar_of_two_ratios_CLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (v1 v2 : E) (a : ℝ)
    (hv1 : T v1 = a • v1) (hv1ne : v1 ≠ 0) (hv2 : T v2 ≠ a • v2) (c : ℝ) :
    T ≠ c • (1 : E →L[ℝ] E) := by
  intro hcontra
  have h1 : (c • v1 : E) = a • v1 := by
    have hx := congrArg (fun f : E →L[ℝ] E => f v1) hcontra
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at hx
    rw [← hx, hv1]
  have hac : a = c := by
    have hsub : (a - c) • v1 = (0 : E) := by
      rw [sub_smul, h1]; abel
    rcases smul_eq_zero.mp hsub with h' | h'
    · linarith [sub_eq_zero.mp h']
    · exact absurd h' hv1ne
  apply hv2
  have hx2 := congrArg (fun f : E →L[ℝ] E => f v2) hcontra
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at hx2
  rw [hx2, ← hac]

/-- **`deltaKBaseSU2NonScalar`'s value at `v1 := bfl2Equiv.symm constDirConfig`**: the curl term
vanishes (`constDirConfig` is in its kernel at `trivialU`), so the WHOLE assembled operator reduces
to the pure scalar-term contribution `a₀ • v1`, `a₀ := (baseG+κ(trivialU))⁻¹ - usedAt bc 0 +
sourceCorrection's own scalar`. -/
theorem deltaKBaseSU2NonScalar_v1
    (bc : BaseConstant) (v0 J : BFL2 witnessL) :
    deltaKBaseSU2NonScalar bc v0 J (trivialU witnessL)
        ((bfl2Equiv (Lat := witnessL)).symm constDirConfig) =
      ((baseG + kappa (trivialU witnessL))⁻¹ - usedAt bc 0 +
          (-2 * (inner ℝ (AdalyFormal.Balaban.VariationalProjectorH1.solutionOperator
            (AdalyFormal.Balaban.FaithfulCoercivitySU2.su2CovarianceData (trivialU witnessL)) v0)
            J : ℝ))) •
        ((bfl2Equiv (Lat := witnessL)).symm constDirConfig) := by
  unfold deltaKBaseSU2NonScalar
  show curlCLM_BFL2 (trivialU witnessL) ((bfl2Equiv (Lat := witnessL)).symm constDirConfig) +
      GinvSU2 (trivialU witnessL) ((bfl2Equiv (Lat := witnessL)).symm constDirConfig) -
      usedAt bc 0 • ((bfl2Equiv (Lat := witnessL)).symm constDirConfig) +
      sourceCorrectionSU2 (trivialU witnessL) v0 J
        ((bfl2Equiv (Lat := witnessL)).symm constDirConfig) = _
  have hcurl : curlCLM_BFL2 (trivialU witnessL)
      ((bfl2Equiv (Lat := witnessL)).symm constDirConfig) = 0 := by
    apply (bfl2Equiv (Lat := witnessL)).injective
    rw [curlCLM_BFL2_apply, LinearEquiv.apply_symm_apply, bondLaplacianCovLM_constDirConfig_zero,
      map_zero]
  have hGinv : GinvSU2 (trivialU witnessL) ((bfl2Equiv (Lat := witnessL)).symm constDirConfig) =
      (baseG + kappa (trivialU witnessL))⁻¹ •
        ((bfl2Equiv (Lat := witnessL)).symm constDirConfig) := rfl
  have hsrc : sourceCorrectionSU2 (trivialU witnessL) v0 J
      ((bfl2Equiv (Lat := witnessL)).symm constDirConfig) =
      (-2 * (inner ℝ (AdalyFormal.Balaban.VariationalProjectorH1.solutionOperator
        (AdalyFormal.Balaban.FaithfulCoercivitySU2.su2CovarianceData (trivialU witnessL)) v0)
        J : ℝ)) • ((bfl2Equiv (Lat := witnessL)).symm constDirConfig) := rfl
  rw [hcurl, hGinv, hsrc, zero_add, ← sub_smul, ← add_smul]

#print axioms deltaKBaseSU2NonScalar_v1

/-- **THE MANDATED THEOREM: `deltaK_not_scalar`.** `deltaKBaseSU2NonScalar bc v0 J (trivialU
witnessL)` is NOT `c • id` for ANY `c : ℝ` — the assembled `Δ_k(trivialU)`, curl term + `κ`-scalar
+ `a`-term + source term TOGETHER, is provably non-scalar on the FULL carrier `BFL2 witnessL`.
Witnesses: `v1 := bfl2Equiv.symm constDirConfig` (ratio `a₀`, the scalar-only value, §6's own
computation) and `v2 := bfl2Equiv.symm bondWitnessConfig` (a DIFFERENT ratio, since the curl term's
contribution there is nonzero and does not cancel against ANY value of `a₀` — proved by the same
kernel-checked bond-component evaluation `bondLaplacianCovLM_not_scalar` already used). -/
theorem deltaK_not_scalar (bc : BaseConstant) (v0 J : BFL2 witnessL) (c : ℝ) :
    deltaKBaseSU2NonScalar bc v0 J (trivialU witnessL) ≠ c • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) := by
  set v1 : BFL2 witnessL := (bfl2Equiv (Lat := witnessL)).symm constDirConfig with hv1def
  set v2 : BFL2 witnessL := (bfl2Equiv (Lat := witnessL)).symm bondWitnessConfig with hv2def
  set a₀ : ℝ := (baseG + kappa (trivialU witnessL))⁻¹ - usedAt bc 0 +
    (-2 * (inner ℝ (AdalyFormal.Balaban.VariationalProjectorH1.solutionOperator
      (AdalyFormal.Balaban.FaithfulCoercivitySU2.su2CovarianceData (trivialU witnessL)) v0)
      J : ℝ)) with ha0def
  apply not_scalar_of_two_ratios_CLM (deltaKBaseSU2NonScalar bc v0 J (trivialU witnessL)) v1 v2 a₀
  · exact deltaKBaseSU2NonScalar_v1 bc v0 J
  · intro h
    apply constDirConfig_ne_zero
    have := congrArg (bfl2Equiv (Lat := witnessL)) h
    simpa [hv1def] using this
  · -- `deltaKBaseSU2NonScalar bc v0 J (trivialU) v2 ≠ a₀ • v2`: evaluate the bond component
    -- `(witnessZPoint,0)`, where `v2`'s underlying value is `0`, so EVERY scalar-shaped summand
    -- contributes exactly `0` there — leaving only the curl term's own (nonzero) value.
    intro hcontra
    have hcomp := congrArg (fun w : BFL2 witnessL => (bfl2Equiv (Lat := witnessL)) w)
      hcontra
    have hv2zero : bondWitnessConfig (witnessZPoint, (0 : Fin 3)) = 0 :=
      bondWitnessConfig_elsewhere (by decide)
    have hlhs : (bfl2Equiv (Lat := witnessL))
        (deltaKBaseSU2NonScalar bc v0 J (trivialU witnessL) v2) (witnessZPoint, (0 : Fin 3)) =
        bondLaplacianCovLM (trivialU witnessL) bondWitnessConfig (witnessZPoint, (0 : Fin 3)) := by
      have hunfold : deltaKBaseSU2NonScalar bc v0 J (trivialU witnessL) v2 =
          curlCLM_BFL2 (trivialU witnessL) v2 + GinvSU2 (trivialU witnessL) v2 -
            usedAt bc 0 • v2 + sourceCorrectionSU2 (trivialU witnessL) v0 J v2 := rfl
      have hGinv2 : GinvSU2 (trivialU witnessL) v2 =
          (baseG + kappa (trivialU witnessL))⁻¹ • v2 := rfl
      have hsrc2 : sourceCorrectionSU2 (trivialU witnessL) v0 J v2 =
          (-2 * (inner ℝ (AdalyFormal.Balaban.VariationalProjectorH1.solutionOperator
            (AdalyFormal.Balaban.FaithfulCoercivitySU2.su2CovarianceData (trivialU witnessL)) v0)
            J : ℝ)) • v2 := rfl
      have hv2coord : (bfl2Equiv (Lat := witnessL)) v2 (witnessZPoint, (0 : Fin 3)) = 0 := by
        rw [hv2def]; rw [LinearEquiv.apply_symm_apply]; exact hv2zero
      have hcurlcoord : (bfl2Equiv (Lat := witnessL)) (curlCLM_BFL2 (trivialU witnessL) v2)
          (witnessZPoint, (0 : Fin 3)) =
          bondLaplacianCovLM (trivialU witnessL) bondWitnessConfig (witnessZPoint, (0 : Fin 3)) := by
        rw [curlCLM_BFL2_apply, hv2def, LinearEquiv.apply_symm_apply]
      rw [hunfold, hGinv2, hsrc2]
      simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      rw [hv2coord, hcurlcoord]
      simp
    have hrhs : (bfl2Equiv (Lat := witnessL)) (a₀ • v2) (witnessZPoint, (0 : Fin 3)) =
        a₀ • bondWitnessConfig (witnessZPoint, (0 : Fin 3)) := by
      have hv2coord : (bfl2Equiv (Lat := witnessL)) v2 (witnessZPoint, (0 : Fin 3)) =
          bondWitnessConfig (witnessZPoint, (0 : Fin 3)) := by
        rw [hv2def]; rw [LinearEquiv.apply_symm_apply]
      simp only [map_smul, Pi.smul_apply]
      rw [hv2coord]
    have hcompPt := congrFun hcomp (witnessZPoint, (0 : Fin 3))
    rw [hlhs, hrhs, hv2zero, smul_zero, bondLaplacianCovLM_trivialU_value] at hcompPt
    exact suTwoWitness_ne_zero (neg_eq_zero.mp hcompPt)

#print axioms deltaK_not_scalar

/-! ## §7 — `UconfigReg8`: a GENERIC (disclosed-vacuous) regularity threshold admitting BOTH
`trivialU` and `adWitnessU` — needed so `Δ_nonconstant`'s witness pair (chosen for its ALREADY
fully-computed curl-operator difference) is well-typed as a pair of REGULAR configurations, per
`CoercivityHypothesis`'s own `Uconfig` slot. Named residual #2 in the module docstring: ~~this is
STRICTLY WEAKER than `FaithfulCoercivitySU2.UconfigReg`'s genuine `Mα₀ = 0` filter.~~

⚠ **CORRECTED 2026-07-26 (`compute/uconfigreg_reindex/`).** That comparison is backwards in the
way that matters, on both halves:

* **"genuine"** — `FaithfulCoercivitySU2.UconfigReg` is `{U // IsRegularHolonomy U 0}`, and
  `NonFlatBackground.isRegularHolonomy_zero_iff_flat` proves `IsRegularHolonomy U 0 ↔ ∀ p,
  holonomyElem U p = 1`. At threshold `0` the "regular" set is EXACTLY THE FLAT SET: it contains no
  configuration with curvature at all. It is not a genuine filter on Bałaban's regularity
  condition, it is the degenerate endpoint of it. Its degeneracy was NEVER disclosed anywhere in
  this tree until 2026-07-26; `UconfigReg8`'s vacuity, by contrast, was disclosed in this very
  docstring from the start.
* **"STRICTLY WEAKER"** — as a FILTER `Mα₀ = 8` is indeed weaker (it admits everything), but the
  quantified CLAIM it induces (`∀ U : UconfigReg8, …`) is strictly STRONGER than the one over
  `UconfigReg`, because it quantifies over a strictly larger set. And in the sense the physics
  cares about, `UconfigReg8` is the LESS degenerate of the two: it CONTAINS backgrounds with
  nonzero curvature, and `UconfigReg` provably does not (`uconfigReg_vs_uconfigReg8`, §7b).

Both thresholds are degenerate, in opposite directions: `0` admits nothing curved, `8` admits
everything. Bałaban's condition is `0 < Mα₀` SMALL; the non-degenerate domain is
`FaithfulCoercivitySU2.UconfigRegPos α` for `α > 0`, which contains curved backgrounds
(`FaithfulCoercivitySU2.exists_curved_mem_UconfigRegPos`) while excluding large curvature. -/

/-- **Every `holonomyDefectSq` value is `≤ 8`, for EVERY `U`** — proved directly from `SU(2)`
unitarity (the same columns-are-unit-vectors argument `holonomyDefectSq_nonneg` uses for the LOWER
bound `≥ 0`, mirrored here for the upper one: `Re(g_00), Re(g_11) ≥ -1` from `normSq ≤ 1`, giving
`Re(tr g) ≥ -2`, hence `defect = 4 - 2Re(tr g) ≤ 8`). Consequently `IsRegularHolonomy U 8` holds
for EVERY `U` — this specific threshold is DISCLOSED VACUOUS, not a genuine filter. -/
theorem holonomyDefectSq_le_eight {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : holonomyDefectSq U p ≤ 8 := by
  set g : Matrix (Fin 2) (Fin 2) ℂ := (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) with hg
  have hmem : g ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    have hm : g ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := SetLike.coe_mem (holonomyElem U p)
    exact (Matrix.mem_specialUnitaryGroup_iff.mp hm).1
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hmem
  have hrow0 := congrFun (congrFun hmem 0) 0
  have hrow1 := congrFun (congrFun hmem 1) 1
  simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply] at hrow0 hrow1
  have e00 : g 0 0 * star (g 0 0) = (Complex.normSq (g 0 0) : ℂ) := by
    rw [← starRingEnd_apply]; exact Complex.mul_conj (g 0 0)
  have e10 : g 0 1 * star (g 0 1) = (Complex.normSq (g 0 1) : ℂ) := by
    rw [← starRingEnd_apply]; exact Complex.mul_conj (g 0 1)
  have e01 : g 1 0 * star (g 1 0) = (Complex.normSq (g 1 0) : ℂ) := by
    rw [← starRingEnd_apply]; exact Complex.mul_conj (g 1 0)
  have e11 : g 1 1 * star (g 1 1) = (Complex.normSq (g 1 1) : ℂ) := by
    rw [← starRingEnd_apply]; exact Complex.mul_conj (g 1 1)
  rw [e00, e10] at hrow0
  rw [e01, e11] at hrow1
  have hcol0' : Complex.normSq (g 0 0) + Complex.normSq (g 0 1) = 1 := by
    have := congrArg Complex.re hrow0; simpa using this
  have h00le : Complex.normSq (g 0 0) ≤ 1 := by
    nlinarith [Complex.normSq_nonneg (g 0 1)]
  have hcol1' : Complex.normSq (g 1 0) + Complex.normSq (g 1 1) = 1 := by
    have := congrArg Complex.re hrow1; simpa using this
  have h11le : Complex.normSq (g 1 1) ≤ 1 := by
    nlinarith [Complex.normSq_nonneg (g 1 0)]
  have hre00 : -1 ≤ (g 0 0).re := by
    have hns : Complex.normSq (g 0 0) = (g 0 0).re * (g 0 0).re + (g 0 0).im * (g 0 0).im :=
      Complex.normSq_apply (g 0 0)
    nlinarith [sq_nonneg ((g 0 0).im), sq_nonneg ((g 0 0).re + 1)]
  have hre11 : -1 ≤ (g 1 1).re := by
    have hns : Complex.normSq (g 1 1) = (g 1 1).re * (g 1 1).re + (g 1 1).im * (g 1 1).im :=
      Complex.normSq_apply (g 1 1)
    nlinarith [sq_nonneg ((g 1 1).im), sq_nonneg ((g 1 1).re + 1)]
  have htrace : (Matrix.trace g).re = (g 0 0).re + (g 1 1).re := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Complex.add_re]
  unfold holonomyDefectSq
  rw [← hg, htrace]
  linarith

#print axioms holonomyDefectSq_le_eight

/-- **The (disclosed-vacuous) regular-`U` subtype**, at the GENERIC threshold `8`. -/
abbrev UconfigReg8 := {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  witnessL // IsRegularHolonomy U (8 : ℝ)}

noncomputable def uReg8_0 : UconfigReg8 :=
  ⟨trivialU witnessL, fun p => holonomyDefectSq_le_eight (trivialU witnessL) p⟩

noncomputable def uReg8_1 : UconfigReg8 :=
  ⟨adWitnessU, fun p => holonomyDefectSq_le_eight adWitnessU p⟩

theorem uReg8_0_ne_uReg8_1 : uReg8_0 ≠ uReg8_1 := by
  intro h
  have hval : (trivialU witnessL) = adWitnessU := congrArg Subtype.val h
  have h0 : adWitnessU (adWitnessInternalSite, (1 : Fin 3)) =
      (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by rw [← hval]; rfl
  have h1 : adWitnessU (adWitnessInternalSite, (1 : Fin 3)) =
      AdalyFormal.Balaban.CovariantOperators.witnessMElem := by
    unfold adWitnessU; rw [if_pos rfl]
  rw [h1] at h0
  exact AdalyFormal.Balaban.DeltaKFull.witnessMElem_ne_one h0

instance : Nontrivial UconfigReg8 := ⟨uReg8_0, uReg8_1, uReg8_0_ne_uReg8_1⟩

#print axioms uReg8_0_ne_uReg8_1

/-! ### §7b — THE CORRECTED COMPARISON, AS A THEOREM (2026-07-26)

The §7 banner's correction, made checkable rather than asserted. -/

/-- **`UconfigReg8` IS VACUOUS AS A FILTER BUT CONTAINS CURVED BACKGROUNDS;
`FaithfulCoercivitySU2.UconfigReg` IS A STRICT FILTER AND CONTAINS NONE.**

Three clauses:
1. `IsRegularHolonomy U 8` for EVERY `U` — the disclosed vacuity of the `8` threshold.
2. `UconfigReg8` nevertheless contains a background with NONZERO CURVATURE (`witnessU`, whose
   plaquette holonomy is `witnessMElem ≠ 1`, `NonFlatBackground.witnessU_curvature_ne_one`).
3. `FaithfulCoercivitySU2.UconfigReg` contains NO such background, for any witness
   (`FaithfulCoercivitySU2.no_curved_mem_UconfigReg`).

So on the axis that matters — does the domain of `∀ U` see the gauge field's curvature at all —
the `Mα₀ = 0` domain is the degenerate one, and the docstring calling it "genuine" and calling
`Mα₀ = 8` "strictly weaker" had the comparison backwards.

**OPS-3 — how this fails.** Clause 1 is false at any threshold `< 8` (`RegularityHolonomy
.holonomyDefectSq_centralHolonomyU_witnessPlaquette` computes the value `8`, attained). Clause 2
fails if `witnessU` is replaced by `pureGaugeU`, which is FLAT
(`NonFlatBackground.pureGaugeU_holonomy_eq_one`) — the substitution that produced the original
mislabelling. Clause 3 is the exact negation of clause 2's shape at threshold `0`, and would be
false at ANY positive threshold (`FaithfulCoercivitySU2.exists_curved_mem_UconfigRegPos`). -/
theorem uconfigReg_vs_uconfigReg8 :
    (∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL,
        IsRegularHolonomy U (8 : ℝ)) ∧
      (∃ U : UconfigReg8, ∃ p : PeriodicLatticePlaquette witnessL,
        holonomyElem U.val p ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
      ¬ ∃ U : AdalyFormal.Balaban.FaithfulCoercivitySU2.UconfigReg,
          ∃ p : PeriodicLatticePlaquette witnessL,
            holonomyElem U.val p ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨fun U p => holonomyDefectSq_le_eight U p,
    ⟨⟨AdalyFormal.Balaban.CovariantOperators.witnessU,
        fun p => holonomyDefectSq_le_eight _ p⟩,
      AdalyFormal.Balaban.CovariantOperators.witnessPlaquette,
      AdalyFormal.Balaban.NonFlatBackground.witnessU_curvature_ne_one⟩,
    AdalyFormal.Balaban.FaithfulCoercivitySU2.no_curved_mem_UconfigReg⟩

#print axioms uconfigReg_vs_uconfigReg8

/-! ## §8 — `Δ_nonconstant`, PROVED on `deltaKBaseSU2NonScalar` (the UNSANDWICHED operator,
`V := ⊤`, matching `Coercivity.lean`'s own Gap-1 precedent — the C-sandwiched/`V`-restricted
version is named residual #1 above, not attempted). Reuses the SAME bond-component evaluation
trick as `deltaK_not_scalar`: `bondWitnessConfig` vanishes at `(witnessZPoint,0)`, so every
scalar-shaped summand contributes exactly `0` there for EITHER `U`, leaving only the curl term's
own (already fully computed, differing) value. -/

theorem deltaKBaseSU2NonScalar_nonconstant (bc : BaseConstant) (v0 J : BFL2 witnessL) :
    deltaKBaseSU2NonScalar bc v0 J (trivialU witnessL) ≠
      deltaKBaseSU2NonScalar bc v0 J adWitnessU := by
  intro hcontra
  set v2 : BFL2 witnessL := (bfl2Equiv (Lat := witnessL)).symm bondWitnessConfig with hv2def
  have hcomp := congrArg (fun f : BFL2 witnessL →L[ℝ] BFL2 witnessL =>
    (bfl2Equiv (Lat := witnessL)) (f v2)) hcontra
  have hcompPt := congrFun hcomp (witnessZPoint, (0 : Fin 3))
  have hv2zero : bondWitnessConfig (witnessZPoint, (0 : Fin 3)) = 0 :=
    bondWitnessConfig_elsewhere (by decide)
  have key : ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL,
      (bfl2Equiv (Lat := witnessL)) (deltaKBaseSU2NonScalar bc v0 J U v2)
        (witnessZPoint, (0 : Fin 3)) =
        bondLaplacianCovLM U bondWitnessConfig (witnessZPoint, (0 : Fin 3)) := by
    intro U
    have hunfold : deltaKBaseSU2NonScalar bc v0 J U v2 =
        curlCLM_BFL2 U v2 + GinvSU2 U v2 - usedAt bc 0 • v2 + sourceCorrectionSU2 U v0 J v2 := rfl
    have hGinv2 : GinvSU2 U v2 = (baseG + kappa U)⁻¹ • v2 := rfl
    have hsrc2 : sourceCorrectionSU2 U v0 J v2 =
        (-2 * (inner ℝ (AdalyFormal.Balaban.VariationalProjectorH1.solutionOperator
          (AdalyFormal.Balaban.FaithfulCoercivitySU2.su2CovarianceData U) v0) J : ℝ)) • v2 := rfl
    have hv2coord : (bfl2Equiv (Lat := witnessL)) v2 (witnessZPoint, (0 : Fin 3)) = 0 := by
      rw [hv2def]; rw [LinearEquiv.apply_symm_apply]; exact hv2zero
    have hcurlcoord : (bfl2Equiv (Lat := witnessL)) (curlCLM_BFL2 U v2)
        (witnessZPoint, (0 : Fin 3)) =
        bondLaplacianCovLM U bondWitnessConfig (witnessZPoint, (0 : Fin 3)) := by
      rw [curlCLM_BFL2_apply, hv2def, LinearEquiv.apply_symm_apply]
    rw [hunfold, hGinv2, hsrc2]
    simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [hv2coord, hcurlcoord]
    simp
  rw [key, key] at hcompPt
  rw [bondLaplacianCovLM_trivialU_value, bondLaplacianCovLM_adWitnessU_value] at hcompPt
  apply suTwoWitness_ne_zero
  have h2 : (2 : ℝ) • suTwoWitness = 0 := by
    linear_combination (norm := module) (-1 : ℝ) • hcompPt
  rcases smul_eq_zero.mp h2 with h' | h'
  · norm_num at h'
  · exact h'

#print axioms deltaKBaseSU2NonScalar_nonconstant

/-! ## §9 — THE DELIVERABLE: `faithfulCoercivityHypothesisSU2NonScalar`, `V := ⊤` (Gap-1
precedent, `Coercivity.lean`), the `bc.a`/source-term FIX, ONE honest sorry over the GENUINE,
non-scalar, PSD operator `deltaKBaseSU2NonScalar`. -/

/-- **THE `bc.a` FIX**: `hbc` explicitly bounds `usedAt bc 0 ≤ 1/2`, blocking BOTH published
counterexamples (`bc.a := 2 > 1/2` cannot even be supplied — the hypothesis fails to typecheck a
call with that value). `hvJ` bounds the source term the same way (S82: guards the analogous
attack via unboundedly large `⟪v0,J⟫`, since a mutation making the source term arbitrarily
negative would defeat any FIXED `bc` bound).

**⚠⚠ REFUTED — THIS STATEMENT IS FALSE (already_exists lane, 2026-07-28; S75 propagation).** The two
`1/2` bounds are each fine and JOINTLY EXACTLY TOO WEAK: at `bc.a = 1/2` and `2⟪v0,J⟫ = 1/2` (both
PERMITTED, with equality) the operator's value at the curl-kernel vector
`v₁ := bfl2Equiv.symm constDirConfig` is `((baseG+κ(trivialU))⁻¹ − 1)·‖v₁‖² < 0`, so no `γ > 0` can
exist. Kernel-checked: `gamma_exists_su2_nonscalar_refuted` (§12). **The `sorry` below is therefore
NOT closable and is deliberately left in place** — closing it is impossible (L4: no
`sorry`→axiom) and weakening the statement to make it provable is forbidden (L5). The REPAIRED
statement, with ONE joint bound against the explicit uniform floor `m₀ := (2‖suTwoWitness‖²+1)⁻¹`, is
PROVED sorry-free as `gamma_exists_su2_nonscalar_repaired` (§12b), and
`faithfulCoercivityHypothesisSU2NonScalarRepaired` is the resulting sorry-free
`CoercivityHypothesis`. **Consumers must migrate to the repaired forms.**

**Prior art in this tree, disclosed (LAW-19).** `U1CurlCoercivity.lean` PART A already carried this
refutation at the SAME witness — `smallBC := ⟨1/2,_⟩`, `smallJ` with `⟪v1,smallJ⟫ = 1/4`, `a0_neg`,
`no_nonneg_comparison_survives_at_v1`, `no_curl_relative_coercivity_su2nonscalar` — proving no
nonnegative-functional-relative bound survives at `v₁`. What §12 adds is (i) the refutation stated in
the EXACT `∃bc v0 J` shape of THIS theorem with `hbc`,`hvJ` discharged, which is what makes the
theorem-as-typed false rather than one comparison false, and (ii) the repair itself, which
`U1CurlCoercivity`'s own "does NOT close" list names as owed and prices exactly as done here ("tying
`a` to the INFIMUM of the operator's positive scalar part"). -/
theorem gamma_exists_su2_nonscalar (bc : BaseConstant) (hbc : usedAt bc 0 ≤ (1 : ℝ) / 2)
    (v0 J : BFL2 witnessL)
    (hvJ : |2 * (inner ℝ (AdalyFormal.Balaban.VariationalProjectorH1.solutionOperator
      (AdalyFormal.Balaban.FaithfulCoercivitySU2.su2CovarianceData (trivialU witnessL)) v0)
      J : ℝ)| ≤ (1 : ℝ) / 2) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (k : ℕ) (U : UconfigReg8) (v : BFL2 witnessL),
      γ * ‖v‖ ^ 2 ≤ (inner ℝ v (deltaKBaseSU2NonScalar bc v0 J U.val v) : ℝ) := by
  sorry

/-- **⚠ RESTS ON A REFUTED STATEMENT (2026-07-28).** `γ''`/`coercive` below are `Classical.choose`
of `gamma_exists_su2_nonscalar`, which §12 proves FALSE; this definition therefore carries `sorryAx`
and cannot be repaired in place without weakening (L5). Use
`faithfulCoercivityHypothesisSU2NonScalarRepaired` (§12b) instead — same `Δ`, `V`, `V_ne_bot`,
`Δ_nonconstant`, sorry-free `coercive`. Retained, not deleted, because downstream modules reference
it and because deleting the record would erase the defect's history.

**THE FULL DELIVERABLE**: `Δ`, `V := ⊤`, `V_ne_bot`, `Δ_nonconstant` — ALL PROVED, `sorry`-free;
`Δ_nonconstant` DERIVED from the genuinely non-scalar curl operator's own `U`-dependence (§8), not
assumed. `coercive`/`γ''` are the ONE honest, deferred claim (`gamma_exists_su2_nonscalar`), now
over a provably NON-SCALAR operator (`deltaK_not_scalar`, §6) — the load-bearing repair this
dispatch was for. -/
noncomputable def faithfulCoercivityHypothesisSU2NonScalar
    (bc : BaseConstant) (hbc : usedAt bc 0 ≤ (1 : ℝ) / 2) (v0 J : BFL2 witnessL)
    (hvJ : |2 * (inner ℝ (AdalyFormal.Balaban.VariationalProjectorH1.solutionOperator
      (AdalyFormal.Balaban.FaithfulCoercivitySU2.su2CovarianceData (trivialU witnessL)) v0)
      J : ℝ)| ≤ (1 : ℝ) / 2) :
    AdalyFormal.Balaban.CoercivityHypothesis (BFL2 witnessL) UconfigReg8 where
  Δ := fun _ U => deltaKBaseSU2NonScalar bc v0 J U.val
  V := ⊤
  V_ne_bot := Submodule.ne_bot_iff ⊤ |>.mpr
    ⟨(bfl2Equiv (Lat := witnessL)).symm constDirConfig, Submodule.mem_top, by
      intro h
      apply constDirConfig_ne_zero
      have := congrArg (bfl2Equiv (Lat := witnessL)) h
      simpa using this⟩
  Δ_nonconstant := ⟨0, uReg8_0, uReg8_1, uReg8_0_ne_uReg8_1,
    deltaKBaseSU2NonScalar_nonconstant bc v0 J⟩
  γ'' := Classical.choose (gamma_exists_su2_nonscalar bc hbc v0 J hvJ)
  γ''_pos := (Classical.choose_spec (gamma_exists_su2_nonscalar bc hbc v0 J hvJ)).1
  coercive := fun k U v _ =>
    (Classical.choose_spec (gamma_exists_su2_nonscalar bc hbc v0 J hvJ)).2 k U v

#print axioms faithfulCoercivityHypothesisSU2NonScalar

/-! ## §10 — JUNK-INHABITATION AUDIT (S91/OPS-3): the `bc.a` exploit is now BLOCKED AT THE TYPE
LEVEL, not merely shown to break a bound. -/

/-- **`bc.a := 2` (both prosecutions' exact counterexample value) CANNOT be supplied** — `hbc`
requires `usedAt bc 0 ≤ 1/2`, and `usedAt bc 0 = bc.a` (`ConstantA.usedAt`, `rfl`), so `bc.a := 2`
fails `hbc`'s own hypothesis at the call site, not merely at the (now-`sorry`) conclusion. -/
example (bigBC : BaseConstant) (hbig : bigBC.a = 2) : ¬ (usedAt bigBC 0 ≤ (1 : ℝ) / 2) := by
  unfold usedAt; rw [hbig]; norm_num

/-! ## §11 — `deltaKC_su2NonScalar`: the `(3.157)` `C`-REPARAMETRIZATION SANDWICH, KEEPING
`FaithfulCoercivitySU2`'s three structural defect-fixes RE-WIRED against the un-scalarized base
operator (LAW-19 reuse of `ReparamDataSU2`/`reparamDataSU2Witness`/`reparamDataSU2_blocks_id`/
`_zero`/`subspace156BFL2_ne_top` — none rebuilt). ~~Non-scalarity of THIS sandwiched, `V`-restricted
operator is named residual #1 (module docstring) — NOT attempted here (needs admissible witnesses
this tree does not have).~~ **REDUCED 2026-07-28, §13 below: the sandwich drops out on `V` and the
whole question becomes two Rayleigh quotients; no new witness is needed, the kernel one is forced by
a dimension count whose two inputs are already proved.** What IS delivered: a genuine, well-typed `C*Δ_kC` assembly over the
UN-SCALARIZED base, with `C := id`/`C := 0` STILL structurally excluded (the SAME theorems apply
unchanged, since `ReparamDataSU2`'s obligations do not depend on which operator it sandwiches) and
`J ≠ 0` available as an explicit guard on the constructor below (mirroring
`FaithfulCoercivitySU2.faithfulCoercivityHypothesisSU2`'s own `_hJ` pattern — an honestly-disclosed
UNUSED wrapper hypothesis there too, per Sol's own finding on that file; reproduced here, not a new
defect). -/

/-- **`C*Δ_kC`, over the UN-SCALARIZED base `deltaKBaseSU2NonScalar`.** -/
noncomputable def deltaKC_su2NonScalar (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    BFL2 witnessL →L[ℝ] BFL2 witnessL :=
  RD.Cadj ∘L (deltaKBaseSU2NonScalar bc v0 J U) ∘L RD.C

/-- **`C := id`/`C := 0` remain STRUCTURALLY EXCLUDED** for this sandwich — inherited verbatim from
`FaithfulCoercivitySU2.reparamDataSU2_blocks_id`/`_zero` (those theorems constrain `ReparamDataSU2`
itself, independent of which operator it will sandwich), restated here as this section's own audit
summary, `sorry`-free. -/
theorem deltaKC_su2NonScalar_C_not_id_or_zero :
    (¬ ∃ RD : ReparamDataSU2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
        AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL),
        RD.C = (0 : BFL2 witnessL →L[ℝ] BFL2 witnessL)) ∧
    (¬ ∃ RD : ReparamDataSU2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
        AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL),
        RD.C = (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL)) :=
  ⟨reparamDataSU2_blocks_zero,
    reparamDataSU2_blocks_id (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
      AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL)⟩

/-- **A CONCRETE, non-degenerate witness `RD`** — literally `reparamDataSU2Witness`, reused
verbatim (LAW-19); `deltaKC_su2NonScalar` at this `RD` is a genuine, fully-assembled, well-typed
`C*Δ_kC` object over the un-scalarized `Δ_k(U)`. -/
noncomputable example (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    BFL2 witnessL →L[ℝ] BFL2 witnessL :=
  deltaKC_su2NonScalar bc v0 J (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
    AdalyFormal.Balaban.AdmissibleSubspace.witnessEll
    (reparamDataSU2Witness Finset.univ ∅ AdalyFormal.Balaban.AdmissibleSubspace.witnessEll
      (trivialU witnessL)) U

#print axioms deltaKC_su2NonScalar
#print axioms deltaKC_su2NonScalar_C_not_id_or_zero

/-! ## §12 — **`gamma_exists_su2_nonscalar` IS FALSE AS WRITTEN** (already_exists lane, 2026-07-28),
and the REPAIRED statement, PROVED

**Fact, not a verdict.** §9's `gamma_exists_su2_nonscalar` (`sorry`, still present and untouched
below/above — a false statement cannot be closed and must not be weakened, L5) is REFUTED here in the
kernel: `gamma_exists_su2_nonscalar_refuted` exhibits `bc,v0,J` satisfying BOTH of §9's own smallness
hypotheses `hbc`,`hvJ` for which NO positive `γ` exists.

**Why (the arithmetic, in exact rationals).** `§12`'s first result computes the quadratic form
exactly:
`⟪v,Δ_k(U)v⟫ = ⟪v,D_UD_U^*v⟫ + ((baseG+κ(U))⁻¹ − bc.a − 2⟪v0,J⟫)·‖v‖²`
(the source scalar is `U`-independent because `solutionOperator (su2CovarianceData U) = id`
unconditionally — `FaithfulCoercivitySU2.solutionOperator_su2_eq_id`, that file's own disclosed
consequence of `Q := 1`). Now:
* the curl term is PSD (`curlCLM_BFL2_nonneg`) but has a NONZERO KERNEL at `trivialU`
  (`bondLaplacianCovLM_constDirConfig_zero`), so it contributes EXACTLY `0` at `v := v₁`;
* `baseG + κ(trivialU) > 1` strictly (`baseG = ‖suTwoWitness‖²+1` and `kappa_trivialU_pos`), hence
  `(baseG+κ(trivialU))⁻¹ < 1`;
* `hbc` PERMITS `bc.a = 1/2` and `hvJ` PERMITS `2⟪v0,J⟫ = 1/2`, summing to exactly `1`.
So at that admissible data `⟪v₁,Δ_k(trivialU)v₁⟫ = ((baseG+κ(1))⁻¹ − 1)·‖v₁‖² < 0`, while every
`γ > 0` demands `γ‖v₁‖² > 0`. The two `1/2` bounds §9 chose as "this file's own honest smallness
bound" are each individually fine and JOINTLY EXACTLY TOO WEAK — they leave no room against the
`(baseG+κ)⁻¹ ≤ 1` ceiling that the same docstring cites. `trivialU ∈ UconfigReg8` (`uReg8_0`), so
the refutation lives inside §9's own quantifier domain.

**The repair, PROVED (`gamma_exists_su2_nonscalar_repaired`).** Replace the two independent `1/2`s by
ONE joint bound against the EXPLICIT uniform floor the tree already supports:
`m₀ := (2‖suTwoWitness‖²+1)⁻¹ ≤ (baseG+κ(U))⁻¹` for EVERY `U` (from `kappa_bound`'s
`|κ(U)| ≤ ‖suTwoWitness‖²`), and require `bc.a + 2⟪v0,J⟫ ≤ m₀/2`. Then `γ := m₀/2` works, uniformly
in `k` and `U`. `§12`'s non-vacuity witness shows the repaired hypothesis is satisfiable at
`v0 ≠ 0`, `J ≠ 0`, `⟪v0,J⟫ ≠ 0` and `bc.a > 0` — it is not the `v0=J=0` degenerate point.

**What §12 does NOT claim.** The coercivity it proves is carried ENTIRELY by the scalar
`(baseG+κ(U))⁻¹` term; the curl term contributes only `≥ 0` and cannot contribute more (it has a
kernel). So this is not a spectral-gap statement about `D_UD_U^*`, and it is not CMP99b p.428's
deferred claim. It is the honest statement of what THIS assembled operator satisfies. -/

/-- **THE POINTWISE VALUE of `deltaKBaseSU2NonScalar`**: the curl term plus ONE explicit real scalar
times the identity — the scalar's source part `U`-INDEPENDENT via `solutionOperator_su2_eq_id`. Every
later result in §12/§13 is a corollary of this one line. -/
theorem deltaKBaseSU2NonScalar_apply (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (v : BFL2 witnessL) :
    deltaKBaseSU2NonScalar bc v0 J U v =
      curlCLM_BFL2 U v +
        ((baseG + kappa U)⁻¹ - usedAt bc 0 - 2 * (inner ℝ v0 J : ℝ)) • v := by
  show curlCLM_BFL2 U v + GinvSU2 U v - usedAt bc 0 • v + sourceCorrectionSU2 U v0 J v = _
  have hG : GinvSU2 U v = (baseG + kappa U)⁻¹ • v := rfl
  have hs : sourceCorrectionSU2 U v0 J v =
      (-2 * (inner ℝ (AdalyFormal.Balaban.VariationalProjectorH1.solutionOperator
        (AdalyFormal.Balaban.FaithfulCoercivitySU2.su2CovarianceData U) v0) J : ℝ)) • v := rfl
  rw [hG, hs, AdalyFormal.Balaban.FaithfulCoercivitySU2.solutionOperator_su2_eq_id]
  module

/-- **THE EXACT QUADRATIC FORM of `deltaKBaseSU2NonScalar`.** -/
theorem deltaKBaseSU2NonScalar_quadForm (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (v : BFL2 witnessL) :
    (inner ℝ v (deltaKBaseSU2NonScalar bc v0 J U v) : ℝ) =
      (inner ℝ v (curlCLM_BFL2 U v) : ℝ) +
        ((baseG + kappa U)⁻¹ - usedAt bc 0 - 2 * (inner ℝ v0 J : ℝ)) * ‖v‖ ^ 2 := by
  rw [deltaKBaseSU2NonScalar_apply, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]

#print axioms deltaKBaseSU2NonScalar_apply
#print axioms deltaKBaseSU2NonScalar_quadForm

/-- **`v₁`, the curl kernel vector, as a `BFL2` element** — §1's `constDirConfig`, transported. -/
noncomputable def constDirBFL2 : BFL2 witnessL :=
  (bfl2Equiv (Lat := witnessL)).symm constDirConfig

theorem constDirBFL2_ne_zero : constDirBFL2 ≠ 0 := by
  intro h
  apply constDirConfig_ne_zero
  have := congrArg (bfl2Equiv (Lat := witnessL)) h
  simpa [constDirBFL2] using this

theorem constDirBFL2_norm_sq_pos : 0 < ‖constDirBFL2‖ ^ 2 :=
  pow_pos (norm_pos_iff.mpr constDirBFL2_ne_zero) 2

theorem constDirBFL2_norm_ne_zero : ‖constDirBFL2‖ ≠ 0 :=
  norm_ne_zero_iff.mpr constDirBFL2_ne_zero

/-- **The curl term VANISHES at `v₁`, at `trivialU`** — `constDirConfig` is in `D_1D_1^*`'s kernel. -/
theorem curlCLM_BFL2_constDirBFL2_zero :
    curlCLM_BFL2 (trivialU witnessL) constDirBFL2 = 0 := by
  apply (bfl2Equiv (Lat := witnessL)).injective
  rw [curlCLM_BFL2_apply, constDirBFL2, LinearEquiv.apply_symm_apply,
    bondLaplacianCovLM_constDirConfig_zero, map_zero]

#print axioms constDirBFL2_ne_zero
#print axioms constDirBFL2_norm_sq_pos
#print axioms constDirBFL2_norm_ne_zero
#print axioms curlCLM_BFL2_constDirBFL2_zero

/-- **`(baseG+κ(trivialU))⁻¹ < 1`** — `baseG = ‖suTwoWitness‖²+1 ≥ 1` and `κ(trivialU) > 0`. -/
theorem ginv_scalar_trivialU_lt_one : (baseG + kappa (trivialU witnessL))⁻¹ < 1 := by
  have hk := AdalyFormal.Balaban.FaithfulCoercivitySU2.kappa_trivialU_pos
  have hsq : (0 : ℝ) ≤ ‖(suTwoWitness : SuTwo)‖ ^ 2 := sq_nonneg _
  have hgt : (1 : ℝ) < baseG + kappa (trivialU witnessL) := by
    show (1 : ℝ) < ‖(suTwoWitness : SuTwo)‖ ^ 2 + 1 + kappa (trivialU witnessL)
    linarith
  have hpos : (0 : ℝ) < baseG + kappa (trivialU witnessL) := by linarith
  rw [inv_eq_one_div, div_lt_one hpos]
  exact hgt

#print axioms ginv_scalar_trivialU_lt_one

/-- **THE REFUTATION.** `bc.a := 1/2`, `J := v₁`, `v0 := (1/(4‖v₁‖²))•v₁` — both of §9's smallness
hypotheses hold (`hvJ` with EQUALITY, `|2·(1/4)| = 1/2`), and no positive `γ` exists. -/
theorem gamma_exists_su2_nonscalar_refuted :
    ∃ (bc : BaseConstant) (v0 J : BFL2 witnessL),
      usedAt bc 0 ≤ (1 : ℝ) / 2 ∧
      |2 * (inner ℝ (AdalyFormal.Balaban.VariationalProjectorH1.solutionOperator
        (AdalyFormal.Balaban.FaithfulCoercivitySU2.su2CovarianceData (trivialU witnessL)) v0)
        J : ℝ)| ≤ (1 : ℝ) / 2 ∧
      ¬ ∃ γ : ℝ, 0 < γ ∧ ∀ (k : ℕ) (U : UconfigReg8) (v : BFL2 witnessL),
        γ * ‖v‖ ^ 2 ≤ (inner ℝ v (deltaKBaseSU2NonScalar bc v0 J U.val v) : ℝ) := by
  have hnsq : (0 : ℝ) < ‖constDirBFL2‖ ^ 2 := constDirBFL2_norm_sq_pos
  have hne : ‖constDirBFL2‖ ≠ 0 := constDirBFL2_norm_ne_zero
  refine ⟨⟨1 / 2, by norm_num⟩, (1 / (4 * ‖constDirBFL2‖ ^ 2)) • constDirBFL2, constDirBFL2,
    by norm_num [usedAt], ?_, ?_⟩
  · rw [AdalyFormal.Balaban.FaithfulCoercivitySU2.solutionOperator_su2_eq_id,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [show 1 / (4 * ‖constDirBFL2‖ ^ 2) * ‖constDirBFL2‖ ^ 2 = 1 / 4 by
      field_simp]
    norm_num
  · rintro ⟨γ, hγ, hbound⟩
    have hb := hbound 0 uReg8_0 constDirBFL2
    have hval : (inner ℝ constDirBFL2 (deltaKBaseSU2NonScalar ⟨1 / 2, by norm_num⟩
        ((1 / (4 * ‖constDirBFL2‖ ^ 2)) • constDirBFL2) constDirBFL2
        (uReg8_0 : UconfigReg8).val constDirBFL2) : ℝ) =
        ((baseG + kappa (trivialU witnessL))⁻¹ - 1) * ‖constDirBFL2‖ ^ 2 := by
      have hU : (uReg8_0 : UconfigReg8).val = trivialU witnessL := rfl
      rw [hU, deltaKBaseSU2NonScalar_quadForm, curlCLM_BFL2_constDirBFL2_zero, inner_zero_right,
        real_inner_smul_left, real_inner_self_eq_norm_sq]
      have hinner : (1 / (4 * ‖constDirBFL2‖ ^ 2)) * ‖constDirBFL2‖ ^ 2 = 1 / 4 := by field_simp
      rw [hinner]
      show (0 : ℝ) + ((baseG + kappa (trivialU witnessL))⁻¹ - usedAt ⟨1 / 2, by norm_num⟩ 0
        - 2 * (1 / 4)) * ‖constDirBFL2‖ ^ 2 = _
      have ha : usedAt (⟨1 / 2, by norm_num⟩ : BaseConstant) 0 = 1 / 2 := rfl
      rw [ha]
      ring
    rw [hval] at hb
    have hlt := ginv_scalar_trivialU_lt_one
    nlinarith

#print axioms gamma_exists_su2_nonscalar_refuted

/-! ### §12b — the REPAIRED statement, PROVED -/

/-- **The EXPLICIT uniform floor `m₀ := (2‖suTwoWitness‖²+1)⁻¹`** — every factor counted:
`baseG = ‖suTwoWitness‖²+1` by definition and `|κ(U)| ≤ ‖suTwoWitness‖²` by `kappa_bound`, so
`baseG+κ(U) ≤ 2‖suTwoWitness‖²+1` for EVERY `U`. -/
theorem baseG_add_kappa_le_uniform
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    baseG + kappa U ≤ 2 * ‖(suTwoWitness : SuTwo)‖ ^ 2 + 1 := by
  have h := abs_le.mp (AdalyFormal.Balaban.FaithfulCoercivitySU2.kappa_bound U)
  show ‖(suTwoWitness : SuTwo)‖ ^ 2 + 1 + kappa U ≤ _
  linarith [h.2]

theorem ginv_scalar_lower_uniform
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    (2 * ‖(suTwoWitness : SuTwo)‖ ^ 2 + 1)⁻¹ ≤ (baseG + kappa U)⁻¹ := by
  have hpos : (0 : ℝ) < baseG + kappa U := by
    linarith [AdalyFormal.Balaban.FaithfulCoercivitySU2.baseG_add_kappa_pos U]
  have hle := baseG_add_kappa_le_uniform U
  have hpos2 : (0 : ℝ) < 2 * ‖(suTwoWitness : SuTwo)‖ ^ 2 + 1 := by positivity
  rw [inv_eq_one_div, inv_eq_one_div, div_le_div_iff₀ hpos2 hpos]
  linarith

#print axioms baseG_add_kappa_le_uniform
#print axioms ginv_scalar_lower_uniform

/-- **THE REPAIRED COERCIVITY, PROVED (no `sorry`).** ONE joint smallness bound against the explicit
uniform floor `m₀`, in place of §9's two independent `1/2`s (which `gamma_exists_su2_nonscalar_refuted`
proves are jointly too weak). `γ := m₀/2`, uniform in `k` and `U`. -/
theorem gamma_exists_su2_nonscalar_repaired (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (hsmall : usedAt bc 0 + 2 * (inner ℝ v0 J : ℝ) ≤
      (2 * ‖(suTwoWitness : SuTwo)‖ ^ 2 + 1)⁻¹ / 2) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (k : ℕ) (U : UconfigReg8) (v : BFL2 witnessL),
      γ * ‖v‖ ^ 2 ≤ (inner ℝ v (deltaKBaseSU2NonScalar bc v0 J U.val v) : ℝ) := by
  refine ⟨(2 * ‖(suTwoWitness : SuTwo)‖ ^ 2 + 1)⁻¹ / 2, by positivity, fun _ U v => ?_⟩
  rw [deltaKBaseSU2NonScalar_quadForm]
  have hcurl := curlCLM_BFL2_nonneg U.val v
  have hlow := ginv_scalar_lower_uniform U.val
  have hnv : (0 : ℝ) ≤ ‖v‖ ^ 2 := sq_nonneg _
  have hcoef : (2 * ‖(suTwoWitness : SuTwo)‖ ^ 2 + 1)⁻¹ / 2 ≤
      (baseG + kappa U.val)⁻¹ - usedAt bc 0 - 2 * (inner ℝ v0 J : ℝ) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hcoef hnv]

#print axioms gamma_exists_su2_nonscalar_repaired

/-- **THE REPAIRED HYPOTHESIS IS NON-VACUOUS AT NONZERO DATA (S82/S91 guard).** `v0 ≠ 0`, `J ≠ 0`,
`⟪v0,J⟫ ≠ 0`, `bc.a > 0`: the repaired bound is not satisfied only at the `v0=J=0` degenerate
point. Data: `bc.a := m₀/8`, `J := v₁`, `v0 := (m₀/(16‖v₁‖²))•v₁`, so `2⟪v0,J⟫ = m₀/8` and the sum is
`m₀/4 ≤ m₀/2`. -/
theorem gamma_exists_su2_nonscalar_repaired_nonvacuous :
    ∃ (bc : BaseConstant) (v0 J : BFL2 witnessL),
      v0 ≠ 0 ∧ J ≠ 0 ∧ (inner ℝ v0 J : ℝ) ≠ 0 ∧
      usedAt bc 0 + 2 * (inner ℝ v0 J : ℝ) ≤
        (2 * ‖(suTwoWitness : SuTwo)‖ ^ 2 + 1)⁻¹ / 2 := by
  have hnsq : (0 : ℝ) < ‖constDirBFL2‖ ^ 2 := constDirBFL2_norm_sq_pos
  have hne : ‖constDirBFL2‖ ≠ 0 := constDirBFL2_norm_ne_zero
  set m : ℝ := (2 * ‖(suTwoWitness : SuTwo)‖ ^ 2 + 1)⁻¹ with hm
  have hmpos : 0 < m := by rw [hm]; positivity
  have hinner : (inner ℝ ((m / (16 * ‖constDirBFL2‖ ^ 2)) • constDirBFL2) constDirBFL2 : ℝ) =
      m / 16 := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  refine ⟨⟨m / 8, by positivity⟩, (m / (16 * ‖constDirBFL2‖ ^ 2)) • constDirBFL2, constDirBFL2,
    ?_, constDirBFL2_ne_zero, ?_, ?_⟩
  · intro h
    have : (inner ℝ ((m / (16 * ‖constDirBFL2‖ ^ 2)) • constDirBFL2) constDirBFL2 : ℝ) = 0 := by
      rw [h, inner_zero_left]
    rw [hinner] at this
    linarith
  · rw [hinner]; positivity
  · rw [hinner]
    show m / 8 + 2 * (m / 16) ≤ m / 2
    linarith

#print axioms gamma_exists_su2_nonscalar_repaired_nonvacuous

/-- **THE REPAIRED FULL DELIVERABLE, `sorry`-FREE.** Identical to §9's
`faithfulCoercivityHypothesisSU2NonScalar` except that `γ''`/`coercive` come from the PROVED
`gamma_exists_su2_nonscalar_repaired` instead of the refuted `sorry`. `Δ`, `V := ⊤`, `V_ne_bot`,
`Δ_nonconstant` are §9's, unchanged. `#print axioms` on this definition carries NO `sorryAx`. -/
noncomputable def faithfulCoercivityHypothesisSU2NonScalarRepaired
    (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (hsmall : usedAt bc 0 + 2 * (inner ℝ v0 J : ℝ) ≤
      (2 * ‖(suTwoWitness : SuTwo)‖ ^ 2 + 1)⁻¹ / 2) :
    AdalyFormal.Balaban.CoercivityHypothesis (BFL2 witnessL) UconfigReg8 where
  Δ := fun _ U => deltaKBaseSU2NonScalar bc v0 J U.val
  V := ⊤
  V_ne_bot := Submodule.ne_bot_iff ⊤ |>.mpr
    ⟨constDirBFL2, Submodule.mem_top, constDirBFL2_ne_zero⟩
  Δ_nonconstant := ⟨0, uReg8_0, uReg8_1, uReg8_0_ne_uReg8_1,
    deltaKBaseSU2NonScalar_nonconstant bc v0 J⟩
  γ'' := Classical.choose (gamma_exists_su2_nonscalar_repaired bc v0 J hsmall)
  γ''_pos := (Classical.choose_spec (gamma_exists_su2_nonscalar_repaired bc v0 J hsmall)).1
  coercive := fun k U v _ =>
    (Classical.choose_spec (gamma_exists_su2_nonscalar_repaired bc v0 J hsmall)).2 k U v

#print axioms faithfulCoercivityHypothesisSU2NonScalarRepaired

/-! ## §13 — **RESIDUAL #1 (the `C`-SANDWICHED, `V`-RESTRICTED operator) REDUCED IN LEAN**
(already_exists lane, 2026-07-28)

The module docstring's residual #1 says non-scalarity of `RD.Cadj ∘ Base ∘ RD.C` restricted to
`v ∈ subspace156BFL2` is "a fresh construction problem this file does not attempt (needs witnesses
this tree does not have)". **The sandwich is not the obstacle.** `ReparamDataSU2.retraction` says
`C v = v` for every `v ∈ V`, and `adjoint_law` then gives, for `v ∈ V`,

`⟪v, C^*Δ_k(U)C v⟫ = ⟪v, D_UD_U^*v⟫ + s(U)·‖v‖²`,  `s(U) := (baseG+κ(U))⁻¹ − bc.a − 2⟪v0,J⟫`

with NO reference to `C` at all (§13's `inner_deltaKC_su2NonScalar_on_admissible`). Hence
scalarity on `V` forces the RAYLEIGH QUOTIENT `⟪v,D_UD_U^*v⟫/‖v‖²` to be CONSTANT on `V`, and
residual #1 follows from ANY two admissible vectors with different quotients
(`deltaKC_su2NonScalar_not_scalar_of_two_rayleigh`) — in particular from one admissible vector in
`ker D_U^*` and one outside it (`deltaKC_su2NonScalar_not_scalar_of_kernel_and_positive`).
This holds for EVERY `RD`, not just `reparamDataSU2Witness`, and for EVERY `U`, `Λ`, `S'`, `ell`.

**What is left, priced, with every ingredient's existence CONFIRMED (OPS-5).** Two admissible
vectors with different quotients, at `Λ := univ`, `S' := ∅`:
* the NON-KERNEL one: `NonDegenerateInstances.signDir01SuTwo` lies in `subspace156G` (that file's
  `signDir01_mem_subspace156G`) and `D_1D_1^*` sends it to `4 • suTwoWitness` at `(witnessY,1)`
  (`bondLaplacian_signDir01_at_witnessY_dir1`), so `D_1^*` does not kill it and its quotient is
  `> 0` once `⟪v,D D^*v⟫ = ‖D^*v‖²` is routed through `covSiteInner`;
* the KERNEL one exists BY COUNTING, and the count closes: `dim V ≥ 168·dim 𝔰𝔲(2)`
  (`finrank_subspace156BFL2_univ_empty`), `dim ker D_U^* ≥ 192·dim 𝔰𝔲(2) − 64·dim 𝔰𝔲(2)`
  (`finrank_ker_gradAdjoint_lower`), ambient `192·dim 𝔰𝔲(2)` (`finrank_bondFn`), so by
  `Submodule.finrank_sup_add_finrank_inf_eq`
  `dim (V ⊓ ker D_U^*) ≥ 168 + 128 − 192 = 104` times `dim 𝔰𝔲(2)`, hence `> 0`.
  **This is the OPPOSITE inequality to §7d's** (which showed `V ⊄ ker(D_UD_U^*)`); both hold, and
  together they say `V` meets the kernel AND is not inside it — exactly two different quotients.

~~The two remaining mechanical steps are (i) transporting `subspace156G`-membership and
`ker (gradCovariantAdjointLM U)` across `bfl2Equiv` into the `BFL2` carrier, and (ii) the
`⟪v,D D^*v⟫ = ‖D^*v‖²` identity in `covSiteInner`.~~ Neither is a construction problem and neither
needs a new witness — which is what residual #1's own text asserted was missing. `NonDegenerateInstances`
is importable from here without a cycle (it imports only `DeltaKUnified` and `BondSU2Space`, both
already ancestors of this file); this section deliberately does NOT add that import, so that the
reduction below stands on this file's existing dependencies alone.

⚠ **RESIDUAL #1 IS CLOSED (2026-07-28, faithful_chain lane).** Both steps are DONE, in
`Balaban/FaithfulRepairNonScalarRayleigh.lean` (which does add the import, exactly as priced here):
step (ii) is `inner_curl_eq_covSiteInner` (every `U`), step (i) is `signDir01BFL2_mem` and
`kerAdjBFL2`/`finrank_kerAdjBFL2`, the dimension count is `finrank_inf_lower`
(`104·dim 𝔰𝔲(2) ≤ dim (V ⊓ ker D_U^*)`, every `U`, every `ell`), and the conclusion is
`deltaKC_su2NonScalar_not_scalar_on_V` — the `C`-sandwiched, `V`-restricted operator is NOT `c • id`
on `subspace156BFL2 univ ∅ ell (trivialU witnessL)`, for every `bc`, `v0`, `J`, `ell`, `RD`, `c`.
`#print axioms`: no `sorryAx`. The residual's own text ("needs witnesses this tree does not have")
was wrong twice over — the tree had them, and the counting route this section priced is the one that
worked. The conclusion is at `U = trivialU` only because
`NonDegenerateInstances.bondLaplacian_signDir01_at_witnessY_dir1` is the tree's only computed nonzero
curl VALUE; `deltaKC_su2NonScalar_not_scalar_on_V_general` takes that value as a hypothesis so a
curved-`U` extension costs exactly one computation. -/

/-- `⟪v, C^* v⟫ = ‖v‖²` for admissible `v` — `adjoint_law` then `retraction`. -/
theorem inner_Cadj_self_on_admissible
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    (v : BFL2 witnessL) (hv : v ∈ subspace156BFL2 Lambda S' ell (trivialU witnessL)) :
    (inner ℝ v (RD.Cadj v) : ℝ) = ‖v‖ ^ 2 := by
  rw [← RD.adjoint_law v v, RD.retraction v hv, real_inner_self_eq_norm_sq]

/-- `⟪v, C^*(D_UD_U^*v)⟫ = ⟪v, D_UD_U^*v⟫` for admissible `v` — the `C` drops out entirely. -/
theorem inner_Cadj_curl_on_admissible
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (v : BFL2 witnessL) (hv : v ∈ subspace156BFL2 Lambda S' ell (trivialU witnessL)) :
    (inner ℝ v (RD.Cadj (curlCLM_BFL2 U v)) : ℝ) = (inner ℝ v (curlCLM_BFL2 U v) : ℝ) := by
  rw [← RD.adjoint_law v (curlCLM_BFL2 U v), RD.retraction v hv]

#print axioms inner_Cadj_self_on_admissible
#print axioms inner_Cadj_curl_on_admissible

/-- **THE SANDWICH DROPS OUT ON `V`**: the quadratic form of `C^*Δ_k(U)C` at an admissible `v` is the
curl term's own quadratic form plus `s(U)·‖v‖²` — no `C` anywhere. -/
theorem inner_deltaKC_su2NonScalar_on_admissible (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (v : BFL2 witnessL) (hv : v ∈ subspace156BFL2 Lambda S' ell (trivialU witnessL)) :
    (inner ℝ v (deltaKC_su2NonScalar bc v0 J Lambda S' ell RD U v) : ℝ) =
      (inner ℝ v (curlCLM_BFL2 U v) : ℝ) +
        ((baseG + kappa U)⁻¹ - usedAt bc 0 - 2 * (inner ℝ v0 J : ℝ)) * ‖v‖ ^ 2 := by
  have hstep : deltaKC_su2NonScalar bc v0 J Lambda S' ell RD U v =
      RD.Cadj (deltaKBaseSU2NonScalar bc v0 J U v) := by
    show RD.Cadj (deltaKBaseSU2NonScalar bc v0 J U (RD.C v)) = _
    rw [RD.retraction v hv]
  rw [hstep, deltaKBaseSU2NonScalar_apply, map_add, map_smul, inner_add_right,
    real_inner_smul_right, inner_Cadj_curl_on_admissible Lambda S' ell RD U v hv,
    inner_Cadj_self_on_admissible Lambda S' ell RD v hv]

#print axioms inner_deltaKC_su2NonScalar_on_admissible

/-- **RESIDUAL #1, REDUCED: two different Rayleigh quotients on `V` kill scalarity of the
SANDWICHED operator**, for every `c`, every `RD`, every `U`. The hypothesis is stated
cross-multiplied to avoid division. -/
theorem deltaKC_su2NonScalar_not_scalar_of_two_rayleigh (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (v1 v2 : BFL2 witnessL)
    (h1 : v1 ∈ subspace156BFL2 Lambda S' ell (trivialU witnessL))
    (h2 : v2 ∈ subspace156BFL2 Lambda S' ell (trivialU witnessL))
    (hray : (inner ℝ v1 (curlCLM_BFL2 U v1) : ℝ) * ‖v2‖ ^ 2 ≠
      (inner ℝ v2 (curlCLM_BFL2 U v2) : ℝ) * ‖v1‖ ^ 2)
    (c : ℝ) :
    ¬ (∀ v ∈ subspace156BFL2 Lambda S' ell (trivialU witnessL),
        deltaKC_su2NonScalar bc v0 J Lambda S' ell RD U v = c • v) := by
  intro hscal
  set sU : ℝ := (baseG + kappa U)⁻¹ - usedAt bc 0 - 2 * (inner ℝ v0 J : ℝ) with hsU
  have key : ∀ w ∈ subspace156BFL2 Lambda S' ell (trivialU witnessL),
      (inner ℝ w (curlCLM_BFL2 U w) : ℝ) = (c - sU) * ‖w‖ ^ 2 := by
    intro w hw
    have hq := inner_deltaKC_su2NonScalar_on_admissible bc v0 J Lambda S' ell RD U w hw
    rw [hscal w hw, real_inner_smul_right, real_inner_self_eq_norm_sq] at hq
    rw [← hsU] at hq
    linarith
  rw [key v1 h1, key v2 h2] at hray
  apply hray
  ring

#print axioms deltaKC_su2NonScalar_not_scalar_of_two_rayleigh

/-- **THE USABLE FORM**: one admissible vector killed by the covariant divergence (Rayleigh `0`) and
one admissible vector with nonzero curl-form suffice. The counting route in §13's banner supplies
exactly this pair at `Λ := univ`, `S' := ∅`. -/
theorem deltaKC_su2NonScalar_not_scalar_of_kernel_and_positive (bc : BaseConstant)
    (v0 J : BFL2 witnessL) (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (v1 v2 : BFL2 witnessL)
    (h1 : v1 ∈ subspace156BFL2 Lambda S' ell (trivialU witnessL))
    (h2 : v2 ∈ subspace156BFL2 Lambda S' ell (trivialU witnessL))
    (hv1 : v1 ≠ 0) (hker : curlCLM_BFL2 U v1 = 0)
    (hpos : (inner ℝ v2 (curlCLM_BFL2 U v2) : ℝ) ≠ 0) (c : ℝ) :
    ¬ (∀ v ∈ subspace156BFL2 Lambda S' ell (trivialU witnessL),
        deltaKC_su2NonScalar bc v0 J Lambda S' ell RD U v = c • v) := by
  refine deltaKC_su2NonScalar_not_scalar_of_two_rayleigh bc v0 J Lambda S' ell RD U v1 v2 h1 h2
    ?_ c
  rw [hker, inner_zero_right, zero_mul]
  have hn1 : ‖v1‖ ^ 2 ≠ 0 := by
    have : (0 : ℝ) < ‖v1‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv1) 2
    exact ne_of_gt this
  exact (mul_ne_zero hpos hn1).symm

#print axioms deltaKC_su2NonScalar_not_scalar_of_kernel_and_positive

end AdalyFormal.Balaban.FaithfulDeltaKNonScalar
