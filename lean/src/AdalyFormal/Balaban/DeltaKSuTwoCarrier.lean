/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CovariantHjFaithful
import AdalyFormal.Balaban.CoercivityRegular
import AdalyFormal.Balaban.SchurNonzero

set_option autoImplicit false

/-!
# `DeltaKSuTwoCarrier.lean` — a `ℕ`-INDEXED OPERATOR FAMILY ON THE su(2) CARRIER

Additive module. No file outside it is edited.

## §0 — THE FINDING, STATED FIRST

`GOAL_LEMMA.md` §7e records a measured gap: *no operator family on `BondFnL2 L` anywhere in the
tree carries a `ℕ` scale argument*, so `CoercUMainPinnedDelta.PinnedCoercivity` has no `k` binder
and claims no RG uniformity. This file closes that gap by CONSTRUCTION.

`deltaKTowerCLM ell k levels U : BondFnL2 L →L[ℝ] BondFnL2 L` is a genuine `ℕ`-indexed family of
`ContinuousLinearMap`s on the su(2)-valued carrier, at a concrete
`U : PeriodicLinkConfiguration (SU(2)) L`, and it is **PROVED `k`-dependent** at an explicit
background, at EVERY level (`deltaKTowerCLM_zero_ne_level`) — not `k`-inert like
`CoercUMainRegular.regularDelta` (`regularDelta_k_constant`).

**What the object IS, stated before any theorem.** `⟨A, Δ̂_k A⟩` is the MINIMISED covariant curl
energy over the level-`k` averaging fibre through `A`, intersected with the `levels`
gauge-tangent subspace: the Schur complement of the fine covariant curl form relative to
`Q_k(U)`. §1 derives, from three adjudicated source pages, that this is CMP99b (3.156)'s `Δ_k`
**at `J = 0`, with `Δ_π` replaced by the bare covariant curl and the gauge-fixing penalty
`‖RD*A‖²` replaced by the `levels` constraint**. §1.5 states exactly what that leaves out. Nothing
below is billed as the complete (3.156).

## §1 — THE SOURCE (quoted with locators, image-verified; LAW-11)

### §1.1 — What is to be built: CMP99b (3.156), printed p.428

`corpus/pages/CMP99b_p428.md`, `verification_status: adjudicated`; source PDF
`balaban_CMP99_1985_propagators_backgroundfield.pdf` sha256 `39f8033b…d542861`, pdf page 40;
400 dpi render `corpus/renders/CMP99b_p428-40.png` sha256
`128b1172e7090661d2c2ead70d9514244567c17a43c709ff87b18603b3012d54`. VERBATIM:

> "integral can be written also as
>
>   `⟨B, (QG₁Q*)⁻¹B⟩ - a⟨B,B⟩ - 2⟨H₁ D̃⁽²⁾(B), J⟩ = ⟨B, Δ_k B⟩.`   (3.156)
>
> This form is considered on the subspace `{B : B = 0 on Λᶜ, B = 0 on ⋃_{y∈Λ'} Ax(y), Q₁B = 0}`."

and, same page, VERBATIM:

> "`e^{(1/2)⟨g, C^{(k)}(Λ)g⟩} = (Z'^{(k)}(Λ))⁻¹ ∫ dB̃ exp[-½⟨B̃, C*Δ_kC B̃⟩ + ⟨B̃, C*g⟩]`
>  `                          = e^{(1/2)⟨C*g, (C*Δ_kC)⁻¹C*g⟩},`   (3.157)"

The pairing symbol in (3.156)'s third term is `J`, not `g` — that page's own MANDATORY
adjudication note, re-verified there by 1.8× crop, with
`corpus/pdftotext_crosscheck/CMP99b_p428.txt` garbled at exactly this locus.

### §1.2 — WHERE THE `k` COMES FROM: CMP99b (3.15) and (3.19), printed p.393

`corpus/pages/CMP99b_p393.md` carries `verification_status: single-read`, so per the LAW-11
correction it is a lead and not citable ground truth on its own. **This lane therefore read the
two load-bearing displays directly off the render** `corpus/renders/CMP99b_p393-05.png`
(2406×3806, sha256 `bfab586ad2ebd8dea88c5aa93bdabe4622bacc3c28535603b5f6af17ec71383d`,
recomputed here and matching that page's frontmatter), at crops `y∈[380,900]` ×1.5,
`y∈[860,1120]` ×1.6 and `y∈[3040,3320]` ×1.6. VERBATIM, as read from the image:

> "We are interested in the linear operators `Q_j(U)`. They are compositions of `j` one-step
> averaging operators
>
>   `Q_j(U) = Q(Ū^{j-1})·⋯·Q(Ū)Q(U),`   (3.15)
>
> where `Q(V)` is given by the explicit formula (124) in [5]."

and the CLOSED FORM of that composition, same page:

> "`(Q'_j(U)λ)(y) = (Q'(Ū^{j-1})·⋯·Q'(Ū)Q'(U)λ)(y)`
>  `             = Σ_{x∈B^j(y)} L^{-jd} R(U(Γ^{(j)}_{y,x})) λ(x),   y ∈ T^{(j)}_{L^jη}.`   (3.19)"

with the one-step operator, in the same display and untagged:

> "`(Q'(V)λ)(y) = Σ_{x∈B(y)} L^{-d} R(V(Γ_{y,x})) λ(x),`"

and the tower the `k` indexes, same page (transcription; the tower structure is corroborated by
the `Ω_j`/`Λ_j` notation used throughout pp.394–430):

> "`Ω_0 ⊃ Ω_1 ⊃ ⋯ ⊃ Ω_k`, `Ω_j ⊂ T_η`, and we define
>  `Λ_j = Ω_j^{(j)}\Ω_{j+1}^{(j)}, j = 0,1,…,k, Ω_{k+1} = ∅`"
>
> "`⟨A, Q*aQ A⟩ = Σ_{j=0}^{k} a Σ_{b∈Λ_j} (L^jη)^{d-2}|(Q_j(U)A)(b)|².`   (3.16)"

**Two things follow, and they are what makes the family below a `ℕ`-family and not decoration.**

1. **`Q_j` is level-indexed and its closed form is a SINGLE block average at block side `L^j`,
   normalisation `L^{-jd}`, transport along `Γ^{(j)}_{y,x}`.** (3.19) says so as an equation; it is
   not an inference of ours. So a faithful level-`k` averaging operator on a lattice whose one-step
   block side is `ell` is a single block average at side `ell^k` — which is exactly
   `LineIntegralCovariant.lineCoarseRestrictCovLM U (ell ^ k)`, the tree's grade-2 covariant
   line-integral `Q` (CMP95 (1.18) / CMP98 (125)), evaluated at total block side `ell ^ k`.
2. **`k` is the TOP of a tower, not a free label.** `Ω_0 ⊃ ⋯ ⊃ Ω_k` and (3.16)'s `Σ_{j=0}^{k}`.
   At `j = 0` the block is a singleton and `L^{-0·d} = 1`: `Q_0` is the identity. §5 below proves
   the Lean family reproduces exactly that at `k = 0`.

### §1.3 — WHY THE MASS TERM `-a⟨B,B⟩` IS CORRECTLY ABSENT: CMP99b (3.128)/(3.129), p.421

`corpus/pages/CMP99b_p421.md`, `verification_status: adjudicated`, render
`corpus/renders/CMP99b_p421-33.png` sha256
`b7ae533e16f0a7dfe9c56a87cb9282b0128b97a5a825cecacb5fd770a5ece580` (recomputed here, matches the
frontmatter). Read directly off the image by this lane at crop `y∈[1780,2350]` ×1.5. VERBATIM:

> "Let us denote the operator defined by the problem (3.127), (3.110) by `H₁`, and by `G₁` the
> operator defined by the quadratic form
>
>   `⟨A, G₁⁻¹A⟩ = ⟨A, Δ_π A⟩ - 2⟨H C_π⁽²⁾(A), J⟩ + ‖RD*A‖² + a‖QA‖²`
>   `           = ⟨A - DG'RD*A, Δ(A - DG'RD*A)⟩`
>   `             - 2⟨H C⁽²⁾(A - DG'RD*A), J⟩`
>   `             + ‖RD*A‖² + a‖QA‖².`   (3.128)
>
> Then we have the formula
>
>   `H₁B = G₁Q*(QG₁Q*)⁻¹B.`   (3.129)"

The `+ a‖QA‖²` summand is unambiguous at that magnification.

**The cancellation, derived here rather than cited.** (3.129) is the statement that `H₁` is the
`G₁⁻¹`-minimiser over the fibre `{A : QA = B}`, so the Schur identity gives
`⟨B,(QG₁Q*)⁻¹B⟩ = min_{QA=B} ⟨A, G₁⁻¹A⟩`. On that fibre the last summand of (3.128) is the
CONSTANT `a‖B‖²`, hence

  `⟨B,(QG₁Q*)⁻¹B⟩ = min_{QA=B}[ ⟨A,Δ_πA⟩ - 2⟨HC_π⁽²⁾(A),J⟩ + ‖RD*A‖² ] + a⟨B,B⟩`,

and substituting into (3.156) the `a⟨B,B⟩` cancels EXACTLY:

  `⟨B,Δ_kB⟩ = min_{QA=B}[ ⟨A,Δ_πA⟩ - 2⟨HC_π⁽²⁾(A),J⟩ + ‖RD*A‖² ] - 2⟨H₁D̃⁽²⁾(B),J⟩`.

**`Δ_k` is a MINIMISED form, and it carries no mass.** This reproduces, from the pages, the
grade-2 verdict already recorded in this tree's `DeltaKSuTwoAssembly.lean` correction banner
(`compute/sol_deltak_readjudicate/SOL_VERDICT.md`); it is re-derived here because the identity of
the object built below depends on it.

### §1.4 — WHAT IS BUILT, AGAINST THAT

`deltaKTowerCLM ell k levels U` has quadratic form

  `⟨A, Δ̂_k A⟩ = min_{v ∈ V_k(U)} ‖D_U(A + v)‖²`,
  `V_k(U) = { A' : Q_{ell^k}(U)A' = 0 ∧ R^{cov}(U)(D_U^*A') = 0 }`

(the minimum is attained at the orthogonal-projection correction; `§3`'s
`inner_deltaKTowerCLM_eq` proves the form equals
`CovariantHjFaithful.deltaJQuadFormCovFaithful (ell^k) levels U`, which is exactly that Schur
complement, built on the FAITHFUL covariant `Q`). Term by term against §1.3's derived formula:

| source ingredient | here | disposition |
|---|---|---|
| `min_{QA=B}` at level `k` | `min over V_k(U)`, `Q_{ell^k}(U)` | PRESENT — this is the `k` axis, §1.2 |
| `-a⟨B,B⟩` | absent | **CORRECTLY absent** — §1.3 proves it cancels identically |
| `⟨A,Δ_πA⟩` | bare covariant curl `‖D_UA‖²` | SCOPE GAP: `Δ_π` is (3.120)'s gauge-projected `Δ = D*D+Δ'`; `compute/cstar_deltak_c_su2/DELTA_PI_ADJUDICATED.md` records that `Δ_π = D_U^*D_U` **on the slice `RD*A = 0`**, which is where the two agree |
| `+‖RD*A‖²` (a PENALTY, added) | the `levels` CONSTRAINT `R^{cov}(D_U^*A')=0` | SCOPE GAP: a penalty and a constraint are different objects; at `levels = oneLevelUniv` (§4) the constraint is EMPTY, so the minimisation runs over the whole fibre |
| `-2⟨HC_π⁽²⁾(A),J⟩`, `-2⟨H₁D̃⁽²⁾(B),J⟩` | absent | UNACCOUNTED; both vanish at `J = 0`, and the source defers `D̃⁽²⁾`'s own estimate (p.427) |
| carrier | fine bonds `BondFnL2 L`; source: unit-lattice `B` | the object here is the PULL-BACK `Q_k^*Δ_kQ_k` — see §6 |

### §1.5 — WHAT IS NOT ESTABLISHED HERE (no residual elected in place of an attempt)

**(R1) The composition law is used in the source's own CLOSED-FORM direction only, and the
`Γ^{(j)}` locator does not resolve.** (3.19) is an EQUATION: the `j`-fold composition equals the
single block average over `B^j(y)` with normalisation `L^{-jd}`. The family below is built on the
right-hand side. Three separate things were checked, and they land differently:

* **Block: EXACT.** `AdmissibleSubspace.blockOf y (ell^k)` is `B^k(y)` at side `ell^k`, under the
  divisibility guard (§7). `blockOf` SILENTLY TRUNCATES otherwise, which is why the guard is carried
  in every statement that needs it.
* **Normalisation: PROVED, not assumed.** `towerNorm_pow` (§3) compiles
  `1/(ell^k)^4 = (1/ell^4)^k`: the one-step bond factor `η^{d+1} = L^{-(d+1)}` composes
  multiplicatively across the tower to the `k`-step factor. Image-corroborated: published **CMP98
  (125)** reads `(Q₀A)_c = Σ_{x∈B(c₋)} L^{-(d+1)} (R_{0,c₋}A)([x,x'])`, which is exactly the tree's
  `lineCoarseRestrictCov` shape and normalisation, and CMP99b's own citation "formula (124) in [5]"
  matches published **CMP98 (124)**, `Q(V₀)A` — so the two papers' numbering DOES line up here.
* **Contour: UNRESOLVED, and the obstruction is at the SOURCE, not in this tree.** CMP99b p.393
  says, image-verified by this lane at crop `y∈[3260,3420]` ×1.7: *"The contours `Γ^{(j)}_{y,x}`,
  `x ∈ B^j(y)`, and the contour variables `U(Γ^{(j)}_{y,x})` were defined by (52), (53) in [5]."*
  Reference [5] is, per CMP99b's own bibliography, *"Averaging operations for lattice gauge
  theories," Harvard preprint HUTMP B147* — the paper published as CMP98. But published **CMP98's
  (52)/(53)** is the REGULARITY CONDITION `|U(∂p) − 1| < α₀η²` and an inequality about it (this
  tree's `k`-half work verbatim-matched exactly that), NOT a contour definition. So the stated
  locator for `Γ^{(j)}` does not land. What IS pinned is the **one-step** contour: published CMP98
  p.24, `corpus/pages/CMP98_p24.md`, `verification_status: adjudicated`, VERBATIM —
  `Γ_{y,x} = [y,(y₁,…,y_{d−1},x_d)] ∪ … ∪ [(y₁,x₂,…,x_d), x]` — the AXIAL-GAUGE STAIRCASE, which is
  the tree's transport convention. **Consequence, stated exactly: the identification of this file's
  `qTowerLM U ell k` with Bałaban's `Q_k(U)` is source-grounded on block, normalisation and (at
  `k ≤ 1`) contour; at `k ≥ 2` it additionally requires `Γ^{(k)}_{y,x}` to be the scale-`ell^k`
  staircase, and the source sentence that would settle that cites an equation pair which, in the
  published numbering, is a different object.** The `Γ^{(j)}` machine-draft reading of CMP98 p.26 is
  NOT citable (`layer: machine-draft`); adjudicating that page against its image is the next step
  and is a page-read, not a proof.

**Why the composition was not proved directly instead.** Attempted, and it is not typable in this
tree — a measured fact, not a difficulty. `Q(Ū^{k-1})⋯Q(U)` needs (i) a reindexing
`CoarseBond L ell → Bond (coarseExtent L ell)` for `SuTwo`-valued fields, which the tree has only
for ℝ-valued fields (`U1AnchorCoarse.lean`, the U(1) lane), and (ii) the BLOCKED configuration `Ū`,
i.e. CMP98 (43), an exact group-valued definition with NO Lean encoding anywhere in this tree
(established this same day on the `k`-half bar). Without `Ū` the second factor of (3.15) cannot be
written down. Separately, the inclusion `ker Q_{ell^j} ⊆ ker Q_{ell^k}` (`j ≤ k`), which would give
`Δ̂_j ≠ Δ̂_k` for `1 ≤ j < k` by the §6a argument, was attempted and is NOT available for the same
reason: the tree's transport anchors every staircase at the block corner, so the level-`k` staircase
from `c₋` to `x` is not the concatenation of the level-`j` staircases through the intermediate
corner except up to the holonomy of the enclosed loops — i.e. it is exactly the `Γ^{(j)}` question
again. §6a therefore separates level `0` from EVERY level `k`, which needs no inclusion, and does
not claim `Δ̂_j ≠ Δ̂_k` for `1 ≤ j < k`.

**(R1b) `lineCoarseRestrictCov` is CMP98 (125), the LEADING TERM of (124), not (124) itself.**
Read off the machine draft of CMP98 p.36 (a LEAD, not citable): (124) has five summands and the
paper says *"The first term on the right-hand side above is the main term in this linear form …
The remaining terms are small"*; (125) names that first term `Q₀`. So the `Q` this file's tower is
built from drops four correction terms of the source's `Q(V₀)`. This is INHERITED from
`LineIntegralCovariant.lean`, not introduced here, and it is recorded because the tower multiplies
whatever error `Q` carries across `k` levels.

**(R2) `J = 0`.** The two source-term summands are absent, as tabulated. No bound on them exists
in this tree and the source defers one of them.

**(R3) `C` (3.157) is not applied here.** This file builds `Δ_k`, not `C*Δ_kC`. `C`'s own defect
(`FullReparamC.fullC` carries a FREE `Dinv` where the source's `C` is DETERMINED by `(QB)(c)=0`)
is recorded in `PinnedOperatorFaithfulness.lean` §1.2 and is untouched here.

**(R4) No regularity restriction on `U`, and no coercivity is claimed.** This file builds an
operator and proves it is `k`-dependent, self-adjoint and positive semidefinite. It proves NO lower
bound. In particular §6 proves the family ANNIHILATES `V_k(U)`, so it is **not** coercive on the
whole space — as it must not be, since (3.156)'s form is considered on p.428's subspace and not on
everything.

**(R5) The tower height on a fixed torus is FINITE** (§7, `tower_height_lt`): `ell^k ∣ L μ + 1`
forces `k < L μ + 1`. p.428 demands `γ₀` uniform in `k`; on a fixed periodic extent only finitely
many levels are block-compatible at all. Stated as a theorem rather than a caveat because it is the
exact shape of the `k`-uniformity limit of this carrier.

## §2 — CONTROLS THIS FILE SHIPS (each is a compiled theorem, not a claim)

* `deltaKTowerCLM_zero_ne_one` — **must-fire on the `k` axis**: the family genuinely moves with `k`
  at an explicit background. The trap it avoids is `CoercUMainRegular.regularDelta`, which discards
  `k` definitionally.
* `deltaKTowerCLM_ell_one` — **the degeneracy, found against this file's own statement**: at
  `ell = 1` the tower COLLAPSES, `Δ̂_k = D_U^*D_U` for every `k`. So `2 ≤ ell` is NECESSARY for the
  `k` axis to carry anything; `ell` is a parameter whose chooser can empty the statement, and this
  says exactly where.
* `tower_zero_survives_towerWitness` — **must-not-fire / S82 garbage substitution** for the
  annihilation theorem: at the SAME background and the SAME field, one level down (`k = 0`, where
  the field is NOT in `V_0`), the operator does NOT annihilate. The annihilation is therefore not
  algebraically forced.
* `deltaKTowerCLM_one_ne_zero_witnessL` — **global non-vacuity at level `k ≥ 1`**: the family is
  not the zero operator there. Added after this lane's nested validator observed that the level-0
  control alone does not exclude that reading.
* `deltaKTowerCLM_coarse_factors` — the family's value depends only on `Q_{ell^k}(U)A`, the property
  `PinnedOperatorFaithfulness.pin_form_does_not_coarse_factor` proves the pinned operator LACKS.
* `deltaKTowerCLM_le_dstarD` — the whole tower is dominated by level `0` in the form order.
  **LABELLED FORCED (S82).** Its proof is the generic Hilbert-space Pythagorean identity and uses no
  property of the covariant curl or of su(2); it would hold with any operator in the `(1-P)∘S` slot.
  It is stated because it is the analytic shape a coercivity argument must work against, and it is
  NOT evidence that the object is faithful. This label was added after this lane's nested validator
  classified it.
* `deltaKTowerCLM_one_ne_deltaKCLMNormalized` — the family is a DIFFERENT operator from the tree's
  pinned (3.10) `Δ`, proved at an explicit gauge-regular background, not argued term-by-term.
* `deltaKTowerCLM_zero` — and yet at `k = 0` it is EXACTLY `D_U^*D_U`, so the two objects are
  related by a proved identity and not merely distinct.
-/

namespace AdalyFormal.Balaban.DeltaKSuTwoCarrier

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlCovariantLM)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf)
open AdalyFormal.Balaban.CovariantHj (covPlaqInner dstarDQuadForm)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2 plaqFnEquiv plaqFnEquiv_symm_apply
  siteFnEquiv inner_plaqFnL2_eq_covPlaqInner RcovLM RcovFun gradCovariantAdjointLM
  deltaKernelImageCov deltaKernelImageCovH kernelSubspaceCov coarseRestrictSiteCovariant
  oneLevelUniv RcovLM_oneLevelUniv_eq_zero)
open AdalyFormal.Balaban.CovariantHjFaithful (curlImageCovHFaithful curlImageCovFaithful
  curlImageCovProjFaithful curlImageCovProjFaithful_fixes
  gaugeConstraintSubspaceCovFaithful mem_gaugeConstraintSubspaceCovFaithful
  curl_mem_curlImageCovFaithful_of_mem
  deltaJQuadFormCovFaithful hjExtensionCovFaithful
  curlCov_hjExtensionCovFaithful hjCorrectionTargetCovFaithful
  curlImageCovHFaithful_ell1_eq_bot deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM)
open AdalyFormal.Balaban.BondSU2Space (bondFnL2Equiv)
open AdalyFormal.Balaban.CStarDeltaKCOperator (dstarDCLM inner_dstarDCLM_eq_dstarDQuadForm
  dstarDLM inner_dstarDLM_symm witField curl_fullC_witField_ne_zero plaqToLp_eq_zero_iff)
open AdalyFormal.Balaban.FullReparamC (fullC fullC_mem_ker dinvC dinvC_hinv)
open AdalyFormal.Balaban.KernelSubspace (Level)
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SchurNonzero (singleBondA0 deltaJQuadFormCovFaithful_pos_witnessEll)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5 witL5_four_le witL5_two_dvd)
open AdalyFormal.Balaban.RegularUDomainWitnessGeneralU (genWitness genWitness_ne_zero
  genWitness_axial genWitness_mem_kerQ tinyU deltaJ_coercive_at_genWitness_tinyU)
open AdalyFormal.Balaban.CoercivityRegular (VReg toLp_mem_VReg mem_admKerBare
  deltaKCLMNormalized_coercive_on_VReg curvedRegularU curvedRegularU_gaugeRegular)
open AdalyFormal.Balaban.LemmaAssemblyNormalized (normGamma normGamma_pos)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized deltaPrimeCLMNormalized)

variable {L : PeriodicLatticeExtent}

/-! ## §3 — THE `ℕ`-INDEXED FAMILY

`Q_k(U) := lineCoarseRestrictCovLM U (ell ^ k)` is (3.19)'s closed form at total block side
`ell ^ k` (§1.2, §1.5 R1). The level-`k` constraint subspace is
`gaugeConstraintSubspaceCovFaithful (ell ^ k) levels U`; nothing new is minted for it (LAW-19). -/

/-- **The `k`-step averaging operator**, (3.19)'s closed form at total block side `ell ^ k`. A named
alias, so the source pin travels with the object and consumers cannot lose the level index. -/
noncomputable def qTowerLM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell k : ℕ) : (Bond L → SuTwo) →ₗ[ℝ] (CoarseBond L (ell ^ k) → SuTwo) :=
  lineCoarseRestrictCovLM U (ell ^ k)

theorem qTowerLM_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell k : ℕ) (A : Bond L → SuTwo) :
    qTowerLM U ell k A = lineCoarseRestrictCovLM U (ell ^ k) A := rfl

/-- **The one-step bond normalisations COMPOSE to the `k`-step one.** `lineCoarseRestrictCov`
carries `η^{d+1} = 1/ell⁴` (`d = 3`, CMP95 (1.18) / CMP98 (125)); at total block side `ell ^ k` that
is `1/(ell^k)^4`, and this is exactly the `k`-fold product of the one-step factor. This is the half
of (3.19)'s composition law that IS provable here (§1.5 R1); it fixes the normalisation axis of the
tower, leaving the contour `Γ^{(j)}` as the sole remaining ingredient. -/
theorem towerNorm_pow (ell k : ℕ) :
    (1 : ℝ) / ((ell : ℝ) ^ k) ^ 4 = ((1 : ℝ) / (ell : ℝ) ^ 4) ^ k := by
  rw [div_pow, one_pow, ← pow_mul, ← pow_mul, Nat.mul_comm k 4]

#print axioms qTowerLM
#print axioms qTowerLM_apply
#print axioms towerNorm_pow

/-- **The covariant curl `D_U`, as a `ContinuousLinearMap` between the two `L²` carriers.**
`LinearMap.toContinuousLinearMap` on the finite-dimensional carrier; no new curl is defined
(LAW-19 — `CovariantOperators.curlCovariantLM` is reused verbatim). -/
noncomputable def curlCLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →L[ℝ] PlaqFnL2 L :=
  LinearMap.toContinuousLinearMap
    ((plaqFnEquiv L).symm.toLinearMap ∘ₗ (curlCovariantLM U) ∘ₗ (bondFnL2Equiv L).toLinearMap)

theorem curlCLM_toLp (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    curlCLM U (WithLp.toLp 2 A) = WithLp.toLp 2 (curlCovariantLM U A) := rfl

/-- **`(1 - P_{W_m}) ∘ D_U`**, `W_m = D_U(V_m(U))`: the residual curl after the level-`m`
minimisation. Its squared norm IS the Schur complement (§3's form theorem). -/
noncomputable def schurCLM (m : ℕ) (levels : List (Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    BondFnL2 L →L[ℝ] PlaqFnL2 L :=
  (ContinuousLinearMap.id ℝ (PlaqFnL2 L) - (curlImageCovHFaithful m levels U).starProjection)
    ∘L curlCLM U

/-- **THE FAMILY.** `Δ̂_k := T_k^* T_k` at level `k` of the `ell`-tower — a `ℕ`-indexed family of
`ContinuousLinearMap`s on `BondFnL2 L`, at a concrete `PeriodicLinkConfiguration (SU(2)) L`. -/
noncomputable def deltaKTowerCLM (ell k : ℕ) (levels : List (Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  ContinuousLinearMap.adjoint (schurCLM (ell ^ k) levels U) ∘L schurCLM (ell ^ k) levels U

theorem schurCLM_toLp (m : ℕ) (levels : List (Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (A : Bond L → SuTwo) :
    schurCLM m levels U (WithLp.toLp 2 A)
      = WithLp.toLp 2 (hjCorrectionTargetCovFaithful m levels U A) := by
  show ((ContinuousLinearMap.id ℝ (PlaqFnL2 L)
      - (curlImageCovHFaithful m levels U).starProjection)
        (curlCLM U (WithLp.toLp 2 A)) : PlaqFnL2 L) = _
  rw [curlCLM_toLp]
  show (WithLp.toLp 2 (curlCovariantLM U A) : PlaqFnL2 L)
      - (curlImageCovHFaithful m levels U).starProjection (WithLp.toLp 2 (curlCovariantLM U A)) = _
  unfold hjCorrectionTargetCovFaithful curlImageCovProjFaithful
  rw [plaqFnEquiv_symm_apply]
  rfl

/-- **THE FAITHFULNESS PIN.** The family's quadratic form IS the FAITHFUL covariant Schur complement
at block side `ell ^ k` — `CovariantHjFaithful.deltaJQuadFormCovFaithful`, which is built on the
grade-2 covariant line-integral `Q` and NOT on the convicted single-bond restriction. Without this
theorem the operator would be an unrelated object with a suggestive name. It also PROMOTES that
form, which existed only as an `ℝ`-valued function, to a genuine operator. -/
theorem inner_deltaKTowerCLM_eq (ell k : ℕ) (levels : List (Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (A : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
        (deltaKTowerCLM ell k levels U (WithLp.toLp 2 A)) : ℝ)
      = deltaJQuadFormCovFaithful (ell ^ k) levels U A := by
  show (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
    (ContinuousLinearMap.adjoint (schurCLM (ell ^ k) levels U)
      (schurCLM (ell ^ k) levels U (WithLp.toLp 2 A))) : ℝ) = _
  rw [ContinuousLinearMap.adjoint_inner_right, schurCLM_toLp, inner_plaqFnL2_eq_covPlaqInner]
  unfold deltaJQuadFormCovFaithful
  rw [curlCov_hjExtensionCovFaithful]

theorem deltaKTowerCLM_symm (ell k : ℕ) (levels : List (Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (x y : BondFnL2 L) :
    (inner ℝ (deltaKTowerCLM ell k levels U x) y : ℝ)
      = inner ℝ x (deltaKTowerCLM ell k levels U y) := by
  show (inner ℝ (ContinuousLinearMap.adjoint (schurCLM (ell ^ k) levels U)
      (schurCLM (ell ^ k) levels U x)) y : ℝ) = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  show (inner ℝ (schurCLM (ell ^ k) levels U x) (schurCLM (ell ^ k) levels U y) : ℝ)
    = inner ℝ x (ContinuousLinearMap.adjoint (schurCLM (ell ^ k) levels U)
        (schurCLM (ell ^ k) levels U y))
  rw [ContinuousLinearMap.adjoint_inner_right]

theorem deltaKTowerCLM_psd (ell k : ℕ) (levels : List (Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (x : BondFnL2 L) :
    (0 : ℝ) ≤ inner ℝ x (deltaKTowerCLM ell k levels U x) := by
  show (0 : ℝ) ≤ inner ℝ x (ContinuousLinearMap.adjoint (schurCLM (ell ^ k) levels U)
      (schurCLM (ell ^ k) levels U x))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact real_inner_self_nonneg

#print axioms curlCLM
#print axioms curlCLM_toLp
#print axioms schurCLM
#print axioms deltaKTowerCLM
#print axioms schurCLM_toLp
#print axioms inner_deltaKTowerCLM_eq
#print axioms deltaKTowerCLM_symm
#print axioms deltaKTowerCLM_psd

/-! ## §4 — THE `levels` LIST AT WHICH THE GAUGE CLAUSE IS EMPTY — **ALREADY IN THE TREE**

This lane first built `[(1, Finset.univ)]` and its three supporting lemmas from scratch, then found
them already present: `CovariantHjMinimizer.oneLevelUniv`, with
`kernelSubspaceCov_oneLevelUniv_eq_bot`, `deltaKernelImageCovH_oneLevelUniv_eq_bot` and
`RcovLM_oneLevelUniv_eq_zero`. The duplicate was DELETED and the tree's object is used below
(LAW-19 — reuse, do not rebuild). Recorded rather than quietly dropped, because a rebuilt detector
is a defect class this campaign has hit seven times.

At `levels = oneLevelUniv L` the gauge clause is identically satisfied, so `V_k(U)` is exactly
`ker Q_{ell^k}(U)`. That is also the honest reading of §1.4's scope row: with the clause empty, the
minimisation runs over the WHOLE level-`k` fibre, where the source instead ADDS a penalty
`‖RD*A‖²`.
-/

/-! ## §5 — LEVEL `0`: the family reduces EXACTLY to `D_U^*D_U`

(3.15) at `j = 0` is the empty composition and (3.19)'s block `B^0(y)` is a singleton with
normalisation `L^0 = 1`: `Q_0` is the identity. The Lean family reproduces exactly that. -/

/-- Symmetric operators with equal quadratic forms are equal (real polarisation). Stated generally
because two operators built by different routes have to be COMPARED, and equality of forms is all
that the Schur construction hands over. -/
theorem eq_of_symm_of_quadForm_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S T : H →L[ℝ] H)
    (hS : ∀ x y : H, (inner ℝ (S x) y : ℝ) = inner ℝ x (S y))
    (hT : ∀ x y : H, (inner ℝ (T x) y : ℝ) = inner ℝ x (T y))
    (hq : ∀ x : H, (inner ℝ x (S x) : ℝ) = inner ℝ x (T x)) : S = T := by
  have hD : ∀ x y : H, (inner ℝ x ((S - T) y) : ℝ) = 0 := by
    have hDsymm : ∀ x y : H, (inner ℝ ((S - T) x) y : ℝ) = inner ℝ x ((S - T) y) := by
      intro x y
      show (inner ℝ (S x - T x) y : ℝ) = inner ℝ x (S y - T y)
      rw [inner_sub_left, inner_sub_right, hS, hT]
    have hDq : ∀ x : H, (inner ℝ x ((S - T) x) : ℝ) = 0 := by
      intro x
      show (inner ℝ x (S x - T x) : ℝ) = 0
      rw [inner_sub_right, hq, sub_self]
    intro x y
    have h1 := hDq (x + y)
    have hx := hDq x
    have hy := hDq y
    have hexp : (inner ℝ (x + y) ((S - T) (x + y)) : ℝ)
        = inner ℝ x ((S - T) x) + inner ℝ x ((S - T) y)
          + inner ℝ y ((S - T) x) + inner ℝ y ((S - T) y) := by
      rw [map_add, inner_add_left, inner_add_right, inner_add_right]
      ring
    have hcross : (inner ℝ y ((S - T) x) : ℝ) = inner ℝ x ((S - T) y) := by
      rw [← hDsymm, real_inner_comm]
    rw [hexp, hx, hy, hcross] at h1
    linarith
  ext y
  have := hD ((S - T) y) y
  have hz : ((S - T) y : H) = 0 := by
    have h2 : (inner ℝ ((S - T) y) ((S - T) y) : ℝ) = 0 := by
      rw [← real_inner_comm] at this ⊢
      exact this
    exact inner_self_eq_zero.mp h2
  have : (S y - T y : H) = 0 := hz
  have := sub_eq_zero.mp this
  exact congrArg id this

theorem dstarDCLM_symm (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x y : BondFnL2 L) :
    (inner ℝ (dstarDCLM U x) y : ℝ) = inner ℝ x (dstarDCLM U y) :=
  inner_dstarDLM_symm U x y

/-- **LEVEL `0` IS `D_U^*D_U`, EXACTLY, AS OPERATORS** — for every `ell`, every `levels`, every `U`.
This is (3.15)/(3.19) at `j = 0` reproduced in Lean, and it is the bridge to the tree's pinned
(3.10) object: `dstarDCLM` is the `D*D` summand of
`DeltaPrimeOperator.deltaKCLMNormalized = dstarDCLM + deltaPrimeCLMNormalized`. -/
theorem deltaKTowerCLM_zero (ell : ℕ) (levels : List (Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    deltaKTowerCLM ell 0 levels U = dstarDCLM U := by
  refine eq_of_symm_of_quadForm_eq _ _ (deltaKTowerCLM_symm ell 0 levels U)
    (dstarDCLM_symm U) ?_
  intro x
  have hx : (WithLp.toLp 2 (WithLp.ofLp x) : BondFnL2 L) = x := rfl
  rw [← hx, inner_deltaKTowerCLM_eq, inner_dstarDCLM_eq_dstarDQuadForm]
  show deltaJQuadFormCovFaithful (ell ^ 0) levels U (WithLp.ofLp x) = _
  rw [pow_zero]
  exact deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm levels U (WithLp.ofLp x)

/-- **THE EXACT RELATION TO THE PINNED (3.10) OPERATOR, ANSWERED AS AN IDENTITY.** `Δ̂_0` does NOT
equal `deltaKCLMNormalized`; it equals its `D*D` summand, and the difference is EXACTLY the `Δ′`
half of (3.10). So the two objects are separated by a named, compiled quantity, not by prose. -/
theorem deltaKCLMNormalized_sub_tower_zero (ell : ℕ) (levels : List (Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    deltaKCLMNormalized U - deltaKTowerCLM ell 0 levels U = deltaPrimeCLMNormalized U := by
  rw [deltaKTowerCLM_zero]
  show dstarDCLM U + deltaPrimeCLMNormalized U - dstarDCLM U = _
  abel

/-- **THE DEGENERACY, PROVED AGAINST THIS FILE'S OWN OBJECT.** At `ell = 1` the tower COLLAPSES:
`Δ̂_k = D_U^*D_U` for EVERY `k`. `ell` is a parameter whose chooser can empty the `k` axis, and this
is exactly where. Consequence for any consumer: `2 ≤ ell` is NECESSARY, not conservative. -/
theorem deltaKTowerCLM_ell_one (k : ℕ) (levels : List (Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    deltaKTowerCLM 1 k levels U = dstarDCLM U := by
  show ContinuousLinearMap.adjoint (schurCLM ((1 : ℕ) ^ k) levels U)
      ∘L schurCLM ((1 : ℕ) ^ k) levels U = _
  rw [one_pow]
  exact deltaKTowerCLM_zero 1 levels U

#print axioms eq_of_symm_of_quadForm_eq
#print axioms dstarDCLM_symm
#print axioms deltaKTowerCLM_zero
#print axioms deltaKCLMNormalized_sub_tower_zero
#print axioms deltaKTowerCLM_ell_one

/-! ## §6 — THE FAMILY ANNIHILATES ITS OWN LEVEL-`k` SUBSPACE, AND IS GENUINELY `k`-DEPENDENT

`PinnedOperatorFaithfulness.lean` §7 proves the pinned (3.10) operator's form is NOT the pull-back
of any coarse operator: it is bounded strictly below on `VReg U ⊆ ker Q`. Any (3.156)-shaped object
must have the OPPOSITE property, since (3.156)'s `Δ_k` is a form in the coarse variable `B = QA`
and is blind to `ker Q`. The family here has it BY CONSTRUCTION, and the theorem says so. -/

/-- **THE ANNIHILATION** — `Δ̂_k` kills `V_k(U)`, i.e. its form factors through `Q_{ell^k}(U)`. -/
theorem deltaKTowerCLM_apply_eq_zero_of_mem (ell k : ℕ) (levels : List (Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {A : Bond L → SuTwo}
    (hA : A ∈ gaugeConstraintSubspaceCovFaithful (ell ^ k) levels U) :
    deltaKTowerCLM ell k levels U (WithLp.toLp 2 A) = 0 := by
  have hT : schurCLM (ell ^ k) levels U (WithLp.toLp 2 A) = 0 := by
    rw [schurCLM_toLp]
    have hz : hjCorrectionTargetCovFaithful (ell ^ k) levels U A = 0 := by
      unfold hjCorrectionTargetCovFaithful
      rw [curlImageCovProjFaithful_fixes _ _ _ (curl_mem_curlImageCovFaithful_of_mem hA), sub_self]
    rw [hz]
    simp
  show ContinuousLinearMap.adjoint (schurCLM (ell ^ k) levels U)
      (schurCLM (ell ^ k) levels U (WithLp.toLp 2 A)) = 0
  rw [hT, map_zero]

/-! ### §6a — the level-`k` witness, at EVERY `k`, EVERY `ell ≥ 2`, EVERY `U`

The `k`-dependence must not rest on a single hand-built pair of levels. `FullReparamC.fullC` and
`CStarDeltaKCOperator.witField` supply a witness at ARBITRARY block side, and both facts needed —
that it is in `ker Q` and that its covariant curl is nonzero — are already in the tree at general
`ell` (LAW-19; `curl_fullC_witField_ne_zero` needs only `2 ≤ ell` and the divisibility guard, with
NO condition on `U` and no `4 ≤ L μ`). -/

/-- **The level-`k` witness**: the `(3.157)`-style reparametrisation at total block side `ell ^ k`,
applied to the single-bond spike at the origin plaquette. -/
noncomputable def towerWitness (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell k : ℕ) : Bond L → SuTwo :=
  fullC U (ell ^ k) (dinvC U (ell ^ k)) (witField (L := L))

theorem towerWitness_mem_ker (ell k : ℕ) (hpos : 0 < ell ^ k)
    (hdvd : ∀ μ : Fin 3, ell ^ k ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    lineCoarseRestrictCovLM U (ell ^ k) (towerWitness U ell k) = 0 :=
  fullC_mem_ker hpos hdvd U (dinvC U (ell ^ k)) (dinvC_hinv hpos hdvd U) (witField (L := L))

theorem towerWitness_curl_ne_zero (ell k : ℕ) (hell2 : 2 ≤ ell ^ k)
    (hdvd : ∀ μ : Fin 3, ell ^ k ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    curlCovariantLM U (towerWitness U ell k) ≠ 0 :=
  curl_fullC_witField_ne_zero U hell2 hdvd (dinvC U (ell ^ k))

theorem towerWitness_mem_towerConstraint (ell k : ℕ) (hpos : 0 < ell ^ k)
    (hdvd : ∀ μ : Fin 3, ell ^ k ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection] :
    towerWitness U ell k ∈ gaugeConstraintSubspaceCovFaithful (ell ^ k) (oneLevelUniv L) U :=
  mem_gaugeConstraintSubspaceCovFaithful.mpr
    ⟨towerWitness_mem_ker ell k hpos hdvd U, RcovLM_oneLevelUniv_eq_zero U _⟩

/-- Level `k` KILLS the level-`k` witness. -/
theorem tower_kills_towerWitness (ell k : ℕ) (hpos : 0 < ell ^ k)
    (hdvd : ∀ μ : Fin 3, ell ^ k ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection] :
    deltaKTowerCLM ell k (oneLevelUniv L) U (WithLp.toLp 2 (towerWitness U ell k)) = 0 :=
  deltaKTowerCLM_apply_eq_zero_of_mem ell k (oneLevelUniv L) U
    (towerWitness_mem_towerConstraint ell k hpos hdvd U)

/-- **MUST-NOT-FIRE / S82 GARBAGE-SUBSTITUTION CONTROL for `..._apply_eq_zero_of_mem`.** Level `0`
does NOT kill the same field, at the same background. So the annihilation is a fact about `V_k` and
not an algebraic identity that would hold on any input. -/
theorem tower_zero_survives_towerWitness (ell k : ℕ) (hell2 : 2 ≤ ell ^ k)
    (hdvd : ∀ μ : Fin 3, ell ^ k ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection] :
    deltaKTowerCLM ell 0 (oneLevelUniv L) U (WithLp.toLp 2 (towerWitness U ell k)) ≠ 0 := by
  intro hzero
  have h0 : (inner ℝ (WithLp.toLp 2 (towerWitness U ell k) : BondFnL2 L)
      (deltaKTowerCLM ell 0 (oneLevelUniv L) U
        (WithLp.toLp 2 (towerWitness U ell k))) : ℝ) = 0 := by
    rw [hzero, inner_zero_right]
  rw [inner_deltaKTowerCLM_eq] at h0
  have hq : deltaJQuadFormCovFaithful (ell ^ 0) (oneLevelUniv L) U (towerWitness U ell k)
      = dstarDQuadForm U (towerWitness U ell k) := by
    rw [pow_zero]
    exact deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm _ _ _
  rw [hq] at h0
  -- `dstarDQuadForm = ‖curl‖²` in `PlaqFnL2`, and the curl is nonzero
  have hcurl : (WithLp.toLp 2 (curlCovariantLM U (towerWitness U ell k)) : PlaqFnL2 L) ≠ 0 := by
    rw [Ne, plaqToLp_eq_zero_iff]
    exact towerWitness_curl_ne_zero ell k hell2 hdvd U
  have hpos : (0 : ℝ) < inner ℝ
      (WithLp.toLp 2 (curlCovariantLM U (towerWitness U ell k)) : PlaqFnL2 L)
      (WithLp.toLp 2 (curlCovariantLM U (towerWitness U ell k))) := real_inner_self_pos.2 hcurl
  rw [inner_plaqFnL2_eq_covPlaqInner] at hpos
  exact absurd h0 (ne_of_gt hpos)

/-- **THE `k`-DEPENDENCE, AT EVERY LEVEL — the axis `CoercUMainRegular.regularDelta` forfeits.**
For EVERY `ell`, EVERY `k` with `2 ≤ ell ^ k`, EVERY background `U`, on any torus whose extent the
level-`k` block divides: level `0` and level `k` are DIFFERENT operators. Not a `k`-decorated
constant; the two levels disagree on a named, explicit field. -/
theorem deltaKTowerCLM_zero_ne_level (ell k : ℕ) (hell2 : 2 ≤ ell ^ k)
    (hdvd : ∀ μ : Fin 3, ell ^ k ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection] :
    deltaKTowerCLM ell 0 (oneLevelUniv L) U ≠ deltaKTowerCLM ell k (oneLevelUniv L) U := by
  intro hEq
  apply tower_zero_survives_towerWitness ell k hell2 hdvd U
  rw [hEq]
  exact tower_kills_towerWitness ell k (by omega) hdvd U

/-- The `ell = 2, k = 1` instance, stated separately because it is the pair the campaign's
`coerc_u_main` conjunct actually asks about. -/
theorem deltaKTowerCLM_zero_ne_one (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection] :
    deltaKTowerCLM 2 0 (oneLevelUniv L) U ≠ deltaKTowerCLM 2 1 (oneLevelUniv L) U :=
  deltaKTowerCLM_zero_ne_level 2 1 (by norm_num) (by simpa using hdvd) U

/-- **GLOBAL NON-VACUITY AT LEVEL `k ≥ 1`, the gap this lane's nested validator found.** The
must-not-fire control above separates level `0` from level `k`; on its own it does NOT exclude the
reading in which `Δ̂_k` is the ZERO operator for every `k ≥ 1`, which would make the annihilation
theorem say nothing. It is not zero: at `L = witnessL` (`4³`, so `2 ∣ L μ + 1 = 4`), at the trivial
background, level `1` of the `2`-tower has a STRICTLY POSITIVE form at
`SchurNonzero.singleBondA0`. Reused, not rebuilt (LAW-19): `SchurNonzero`'s own theorem holds for
EVERY `levels`, so it applies at `oneLevelUniv` with nothing added. -/
theorem deltaKTowerCLM_one_ne_zero_witnessL
    [(deltaKernelImageCovH (trivialU witnessL) (oneLevelUniv witnessL)).HasOrthogonalProjection] :
    deltaKTowerCLM 2 1 (oneLevelUniv witnessL) (trivialU witnessL) ≠ 0 := by
  intro h
  have h0 : (inner ℝ (WithLp.toLp 2 singleBondA0 : BondFnL2 witnessL)
      (deltaKTowerCLM 2 1 (oneLevelUniv witnessL) (trivialU witnessL)
        (WithLp.toLp 2 singleBondA0)) : ℝ)
      = deltaJQuadFormCovFaithful ((2 : ℕ) ^ 1) (oneLevelUniv witnessL) (trivialU witnessL)
          singleBondA0 :=
    inner_deltaKTowerCLM_eq 2 1 (oneLevelUniv witnessL) (trivialU witnessL) singleBondA0
  rw [h] at h0
  rw [ContinuousLinearMap.zero_apply, inner_zero_right] at h0
  have hpow : ((2 : ℕ) ^ 1) = 2 := pow_one 2
  rw [hpow] at h0
  exact absurd h0.symm (ne_of_gt (deltaJQuadFormCovFaithful_pos_witnessEll (oneLevelUniv witnessL)))

#print axioms deltaKTowerCLM_one_ne_zero_witnessL

/-! ### §6b — THE COARSE-FACTORING PROPERTY, WHICH THE PINNED OPERATOR PROVABLY LACKS

`PinnedOperatorFaithfulness.pin_form_does_not_coarse_factor` proves that the pinned (3.10) operator
is NOT a function of the block average — it is bounded strictly below on `ker Q`. Any object
standing for (3.156)'s `Δ_k`, a form in the coarse variable `B = QA`, must be the opposite. Here it
is, as an equation. -/

/-- **`Δ̂_k` DEPENDS ONLY ON `Q_{ell^k}(U)A`.** -/
theorem deltaKTowerCLM_coarse_factors (ell k : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection]
    (A A' : Bond L → SuTwo)
    (h : lineCoarseRestrictCovLM U (ell ^ k) A = lineCoarseRestrictCovLM U (ell ^ k) A') :
    deltaKTowerCLM ell k (oneLevelUniv L) U (WithLp.toLp 2 A)
      = deltaKTowerCLM ell k (oneLevelUniv L) U (WithLp.toLp 2 A') := by
  have hmem : (A - A') ∈ gaugeConstraintSubspaceCovFaithful (ell ^ k) (oneLevelUniv L) U := by
    refine mem_gaugeConstraintSubspaceCovFaithful.mpr ⟨?_, RcovLM_oneLevelUniv_eq_zero U _⟩
    rw [map_sub, h, sub_self]
  have hT : schurCLM (ell ^ k) (oneLevelUniv L) U (WithLp.toLp 2 (A - A')) = 0 := by
    rw [schurCLM_toLp]
    have hz : hjCorrectionTargetCovFaithful (ell ^ k) (oneLevelUniv L) U (A - A') = 0 := by
      unfold hjCorrectionTargetCovFaithful
      rw [curlImageCovProjFaithful_fixes _ _ _ (curl_mem_curlImageCovFaithful_of_mem hmem),
        sub_self]
    rw [hz]
    simp
  have hsub : (WithLp.toLp 2 (A - A') : BondFnL2 L)
      = WithLp.toLp 2 A - WithLp.toLp 2 A' := rfl
  rw [hsub, map_sub, sub_eq_zero] at hT
  show ContinuousLinearMap.adjoint (schurCLM (ell ^ k) (oneLevelUniv L) U)
      (schurCLM (ell ^ k) (oneLevelUniv L) U (WithLp.toLp 2 A)) = _
  rw [hT]
  rfl

/-! ### §6c — THE TOWER IS DOMINATED BY LEVEL `0`

`Δ̂_k ≤ Δ̂_0 = D_U^*D_U` in the form order, at every level. This is the analytic shape any coercivity
argument on the tower has to work against: the tower can only LOSE energy as `k` grows, and §6a says
it genuinely does. -/

/-- **S82: ALGEBRAICALLY FORCED — not verification.** Generic Pythagoras; no covariant-curl or
su(2) content. See §2. -/
theorem deltaKTowerCLM_le_dstarD (ell k : ℕ) (levels : List (Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (x : BondFnL2 L) :
    (inner ℝ x (deltaKTowerCLM ell k levels U x) : ℝ) ≤ inner ℝ x (dstarDCLM U x) := by
  set K := curlImageCovHFaithful (ell ^ k) levels U with hK
  set y := curlCLM U x with hy
  have hres : schurCLM (ell ^ k) levels U x = y - K.starProjection y := rfl
  have hL2 : (inner ℝ x (deltaKTowerCLM ell k levels U x) : ℝ)
      = inner ℝ (y - K.starProjection y) (y - K.starProjection y) := by
    show (inner ℝ x (ContinuousLinearMap.adjoint (schurCLM (ell ^ k) levels U)
      (schurCLM (ell ^ k) levels U x)) : ℝ) = _
    rw [ContinuousLinearMap.adjoint_inner_right, hres]
  have hR2 : (inner ℝ x (dstarDCLM U x) : ℝ) = inner ℝ y y := by
    rw [← deltaKTowerCLM_zero ell levels U]
    show (inner ℝ x (ContinuousLinearMap.adjoint (schurCLM (ell ^ 0) levels U)
      (schurCLM (ell ^ 0) levels U x)) : ℝ) = _
    rw [ContinuousLinearMap.adjoint_inner_right]
    have hbot : curlImageCovHFaithful (ell ^ 0) levels U = ⊥ := by
      rw [pow_zero]
      exact curlImageCovHFaithful_ell1_eq_bot levels U
    have hz : schurCLM (ell ^ 0) levels U x = y := by
      show (y - (curlImageCovHFaithful (ell ^ 0) levels U).starProjection y : PlaqFnL2 L) = y
      have := (Submodule.eq_bot_iff _).mp hbot _
        (Submodule.starProjection_apply_mem (curlImageCovHFaithful (ell ^ 0) levels U) y)
      rw [this, sub_zero]
    rw [hz]
  -- Pythagoras: ‖y‖² = ‖Py‖² + ‖y - Py‖²
  have horth : (inner ℝ (K.starProjection y) (y - K.starProjection y) : ℝ) = 0 :=
    (Submodule.mem_orthogonal _ _).mp (K.sub_starProjection_mem_orthogonal y) _
      (Submodule.starProjection_apply_mem K y)
  have hsplit : (inner ℝ y y : ℝ)
      = inner ℝ (K.starProjection y) (K.starProjection y)
        + inner ℝ (y - K.starProjection y) (y - K.starProjection y) := by
    have hy2 : (K.starProjection y + (y - K.starProjection y) : PlaqFnL2 L) = y := by abel
    calc (inner ℝ y y : ℝ)
        = inner ℝ (K.starProjection y + (y - K.starProjection y))
            (K.starProjection y + (y - K.starProjection y)) := by rw [hy2]
      _ = _ := by
          have hc : (inner ℝ (y - K.starProjection y) (K.starProjection y) : ℝ) = 0 := by
            rw [real_inner_comm]; exact horth
          rw [inner_add_left, inner_add_right, inner_add_right, horth, hc]
          ring
  rw [hL2, hR2, hsplit]
  have := real_inner_self_nonneg (x := K.starProjection y)
  linarith

#print axioms deltaKTowerCLM_apply_eq_zero_of_mem
#print axioms towerWitness
#print axioms towerWitness_mem_ker
#print axioms towerWitness_curl_ne_zero
#print axioms towerWitness_mem_towerConstraint
#print axioms tower_kills_towerWitness
#print axioms tower_zero_survives_towerWitness
#print axioms deltaKTowerCLM_zero_ne_level
#print axioms deltaKTowerCLM_zero_ne_one
#print axioms deltaKTowerCLM_coarse_factors
#print axioms deltaKTowerCLM_le_dstarD

/-! ## §7 — THE TOWER HEIGHT IS FINITE ON A FIXED TORUS (§1.5 R5)

`AdmissibleSubspace.blockOf` SILENTLY TRUNCATES when the block side does not divide the extent, so
every level of the tower carries the compatibility guard `0 < ell ∧ ∀ μ, ell ∣ L μ + 1`. Applied to
`ell ^ k`, that guard has a consequence for the `k` axis which is stated here as a theorem, because
p.428's demand is a bound UNIFORM IN `k`. -/

/-- Compatibility at the TOP level implies it at every level below — so one hypothesis
`∀ μ, ell ^ K ∣ L μ + 1` guards the whole tower up to `K`. -/
theorem tower_compatible_below (ell K : ℕ) (hdvd : ∀ μ : Fin 3, ell ^ K ∣ L μ + 1)
    {j : ℕ} (hj : j ≤ K) : ∀ μ : Fin 3, ell ^ j ∣ L μ + 1 :=
  fun μ => dvd_trans (pow_dvd_pow ell hj) (hdvd μ)

/-- **THE HEIGHT BOUND.** On a fixed periodic extent, block-compatibility at level `k` forces
`k < L μ + 1`. So on this carrier the tower has only finitely many faithful levels, and a bound
"uniform in `k`" is a statement about finitely many operators at each fixed `L`. -/
theorem tower_height_lt (ell k : ℕ) (hell : 2 ≤ ell) (μ : Fin 3)
    (hdvd : ell ^ k ∣ L μ + 1) : k < L μ + 1 := by
  have h1 : ell ^ k ≤ L μ + 1 := Nat.le_of_dvd (Nat.succ_pos _) hdvd
  have h2 : k < ell ^ k := Nat.lt_pow_self hell
  omega

#print axioms tower_compatible_below
#print axioms tower_height_lt

/-! ## §8 — SEPARATION FROM THE PINNED (3.10) OPERATOR, AT AN EXPLICIT GAUGE-REGULAR BACKGROUND

`PinnedOperatorFaithfulness.lean` §3a records that an outright
`deltaKCLMNormalized ≠ Δ_k` was not available there, because `Δ_k` had no definition in this tree.
It has one now, and the inequality is a theorem. -/

theorem toLp_genWitness_ne_zero (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (WithLp.toLp 2 (genWitness U) : BondFnL2 L) ≠ 0 := by
  intro h
  refine genWitness_ne_zero hdvd U ?_
  have hof : (WithLp.ofLp (WithLp.toLp 2 (genWitness U) : BondFnL2 L))
      = WithLp.ofLp (0 : BondFnL2 L) := congrArg _ h
  simpa using hof

theorem deltaKCLMNormalized_ne_zero_at_genWitness :
    deltaKCLMNormalized curvedRegularU
        (WithLp.toLp 2 (genWitness curvedRegularU) : BondFnL2 witL5) ≠ 0 := by
  have hmem : (WithLp.toLp 2 (genWitness curvedRegularU) : BondFnL2 witL5)
      ∈ VReg curvedRegularU :=
    toLp_mem_VReg (mem_admKerBare (genWitness_axial witL5_two_dvd curvedRegularU)
      (genWitness_mem_kerQ witL5_two_dvd curvedRegularU))
  have hco := deltaKCLMNormalized_coercive_on_VReg witL5_four_le witL5_two_dvd
    curvedRegularU curvedRegularU_gaugeRegular _ hmem
  have hne := toLp_genWitness_ne_zero witL5_two_dvd curvedRegularU
  have hn : (0 : ℝ) < ‖(WithLp.toLp 2 (genWitness curvedRegularU) : BondFnL2 witL5)‖ :=
    norm_pos_iff.mpr hne
  intro hz
  rw [hz, inner_zero_right] at hco
  have hn2 : (0 : ℝ) < ‖(WithLp.toLp 2 (genWitness curvedRegularU) : BondFnL2 witL5)‖ ^ 2 :=
    pow_pos hn 2
  have := mul_pos normGamma_pos hn2
  linarith

/-- `genWitness U` lies in the level-`1` subspace of the `2`-tower, at EVERY background. A SECOND
witness, kept because §8 needs one that is ALSO axial (so that it lands in `CoercivityRegular.VReg`),
which `towerWitness` is not known to be. -/
theorem genWitness_mem_towerConstraint
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection] :
    genWitness U ∈ gaugeConstraintSubspaceCovFaithful ((2 : ℕ) ^ 1) (oneLevelUniv L) U := by
  rw [mem_gaugeConstraintSubspaceCovFaithful]
  refine ⟨?_, RcovLM_oneLevelUniv_eq_zero U _⟩
  show lineCoarseRestrictCovLM U ((2 : ℕ) ^ 1) (genWitness U) = 0
  rw [pow_one]
  exact funext (fun c => genWitness_mem_kerQ hdvd U c)

theorem tower_one_kills_genWitness
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection] :
    deltaKTowerCLM 2 1 (oneLevelUniv L) U (WithLp.toLp 2 (genWitness U)) = 0 :=
  deltaKTowerCLM_apply_eq_zero_of_mem 2 1 (oneLevelUniv L) U
    (genWitness_mem_towerConstraint hdvd U)

#print axioms genWitness_mem_towerConstraint
#print axioms tower_one_kills_genWitness

/-- **THE SEPARATION.** At `L = witL5` and the gauge-regular background `curvedRegularU`, the
level-`1` member of the `2`-tower is NOT the tree's pinned (3.10) `Δ`. The witness is the same field
in both halves: `Δ̂_1` annihilates it (it lies in `V_1`), while `deltaKCLMNormalized` cannot (it is
coercive on `VReg`, which contains it). -/
theorem deltaKTowerCLM_one_ne_deltaKCLMNormalized
    [(deltaKernelImageCovH curvedRegularU (oneLevelUniv witL5)).HasOrthogonalProjection] :
    deltaKTowerCLM 2 1 (oneLevelUniv witL5) curvedRegularU ≠ deltaKCLMNormalized curvedRegularU := by
  intro hEq
  apply deltaKCLMNormalized_ne_zero_at_genWitness
  rw [← hEq]
  exact tower_one_kills_genWitness witL5_two_dvd curvedRegularU

#print axioms toLp_genWitness_ne_zero
#print axioms deltaKCLMNormalized_ne_zero_at_genWitness
#print axioms deltaKTowerCLM_one_ne_deltaKCLMNormalized

end AdalyFormal.Balaban.DeltaKSuTwoCarrier
