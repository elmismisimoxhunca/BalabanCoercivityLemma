/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CurvedTower

set_option autoImplicit false

/-!
# `CovariantDoor.lean` — the one-level door with a COVARIANT averaging operator

Lane record: `compute/covariant_door/PROGRESS.md`.

`CurvedTower.lean` removed `U = 1` from the level OPERATOR and from the coarse gauge-fixing
CLAUSE, and then disclosed, in its own §0, what it had not removed:

> **The rung's averaging operator `Q` is still the FLAT `qCLM (trivialU Λ) 2`.**

and, in §9b, exactly what closing that would take:

> `curvedLevel_fine_pos` also consumes `‖Q x‖ = ‖qCLM (trivialU Λ) 2 x‖`, which is FALSE at a
> covariant `Q`; replacing it needs the two-sided version of the same estimate fed back through
> `curvedLevel_defect_bound`.

This module runs that re-derivation. Nothing here is assumed and nothing here is new
literature: `CurvedTower.coarseEnergy_qDiff_le`
(`coarseEnergy(Q₂(U)v − Q₂(1)v) ≤ 32α²·bondEnergy v`)
already existed; what was missing was the derivation that carries it through
`ExtentUniformCoercivity.master_defect_bound_sharp` and through `VRestrictedRoute`'s Stokes bound.

## §0 — WHAT IS PROVED, AND WHAT IS NOT

Write `α ≥ frobSupBond U` for the FINE background's radius, `ᾱ ≥ frobSupBond Ū` for the coarse one,
`ε` for `CovariantFibreTransfer`'s Young parameter and `η, η′ > 0` for the two Young parameters
introduced here.

1. **`master_defect_bound_covariantQ`** (§3) — `ExtentUniformCoercivity.master_defect_bound_sharp`
   with the COVARIANT coarse slot:

       (1 − covTax α η)·bondEnergy A ≤ 13264896·curlEnergy A + 6632448·P_Ax(A)
                                       + covB η · coarseEnergy (Q₂(U)A) ,
       covTax α η = 434664114176·(1+1/η)·α²  (= 13583253568·32·(1+1/η)) ,
       covB η     = 13583253568·(1+η) .

   The `32` is `coarseEnergy_qDiff_le`'s own counted constant and the `13583253568` is the flat
   bound's own; NOTHING is refitted. The Young parameter `η` is used in place of the crude
   `‖x‖² ≤ 2‖y‖² + 2‖x−y‖²` precisely so the flat limit is recovered exactly rather than up to a
   factor `2` (§7).

2. **`covLevel_defect_bound`** (§4) — the same at a `CurvedTower.CurvedLevel`:

       (defKappa ρ σ − covTax α η)·‖v‖² ≤ defA c·(⟨v,Δv⟩+⟨v,Pv⟩) + covB η·‖Q₂(U)v‖² .

   `defA` is UNCHANGED. This is literally `CurvedTower.curvedLevel_defect_bound` with `Q₂(1)`
   replaced by `Q₂(U)`, `defKappa` taxed and `defB` replaced by `covB η`.

3. **`coarseCurlEnergy_cov_le`** (§5) — Stokes at the covariant `Q`.
   `VRestrictedRoute.coarseCurlEnergy_Q_le` is a statement about the FLAT `Q₂(1)`; the covariant
   version costs a second Young parameter and the same `α²` remainder:

       coarseCurlEnergy (Q₂(U)A) ≤ (1+η′)·½·curlEnergy A + (1+1/η′)·1024·α²·bondEnergy A ,

   `1024 = 32·32`: `plaqEnergy_flatCurl_le`'s `32` against `coarseEnergy_qDiff_le`'s `32`.

4. **`covariant_gf_on_preimage`** (§6) — THE COVARIANT DOOR at an abstract curved level, and
   **`coercive_on_VSrc_covariantQ`** (§6b) — the same at `Δ_k(U)` itself, with `(c,ρ,σ)` supplied by
   `CurvedTower.curvedBaseLevel`. The fully covariant one-level statement: the operator is
   `Δ_k(U)`, the coarse clause is at `Ū`, AND the averaging that computes the coarse datum is
   `Q₂(U)`, at the SAME `U` as the operator.

5. **Thresholds, two-sided** (§7): the constant is positive at `α = 10⁻¹²` and NONPOSITIVE at
   `α = 10⁻⁹` with everything else fixed — so the NEW, `Q`-covariance tax is itself two-sided, not
   a decoration; and the lattice constant is positive at `α₀ = ᾱ = 10⁻²⁰` and nonpositive at
   `α₀ = 10⁻¹⁹`, matching `CurvedTower`'s own two-sided window.

6. **Flat limit** (§7): at `α = 0`, `(c,ρ,σ) = (1,0,0)` and `ε = η = η′ = 10⁻¹²`, `gammaCov` is
   within a relative `10⁻⁹` of `VRestrictedRoute.gammaV` — the flat door's own constant. The
   covariant machinery costs a relative `3·10⁻¹⁰` at those parameters, not a factor.

7. **Must-fire** (§8): at a genuinely curved FINE background and a genuinely curved COARSE
   background there EXISTS a nonzero fine field whose COVARIANT coarse datum is the source's own
   witness, and the door fires there with both sides strictly positive. The existence is not
   abstract: it is `CurvedTower.qCLM_surjective_of_small` — the residual `CurvedTower` §9 named and
   §9b closed — so the hypothesis domain of §6b is proved NONEMPTY at a curved background rather
   than assumed to be.

8. **`covariantRung`** (§10) — a `TowerOneStep.Rung` whose averaging operator is the COVARIANT
   `Q₂(U)`, every field discharged, none at `trivialU`; and
   **`covariant_next_coercive_on_VCurved`**, the `(γ_cov − δ)/q²` one-step law at that rung.
   `cwCovariantRung` (§11) inhabits it at the curved `cwU`, and `cwCovariantRung_Q` is a
   kernel-checked equation saying its `Q` is `qLevelCov`, not `qLevel`.

9. **`qCLM_cov_ne_qCLM_flat`** (§11b) — the covariant average is NOT the flat average, so this
   module's hypothesis is a DIFFERENT predicate from `CurvedTower.coercive_on_VSrc_curved`'s and
   not a re-spelling of it. Reused from `LineIntegralCovariant`, not rebuilt (LAW-19), and read
   its scope limit below.

**WHAT IS NOT CLAIMED.**

* **The separation of §11b is proved at `witnessU`, NOT at this module's own `cwU`.** At `cwU` — a
  single `rotElem 10⁻²¹` bond — this module does not prove that `Q₂(cwU)` and `Q₂(1)` take different
  values on any field. What that proof would need is an off-axis non-fixed-vector fact for
  `RMap (rotElem 10⁻²¹)` together with non-cancellation of the block sum; it is a computation, not a
  rewrite, and it is not done here. It is not needed for anything above: the door quantifies over
  `U`, so ONE background at which the two averages differ already separates the two statements, and
  the `cwU` witnesses do a different job (inhabitation). Both jobs are done; neither is doing the
  other's.
* ~~**This is the DOOR, not the RUNG.** `CurvedTower.curvedRung`'s `Q` is still flat and this module
  does not change it. §9 states precisely which `Rung` field is still open after this module and
  which are now discharged — the honest ledger is that `hinj`/`hMpos` are now reachable at a
  covariant `Q` (§9's `covLevel_fine_pos`, proved here) and `hQstarInj` is reachable from
  `qCLM_surjective_of_small`, while `Rung.hQ`'s `‖Qx‖ ≤ q‖x‖` and the `T_S` section identity at a
  covariant `Q` are NOT re-derived here.~~ **SUPERSEDED by §10 in this same pass (S75), retained
  struck.** The item was written before §10 was attempted and was wrong on the facts:
  `TowerMilestone.qLevel` is `coarseIso ∘ qCLM (trivialU Λ) 2` and every lemma about it is generic
  in `U` except `qLevelStar_injective`, so `covariantRung` below IS built here and `Rung.hQ` is
  `qCLM_le U 2` — general in `U` all along. The `T_S` identity is a THEOREM of `Rung` (derived from
  the other fields), never a field to re-derive. **`CurvedTower.curvedRung`'s `Q` is indeed still
  flat**; `covariantRung` is a different rung living in this module, and `CurvedTower.lean` is
  another lane's write scope, so nothing there is edited.
* **No tower at depth.** `CurvedTower` §10's obstruction (no blocking map `U ↦ Ū` exists in this
  tree) is untouched by anything here: `Ū` is still a free universally quantified datum and a
  depth-`k` chain would need `k` of them with their radii tied to `α` by a blocking estimate that
  does not exist in this import closure. `covariantRung` removes the FLATNESS of `Q`; it does not
  create a blocking map.
* **`covariantRung` is not `CurvedTower.curvedStepLevel` at a covariant `Q`.** The curved STEP
  (`CurvedLevel` reproduced on the coarse carrier) is not re-run here; the `(c,ρ,σ) ↦ (c',ρ',σ')`
  recursion and its `13583253568/(2κ)` growth factor are `CurvedTower` §10's and are unchanged.
* `J = 0`; `ell = 2`; `𝔰𝔲(2)`; periodic torus. Standing campaign scope, unchanged.
-/

namespace AdalyFormal.Balaban.CovariantDoor

open scoped InnerProductSpace
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLinkConfiguration)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.BridgeInverse (CoarseFnL2 qCLM)
open AdalyFormal.Balaban.U1AnchorCoarse (coarseExtent)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.FibreCoercivity (curlEnergy curlEnergy_nonneg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg frobSupBond)
open AdalyFormal.Balaban.AxialCoercivity (pAx pAxCLM pAx_nonneg pAxCLM_pos inner_pAxCLM_eq')
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized inner_deltaKCLMNormalized_eq)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.OnRangeCoercivity (norm_sq_eq_bondEnergy injective_of_pos_definite
  next_coercive_gf_on_subspace)
open AdalyFormal.Balaban.ExtentUniformCoercivity (coarseEnergy coarseEnergy_nonneg
  master_defect_bound_sharp norm_sq_coarseFnL2 flatCurlValue_sub)
open AdalyFormal.Balaban.ComposedCoercivity (driftRemainder)
open AdalyFormal.Balaban.CovariantFibreTransfer (gammaCurved gammaCurved_pos_iff)
open AdalyFormal.Balaban.WitnessInequality (plaqEnergy_flatCurl_le)
open AdalyFormal.Balaban.VRestrictedRoute (pullS cEnergy bondEnergy_pullS curlEnergy_pullS
  coarseCurlEnergy coarseCurlEnergy_Q_le two_pos' two_dvd_of_four coarse_two_dvd gammaV)
open AdalyFormal.Balaban.TowerOneStep (PiCorrectionBound piOp piOp_apply piOp_symm Rung)
open AdalyFormal.Balaban.BridgeInverse (fineCLM fineCLM_inner qstarCLM qCLM_hadj qCLM_le
  qCLM_norm_pos qstar_injective_of_surjective)
open AdalyFormal.Balaban.TowerMilestone (coarseIso)
open AdalyFormal.Balaban.AxialCoercivity (pAxCLM_symm)
open AdalyFormal.Balaban.CurvedTower (VCurved CurvedLevel defA defKappa defB defA_pos defB_pos
  fibre_bound_on_VCurved curvedBaseLevel gammaLevel coarseEnergy_qDiff_le qCLM_surjective_of_small)

variable {L Λ : PeriodicLatticeExtent}

/-! ## §1 — YOUNG'S SPLIT, ONCE, AT THREE CARRIERS

Every constant below is a Young split of `‖x‖²` against `‖y‖²` and `‖x−y‖²`. The parametric form
`(1+η)/(1+1/η)` is used rather than the fixed `(2,2)` for one reason, stated so it can be attacked:
with `(2,2)` the flat limit of this module's door constant would be a factor `2` away from
`VRestrictedRoute.gammaV`, and §7 would then have to disclose a factor rather than a `3·10⁻¹⁰`. -/

/-- `2ab ≤ ηa² + b²/η`, the scalar Young inequality. -/
theorem two_mul_le_young (a b : ℝ) {eta : ℝ} (heta : 0 < eta) :
    2 * a * b ≤ eta * a ^ 2 + (1 / eta) * b ^ 2 := by
  have hid : eta * a ^ 2 + (1 / eta) * b ^ 2 - 2 * a * b = (1 / eta) * (eta * a - b) ^ 2 := by
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ (1 / eta) * (eta * a - b) ^ 2 :=
    mul_nonneg (le_of_lt (one_div_pos.2 heta)) (sq_nonneg _)
  linarith

/-- **THE SPLIT.** `‖x‖² ≤ (1+η)‖y‖² + (1+1/η)‖x−y‖²`, in any normed group. REUSABLE (LAW-19): the
tree carried only the `η = 1` instance (`FibreCoercivity.sq_two`). -/
theorem norm_sq_young {E : Type*} [NormedAddCommGroup E] (x y : E) {eta : ℝ} (heta : 0 < eta) :
    ‖x‖ ^ 2 ≤ (1 + eta) * ‖y‖ ^ 2 + (1 + 1 / eta) * ‖x - y‖ ^ 2 := by
  have hxy : y + (x - y) = x := by abel
  have htri : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    have h := norm_add_le y (x - y)
    rwa [hxy] at h
  have hsq : ‖x‖ ^ 2 ≤ (‖y‖ + ‖x - y‖) ^ 2 := by
    nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x - y), htri]
  have h1 := two_mul_le_young ‖y‖ ‖x - y‖ heta
  nlinarith [hsq, h1]

/-- The split, summed over coarse bonds. -/
theorem coarseEnergy_young (F G : CoarseBond Λ 2 → SuTwo) {eta : ℝ} (heta : 0 < eta) :
    coarseEnergy F ≤ (1 + eta) * coarseEnergy G
      + (1 + 1 / eta) * coarseEnergy (fun c => F c - G c) := by
  unfold coarseEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun c _ => norm_sq_young (F c) (G c) heta)

/-- The split, summed over plaquettes. `flatCurlValue` is linear, so the split passes through it
(`ExtentUniformCoercivity.flatCurlValue_sub`, REUSED). -/
theorem curlEnergy_young (A B : Bond Λ → SuTwo) {eta : ℝ} (heta : 0 < eta) :
    curlEnergy A ≤ (1 + eta) * curlEnergy B
      + (1 + 1 / eta) * curlEnergy (fun b => A b - B b) := by
  unfold curlEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun p _ => ?_)
  rw [flatCurlValue_sub A B p]
  exact norm_sq_young _ _ heta

/-- `‖F − G‖` and `‖G − F‖` give the same energy. -/
theorem coarseEnergy_sub_comm (F G : CoarseBond Λ 2 → SuTwo) :
    coarseEnergy (fun c => F c - G c) = coarseEnergy (fun c => G c - F c) :=
  Finset.sum_congr rfl (fun c _ => by rw [norm_sub_rev])

/-- `cEnergy` at `ell = 2` IS `coarseEnergy` — a reindexing-free identity, so `rfl`. -/
theorem cEnergy_eq_coarseEnergy (F : CoarseBond Λ 2 → SuTwo) : cEnergy F = coarseEnergy F := rfl

/-! ## §2 — THE TWO TAXES

`covB η` is the coarse coefficient, `covTax α η` the `‖A‖²` tax the covariant slot costs. Both are
COMPOSED: `covB` from `master_defect_bound_sharp`'s own `13583253568`, `covTax` from that same
number against `coarseEnergy_qDiff_le`'s counted `32`. -/

/-- `covB η = 13583253568·(1+η)`. -/
noncomputable def covB (eta : ℝ) : ℝ := 13583253568 * (1 + eta)

/-- `covTax α η = 434664114176·(1+1/η)·α²`, and `434664114176 = 13583253568 · 32`. -/
noncomputable def covTax (alpha eta : ℝ) : ℝ := 434664114176 * (1 + 1 / eta) * alpha ^ 2

/-- The tax's coefficient is the flat coarse coefficient against the qDiff constant — recorded as a
kernel-checked equation so the numeral cannot drift from its factorisation. -/
theorem covTax_coefficient_factors : (434664114176 : ℝ) = 13583253568 * 32 := by norm_num

theorem covB_pos {eta : ℝ} (heta : 0 < eta) : 0 < covB eta := by
  unfold covB; nlinarith

theorem covB_nonneg {eta : ℝ} (heta : 0 ≤ eta) : 0 ≤ covB eta := by
  unfold covB; nlinarith

theorem covTax_nonneg {alpha eta : ℝ} (heta : 0 < eta) : 0 ≤ covTax alpha eta := by
  unfold covTax
  have h : (0 : ℝ) ≤ 1 + 1 / eta := by positivity
  nlinarith [sq_nonneg alpha]

/-- `covTax` vanishes at a FLAT background, for every `η` — this is what makes the flat limit of §7
exact rather than approximate. -/
@[simp] theorem covTax_at_zero (eta : ℝ) : covTax 0 eta = 0 := by
  unfold covTax; ring

/-- `covB η → 13583253568 = defB` as `η ↓ 0`, on the nose at `η = 0`. -/
theorem covB_at_zero : covB 0 = defB := by
  unfold covB defB; norm_num

/-- `κ_cov = defKappa ρ σ − covTax α η`. -/
noncomputable def covKappa (rho sigma alpha eta : ℝ) : ℝ :=
  defKappa rho sigma - covTax alpha eta

/-- At a flat background the covariant `κ` IS `CurvedTower`'s. -/
theorem covKappa_at_zero (rho sigma eta : ℝ) : covKappa rho sigma 0 eta = defKappa rho sigma := by
  unfold covKappa; rw [covTax_at_zero]; ring

/-! ## §3 — THE MASTER DEFECT BOUND WITH THE COVARIANT COARSE SLOT -/

/-- **THE FLAT COARSE ENERGY, CONTROLLED BY THE COVARIANT ONE.**
`coarseEnergy(Q₂(1)A) ≤ (1+η)·coarseEnergy(Q₂(U)A) + (1+1/η)·32α²·bondEnergy A`. -/
theorem coarseEnergy_flat_le_cov (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    {alpha : ℝ} (halpha0 : 0 ≤ alpha) (hsup : frobSupBond U ≤ alpha)
    {eta : ℝ} (heta : 0 < eta) (A : Bond Λ → SuTwo) :
    coarseEnergy (lineCoarseRestrictCov (trivialU Λ) 2 A)
      ≤ (1 + eta) * coarseEnergy (lineCoarseRestrictCov U 2 A)
        + (1 + 1 / eta) * (32 * alpha ^ 2 * bondEnergy A) := by
  have hy := coarseEnergy_young (lineCoarseRestrictCov (trivialU Λ) 2 A)
    (lineCoarseRestrictCov U 2 A) heta
  rw [coarseEnergy_sub_comm] at hy
  have hq := coarseEnergy_qDiff_le hdvd U halpha0 hsup A
  have hinv : (0 : ℝ) ≤ 1 + 1 / eta := by positivity
  have hstep := mul_le_mul_of_nonneg_left hq hinv
  linarith [hy, hstep]

/-- **THE COVARIANT MASTER DEFECT BOUND.** `ExtentUniformCoercivity.master_defect_bound_sharp` with
`‖Q₂(U)A‖²` in the coarse slot, the `Q`-drift absorbed into `covTax`. At `U = 1` and `η ↓ 0` it is
the flat bound verbatim (`covTax_at_zero`, `covB_at_zero`). -/
theorem master_defect_bound_covariantQ (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    {alpha : ℝ} (halpha0 : 0 ≤ alpha) (hsup : frobSupBond U ≤ alpha)
    {eta : ℝ} (heta : 0 < eta) (A : Bond Λ → SuTwo) :
    (1 - covTax alpha eta) * bondEnergy A
      ≤ 13264896 * curlEnergy A + 6632448 * pAx A (CoarseLattice Λ 2) 2
        + covB eta * coarseEnergy (lineCoarseRestrictCov U 2 A) := by
  have hm := master_defect_bound_sharp hdvd A
  have hz := coarseEnergy_flat_le_cov hdvd U halpha0 hsup heta A
  unfold covTax covB
  nlinarith [hm, hz]

/-! ## §4 — THE COVARIANT DEFECT BOUND AT A `CurvedLevel`

This is the sentence `CurvedTower` §9b said was missing, executed: the two-sided estimate fed back
through `curvedLevel_defect_bound`. -/

/-- **REUSABLE (LAW-19).** `ExtentUniformCoercivity.norm_sq_qCLM` is stated only at `trivialU`; its
proof never uses the background. This is the same statement at an ARBITRARY `U`. -/
theorem norm_sq_qCLM_cov (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    (x : BondFnL2 Λ) :
    ‖qCLM U 2 x‖ ^ 2 = coarseEnergy (lineCoarseRestrictCov U 2 (WithLp.ofLp x)) := by
  have h : (qCLM U 2 x : CoarseFnL2 Λ 2)
      = WithLp.toLp 2 (lineCoarseRestrictCov U 2 (WithLp.ofLp x)) := rfl
  rw [h, norm_sq_coarseFnL2]

/-- **THE COVARIANT LEVEL DEFECT BOUND.** `CurvedTower.curvedLevel_defect_bound` with `Q₂(U)` in the
coarse slot. `defA` is unchanged; `defKappa` pays `covTax`; `defB` becomes `covB η`. -/
theorem covLevel_defect_bound {c rho sigma : ℝ} (lvl : CurvedLevel Λ c rho sigma)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    {alpha : ℝ} (halpha0 : 0 ≤ alpha) (hsup : frobSupBond U ≤ alpha)
    {eta : ℝ} (heta : 0 < eta) (v : BondFnL2 Λ) :
    covKappa rho sigma alpha eta * ‖v‖ ^ 2
      ≤ defA c * ((inner ℝ v (lvl.op v) : ℝ)
          + (inner ℝ v (pAxCLM (CoarseLattice Λ 2) 2 v) : ℝ))
        + covB eta * ‖qCLM U 2 v‖ ^ 2 := by
  have hm := master_defect_bound_covariantQ hdvd U halpha0 hsup heta (WithLp.ofLp v)
  have hn : ‖v‖ ^ 2 = bondEnergy (WithLp.ofLp v) := norm_sq_eq_bondEnergy v
  have hP : (inner ℝ v (pAxCLM (CoarseLattice Λ 2) 2 v) : ℝ)
      = pAx (WithLp.ofLp v) (CoarseLattice Λ 2) 2 := inner_pAxCLM_eq' _ _ v
  have hQ : ‖qCLM U 2 v‖ ^ 2 = coarseEnergy (lineCoarseRestrictCov U 2 (WithLp.ofLp v)) :=
    norm_sq_qCLM_cov U v
  have hcurl := lvl.hcurl v
  have hlow := lvl.hlow v
  rw [hn] at hcurl hlow
  rw [hP] at hcurl ⊢
  rw [hn, hQ]
  unfold covKappa defKappa defA
  nlinarith [hm, hcurl, hlow]

/-! ## §5 — STOKES AT THE COVARIANT `Q`

`VRestrictedRoute.coarseCurlEnergy_Q_le` is a statement about the FLAT average. `CurvedTower` §5
noted that this was harmless there because both of its sides were flat objects; once the coarse
datum itself is `Q₂(U)A` that is no longer so, and the transfer costs the same `α²` remainder plus a
second Young parameter. -/

/-- **STOKES, COVARIANT.** `coarseCurlEnergy(Q₂(U)A) ≤ (1+η′)·½·curlEnergy A
+ (1+1/η′)·1024·α²·bondEnergy A`, with `1024 = 32·32` — `plaqEnergy_flatCurl_le`'s `32` (the curl of
a field is `32` times its energy) against `coarseEnergy_qDiff_le`'s `32`. -/
theorem coarseCurlEnergy_cov_le (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    {alpha : ℝ} (halpha0 : 0 ≤ alpha) (hsup : frobSupBond U ≤ alpha)
    {etaP : ℝ} (hetaP : 0 < etaP) (A : Bond Λ → SuTwo) :
    coarseCurlEnergy hdvd (lineCoarseRestrictCov U 2 A)
      ≤ (1 + etaP) * (1 / 2 * curlEnergy A)
        + (1 + 1 / etaP) * (1024 * alpha ^ 2 * bondEnergy A) := by
  set Fu := lineCoarseRestrictCov U 2 A with hFu
  set F1 := lineCoarseRestrictCov (trivialU Λ) 2 A with hF1
  -- transport both coarse fields to the coarse-index lattice, where `curlEnergy_young` applies
  have hPu : curlEnergy (pullS two_pos' hdvd Fu) = coarseCurlEnergy hdvd Fu :=
    curlEnergy_pullS two_pos' hdvd Fu
  have hP1 : curlEnergy (pullS two_pos' hdvd F1) = coarseCurlEnergy hdvd F1 :=
    curlEnergy_pullS two_pos' hdvd F1
  have hyoung := curlEnergy_young (pullS two_pos' hdvd Fu) (pullS two_pos' hdvd F1) hetaP
  have hdiff : (fun b => pullS two_pos' hdvd Fu b - pullS two_pos' hdvd F1 b)
      = pullS two_pos' hdvd (fun c => Fu c - F1 c) := rfl
  rw [hdiff, hPu, hP1] at hyoung
  -- the remainder: `curl ≤ 32·bondEnergy` on the coarse-index lattice, then the qDiff bound
  have h32 : curlEnergy (pullS two_pos' hdvd (fun c => Fu c - F1 c))
      ≤ 32 * bondEnergy (pullS two_pos' hdvd (fun c => Fu c - F1 c)) :=
    plaqEnergy_flatCurl_le _
  have hbe : bondEnergy (pullS two_pos' hdvd (fun c => Fu c - F1 c))
      = coarseEnergy (fun c => Fu c - F1 c) := by
    rw [bondEnergy_pullS two_pos' hdvd, cEnergy_eq_coarseEnergy]
  have hq := coarseEnergy_qDiff_le hdvd U halpha0 hsup A
  rw [hbe] at h32
  -- flat Stokes, unchanged
  have hstokes := coarseCurlEnergy_Q_le (L := Λ) (ell := 2) two_pos' hdvd A
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2] at hstokes
  -- assemble
  have hp1 : (0 : ℝ) ≤ 1 + etaP := by linarith
  have hp2 : (0 : ℝ) ≤ 1 + 1 / etaP := by positivity
  have s1 : (1 + etaP) * coarseCurlEnergy hdvd F1 ≤ (1 + etaP) * (1 / 2 * curlEnergy A) :=
    mul_le_mul_of_nonneg_left hstokes hp1
  have s2 : (1 + 1 / etaP) * curlEnergy (pullS two_pos' hdvd (fun c => Fu c - F1 c))
      ≤ (1 + 1 / etaP) * (32 * (32 * alpha ^ 2 * bondEnergy A)) := by
    refine mul_le_mul_of_nonneg_left (le_trans h32 ?_) hp2
    linarith [hq]
  have hexp : (1 + 1 / etaP) * (32 * (32 * alpha ^ 2 * bondEnergy A))
      = (1 + 1 / etaP) * (1024 * alpha ^ 2 * bondEnergy A) := by ring
  rw [hexp] at s2
  linarith [hyoung, s1, s2]

/-! ## §6 — THE COVARIANT DOOR -/

/-- The numerator of the covariant door's constant. -/
noncomputable def covNum (rho sigma alpha eta etaP gc : ℝ) : ℝ :=
  2 * gc * covKappa rho sigma alpha eta
    - covB eta * ((1 + etaP) * rho + 2048 * (1 + 1 / etaP) * alpha ^ 2)

/-- The denominator. -/
noncomputable def covDen (c eta etaP gc : ℝ) : ℝ :=
  2 * gc * defA c + covB eta * (1 + etaP) * c

/-- **THE COVARIANT DOOR'S CONSTANT.**

    γ_cov = [2gc(defKappa ρ σ − covTax α η) − covB η((1+η′)ρ + 2048(1+1/η′)α²)]
            / [2gc·defA c + covB η(1+η′)c] .

`L`-free and level-free; `2048 = 2·1024` is §5's `1024` carried through the factor `2` that clears
the `½` of Stokes. -/
noncomputable def gammaCov (c rho sigma alpha eta etaP gc : ℝ) : ℝ :=
  covNum rho sigma alpha eta etaP gc / covDen c eta etaP gc

theorem covDen_pos {c eta etaP gc : ℝ} (hc : 0 ≤ c) (heta : 0 < eta) (hetaP : 0 < etaP)
    (hgc : 0 < gc) : 0 < covDen c eta etaP gc := by
  unfold covDen
  have h1 : 0 < defA c := defA_pos hc
  have h2 : 0 < covB eta := covB_pos heta
  have hp : (0 : ℝ) ≤ 1 + etaP := by linarith
  have h3 : (0 : ℝ) ≤ covB eta * (1 + etaP) * c :=
    mul_nonneg (mul_nonneg h2.le hp) hc
  nlinarith

/-- **THE COVARIANT DOOR AT A LEVEL.** For every `u` whose COVARIANT coarse datum — computed with
`Q₂(U)` at the SAME `U` the level's operator carries — lies in the source's subspace at the next
lattice read with the covariant `Q₁(Ū)`,

    γ_cov · ‖u‖² ≤ ⟨u, Δ u⟩ + ⟨u, P_Ax u⟩ .

Compare `CurvedTower.curved_gf_on_preimage`: there the coarse datum is `qLevel`, i.e. the FLAT
average. -/
theorem covariant_gf_on_preimage {c rho sigma : ℝ} (lvl : CurvedLevel Λ c rho sigma) (hc : 0 ≤ c)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hdvd' : ∀ μ : Fin 3, (2 : ℕ) ∣ (coarseExtent Λ 2 μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    {alpha : ℝ} (halpha0 : 0 ≤ alpha) (hsupU : frobSupBond U ≤ alpha)
    (Ubar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (coarseExtent Λ 2))
    {abar : ℝ} (habar : 0 ≤ abar) (hsupbar : frobSupBond Ubar ≤ abar)
    {eps : ℝ} (heps : 0 < eps) (hgc : 0 < gammaCurved abar eps)
    {eta etaP : ℝ} (heta : 0 < eta) (hetaP : 0 < etaP)
    (u : BondFnL2 Λ)
    (hu : VCurved (coarseExtent Λ 2) Ubar
      (pullS two_pos' hdvd (lineCoarseRestrictCov U 2 (WithLp.ofLp u)))) :
    gammaCov c rho sigma alpha eta etaP (gammaCurved abar eps) * ‖u‖ ^ 2
      ≤ (inner ℝ u (lvl.op u) : ℝ)
        + (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ) := by
  set gc : ℝ := gammaCurved abar eps with hgcdef
  -- (a) the coarse fibre bound, at the COVARIANT datum
  have hfib := fibre_bound_on_VCurved hdvd' Ubar habar hsupbar heps hu
  rw [bondEnergy_pullS two_pos' hdvd, cEnergy_eq_coarseEnergy,
    curlEnergy_pullS two_pos' hdvd] at hfib
  -- (b) Stokes at the covariant `Q`
  have hst := coarseCurlEnergy_cov_le hdvd U halpha0 hsupU hetaP (WithLp.ofLp u)
  -- (c) the covariant defect bound
  have hdef := covLevel_defect_bound lvl hdvd U halpha0 hsupU heta u
  have hQ : ‖qCLM U 2 u‖ ^ 2 = coarseEnergy (lineCoarseRestrictCov U 2 (WithLp.ofLp u)) :=
    norm_sq_qCLM_cov U u
  have hE : ‖u‖ ^ 2 = bondEnergy (WithLp.ofLp u) := norm_sq_eq_bondEnergy u
  have hcurl := lvl.hcurl u
  rw [hQ] at hdef
  set D : ℝ := (inner ℝ u (lvl.op u) : ℝ) with hD
  set P : ℝ := (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ) with hP
  set Zu : ℝ := coarseEnergy (lineCoarseRestrictCov U 2 (WithLp.ofLp u)) with hZu
  set E : ℝ := ‖u‖ ^ 2 with hEd
  set C : ℝ := curlEnergy (WithLp.ofLp u) with hCd
  rw [← hE] at hst
  have hB0 : (0 : ℝ) ≤ covB eta := covB_nonneg (le_of_lt heta)
  have hp1 : (0 : ℝ) ≤ 1 + etaP := by linarith
  -- `gc · Zu ≤ (1+η′)·½·C + (1+1/η′)·1024α²E`
  have s1 : gc * Zu ≤ (1 + etaP) * (1 / 2 * C) + (1 + 1 / etaP) * (1024 * alpha ^ 2 * E) :=
    le_trans hfib hst
  have s2 : 2 * covB eta * (gc * Zu)
      ≤ 2 * covB eta * ((1 + etaP) * (1 / 2 * C) + (1 + 1 / etaP) * (1024 * alpha ^ 2 * E)) :=
    mul_le_mul_of_nonneg_left s1 (by linarith)
  have s3 : 2 * gc * (covKappa rho sigma alpha eta * E)
      ≤ 2 * gc * (defA c * (D + P) + covB eta * Zu) :=
    mul_le_mul_of_nonneg_left hdef (by linarith)
  have s4 : covB eta * (1 + etaP) * C ≤ covB eta * (1 + etaP) * (c * (D + P) + rho * E) :=
    mul_le_mul_of_nonneg_left hcurl (by nlinarith)
  have hden : 0 < covDen c eta etaP gc := covDen_pos hc heta hetaP hgc
  unfold gammaCov covNum covDen
  unfold covDen at hden
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [s2, s3, s4]

/-! ### §6b — THE COVARIANT DOOR AT THE LATTICE, EVERY PARAMETER DISCHARGED

`(c,ρ,σ) = (2, driftRemainder α₀, 272α₀)` from `CurvedTower.curvedBaseLevel`, and the `α` of the
`Q`-drift is the SAME `α₀` that bounds the operator's background. That identification is the whole
point: operator curved, tax real, `Q` curved, ONE background. -/

/-- The covariant door's constant at the lattice. -/
noncomputable def gammaCovLattice (alpha0 abar eps eta etaP : ℝ) : ℝ :=
  gammaCov 2 (driftRemainder alpha0) (272 * alpha0) alpha0 eta etaP (gammaCurved abar eps)

/-- **THE FULLY COVARIANT ONE-LEVEL STATEMENT.** For every fine field whose coarse datum, COMPUTED
WITH `Q₂(U)`, lies in p.428's subspace read with the covariant `Q₁(Ū)`,

    γ_cov(α₀,ᾱ,ε,η,η′) · bondEnergy A ≤ ⟨A, Δ_k(U) A⟩ + P_Ax(A) .

Compare `CurvedTower.coercive_on_VSrc_curved`, whose hypothesis reads the datum at
`lineCoarseRestrictCov (trivialU L) 2 A`. -/
theorem coercive_on_VSrc_covariantQ (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ alpha0)
    (Ubar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (coarseExtent L 2))
    {abar : ℝ} (habar : 0 ≤ abar) (hsupbar : frobSupBond Ubar ≤ abar)
    {eps : ℝ} (heps : 0 < eps) (hgc : 0 < gammaCurved abar eps)
    {eta etaP : ℝ} (heta : 0 < eta) (hetaP : 0 < etaP)
    (A : Bond L → SuTwo)
    (hA : VCurved (coarseExtent L 2) Ubar
      (pullS two_pos' (two_dvd_of_four hdvd4) (lineCoarseRestrictCov U 2 A))) :
    gammaCovLattice alpha0 abar eps eta etaP * bondEnergy A
      ≤ deltaKQuadFormNormalizedCorrected U A + pAx A (CoarseLattice L 2) 2 := by
  have hmain := covariant_gf_on_preimage (curvedBaseLevel halpha U hsup) (by norm_num)
    (two_dvd_of_four hdvd4) (coarse_two_dvd hdvd4) U halpha hsup Ubar habar hsupbar heps hgc
    heta hetaP (WithLp.toLp 2 A) hA
  have hE : ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2 = bondEnergy A := norm_sq_eq_bondEnergy _
  have hop : (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
        ((curvedBaseLevel halpha U hsup).op (WithLp.toLp 2 A)) : ℝ)
      = deltaKQuadFormNormalizedCorrected U A := inner_deltaKCLMNormalized_eq U A
  have hP : (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
        (pAxCLM (CoarseLattice L 2) 2 (WithLp.toLp 2 A)) : ℝ)
      = pAx A (CoarseLattice L 2) 2 := inner_pAxCLM_eq' _ _ _
  rw [hE, hop, hP] at hmain
  exact hmain

/-! ## §7 — THRESHOLDS, TWO-SIDED, AND THE FLAT LIMIT -/

/-- **THE FLAT LEVEL CONSTANT, EXACTLY.** At `α = 0`, `(c,ρ,σ) = (1,0,0)` and a flat coarse
background, `γ_cov = 1/(19897344 + (1+η)(1+η′)(1+ε)·22522555740143616)` — the same shape as
`CurvedTower.gammaLevel_flat_eq`, with the two new Young parameters entering only as `(1+η)(1+η′)`
against `defB`. -/
theorem gammaCov_flat_eq {eps eta etaP : ℝ} (heps : 0 < eps) (heta : 0 < eta)
    (hetaP : 0 < etaP) :
    gammaCov 1 0 0 0 eta etaP (gammaCurved 0 eps)
      = 1 / (19897344 + (1 + eta) * (1 + etaP) * (1 + eps) * 22522555740143616) := by
  have he : (0 : ℝ) < 1 + eps := by linarith
  have hd0 : (0 : ℝ) < (1 + eps) * 3316224 := by nlinarith
  have hg : gammaCurved 0 eps = 1 / ((1 + eps) * 3316224) :=
    AdalyFormal.Balaban.CurvedTower.gammaCurved_at_zero eps
  have hginv : (0 : ℝ) < 1 / ((1 + eps) * 3316224) := div_pos one_pos hd0
  have hnum : covNum 0 0 0 eta etaP (gammaCurved 0 eps) = 2 * gammaCurved 0 eps := by
    unfold covNum covKappa defKappa covB
    rw [covTax_at_zero]
    ring
  have hden : covDen 1 eta etaP (gammaCurved 0 eps)
      = 2 * gammaCurved 0 eps * 19897344 + 13583253568 * (1 + eta) * (1 + etaP) := by
    unfold covDen defA covB
    ring
  unfold gammaCov
  rw [hnum, hden, hg]
  have hD1 : (0 : ℝ) < 2 * (1 / ((1 + eps) * 3316224)) * 19897344
      + 13583253568 * (1 + eta) * (1 + etaP) := by nlinarith [hginv, heta, hetaP]
  have hD2 : (0 : ℝ)
      < 19897344 + (1 + eta) * (1 + etaP) * (1 + eps) * 22522555740143616 := by
    have h1 : (0 : ℝ) < 1 + eta := by linarith
    have h2 : (0 : ℝ) < 1 + etaP := by linarith
    have hprod : (0 : ℝ) < (1 + eta) * (1 + etaP) * (1 + eps) := mul_pos (mul_pos h1 h2) he
    linarith [hprod]
  rw [div_eq_div_iff (ne_of_gt hD1) (ne_of_gt hD2)]
  field_simp
  ring

/-- **THE FLAT LIMIT RECOVERS `gammaV`.** At `ε = η = η′ = 10⁻¹²` the FULLY COVARIANT constant is
within a relative `10⁻⁹` of `VRestrictedRoute.gammaV`, the flat door's own constant. So making the
averaging covariant costs a relative `3·10⁻¹⁰` at those parameters — not a factor `2` (which the
crude `‖x‖² ≤ 2‖y‖²+2‖x−y‖²` split would have cost) and not a factor `48`. -/
theorem gammaCov_flat_recovers_gammaV :
    gammaV * (1 - 1 / 10 ^ 9)
        ≤ gammaCov 1 0 0 0 (1 / 10 ^ 12) (1 / 10 ^ 12) (gammaCurved 0 (1 / 10 ^ 12))
      ∧ gammaCov 1 0 0 0 (1 / 10 ^ 12) (1 / 10 ^ 12) (gammaCurved 0 (1 / 10 ^ 12))
        ≤ gammaV := by
  rw [gammaCov_flat_eq (by norm_num : (0:ℝ) < 1 / 10 ^ 12)
    (by norm_num : (0:ℝ) < 1 / 10 ^ 12) (by norm_num : (0:ℝ) < 1 / 10 ^ 12)]
  unfold gammaV
  constructor <;> norm_num

/-- **THE NEW TAX IS TWO-SIDED ON ITS OWN AXIS.** `covKappa` — the covariant master bound's leading
coefficient, with NO drift (`ρ = σ = 0`) — is positive at `α = 10⁻⁷` and nonpositive at
`α = 10⁻⁵`, at `η = 1`. So `covTax` is a real constraint, not a decoration. -/
theorem covKappa_two_sided :
    0 < covKappa 0 0 (1 / 10 ^ 7) 1 ∧ covKappa 0 0 (1 / 10 ^ 5) 1 ≤ 0 := by
  unfold covKappa defKappa covTax
  constructor <;> norm_num

/-- **THE DOOR'S CONSTANT IS TWO-SIDED IN THE `Q`-DRIFT.** With the drift parameters set to ZERO
(`(c,ρ,σ) = (1,0,0)`, so `CurvedTower`'s own taxes are switched off) and everything else fixed
(`ᾱ = 10⁻²⁰`, `ε = η = η′ = 1`), `gammaCov` is STRICTLY POSITIVE at `α = 10⁻¹²` and NONPOSITIVE at
`α = 10⁻⁹`. The only thing that changes between the two is the covariance of `Q`. -/
theorem gammaCov_two_sided_in_alpha :
    0 < gammaCov 1 0 0 (1 / 10 ^ 12) 1 1 (gammaCurved (1 / 10 ^ 20) 1)
      ∧ gammaCov 1 0 0 (1 / 10 ^ 9) 1 1 (gammaCurved (1 / 10 ^ 20) 1) ≤ 0 := by
  unfold gammaCov covNum covDen covKappa defKappa covTax covB defA
    AdalyFormal.Balaban.CovariantFibreTransfer.gammaCurved
  constructor <;> norm_num

/-- **THE LATTICE CONSTANT CLOSES** at `α₀ = ᾱ = 10⁻²⁰`, `ε = 1`, `η = η′ = 10⁻¹²`, at the lattice
level's own `(c,ρ,σ) = (2, driftRemainder α₀, 272α₀)`. -/
theorem gammaCovLattice_pos_at_1e_neg_20 :
    0 < gammaCovLattice (1 / 10 ^ 20) (1 / 10 ^ 20) 1 (1 / 10 ^ 12) (1 / 10 ^ 12) := by
  unfold gammaCovLattice gammaCov covNum covDen covKappa defKappa covTax covB defA
    AdalyFormal.Balaban.ComposedCoercivity.driftRemainder
    AdalyFormal.Balaban.CovariantFibreTransfer.gammaCurved
  norm_num

/-- **AND IT FAILS ONE DECADE COARSER.** At `α₀ = 10⁻¹⁹` the same constant is nonpositive — the
same two-sided window `CurvedTower.gammaLevel_nonpos_at_1e_neg_19` records, so the covariant `Q` did
not silently widen it. -/
theorem gammaCovLattice_nonpos_at_1e_neg_19 :
    gammaCovLattice (1 / 10 ^ 19) (1 / 10 ^ 20) 1 (1 / 10 ^ 12) (1 / 10 ^ 12) ≤ 0 := by
  unfold gammaCovLattice gammaCov covNum covDen covKappa defKappa covTax covB defA
    AdalyFormal.Balaban.ComposedCoercivity.driftRemainder
    AdalyFormal.Balaban.CovariantFibreTransfer.gammaCurved
  norm_num

/-! ## §8 — MUST-FIRE: the covariant door's hypothesis is INHABITED at a curved background

§7 says the constant is positive. It says nothing about the statement having any instance. This
section supplies one, and the supply is the interesting part: the coarse datum of §6b is computed
with `Q₂(U)`, so a witness cannot be built by lifting a coarse field through the FLAT section the
way `CurvedTower` §8b does. It is built instead from `CurvedTower.qCLM_surjective_of_small` — the
residual `CurvedTower` §9 NAMED and §9b CLOSED. The covariant average is surjective at
`32α < 1`, and `10⁻²⁰` is twenty decades inside that, so the coarse datum can be PRESCRIBED. -/

section MustFire

open AdalyFormal.Balaban.BridgeRestricted (rotGen rotGen_ne_zero)
open AdalyFormal.Balaban.VRestrictedRoute (vWitFine vWitCoarse_ne_zero pullC_vWitCoarse)
open AdalyFormal.Balaban.CurvedTower (cwL cwT cwU cwUbar cwF cwL_dvd4 cwL_dvd2 cwL_coarse_dvd2
  cwU_frobSup cwUbar_frobSup cwU_curved cwUbar_curved bondRot_fix_rotGen vWitFine_mem_VCurved)

/-- `Q₂(cwU)` is surjective: `frobSupBond cwU ≤ 10⁻²⁰` and `32·10⁻²⁰ < 1`. -/
theorem qCLM_cwU_surjective : Function.Surjective (qCLM cwU 2) :=
  qCLM_surjective_of_small cwL_dvd2 cwU (by norm_num) cwU_frobSup (by norm_num)

/-- The two thresholds §6b consumes, at the must-fire parameters. -/
theorem cw_cov_threshold :
    0 < gammaCovLattice (1 / 10 ^ 20) (1 / 10 ^ 20) 1 (1 / 10 ^ 12) (1 / 10 ^ 12) :=
  gammaCovLattice_pos_at_1e_neg_20

/-- **MUST-FIRE ON THE COVARIANT DOOR.** There is a NONZERO fine field on a lattice of side `8`
whose COVARIANT coarse datum `Q₂(U)A` is `VRestrictedRoute`'s own coarse witness — hence lies in the
source's subspace at the coarse lattice read with the covariant `Q₁(Ū)` — at a FINE background and a
COARSE background both of which have plaquette holonomy `≠ 1`, and at which
`coercive_on_VSrc_covariantQ` fires with a strictly positive left-hand side.

**S91 note.** The existential data `A` is not free: it is PINNED by
`lineCoarseRestrictCov cwU 2 A = cwF`, an equation against a named, previously-constructed object
(`CurvedTower.cwF = VRestrictedRoute.vWitCoarse cwL_dvd4 rotGen`). A prover cannot satisfy this
clause by choosing a degenerate `A`; `cwF ≠ 0` forces `A ≠ 0`, and that is proved rather than
assumed. -/
theorem covariant_door_must_fire :
    ∃ A : Bond cwL → SuTwo,
      lineCoarseRestrictCov cwU 2 A = cwF
      ∧ A ≠ 0
      ∧ AdalyFormal.Balaban.DeltaPrime.holonomyElem cwU
          (AdalyFormal.Balaban.FibreCoercivity.zeroSite cwL,
            (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
          ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ AdalyFormal.Balaban.DeltaPrime.holonomyElem cwUbar
          (AdalyFormal.Balaban.FibreCoercivity.zeroSite (coarseExtent cwL 2),
            (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
          ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ 0 < gammaCovLattice (1 / 10 ^ 20) (1 / 10 ^ 20) 1 (1 / 10 ^ 12) (1 / 10 ^ 12)
      ∧ 0 < gammaCovLattice (1 / 10 ^ 20) (1 / 10 ^ 20) 1 (1 / 10 ^ 12) (1 / 10 ^ 12)
          * bondEnergy A
      ∧ 0 < deltaKQuadFormNormalizedCorrected cwU A + pAx A (CoarseLattice cwL 2) 2
      ∧ gammaCovLattice (1 / 10 ^ 20) (1 / 10 ^ 20) 1 (1 / 10 ^ 12) (1 / 10 ^ 12) * bondEnergy A
          ≤ deltaKQuadFormNormalizedCorrected cwU A + pAx A (CoarseLattice cwL 2) 2 := by
  obtain ⟨x, hx⟩ := qCLM_cwU_surjective (WithLp.toLp 2 cwF)
  -- the prescribed COVARIANT coarse datum
  have hdatum : lineCoarseRestrictCov cwU 2 (WithLp.ofLp x) = cwF :=
    congrArg (fun z : CoarseFnL2 cwL 2 => WithLp.ofLp z) hx
  have hcwFne : cwF ≠ 0 := vWitCoarse_ne_zero cwL_dvd4 rotGen_ne_zero
  have hAne : (WithLp.ofLp x : Bond cwL → SuTwo) ≠ 0 := by
    intro h0
    refine hcwFne ?_
    rw [← hdatum, h0]
    exact (AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCovLM cwU 2).map_zero
  -- the datum lands in the source's subspace at the coarse lattice, read with the covariant `Q₁(Ū)`
  have hmem : VCurved (coarseExtent cwL 2) cwUbar
      (pullS two_pos' (two_dvd_of_four cwL_dvd4)
        (lineCoarseRestrictCov cwU 2 (WithLp.ofLp x))) := by
    rw [hdatum]
    have h : pullS two_pos' (two_dvd_of_four cwL_dvd4) cwF
        = vWitFine (Lc := coarseExtent cwL 2) rotGen := pullC_vWitCoarse cwL_dvd4 rotGen
    rw [h]
    exact vWitFine_mem_VCurved cwL_coarse_dvd2 cwUbar (fun b => bondRot_fix_rotGen _ cwT b)
  have hgc : 0 < gammaCurved (1 / 10 ^ 20 : ℝ) 1 := by
    rw [gammaCurved_pos_iff]; norm_num
  have hmain := coercive_on_VSrc_covariantQ cwL_dvd4 (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 20) cwU
    cwU_frobSup cwUbar (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 20) cwUbar_frobSup
    (by norm_num : (0:ℝ) < 1) hgc (by norm_num : (0:ℝ) < 1 / 10 ^ 12)
    (by norm_num : (0:ℝ) < 1 / 10 ^ 12) (WithLp.ofLp x) hmem
  have hgam := cw_cov_threshold
  obtain ⟨b0, hb0⟩ : ∃ b0 : Bond cwL, (WithLp.ofLp x : Bond cwL → SuTwo) b0 ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hAne (funext hcon)
  have hE : 0 < bondEnergy (WithLp.ofLp x : Bond cwL → SuTwo) :=
    AdalyFormal.Balaban.FibreAggregate.bondEnergy_pos _ hb0
  exact ⟨WithLp.ofLp x, hdatum, hAne, cwU_curved, cwUbar_curved, hgam, mul_pos hgam hE,
    lt_of_lt_of_le (mul_pos hgam hE) hmain, hmain⟩

end MustFire

/-! ## §9 — WHAT THIS MODULE DOES AND DOES NOT DISCHARGE IN `TowerOneStep.Rung`

`CurvedTower` §9 listed the five `Rung` fields against a covariant `Q` and marked `hQstarInj`
BLOCKED; §9b then closed it (`qCLM_surjective_of_small`). The list, re-read after this module:

* `hadj` — `BridgeInverseCarrier.qCLM_hadj U ell` is general in `U`. ✓ (unchanged)
* `hQ`, `hq` — `qCLM_le`, `qCLM_norm_pos` are general in `U`. ✓ (unchanged)
* `hQstarInj` — reachable from `CurvedTower.qCLM_surjective_of_small` at `32α < 1`. ✓
* `hinj`, `hMpos` — these consumed `‖Q x‖ = ‖qCLM (trivialU Λ) 2 x‖`, which is FALSE at a covariant
  `Q`. **`covLevel_fine_pos` below removes that consumption**: it is
  `CurvedTower.curvedLevel_fine_pos` with the flat-`Q` norm identity replaced by the COVARIANT one,
  its proof running through `covLevel_defect_bound` instead of `curvedLevel_defect_bound`. So the
  sentence `CurvedTower` §9b left standing — *"replacing it needs the two-sided version of the same
  estimate fed back through `curvedLevel_defect_bound`"* — is discharged, and that sentence is
  SUPERSEDED there (S75; it is retained in `CurvedTower` struck-through in effect by this module's
  header, which this module cannot edit — write-scope: `CurvedTower.lean` belongs to another lane).

~~**WHAT IS STILL NOT ASSEMBLED, precisely.** A covariant `curvedRung` needs, beyond the five fields
above, the `Rung` structure's own coarse-side data at a covariant `Q`: `qLevel`/`qLevelStar` are
built in `TowerMilestone` at `trivialU` (their `T_S` section identity is proved through the flat
lift), and re-deriving THAT at `qCLM U 2` is a separate construction which this module does not
perform. Stating it as done would be false; the door above does not use it.~~

**SUPERSEDED by §10 IN THE SAME PASS (S75), retained struck.** The paragraph above was written
before §10 was attempted, and it was wrong twice: `T_S` is a THEOREM of `Rung` derived from the
structure's fields (`TowerOneStep.Rung.T_S`), not a field that needs re-deriving; and
`qLevel`/`qLevelStar` are `coarseIso ∘ qCLM (trivialU Λ) 2` and its adjoint, whose every supporting
lemma is generic in `U`. §10 performs the construction: `qLevelCov`, `qLevelStarCov`,
`norm_qLevelCov`, `qLevelCov_hadj`, `qLevelStarCov_injective`, and `covariantRung` itself. The list
above therefore reads, after §10: **all six fields discharged at a covariant `Q`.** -/

/-- **`M` IS POSITIVE DEFINITE AT A CURVED LEVEL, WITH A COVARIANT `Q`.**
`CurvedTower.curvedLevel_fine_pos` with `hQnorm` read at `qCLM U 2` in place of
`qCLM (trivialU Λ) 2`,
and `a ≥ covB η / defA c` in place of `a ≥ defB / defA c`. -/
theorem covLevel_fine_pos {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {c rho sigma : ℝ} (lvl : CurvedLevel Λ c rho sigma) (hc : 0 ≤ c)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    {alpha : ℝ} (halpha0 : 0 ≤ alpha) (hsup : frobSupBond U ≤ alpha)
    {eta : ℝ} (heta : 0 < eta)
    {Dpi : BondFnL2 Λ →L[ℝ] BondFnL2 Λ} {delta : ℝ} (hpi : PiCorrectionBound Dpi delta)
    (hthr : defA c * delta < covKappa rho sigma alpha eta)
    {a : ℝ} (ha : covB eta / defA c ≤ a)
    (Q : BondFnL2 Λ →L[ℝ] K) (Qstar : K →L[ℝ] BondFnL2 Λ)
    (hadj : ∀ (x : BondFnL2 Λ) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hQnorm : ∀ x : BondFnL2 Λ, ‖Q x‖ = ‖qCLM U 2 x‖)
    (v : BondFnL2 Λ) (hv : v ≠ 0) :
    (0 : ℝ) < (inner ℝ v
      (fineCLM (piOp lvl.op Dpi) (pAxCLM (CoarseLattice Λ 2) 2) Q Qstar a v) : ℝ) := by
  rw [fineCLM_inner _ _ _ _ _ hadj v, hQnorm v]
  have hAc : 0 < defA c := defA_pos hc
  have haB : covB eta ≤ defA c * a := by
    rw [div_le_iff₀ hAc] at ha
    linarith [ha]
  set D : ℝ := (inner ℝ v (lvl.op v) : ℝ) with hD
  set P : ℝ := (inner ℝ v (pAxCLM (CoarseLattice Λ 2) 2 v) : ℝ) with hP
  set Z : ℝ := ‖qCLM U 2 v‖ ^ 2 with hZ
  have hZnn : (0 : ℝ) ≤ Z := sq_nonneg _
  have hvn : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
  have hdef : covKappa rho sigma alpha eta * ‖v‖ ^ 2 ≤ defA c * (D + P) + covB eta * Z :=
    covLevel_defect_bound lvl hdvd U halpha0 hsup heta v
  have hpiv : (inner ℝ v (Dpi v) : ℝ) ≤ delta * ‖v‖ ^ 2 := le_trans (le_abs_self _) (hpi v)
  by_contra hcon
  simp only [not_lt] at hcon
  have hsplit : (inner ℝ v (piOp lvl.op Dpi v) : ℝ) = D - (inner ℝ v (Dpi v) : ℝ) := by
    rw [piOp_apply, inner_sub_right]
  rw [hsplit] at hcon
  have hDP : D + P ≤ delta * ‖v‖ ^ 2 - a * Z := by nlinarith [hcon, hpiv]
  have hstep : covKappa rho sigma alpha eta * ‖v‖ ^ 2
      ≤ defA c * (delta * ‖v‖ ^ 2) + (covB eta - defA c * a) * Z := by
    nlinarith [hdef, hDP, hAc]
  have hneg : (covB eta - defA c * a) * Z ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hZnn
  nlinarith [hstep, hneg, hthr, hvn]

/-- **THE `a`-THRESHOLD OF §9 IS TWO-SIDED IN `η`.** `covB η / defA c` is the exact augmentation
weight `covLevel_fine_pos` needs; at `c = 2` and `η = 1` it is `2·13583253568/33162240`, strictly
larger than `CurvedTower`'s flat `defB / defA 2` — the covariant `Q` costs a heavier augmentation,
and by exactly the factor `(1+η)`. Recorded as an inequality so the claim is kernel-checked. -/
theorem covB_div_defA_gt_defB_div_defA :
    defB / defA 2 < covB 1 / defA 2 := by
  unfold defB covB defA
  norm_num

/-! ## §10 — THE COVARIANT RUNG

§9 said the `Rung` structure's own coarse-side data at a covariant `Q` was a separate construction.
It is a separate construction and it is performed here, in the same pass, because it is mechanical:
`TowerMilestone.qLevel` is `coarseIso ∘ qCLM (trivialU Λ) 2` and every lemma about it is generic in
`U` EXCEPT `qLevelStar_injective`, whose single non-generic input is
`BridgeInverseCarrier.qCLM_surjective_trivialU` — and `CurvedTower.qCLM_surjective_of_small`
replaces exactly that, at `32α < 1`.

So this section is not new mathematics on top of §6; it is §6's door plus the transport, and it
produces the object the campaign's `(γ−δ)/q²` machinery consumes: a `TowerOneStep.Rung` whose
averaging operator is the COVARIANT `Q₂(U)`.

⚠ **Read the scope.** `covariantRung`'s `hQstarInj` needs `32α < 1`; every coercivity constant in
§7 needs `α` some twelve decades smaller than that, so surjectivity is not what binds. What is NOT
here remains what `CurvedTower` §10 says: no blocking map `U ↦ Ū`, hence no tower at depth. -/

section CovariantRung

/-- **THE LEVEL-`Λ` COVARIANT AVERAGING.** `TowerMilestone.qLevel` with `Q₂(U)` in place of
`Q₂(1)`. -/
noncomputable def qLevelCov (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) :
    BondFnL2 Λ →L[ℝ] BondFnL2 (coarseExtent Λ 2) :=
  (coarseIso hdvd).toLinearIsometry.toContinuousLinearMap.comp (qCLM U 2)

/-- Its adjoint. -/
noncomputable def qLevelStarCov
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) :
    BondFnL2 (coarseExtent Λ 2) →L[ℝ] BondFnL2 Λ :=
  (qstarCLM U 2).comp (coarseIso hdvd).symm.toLinearIsometry.toContinuousLinearMap

@[simp] theorem qLevelCov_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) (x : BondFnL2 Λ) :
    qLevelCov U hdvd x = coarseIso hdvd (qCLM U 2 x) := rfl

@[simp] theorem qLevelStarCov_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) (B : BondFnL2 (coarseExtent Λ 2)) :
    qLevelStarCov U hdvd B = qstarCLM U 2 ((coarseIso hdvd).symm B) := rfl

/-- **THE BRIDGE TO §6's HYPOTHESIS.** The rung's coarse datum, read as a bond field on the coarse
lattice, IS the object §6's `VCurved` hypothesis is about — definitionally, so no conversion is
smuggled in. -/
theorem ofLp_qLevelCov (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) (x : BondFnL2 Λ) :
    WithLp.ofLp (qLevelCov U hdvd x)
      = pullS two_pos' hdvd (lineCoarseRestrictCov U 2 (WithLp.ofLp x)) := rfl

theorem norm_qLevelCov (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) (x : BondFnL2 Λ) :
    ‖qLevelCov U hdvd x‖ = ‖qCLM U 2 x‖ := by
  rw [qLevelCov_apply]
  exact (coarseIso hdvd).norm_map _

theorem qLevelCov_hadj (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (x : BondFnL2 Λ) (B : BondFnL2 (coarseExtent Λ 2)) :
    (inner ℝ (qLevelStarCov U hdvd B) x : ℝ) = (inner ℝ B (qLevelCov U hdvd x) : ℝ) := by
  rw [qLevelStarCov_apply, qLevelCov_apply, qCLM_hadj U 2 x ((coarseIso hdvd).symm B)]
  rw [show (inner ℝ B (coarseIso hdvd (qCLM U 2 x)) : ℝ)
      = (inner ℝ (coarseIso hdvd ((coarseIso hdvd).symm B))
          (coarseIso hdvd (qCLM U 2 x)) : ℝ) by
    rw [LinearIsometryEquiv.apply_symm_apply]]
  exact ((coarseIso hdvd).inner_map_map _ _).symm

/-- **THE FIELD `CurvedTower` §9 CALLED BLOCKED, AT THE LEVEL CARRIER.** `Q*` is injective at every
background with `32α < 1`; the only non-generic input of `TowerMilestone.qLevelStar_injective` was
`qCLM_surjective_trivialU`, and `CurvedTower.qCLM_surjective_of_small` replaces it. -/
theorem qLevelStarCov_injective (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    {alpha : ℝ} (halpha0 : 0 ≤ alpha) (hsup : frobSupBond U ≤ alpha) (hsmall : 32 * alpha < 1) :
    Function.Injective (qLevelStarCov U hdvd) := by
  intro B C h
  have h1 : qstarCLM U 2 ((coarseIso hdvd).symm B) = qstarCLM U 2 ((coarseIso hdvd).symm C) := h
  have h2 := qstar_injective_of_surjective (qCLM U 2) (qstarCLM U 2) (qCLM_hadj U 2)
    (qCLM_surjective_of_small hdvd U halpha0 hsup hsmall) h1
  exact (coarseIso hdvd).symm.injective h2

/-- **THE TAXED COVARIANT DOOR.** (3.120)'s correction is present and its two-sided bound `δ` is
paid exactly once. -/
theorem covariant_gf_pi_on_preimage {c rho sigma : ℝ} (lvl : CurvedLevel Λ c rho sigma)
    (hc : 0 ≤ c) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hdvd' : ∀ μ : Fin 3, (2 : ℕ) ∣ (coarseExtent Λ 2 μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    {alpha : ℝ} (halpha0 : 0 ≤ alpha) (hsupU : frobSupBond U ≤ alpha)
    (Ubar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (coarseExtent Λ 2))
    {abar : ℝ} (habar : 0 ≤ abar) (hsupbar : frobSupBond Ubar ≤ abar)
    {eps : ℝ} (heps : 0 < eps) (hgc : 0 < gammaCurved abar eps)
    {eta etaP : ℝ} (heta : 0 < eta) (hetaP : 0 < etaP)
    {Dpi : BondFnL2 Λ →L[ℝ] BondFnL2 Λ} {delta : ℝ} (hpi : PiCorrectionBound Dpi delta)
    (u : BondFnL2 Λ)
    (hu : VCurved (coarseExtent Λ 2) Ubar
      (pullS two_pos' hdvd (lineCoarseRestrictCov U 2 (WithLp.ofLp u)))) :
    (gammaCov c rho sigma alpha eta etaP (gammaCurved abar eps) - delta) * ‖u‖ ^ 2
      ≤ (inner ℝ u (piOp lvl.op Dpi u) : ℝ)
        + (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ) := by
  have hmain := covariant_gf_on_preimage lvl hc hdvd hdvd' U halpha0 hsupU Ubar habar hsupbar
    heps hgc heta hetaP u hu
  have hpiv : (inner ℝ u (Dpi u) : ℝ) ≤ delta * ‖u‖ ^ 2 := le_trans (le_abs_self _) (hpi u)
  have hsplit : (inner ℝ u (piOp lvl.op Dpi u) : ℝ)
      = (inner ℝ u (lvl.op u) : ℝ) - (inner ℝ u (Dpi u) : ℝ) := by
    rw [piOp_apply, inner_sub_right]
  rw [hsplit]
  nlinarith [hmain, hpiv]

/-- **THE COVARIANT RUNG.** `TowerOneStep.Rung` at the index operator `piOp lvl.op Dpi`, with the
averaging operator `Q₂(U)` — every field discharged, none at `trivialU`. -/
noncomputable def covariantRung {c rho sigma : ℝ} (lvl : CurvedLevel Λ c rho sigma) (hc : 0 ≤ c)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    {alpha : ℝ} (halpha0 : 0 ≤ alpha) (hsup : frobSupBond U ≤ alpha) (hsmall : 32 * alpha < 1)
    {eta : ℝ} (heta : 0 < eta)
    {Dpi : BondFnL2 Λ →L[ℝ] BondFnL2 Λ}
    (hDpiSym : ∀ u v : BondFnL2 Λ, (inner ℝ u (Dpi v) : ℝ) = (inner ℝ (Dpi u) v : ℝ))
    {delta : ℝ} (hpi : PiCorrectionBound Dpi delta)
    (hthr : defA c * delta < covKappa rho sigma alpha eta)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : covB eta / defA c ≤ a) :
    Rung (BondFnL2 Λ) (BondFnL2 (coarseExtent Λ 2)) (piOp lvl.op Dpi) where
  Q := qLevelCov U hdvd
  Qstar := qLevelStarCov U hdvd
  P := pAxCLM (CoarseLattice Λ 2) 2
  a := a
  q := ‖qCLM U 2‖
  hadj := qLevelCov_hadj U hdvd
  ha := ha0
  hq := qCLM_norm_pos (by norm_num) hdvd hwide _
  hQ := fun x => by
    rw [norm_qLevelCov U hdvd x]
    exact qCLM_le U 2 x
  hDsym := piOp_symm lvl.op Dpi lvl.hsym hDpiSym
  hPsym := pAxCLM_symm (CoarseLattice Λ 2) 2
  hPpos := pAxCLM_pos (CoarseLattice Λ 2) 2
  hinj := injective_of_pos_definite _
    (fun x hx => covLevel_fine_pos lvl hc hdvd U halpha0 hsup heta hpi hthr ha _ _
      (qLevelCov_hadj U hdvd) (norm_qLevelCov U hdvd) x hx)
  hMpos := fun x hx =>
    covLevel_fine_pos lvl hc hdvd U halpha0 hsup heta hpi hthr ha _ _
      (qLevelCov_hadj U hdvd) (norm_qLevelCov U hdvd) x hx
  hQstarInj := qLevelStarCov_injective hdvd U halpha0 hsup hsmall

/-- **THE FULLY COVARIANT ONE-STEP LAW.** The RG image of the curved level operator is
`((γ_cov − δ)/q²)`-coercive on the source's subspace at the coarse lattice — with the level operator
curved, the coarse gauge-fixing clause curved, `δ` real, AND the averaging operator that defines
both the rung and the coarse datum equal to the COVARIANT `Q₂(U)`. -/
theorem covariant_next_coercive_on_VCurved {c rho sigma : ℝ} (lvl : CurvedLevel Λ c rho sigma)
    (hc : 0 ≤ c) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1)
    (hdvd' : ∀ μ : Fin 3, (2 : ℕ) ∣ (coarseExtent Λ 2 μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    {alpha : ℝ} (halpha0 : 0 ≤ alpha) (hsup : frobSupBond U ≤ alpha) (hsmall : 32 * alpha < 1)
    (Ubar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (coarseExtent Λ 2))
    {abar : ℝ} (habar : 0 ≤ abar) (hsupbar : frobSupBond Ubar ≤ abar)
    {eps : ℝ} (heps : 0 < eps) (hgc : 0 < gammaCurved abar eps)
    {eta etaP : ℝ} (heta : 0 < eta) (hetaP : 0 < etaP)
    {Dpi : BondFnL2 Λ →L[ℝ] BondFnL2 Λ}
    (hDpiSym : ∀ u v : BondFnL2 Λ, (inner ℝ u (Dpi v) : ℝ) = (inner ℝ (Dpi u) v : ℝ))
    {delta : ℝ} (hpi : PiCorrectionBound Dpi delta)
    (hthr : defA c * delta < covKappa rho sigma alpha eta)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : covB eta / defA c ≤ a)
    (hpos : 0 < gammaCov c rho sigma alpha eta etaP (gammaCurved abar eps) - delta)
    {B : BondFnL2 (coarseExtent Λ 2)}
    (hB : VCurved (coarseExtent Λ 2) Ubar (WithLp.ofLp B)) :
    (gammaCov c rho sigma alpha eta etaP (gammaCurved abar eps) - delta)
        / ‖qCLM U 2‖ ^ 2 * ‖B‖ ^ 2
      ≤ (inner ℝ B ((covariantRung lvl hc hdvd hwide U halpha0 hsup hsmall heta hDpiSym hpi hthr
          ha0 ha).next B) : ℝ) := by
  refine next_coercive_gf_on_subspace
    (covariantRung lvl hc hdvd hwide U halpha0 hsup hsmall heta hDpiSym hpi hthr ha0 ha) hpos
    (fun C => VCurved (coarseExtent Λ 2) Ubar (WithLp.ofLp C)) ?_ hB
  intro C hC
  set r := covariantRung lvl hc hdvd hwide U halpha0 hsup hsmall heta hDpiSym hpi hthr ha0 ha
    with hr
  have hQ : qLevelCov U hdvd (r.G (r.Qstar (r.S C))) = C := r.T_S C
  refine covariant_gf_pi_on_preimage lvl hc hdvd hdvd' U halpha0 hsup Ubar habar hsupbar heps hgc
    heta hetaP hpi (r.G (r.Qstar (r.S C))) ?_
  show VCurved (coarseExtent Λ 2) Ubar
    (WithLp.ofLp (qLevelCov U hdvd (r.G (r.Qstar (r.S C)))))
  rw [hQ]
  exact hC

end CovariantRung

/-! ## §11 — NONVACUITY WITNESSES, PER HEADLINE `∀`-STATEMENT

An `∃`-detector cannot see an EMPTY HYPOTHESIS DOMAIN, and a `∀`-statement over an empty domain is
true and worthless. Each theorem below exhibits, at the SAME curved lattice `cwL`/`cwU`/`cwUbar` the
must-fire section uses, a point of the hypothesis domain of one of §3–§6's headline
`∀`-statements at which the statement is NOT trivial — the quantity being bounded is strictly
positive there. -/

section Nonvacuity

open AdalyFormal.Balaban.BridgeRestricted (rotGen rotGen_ne_zero)
open AdalyFormal.Balaban.VRestrictedRoute (vWitFine vWitCoarse_ne_zero pullC_vWitCoarse
  witness_coarseCurl_pos)
open AdalyFormal.Balaban.CurvedTower (cwL cwT cwU cwUbar cwF cwL_dvd4 cwL_dvd2 cwL_coarse_dvd2
  cwL_wide cwU_frobSup cwUbar_frobSup)

/-- **`master_defect_bound_covariantQ` IS NOT VACUOUS.** Its leading coefficient `1 − covTax α η` is
strictly positive at the must-fire parameters, so the bound it asserts is a bound on a strictly
positive multiple of `bondEnergy A` — not on `0`. -/
theorem master_bound_leading_coefficient_pos :
    0 < 1 - covTax (1 / 10 ^ 20) (1 / 10 ^ 12) := by
  unfold covTax
  norm_num

/-- **`covLevel_defect_bound` IS NOT VACUOUS AT THE LATTICE LEVEL.** `covKappa` at the lattice's own
`(ρ,σ)` and the must-fire `(α,η)` is strictly positive. -/
theorem covKappa_lattice_pos :
    0 < covKappa (driftRemainder (1 / 10 ^ 20)) (272 * (1 / 10 ^ 20)) (1 / 10 ^ 20)
      (1 / 10 ^ 12) := by
  unfold covKappa defKappa covTax AdalyFormal.Balaban.ComposedCoercivity.driftRemainder
  norm_num

/-- **`coarseCurlEnergy_cov_le` IS NOT VACUOUS.** Its left-hand side is strictly positive at a field
whose covariant coarse datum is `cwF`: `VRestrictedRoute` proves `coarseCurlEnergy cwF > 0`. So §5
is not a bound on `0 ≤ …`. -/
theorem coarseCurl_cov_lhs_pos_witness :
    ∃ A : Bond cwL → SuTwo,
      lineCoarseRestrictCov cwU 2 A = cwF
      ∧ 0 < coarseCurlEnergy cwL_dvd2 (lineCoarseRestrictCov cwU 2 A)
      ∧ coarseCurlEnergy cwL_dvd2 (lineCoarseRestrictCov cwU 2 A)
        ≤ (1 + (1 : ℝ)) * (1 / 2 * curlEnergy A)
          + (1 + 1 / (1 : ℝ)) * (1024 * (1 / 10 ^ 20 : ℝ) ^ 2 * bondEnergy A) := by
  obtain ⟨x, hx⟩ := qCLM_cwU_surjective (WithLp.toLp 2 cwF)
  have hdatum : lineCoarseRestrictCov cwU 2 (WithLp.ofLp x) = cwF :=
    congrArg (fun z : CoarseFnL2 cwL 2 => WithLp.ofLp z) hx
  refine ⟨WithLp.ofLp x, hdatum, ?_, ?_⟩
  · rw [hdatum]
    exact witness_coarseCurl_pos cwL_dvd4 rotGen_ne_zero
  · exact coarseCurlEnergy_cov_le cwL_dvd2 cwU (by norm_num) cwU_frobSup (by norm_num)
      (WithLp.ofLp x)

/-- **`covLevel_fine_pos` IS NOT VACUOUS: its abstract `Q` IS INHABITED by the covariant `Q₂(U)`.**
The hypothesis `∀x, ‖Qx‖ = ‖qCLM U 2 x‖` is what makes that theorem usable at a covariant averaging
rather than at the flat one; here it is discharged at `Q = qLevelCov`, `Q* = qLevelStarCov`, at the
curved background `cwU`, with all three thresholds satisfied. -/
theorem covLevel_fine_pos_inhabited (v : BondFnL2 cwL) (hv : v ≠ 0) :
    (0 : ℝ) < (inner ℝ v
      (fineCLM (piOp (deltaKCLMNormalized cwU)
          (AdalyFormal.Balaban.DeltaPrimeOperator.deltaPrimeCLMNormalized cwU))
        (pAxCLM (CoarseLattice cwL 2) 2) (qLevelCov cwU cwL_dvd2) (qLevelStarCov cwU cwL_dvd2)
        (covB (1 / 10 ^ 12) / defA 2) v) : ℝ) := by
  refine covLevel_fine_pos (curvedBaseLevel (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 20) cwU cwU_frobSup)
    (by norm_num) cwL_dvd2 cwU (by norm_num) cwU_frobSup (by norm_num : (0:ℝ) < 1 / 10 ^ 12)
    (AdalyFormal.Balaban.CurvedTower.piCorrectionBound_deltaPrimeNormalized
      (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 20) cwU cwU_frobSup) ?_ le_rfl _ _
    (qLevelCov_hadj cwU cwL_dvd2) (norm_qLevelCov cwU cwL_dvd2) v hv
  unfold covKappa defKappa covTax defA AdalyFormal.Balaban.ComposedCoercivity.driftRemainder
  norm_num

/-- **THE COVARIANT RUNG IS INHABITED AT A CURVED BACKGROUND.** Every field of `covariantRung` is
discharged at `cwU` — including `hQstarInj`, which needed `32α < 1` and gets it twenty decades over.
The `Prop`-level content is that the structure exists; the term is the witness. -/
noncomputable def cwCovariantRung :
    Rung (BondFnL2 cwL) (BondFnL2 (coarseExtent cwL 2))
      (piOp (deltaKCLMNormalized cwU)
        (AdalyFormal.Balaban.DeltaPrimeOperator.deltaPrimeCLMNormalized cwU)) :=
  covariantRung (curvedBaseLevel (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 20) cwU cwU_frobSup)
    (by norm_num) cwL_dvd2 cwL_wide cwU (by norm_num) cwU_frobSup (by norm_num)
    (by norm_num : (0:ℝ) < 1 / 10 ^ 12)
    (AdalyFormal.Balaban.CurvedTower.deltaPrimeCLMNormalized_sym cwU)
    (AdalyFormal.Balaban.CurvedTower.piCorrectionBound_deltaPrimeNormalized
      (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 20) cwU cwU_frobSup)
    (by
      unfold covKappa defKappa covTax defA AdalyFormal.Balaban.ComposedCoercivity.driftRemainder
      norm_num)
    (a := covB (1 / 10 ^ 12) / defA 2) (by unfold covB defA; norm_num) le_rfl

/-- The rung's averaging operator IS the covariant one — recorded as a kernel-checked equation so
"`Q` is curved" is not a docstring claim. Contrast `CurvedTower.curvedRung`, whose `Q` is
`qLevel hdvd = coarseIso ∘ qCLM (trivialU cwL) 2`. -/
theorem cwCovariantRung_Q : cwCovariantRung.Q = qLevelCov cwU cwL_dvd2 := rfl

/-- What this proves, EXACTLY: the rung's `Q` is the covariant averaging (by `rfl`) AND its
pointwise action is the covariant line-restriction formula — a DENOTATION PIN (two equalities),
not a separation. (Second-family gate correction, 2026-08-01: an earlier wording here called this
"the disjunction it honestly is"; the declaration is a conjunction and separates nothing. The
flat-vs-covariant SEPARATION lives in `witnessL`/`witnessU` on their own lattice — see §0's
disclaimer on the lattice split.) The name's `_ne_flat_or_data` suffix is historical and
overstates the content; it is retained so the registry row and `#print` anchors stay stable, with
this docstring as the correction of record. -/
theorem cwCovariantRung_Q_ne_flat_or_data :
    cwCovariantRung.Q = qLevelCov cwU cwL_dvd2
      ∧ ∀ x : BondFnL2 cwL, WithLp.ofLp (cwCovariantRung.Q x)
          = pullS two_pos' cwL_dvd2 (lineCoarseRestrictCov cwU 2 (WithLp.ofLp x)) :=
  ⟨rfl, fun x => ofLp_qLevelCov cwU cwL_dvd2 x⟩

/-- The `(γ_cov − δ)` threshold of the covariant ONE-STEP LAW, at the must-fire parameters and the
lattice's own `δ = 272α₀`. -/
theorem cw_cov_pi_threshold :
    0 < gammaCovLattice (1 / 10 ^ 20) (1 / 10 ^ 20) 1 (1 / 10 ^ 12) (1 / 10 ^ 12)
      - 272 * (1 / 10 ^ 20 : ℝ) := by
  unfold gammaCovLattice gammaCov covNum covDen covKappa defKappa covTax covB defA
    AdalyFormal.Balaban.ComposedCoercivity.driftRemainder
    AdalyFormal.Balaban.CovariantFibreTransfer.gammaCurved
  norm_num

/-- **MUST-NOT-FIRE ON THE ONE-STEP LAW.** One decade coarser the taxed constant is nonpositive. -/
theorem cw_cov_pi_threshold_fails_at_1e_neg_19 :
    gammaCovLattice (1 / 10 ^ 19) (1 / 10 ^ 20) 1 (1 / 10 ^ 12) (1 / 10 ^ 12)
      - 272 * (1 / 10 ^ 19 : ℝ) ≤ 0 := by
  have h := gammaCovLattice_nonpos_at_1e_neg_19
  have h2 : (0 : ℝ) < 272 * (1 / 10 ^ 19 : ℝ) := by norm_num
  linarith

/-- **MUST-FIRE ON THE COVARIANT ONE-STEP LAW.** At the curved coarse background `cwUbar`, the
source's own nonzero coarse-lattice field lies in `VCurved`, the taxed constant is strictly
positive, and `covariant_next_coercive_on_VCurved` fires at `cwCovariantRung` with a strictly
positive left-hand side — so `⟨B, Δ_{k+1} B⟩` is strictly positive there. -/
theorem covariant_next_must_fire :
    VCurved (coarseExtent cwL 2) cwUbar
        (WithLp.ofLp (WithLp.toLp 2 (vWitFine (Lc := coarseExtent cwL 2) rotGen)))
      ∧ (WithLp.toLp 2 (vWitFine (Lc := coarseExtent cwL 2) rotGen) :
          BondFnL2 (coarseExtent cwL 2)) ≠ 0
      ∧ 0 < (gammaCovLattice (1 / 10 ^ 20) (1 / 10 ^ 20) 1 (1 / 10 ^ 12) (1 / 10 ^ 12)
              - 272 * (1 / 10 ^ 20 : ℝ)) / ‖qCLM cwU 2‖ ^ 2
            * ‖(WithLp.toLp 2 (vWitFine (Lc := coarseExtent cwL 2) rotGen) :
                BondFnL2 (coarseExtent cwL 2))‖ ^ 2
      ∧ 0 < (inner ℝ (WithLp.toLp 2 (vWitFine (Lc := coarseExtent cwL 2) rotGen) :
              BondFnL2 (coarseExtent cwL 2))
            (cwCovariantRung.next
              (WithLp.toLp 2 (vWitFine (Lc := coarseExtent cwL 2) rotGen))) : ℝ)
      ∧ (gammaCovLattice (1 / 10 ^ 20) (1 / 10 ^ 20) 1 (1 / 10 ^ 12) (1 / 10 ^ 12)
              - 272 * (1 / 10 ^ 20 : ℝ)) / ‖qCLM cwU 2‖ ^ 2
            * ‖(WithLp.toLp 2 (vWitFine (Lc := coarseExtent cwL 2) rotGen) :
                BondFnL2 (coarseExtent cwL 2))‖ ^ 2
          ≤ (inner ℝ (WithLp.toLp 2 (vWitFine (Lc := coarseExtent cwL 2) rotGen) :
              BondFnL2 (coarseExtent cwL 2))
            (cwCovariantRung.next
              (WithLp.toLp 2 (vWitFine (Lc := coarseExtent cwL 2) rotGen))) : ℝ) := by
  have hmem : VCurved (coarseExtent cwL 2) cwUbar (vWitFine (Lc := coarseExtent cwL 2) rotGen) :=
    AdalyFormal.Balaban.CurvedTower.vWitFine_mem_VCurved cwL_coarse_dvd2 cwUbar
      (fun b => AdalyFormal.Balaban.CurvedTower.bondRot_fix_rotGen _ cwT b)
  have hfne : vWitFine (Lc := coarseExtent cwL 2) rotGen ≠ 0 :=
    AdalyFormal.Balaban.CurvedTower.vWitFine_rotGen_ne_zero (by decide)
  have hBne : (WithLp.toLp 2 (vWitFine (Lc := coarseExtent cwL 2) rotGen) :
      BondFnL2 (coarseExtent cwL 2)) ≠ 0 := by
    intro h
    exact hfne (congrArg (fun z : BondFnL2 (coarseExtent cwL 2) => WithLp.ofLp z) h)
  have hqn : 0 < ‖qCLM cwU 2‖ := qCLM_norm_pos (by norm_num) cwL_dvd2 cwL_wide cwU
  have hBn : (0 : ℝ) < ‖(WithLp.toLp 2 (vWitFine (Lc := coarseExtent cwL 2) rotGen) :
      BondFnL2 (coarseExtent cwL 2))‖ ^ 2 := pow_pos (norm_pos_iff.2 hBne) 2
  have hgcc : 0 < gammaCurved (1 / 10 ^ 20 : ℝ) 1 := by
    rw [gammaCurved_pos_iff]; norm_num
  have hlhs : (0 : ℝ)
      < (gammaCovLattice (1 / 10 ^ 20) (1 / 10 ^ 20) 1 (1 / 10 ^ 12) (1 / 10 ^ 12)
          - 272 * (1 / 10 ^ 20 : ℝ)) / ‖qCLM cwU 2‖ ^ 2
        * ‖(WithLp.toLp 2 (vWitFine (Lc := coarseExtent cwL 2) rotGen) :
            BondFnL2 (coarseExtent cwL 2))‖ ^ 2 :=
    mul_pos (div_pos cw_cov_pi_threshold (pow_pos hqn 2)) hBn
  have hmain := covariant_next_coercive_on_VCurved
    (curvedBaseLevel (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 20) cwU cwU_frobSup)
    (by norm_num) cwL_dvd2 cwL_wide cwL_coarse_dvd2 cwU (by norm_num) cwU_frobSup (by norm_num)
    cwUbar (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 20) cwUbar_frobSup (by norm_num : (0:ℝ) < 1) hgcc
    (by norm_num : (0:ℝ) < 1 / 10 ^ 12) (by norm_num : (0:ℝ) < 1 / 10 ^ 12)
    (AdalyFormal.Balaban.CurvedTower.deltaPrimeCLMNormalized_sym cwU)
    (AdalyFormal.Balaban.CurvedTower.piCorrectionBound_deltaPrimeNormalized
      (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 20) cwU cwU_frobSup)
    (by
      unfold covKappa defKappa covTax defA AdalyFormal.Balaban.ComposedCoercivity.driftRemainder
      norm_num)
    (a := covB (1 / 10 ^ 12) / defA 2) (by unfold covB defA; norm_num) le_rfl cw_cov_pi_threshold
    (B := WithLp.toLp 2 (vWitFine (Lc := coarseExtent cwL 2) rotGen)) hmem
  exact ⟨hmem, hBne, hlhs, lt_of_lt_of_le hlhs hmain, hmain⟩

/-! ### §11b — THIS DOOR IS NOT THE FLAT DOOR: the two hypotheses are different statements

The whole content of this module is that `coercive_on_VSrc_covariantQ`'s hypothesis reads the coarse
datum at `Q₂(U)` where `CurvedTower.coercive_on_VSrc_curved`'s reads it at `Q₂(1)`. If those two
operators coincided, the module would be a re-spelling. They do not, and the tree already proves it:
`LineIntegralCovariant.lineCoarseRestrictCov_genuinely_U_dependent` exhibits a field and a coarse
bond at which the two averages take values `(1/8)·w` and `−(1/8)·w`. REUSED, not rebuilt (LAW-19).

**Exact scope, stated rather than blurred.** The separation is proved at `witnessU` on `witnessL`,
NOT at this module's own `cwU` on `cwL`. At `cwU` — a single `rotElem 10⁻²¹` bond — this module does
not prove the two averages differ, and it does not need to: the door quantifies over `U`, so a
single background at which `Q₂(U) ≠ Q₂(1)` already makes the covariant hypothesis a different
predicate from the flat one. A prosecutor should read the `cwU` must-fire as inhabitation of the
COVARIANT statement, and this section as the proof that the covariant statement is not the flat one
in disguise; the two jobs are separate and neither is doing the other's work. -/

/-- **THE COVARIANT AVERAGE IS NOT THE FLAT AVERAGE**, on the carriers. There is a lattice, a
background and an `ℓ²` field at which `Q₂(U)x ≠ Q₂(1)x`. -/
theorem qCLM_cov_ne_qCLM_flat :
    ∃ (Lw : PeriodicLatticeExtent)
      (Uw : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Lw)
      (x : BondFnL2 Lw), qCLM Uw 2 x ≠ qCLM (trivialU Lw) 2 x := by
  refine ⟨AdalyFormal.Balaban.AdmissibleSubspace.witnessL,
    AdalyFormal.Balaban.CovariantOperators.witnessU,
    WithLp.toLp 2 AdalyFormal.Balaban.Q1Real.d4ConfigSuTwo, ?_⟩
  intro h
  refine AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov_genuinely_U_dependent ?_
  have h' : lineCoarseRestrictCov AdalyFormal.Balaban.CovariantOperators.witnessU 2
        AdalyFormal.Balaban.Q1Real.d4ConfigSuTwo
      = lineCoarseRestrictCov (trivialU AdalyFormal.Balaban.AdmissibleSubspace.witnessL) 2
        AdalyFormal.Balaban.Q1Real.d4ConfigSuTwo :=
    congrArg (fun z : CoarseFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL 2 =>
      WithLp.ofLp z) h
  exact (congrFun h' AdalyFormal.Balaban.QOne.targetCoarseBond).symm

end Nonvacuity

/-! ## §12 — AXIOM AUDIT -/

#print axioms two_mul_le_young
#print axioms norm_sq_young
#print axioms coarseEnergy_young
#print axioms curlEnergy_young
#print axioms coarseEnergy_sub_comm
#print axioms cEnergy_eq_coarseEnergy
#print axioms covB
#print axioms covTax
#print axioms covTax_coefficient_factors
#print axioms covB_pos
#print axioms covB_nonneg
#print axioms covTax_nonneg
#print axioms covTax_at_zero
#print axioms covB_at_zero
#print axioms covKappa
#print axioms covKappa_at_zero
#print axioms coarseEnergy_flat_le_cov
#print axioms master_defect_bound_covariantQ
#print axioms norm_sq_qCLM_cov
#print axioms covLevel_defect_bound
#print axioms coarseCurlEnergy_cov_le
#print axioms covNum
#print axioms covDen
#print axioms gammaCov
#print axioms covDen_pos
#print axioms covariant_gf_on_preimage
#print axioms gammaCovLattice
#print axioms coercive_on_VSrc_covariantQ
#print axioms gammaCov_flat_eq
#print axioms gammaCov_flat_recovers_gammaV
#print axioms covKappa_two_sided
#print axioms gammaCov_two_sided_in_alpha
#print axioms gammaCovLattice_pos_at_1e_neg_20
#print axioms gammaCovLattice_nonpos_at_1e_neg_19
#print axioms qCLM_cwU_surjective
#print axioms cw_cov_threshold
#print axioms covariant_door_must_fire
#print axioms covLevel_fine_pos
#print axioms covB_div_defA_gt_defB_div_defA
#print axioms qLevelCov
#print axioms qLevelStarCov
#print axioms qLevelCov_apply
#print axioms qLevelStarCov_apply
#print axioms ofLp_qLevelCov
#print axioms norm_qLevelCov
#print axioms qLevelCov_hadj
#print axioms qLevelStarCov_injective
#print axioms covariant_gf_pi_on_preimage
#print axioms covariantRung
#print axioms covariant_next_coercive_on_VCurved
#print axioms master_bound_leading_coefficient_pos
#print axioms covKappa_lattice_pos
#print axioms coarseCurl_cov_lhs_pos_witness
#print axioms covLevel_fine_pos_inhabited
#print axioms cwCovariantRung
#print axioms cwCovariantRung_Q
#print axioms cwCovariantRung_Q_ne_flat_or_data
#print axioms cw_cov_pi_threshold
#print axioms cw_cov_pi_threshold_fails_at_1e_neg_19
#print axioms covariant_next_must_fire
#print axioms qCLM_cov_ne_qCLM_flat

end AdalyFormal.Balaban.CovariantDoor
