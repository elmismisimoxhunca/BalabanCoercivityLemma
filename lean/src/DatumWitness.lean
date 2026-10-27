/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import HrawFeed
import CurvedContent

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.style.longLine false

/-!
# `DatumWitness.lean` — TERMINAL POSITIVITY AT A DATUM WHOSE `Q` HAS A KERNEL

Lane `compute/datum_witness/`.  Write scope: that directory only.  Never `lake build`.

## THE DEGENERACY THIS ADDRESSES, QUOTED

`compute/curved_witness/content/stage/CurvedContent.lean` §8c, verbatim:

> **In particular this lane does NOT remove the datum-level degeneracy.**  `TerminalAssembly`
> §9d proves that at its `assemblyDatum` the Schur complement collapses (`Q = I`,
> `assemblyDatum_Q_bijective`) and the composed floor IS the brick
> (`assemblyDatum_deltaKQuadForm_eq_curl_energy`), so §8's instantiation inherits that.  Of the two
> degeneracies `end_to_end_flat` discloses, this lane removes the SECOND (the vanishing source) and
> leaves the FIRST (`Q = I`) exactly where it was.

## WHAT IS ASSEMBLED HERE, AND FROM WHAT

Two lanes already hold the two halves and neither holds both:

* `compute/hraw_carriers/` built `feedDatum`, a covariance datum on the pair of carriers
  `BondFnL2 L → BondFnL2 L'` (fine → coarse) whose `Q` is a block average with a kernel, and
  applied `terminal_wired_posDef` at it — but with **every source-side binder still hypothetical**
  (`terminal_at_composed_carriers`: `Qext`, `T`, `S`, `hS`, `c₂`, `hD2`, `δ`, `LinkDev`, `hδ`,
  `hH1`, `hT`, `hcard`, `w`, `hw` are all carried).
* `compute/curved_witness/content/` built `spikeU (torus t)`, a background that is curved, whose
  source `J(U*)` is nonzero, and which lies in BOTH smallness classes at one and the same `t` — but
  ran it only at `assemblyDatum`, i.e. at `H = K`, `Q = I`.

This module composes them: the source side is discharged AT `feedDatum`, at the curved
source-bearing `spikeU (torus t)`, with **no hypothesis about the datum left standing** beyond the
two free parameters `ε > 0` (the regulator `feedDatum` carries) and `bc` (the printed constant `a`).

**Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.**

## §0's POINT, STATED ONCE

`DeltaKWiring.collapsed_Q_bijective` shows `Q` is bijective at EVERY datum with `H = K`.  §0 turns
that into the statement that actually matters for the Schur complement: at every such datum the
constraint set `{A : QA = B}` is a SINGLETON, so `⟨B,(QG₁Q*)⁻¹B⟩` is a minimum over one point.  That
is a theorem about the whole class `BalabanCovarianceData (BondFnL2 M) (BondFnL2 M)` — which is
exactly the type of the datum quantified over in `CurvedContent.terminal_posDef_at_spike_any_datum`.
So the "arbitrary datum" of that theorem is arbitrary INSIDE the collapse; §1-§4 leave the class.
-/

namespace AdalyFormal.DatumWitness

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL)
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator
  solutionOperator_apply interpolates isMinimal isMinimal_unique)
open AdalyFormal.HrawCarriers (ScaleQuotient composedQ composedQ_not_injective
  feedDatum feedDatum_Q feedDatum_Ginv feedGinv_posDef terminal_at_composed_carriers)
open AdalyFormal.Balaban.CurvedContent (spikeU spikeK spikeK_pos witnessL_strict witnessL_dvd
  norm_JsuTwo_spike_le norm_JsuTwo_spike_pos JsuTwo_spike_ne_zero spike_is_curved
  frobSupBond_spike_le linkDev_spike_torus spike_at_zero_is_flat)
open AdalyFormal.Balaban.SuTwoLogExp (torus)
open AdalyFormal.Balaban.DeltaKWiring (cdcFormTrue bondQext bondDtilde2 sourceTerm IsSourceOperator
  Qstar_injective norm_cZero_pos)
open AdalyFormal.Balaban.SourceWiredJ (JsuTwo)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.TerminalAssembly (assemblyDatum_hD2 sharpFloorConst)
open AdalyFormal.Balaban.TerminalCompose (gammaBrick gammaBrick_pos)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.MechEdges.G16 (rawSigmaZero)

/-! ## §0 — WHY A NEW PAIR OF CARRIERS IS FORCED

Everything in §0 is about an ARBITRARY datum; nothing about `feedDatum` or the spike is used. -/

section Collapse

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- **AN INJECTIVE `Q` MAKES THE CONSTRAINT SET A SINGLETON.**  `⟨B,(QG₁Q*)⁻¹B⟩` is
`min{⟨A,G₁⁻¹A⟩ : QA = B}`; if `Q` is injective the minimum is over ONE point, so the Schur
complement carries no variational content.  Proved from `interpolates` alone. -/
theorem fiber_singleton_of_Q_injective (D : BalabanCovarianceData H K)
    (hinj : Function.Injective D.Q) (B : K) (A : H) (hA : D.Q A = B) :
    A = solutionOperator D B :=
  hinj (by rw [hA, interpolates D B])

/-- **THE COLLAPSE IS FORCED ON EQUAL CARRIERS.**  At `H = K = BondFnL2 M` — the type of the datum
quantified over in `CurvedContent.terminal_posDef_at_spike_any_datum`, and the type of
`TerminalAssembly.assemblyDatum` and `DeltaKWiring.bondData` — the constraint set is a singleton for
EVERY datum and every `B`.  So no choice of datum on those carriers can exercise the Schur
mechanism: `DeltaKWiring.collapsed_Q_bijective` (REUSED) supplies the injectivity. -/
theorem equal_carrier_fiber_singleton {M : PeriodicLatticeExtent}
    (D : BalabanCovarianceData (BondFnL2 M) (BondFnL2 M)) (B A : BondFnL2 M)
    (hA : D.Q A = B) : A = solutionOperator D B :=
  fiber_singleton_of_Q_injective D
    (AdalyFormal.Balaban.DeltaKWiring.collapsed_Q_bijective D).1 B A hA

/-- A continuous linear map that is not injective has a nonzero kernel vector. -/
theorem exists_kernel_vector_of_not_injective (f : H →L[ℝ] K) (hf : ¬ Function.Injective f) :
    ∃ x : H, x ≠ 0 ∧ f x = 0 := by
  by_contra hc
  push_neg at hc
  refine hf (fun a b hab => ?_)
  by_contra hne
  exact hc (a - b) (sub_ne_zero.mpr hne) (by rw [map_sub, hab, sub_self])

/-- **THE MINIMISATION IS OVER MORE THAN A POINT, AND THE MINIMISER STRICTLY BEATS.**  Given one
nonzero kernel vector `k` of `Q` and positive definiteness of `G₁⁻¹`, for EVERY `B` the competitor
`H₁B + k` satisfies the constraint, differs from `H₁B`, and has STRICTLY larger energy.  This is the
exact negation of `fiber_singleton_of_Q_injective`'s conclusion, proved through the tree's own
`isMinimal` / `isMinimal_unique` (REUSED, LAW-19). -/
theorem minimiser_strictly_beats (D : BalabanCovarianceData H K)
    (hpd : ∀ x : H, (inner ℝ x (D.Ginv x) : ℝ) = 0 → x = 0)
    (k : H) (hk : k ≠ 0) (hQk : D.Q k = 0) (B : K) :
    D.Q (solutionOperator D B + k) = B
    ∧ solutionOperator D B + k ≠ solutionOperator D B
    ∧ (inner ℝ (solutionOperator D B) (D.Ginv (solutionOperator D B)) : ℝ)
        < inner ℝ (solutionOperator D B + k) (D.Ginv (solutionOperator D B + k)) := by
  have hQA : D.Q (solutionOperator D B + k) = B := by
    rw [map_add, hQk, add_zero, interpolates D B]
  have hne : solutionOperator D B + k ≠ solutionOperator D B := by
    intro h
    exact hk (by simpa using h)
  refine ⟨hQA, hne, lt_of_le_of_ne (isMinimal D B _ hQA) ?_⟩
  intro heq
  exact hne (isMinimal_unique D hpd B _ hQA heq.symm)

/-- `‖H₁‖ > 0` whenever the coarse carrier has a nonzero vector — from `interpolates`, at any
datum. -/
theorem norm_solutionOperator_pos (D : BalabanCovarianceData H K) (y : K) (hy : y ≠ 0) :
    0 < ‖solutionOperator D‖ := by
  rcases (norm_nonneg (solutionOperator D)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz : solutionOperator D = 0 := by
      rw [← ContinuousLinearMap.opNorm_zero_iff]
      exact h.symm
    have hint := interpolates D y
    rw [hz] at hint
    simp only [ContinuousLinearMap.zero_apply, map_zero] at hint
    exact hy hint.symm

/-- `‖Q*‖ > 0` whenever the coarse carrier has a nonzero vector — `Q*` is injective at every datum
(`DeltaKWiring.Qstar_injective`, REUSED). -/
theorem norm_Qstar_pos (D : BalabanCovarianceData H K) (y : K) (hy : y ≠ 0) :
    0 < ‖D.Qstar‖ := by
  rcases (norm_nonneg D.Qstar).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz : D.Qstar = 0 := by
      rw [← ContinuousLinearMap.opNorm_zero_iff]
      exact h.symm
    refine hy (Qstar_injective D ?_)
    rw [hz]
    simp

end Collapse

/-! ## §1 — THE SOURCE, CARRIED INTO THE `A`-SPACE BY `Q*`, AT AN ARBITRARY DATUM

`terminal_wired_posDef`'s `J`-slot is `T (JsuTwo U)` for a bounded `T : Ks →L[ℝ] Hs`.  At the
collapsed carriers `TerminalAssembly` takes `T = I`, which is available only because `Hs = Ks`.  At
a genuine pair of carriers a map must be named.  `Q*` is the canonical one: it is a field of the
structure, it is injective at every datum, and — this is the point — the source term it produces is
computable in closed form from the INTERPOLATION IDENTITY `Q(H₁B) = B`, with no knowledge of `H₁`.

Every declaration in §1 is at an arbitrary `BalabanCovarianceData H (BondFnL2 L)`. -/

section SourceViaQstar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {L : PeriodicLatticeExtent}

/-- **THE SOURCE TERM AT `J = Q*v`, IN CLOSED FORM, AT EVERY DATUM.**

    ⟨H₁D̃⁽²⁾(B), Q*v⟩  =  ‖B‖²·⟨Q(H₁v), v⟩  =  ‖B‖²·‖v‖² .

The middle step is `Q_Qstar_adjoint`, the last is `interpolates`.  Note what is NOT used: nothing
about `H₁` itself, and in particular not `H₁ = I`. -/
theorem sourceTerm_Qstar_eq (D : BalabanCovarianceData H (BondFnL2 L)) (v B : BondFnL2 L) :
    sourceTerm D (bondQext v) (D.Qstar v) B = ‖B‖ ^ 2 * ‖v‖ ^ 2 := by
  show (inner ℝ (solutionOperator D (Dtilde2Shape (bondQext v) B)) (D.Qstar v) : ℝ) = _
  rw [bondDtilde2, map_smul, real_inner_smul_left, ← D.Q_Qstar_adjoint, interpolates D v,
    real_inner_self_eq_norm_sq]

/-- **THE NAMED RESIDUAL `IsSourceOperator` IS DISCHARGED AT EVERY DATUM, WITH `J = Q*v`**, by the
scalar operator `‖v‖²·I`.  Generalises `TerminalAssembly.assemblyDatum_isSourceOperator`, whose
proof goes through `H₁ = I`. -/
theorem isSourceOperator_Qstar (D : BalabanCovarianceData H (BondFnL2 L)) (v : BondFnL2 L) :
    IsSourceOperator D (bondQext v) (D.Qstar v)
      ((‖v‖ ^ 2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L)) := by
  intro B
  rw [sourceTerm_Qstar_eq D v B]
  show (inner ℝ B ((‖v‖ ^ 2 : ℝ) • B) : ℝ) = _
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

/-- **AND IT IS STRICTLY POSITIVE**, hence its contribution `−2·sourceTerm` to `cdcFormTrue`
(`DeltaKWiring.deltaKForm_split`) is strictly negative: the source actively opposes the floor. -/
theorem sourceTerm_Qstar_pos (D : BalabanCovarianceData H (BondFnL2 L)) (v B : BondFnL2 L)
    (hv : v ≠ 0) (hB : B ≠ 0) :
    0 < sourceTerm D (bondQext v) (D.Qstar v) B := by
  rw [sourceTerm_Qstar_eq D v B]
  have h1 : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have h2 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  positivity

/-- `J = Q*v ≠ 0` for `v ≠ 0` — so the `J`-slot really is filled with a nonzero vector of the
`A`-space. -/
theorem Qstar_source_ne_zero (D : BalabanCovarianceData H (BondFnL2 L)) (v : BondFnL2 L)
    (hv : v ≠ 0) : D.Qstar v ≠ 0 := by
  intro h
  exact hv (Qstar_injective D (by rw [h, map_zero]))

end SourceViaQstar

/-! ## §2 — THE DATUM `D*`: THE FINE TORUS OF SIDE `8` OVER THE CURVED WITNESS'S `4³` TORUS

`CurvedContent`'s spike lives on `witnessL = fun _ => 3` (side `4`), at compression scale `ell₀ = 2`.
The `A`-space is one RG step FINER: `fineL = fun _ => 7` (side `8`), with `ScaleQuotient fineL 2
witnessL` — `2·(3+1) = 7+1`.  `feedDatum` (REUSED from `compute/hraw_carriers/`) is then a datum on
`BondFnL2 fineL → BondFnL2 witnessL` whose `Q` is the block average at scale `2` followed by the
extent identification.

Two scale parameters coincide numerically here and are NOT the same parameter: `ell = 2` is the RG
step `fineL → witnessL`, `ell₀ = 2` is the compression scale on `witnessL` that `cdcFormTrue` uses.
Nothing below forces them equal; they are supplied separately to
`terminal_at_composed_carriers`. -/

/-- The fine torus: side `8`. -/
def fineL : PeriodicLatticeExtent := fun _ => 7

/-- `2·(witnessL μ + 1) = fineL μ + 1` for every direction — the scale relation, by computation. -/
theorem starScale : ScaleQuotient fineL 2 witnessL := by intro μ; rfl

/-- **THE DATUM.**  `G₁⁻¹ = D_1^*D_1 + ε·I + a·Q^*Q`, `Q =` block average at scale `2` composed
with the extent identification, `a = bc.a` the printed constant.  `ε > 0` is the regulator
`feedDatum` carries; §5b shows the covariance-side constants do not depend on it. -/
noncomputable def starDatum (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) :
    BalabanCovarianceData (BondFnL2 fineL) (BondFnL2 witnessL) :=
  feedDatum starScale heps (le_of_lt bc.a_pos)

theorem starDatum_Q (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) :
    (starDatum bc heps).Q
      = composedQ starScale (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU fineL) :=
  feedDatum_Q starScale heps (le_of_lt bc.a_pos)

/-! ### §2a — `Q` IS NOT INJECTIVE, AND THE SCHUR MECHANISM IS FORCED TO ACT -/

/-- **`Q` IS NOT INJECTIVE AT `D*`** — `composedQ_not_injective` at `ell = 2` (REUSED): no injective
linear map `BondFnL2 fineL → BondFnL2 witnessL` exists at all, by the dimension count
`card (Bond fineL) = 2³·card (Bond witnessL)`. -/
theorem starDatum_Q_not_injective (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) :
    ¬ Function.Injective (starDatum bc heps).Q := by
  rw [starDatum_Q bc heps]
  exact composedQ_not_injective starScale (le_refl 2) _

/-- **`ker Q ≠ ⊥` AT `D*`**, exhibited as a nonzero vector annihilated by `Q`. -/
theorem starDatum_kernel_nonzero (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) :
    ∃ k : BondFnL2 fineL, k ≠ 0 ∧ (starDatum bc heps).Q k = 0 :=
  exists_kernel_vector_of_not_injective _ (starDatum_Q_not_injective bc heps)

/-- `G₁⁻¹` at `D*` is positive definite in the form `isMinimal_unique` consumes. -/
theorem starDatum_Ginv_definite (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (x : BondFnL2 fineL) (hx : (inner ℝ x ((starDatum bc heps).Ginv x) : ℝ) = 0) : x = 0 := by
  by_contra hne
  have hpos : (0 : ℝ) < inner ℝ x ((starDatum bc heps).Ginv x) := by
    show (0 : ℝ) < inner ℝ x ((feedDatum starScale heps (le_of_lt bc.a_pos)).Ginv x)
    rw [feedDatum_Ginv starScale heps (le_of_lt bc.a_pos)]
    exact feedGinv_posDef starScale heps (le_of_lt bc.a_pos) x hne
  rw [hx] at hpos
  exact lt_irrefl _ hpos

/-- **THE MINIMISATION AT `D*` IS NOT OVER A POINT.**  For EVERY `B` there is a competitor
satisfying the constraint `QA = B`, different from the minimiser `H₁B`, with STRICTLY larger
`⟨A,G₁⁻¹A⟩`.  Contrast `equal_carrier_fiber_singleton` (§0), which says no datum on equal carriers
admits such a competitor. -/
theorem starDatum_minimisation_nondegenerate (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (B : BondFnL2 witnessL) :
    ∃ A : BondFnL2 fineL, (starDatum bc heps).Q A = B
      ∧ A ≠ solutionOperator (starDatum bc heps) B
      ∧ (inner ℝ (solutionOperator (starDatum bc heps) B)
            ((starDatum bc heps).Ginv (solutionOperator (starDatum bc heps) B)) : ℝ)
        < inner ℝ A ((starDatum bc heps).Ginv A) := by
  obtain ⟨k, hk, hQk⟩ := starDatum_kernel_nonzero bc heps
  obtain ⟨h1, h2, h3⟩ :=
    minimiser_strictly_beats (starDatum bc heps) (starDatum_Ginv_definite bc heps) k hk hQk B
  exact ⟨_, h1, h2, h3⟩

/-! ## §3 — THE WINDOW AT THE TIGHTENED CLASS

`hraw_carriers` needs `α₁(U) ≤ 1/(6668·ell₀³) = 1/53344` at `ell₀ = 2`, which is strictly tighter
than the printed `1/(186·ell₀³) = 1/1488` (`sixSixSixEight_strictly_smaller`, CITED).  The spike
gives `α₁ ≤ √2·t`, so the covariance class is `√2·t ≤ 1/53344`.  The source threshold is quadratic
in `t` because BOTH `δ = t` and `c₂ = ‖J(U*)‖ ≤ spikeK·t` are linear in it; the window lemma is
therefore stated for an arbitrary nonnegative coefficient. -/

/-- **THE WINDOW IS NONEMPTY, IN CLOSED FORM, AT THE TIGHTENED CLASS.**  For any `C ≥ 0` there is a
`t ∈ (0,1]` with `√2·t ≤ 1/53344` and `C·t² < 1`.  Witness: `t = min 1 (min (1/80016) (1/(1+C)))`;
`3/(2·80016) = 1/53344` is the whole of the first estimate, with `√2 ≤ 3/2`. -/
theorem window_tight (C : ℝ) (hC : 0 ≤ C) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ Real.sqrt 2 * t ≤ 1 / 53344 ∧ C * t ^ 2 < 1 := by
  have hCpos : (0 : ℝ) < 1 + C := by linarith
  refine ⟨min 1 (min (1 / 80016) (1 / (1 + C))), ?_, min_le_left _ _, ?_, ?_⟩
  · exact lt_min one_pos (lt_min (by norm_num) (by positivity))
  · have h1 : min 1 (min (1 / 80016) (1 / (1 + C))) ≤ 1 / 80016 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h0 : 0 < min 1 (min (1 / 80016) (1 / (1 + C))) :=
      lt_min one_pos (lt_min (by norm_num) (by positivity))
    nlinarith [h1, h2, h0, Real.sqrt_nonneg 2]
  · set t := min 1 (min (1 / 80016) (1 / (1 + C))) with hdef
    have h0 : 0 < t := lt_min one_pos (lt_min (by norm_num) (by positivity))
    have hle1 : t ≤ 1 := min_le_left _ _
    have hleC : t ≤ 1 / (1 + C) := le_trans (min_le_right _ _) (min_le_right _ _)
    have hmul : t * (1 + C) ≤ 1 := by rw [← le_div_iff₀ hCpos]; exact hleC
    nlinarith [h0, hle1, hmul, hC]

/-! ## §4 — THE COMPOSITION

`terminal_at_composed_carriers` (REUSED) has fourteen source-side binders.  Every one of them is
discharged here, at `U* = spikeU (torus t)`:

| binder | supplied by |
|---|---|
| `Qext` | `bondQext (J(U*))` — `DeltaKWiring`'s printed `D̃⁽²⁾` shape |
| `T` | `D*.Qstar`, the datum's own adjoint constraint operator (§1) |
| `S` | `‖J(U*)‖²·I` |
| `hS` | `isSourceOperator_Qstar` — a theorem at EVERY datum, not `H₁ = I` |
| `c₂`, `hc₂` | `‖J(U*)‖`, `norm_JsuTwo_spike_pos` (needs `0 < t < π`) |
| `hD2` | `assemblyDatum_hD2` (datum-free) |
| `δ`, `hδ0`, `hU` | `t`, `linkDev_spike_torus` |
| `hH1`, `hT` | `norm_solutionOperator_pos`, `norm_Qstar_pos` at `J(U*) ≠ 0` |
| `hcard` | `Fintype.card_pos` |
| `hsmall` | `frobSupBond_spike_le` and the window's `√2·t ≤ 1/53344` |
| `hδ` | the window's `starC·t² < 1` |
-/

/-- The coefficient of `t²` in the source threshold at `D*`.  Every factor is the datum's or the
lattice's own: `1370001600` and `ell₀⁶ = 64` are `terminal_wired_posDef`'s, `rawSigmaZero 2 ² = ½`
is the RG step's, `‖H₁‖` and `‖Q*‖` are `D*`'s, `√(2·|Bond witnessL|)` and `spikeK` are the source
lane's. -/
noncomputable def starC (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) : ℝ :=
  (1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2
      * ‖solutionOperator (starDatum bc heps)‖
      * (‖(starDatum bc heps).Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL)))))
    * spikeK

theorem starC_nonneg (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) : 0 ≤ starC bc heps := by
  unfold starC
  have h1 : (0 : ℝ) ≤ spikeK := le_of_lt spikeK_pos
  positivity

/-- **THE TERMINAL POSITIVITY AT A DATUM WHOSE `Q` HAS A KERNEL, AT A CURVED SOURCE-BEARING
BACKGROUND.**

At `ell₀ = 2` on the `4³` torus, at `U* = spikeU (torus t)`, at the datum `D*` of §2 — whose `Q` is
NOT injective (`starDatum_Q_not_injective`) and whose constraint fibres are never singletons
(`starDatum_minimisation_nondegenerate`) — with the source vector `v := J(U*)` carried into the
`A`-space by `Q*`:

    ⟨B̃, C*Δ_k(U*)C B̃⟩  >  0   for every  B̃ ≠ 0  in  ℓ²(Λ̃).

The two hypotheses on `t` are exactly the two smallness classes, in the same parameter: `hcov` is
the TIGHTENED covariance class `√2·t ≤ 1/53344` (not the printed `1/1488`), and `hsrc` is the source
threshold.  §3 proves both are met simultaneously. -/
theorem terminal_posDef_at_star_datum (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hcov : Real.sqrt 2 * t ≤ 1 / 53344)
    (hsrc : starC bc heps * t ^ 2 < 1)
    (w : TildeFn witnessL 2) (hw : w ≠ 0) :
    0 < cdcFormTrue (starDatum bc heps) bc
        (bondQext (JsuTwo (spikeU (torus t))))
        ((starDatum bc heps).Qstar (JsuTwo (spikeU (torus t))))
        (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have htpi : t < Real.pi := by linarith
  have htpi' : t ≤ Real.pi := le_of_lt htpi
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  -- the source vector, nonzero because the background is curved
  set v : BondFnL2 witnessL := JsuTwo (spikeU (torus t)) with hv
  have hvne : v ≠ 0 := JsuTwo_spike_ne_zero ht htpi
  have hc₂ : 0 < ‖v‖ := norm_JsuTwo_spike_pos ht htpi
  -- the two datum-level nondegeneracy binders
  have hH1 : 0 < ‖solutionOperator (starDatum bc heps)‖ :=
    norm_solutionOperator_pos (starDatum bc heps) v hvne
  have hT : 0 < ‖(starDatum bc heps).Qstar‖ := norm_Qstar_pos (starDatum bc heps) v hvne
  have hcard : 0 < Fintype.card (Bond witnessL) := Fintype.card_pos
  have hcardR : (0 : ℝ) < (Fintype.card (Bond witnessL) : ℝ) := by exact_mod_cast hcard
  have hN : (0 : ℝ) < Real.sqrt (2 * (Fintype.card (Bond witnessL))) :=
    Real.sqrt_pos.mpr (by linarith)
  have hσ : (0 : ℝ) < rawSigmaZero 2 ^ 2 := by
    have := AdalyFormal.MechEdges.G16.rawSigmaZero_pos (by norm_num : 0 < 2)
    positivity
  -- the tightened covariance class
  have hsmall : frobSupBond (spikeU (torus t)) ≤ 1 / (6668 * ((2 : ℕ) : ℝ) ^ 3) := by
    have h1 := frobSupBond_spike_le ht0 htpi'
    have h2 : (1 : ℝ) / (6668 * ((2 : ℕ) : ℝ) ^ 3) = 1 / 53344 := by norm_num
    rw [h2]
    linarith
  -- the source threshold, in the exact shape the consumer states it
  have hJle : ‖v‖ ≤ spikeK * t := norm_JsuTwo_spike_le ht0 htpi'
  have hden : (0 : ℝ) < 1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2
      * ‖solutionOperator (starDatum bc heps)‖ * ‖v‖
      * (‖(starDatum bc heps).Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL)))) := by
    positivity
  have hblock : (0 : ℝ) ≤ 1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2
      * ‖solutionOperator (starDatum bc heps)‖
      * (‖(starDatum bc heps).Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL)))) := by
    positivity
  have hδ : t < 1 / (1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2
      * ‖solutionOperator (starDatum bc heps)‖ * ‖v‖
      * (‖(starDatum bc heps).Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL))))) := by
    rw [lt_div_iff₀ hden]
    have hkey : ‖v‖ * t ≤ (spikeK * t) * t := mul_le_mul_of_nonneg_right hJle ht0
    have hexp : t * (1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2
        * ‖solutionOperator (starDatum bc heps)‖ * ‖v‖
        * (‖(starDatum bc heps).Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL)))))
        = (1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2
            * ‖solutionOperator (starDatum bc heps)‖
            * (‖(starDatum bc heps).Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL)))))
          * (‖v‖ * t) := by ring
    have hstar : starC bc heps * t ^ 2
        = (1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2
            * ‖solutionOperator (starDatum bc heps)‖
            * (‖(starDatum bc heps).Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL)))))
          * ((spikeK * t) * t) := by
      unfold starC; ring
    rw [hexp]
    calc (1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2
            * ‖solutionOperator (starDatum bc heps)‖
            * (‖(starDatum bc heps).Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL)))))
          * (‖v‖ * t)
        ≤ (1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2
            * ‖solutionOperator (starDatum bc heps)‖
            * (‖(starDatum bc heps).Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL)))))
          * ((spikeK * t) * t) := mul_le_mul_of_nonneg_left hkey hblock
      _ = starC bc heps * t ^ 2 := hstar.symm
      _ < 1 := hsrc
  -- the feed
  show 0 < cdcFormTrue (feedDatum starScale heps (le_of_lt bc.a_pos)) bc (bondQext v)
      ((feedDatum starScale heps (le_of_lt bc.a_pos)).Qstar v)
      (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w
  exact terminal_at_composed_carriers starScale (le_refl 2) witnessL_strict witnessL_dvd
    (spikeU (torus t)) hsmall bc heps (bondQext v)
    (feedDatum starScale heps (le_of_lt bc.a_pos)).Qstar _
    (isSourceOperator_Qstar (feedDatum starScale heps (le_of_lt bc.a_pos)) v)
    ‖v‖ hc₂ (assemblyDatum_hD2 v) t ht0 (linkDev_spike_torus ht0 htpi') hH1 hT hcard hδ w hw

/-- **THE HEADLINE.**  There is a parameter at which ALL of the following hold at once, at the SAME
datum and the SAME background:

1. `Q` is not injective at the datum, and `ker Q` contains a nonzero vector;
2. the constraint fibre over every `B` contains a competitor that the minimiser STRICTLY beats — so
   `⟨B,(QG₁Q*)⁻¹B⟩` is a minimum over a set with more than one point;
3. the background is CURVED (a plaquette holonomy `≠ 1`, `α₁ > 0`);
4. it lies in the TIGHTENED covariance class `α₁ ≤ 1/(6668·2³)`;
5. the source is present: `J(U*) ≠ 0`, and the source term at `C₀B̃` is STRICTLY POSITIVE, hence
   `−2·sourceTerm` strictly negative;
6. the printed `C*Δ_kC` is positive definite at `C₀B̃`.

Clauses 1 and 2 are what `CurvedContent` §8c records as absent; clauses 3-6 are what
`compute/hraw_carriers/` leaves hypothetical. -/
theorem curved_source_bearing_witness_at_noncollapsed_datum
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (w : TildeFn witnessL 2) (hw : w ≠ 0) :
    (¬ Function.Injective (starDatum bc heps).Q)
    ∧ (∃ k : BondFnL2 fineL, k ≠ 0 ∧ (starDatum bc heps).Q k = 0)
    ∧ (∀ B : BondFnL2 witnessL, ∃ A : BondFnL2 fineL, (starDatum bc heps).Q A = B
        ∧ A ≠ solutionOperator (starDatum bc heps) B
        ∧ (inner ℝ (solutionOperator (starDatum bc heps) B)
              ((starDatum bc heps).Ginv (solutionOperator (starDatum bc heps) B)) : ℝ)
          < inner ℝ A ((starDatum bc heps).Ginv A))
    ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1
      ∧ AdalyFormal.Balaban.DeltaPrime.holonomyElem (spikeU (torus t))
          AdalyFormal.Balaban.CovariantOperators.witnessPlaquette ≠ 1
      ∧ 0 < frobSupBond (spikeU (torus t))
      ∧ frobSupBond (spikeU (torus t)) ≤ 1 / (6668 * ((2 : ℕ) : ℝ) ^ 3)
      ∧ JsuTwo (spikeU (torus t)) ≠ 0
      ∧ 0 < sourceTerm (starDatum bc heps) (bondQext (JsuTwo (spikeU (torus t))))
            ((starDatum bc heps).Qstar (JsuTwo (spikeU (torus t))))
            (cZero (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w)
      ∧ 0 < cdcFormTrue (starDatum bc heps) bc
            (bondQext (JsuTwo (spikeU (torus t))))
            ((starDatum bc heps).Qstar (JsuTwo (spikeU (torus t))))
            (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w := by
  obtain ⟨t, ht, ht1, hcov, hsrc⟩ := window_tight (starC bc heps) (starC_nonneg bc heps)
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have htpi : t < Real.pi := by linarith
  have htpi' : t ≤ Real.pi := le_of_lt htpi
  obtain ⟨hcurv, hfrobpos⟩ := spike_is_curved ht htpi
  refine ⟨starDatum_Q_not_injective bc heps, starDatum_kernel_nonzero bc heps,
    starDatum_minimisation_nondegenerate bc heps, t, ht, ht1, hcurv, hfrobpos, ?_,
    JsuTwo_spike_ne_zero ht htpi, ?_,
    terminal_posDef_at_star_datum bc heps ht ht1 hcov hsrc w hw⟩
  · have h1 := frobSupBond_spike_le (le_of_lt ht) htpi'
    have h2 : (1 : ℝ) / (6668 * ((2 : ℕ) : ℝ) ^ 3) = 1 / 53344 := by norm_num
    rw [h2]
    linarith
  · exact sourceTerm_Qstar_pos (starDatum bc heps) _ _ (JsuTwo_spike_ne_zero ht htpi)
      (norm_pos_iff.mp (norm_cZero_pos (spikeU (torus t)) (dinvC (spikeU (torus t)) 2) w hw))

/-! ## §5 — WHICH CONSTANTS MOVED, AND BY HOW MUCH

The collapsed row (`CurvedContent.terminal_posDef_at_curved_spike`) runs at `σ₀ = 1`, `κ = 0`,
`‖H₁‖ = 1` and the printed class `α₁ ≤ 1/1488`.  Leaving the collapse costs exactly four things, and
each is a theorem here rather than a remark. -/

/-- **σ₀: `1 → ℓ^{-1/2}`, and `σ₀² = ½` at `ℓ = 2`.**  This is the ONLY place the RG step enters the
floor constant. -/
theorem rawSigmaZero_two_sq : rawSigmaZero 2 ^ 2 = 1 / 2 := by
  show (1 / Real.sqrt ((2 : ℕ) : ℝ)) ^ 2 = 1 / 2
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ ((2 : ℕ) : ℝ))]
  norm_num

/-- **κ: `0 → 4√2·α₁(U)`, and it meets the half-drift hypothesis inside the tightened class.**
`halfDrift_of_alpha_small` (REUSED) with the spike's own `α₁ ≤ √2·t`. -/
theorem star_kappa_halfDrift {t : ℝ} (ht0 : 0 ≤ t) (htpi : t ≤ Real.pi)
    (hcov : Real.sqrt 2 * t ≤ 1 / 53344) :
    4 * Real.sqrt 2 * frobSupBond (spikeU (torus t)) ≤ Real.sqrt (gammaBrick 2) / 2 := by
  have hsmall : frobSupBond (spikeU (torus t)) ≤ 1 / (6668 * ((2 : ℕ) : ℝ) ^ 3) := by
    have h1 := frobSupBond_spike_le ht0 htpi
    have h2 : (1 : ℝ) / (6668 * ((2 : ℕ) : ℝ) ^ 3) = 1 / 53344 := by norm_num
    rw [h2]
    linarith
  exact AdalyFormal.HrawCarriers.halfDrift_of_alpha_small (L' := witnessL)
    (by norm_num : 0 < (2 : ℕ)) (spikeU (torus t)) hsmall

/-- **γ₁: `gammaBrick 2 → 2·(√(gammaBrick 2) − 4√2·α₁)²`, and it never falls below HALF the
collapsed value.**  The `2` is `1/σ₀²`; the `≥ ¼` is the half-drift hypothesis.  So the price of
leaving `Q = I` is at most a factor `2` in the floor constant — derived, not chosen. -/
theorem starFloorConst_lower {t : ℝ} (ht0 : 0 ≤ t) (htpi : t ≤ Real.pi)
    (hcov : Real.sqrt 2 * t ≤ 1 / 53344) :
    gammaBrick 2 / 2
      ≤ sharpFloorConst (gammaBrick 2) (4 * Real.sqrt 2 * frobSupBond (spikeU (torus t)))
          (rawSigmaZero 2) := by
  have hγ : 0 < gammaBrick 2 := gammaBrick_pos (by norm_num)
  have hs : Real.sqrt (gammaBrick 2) ^ 2 = gammaBrick 2 := Real.sq_sqrt (le_of_lt hγ)
  have hs0 : (0 : ℝ) ≤ Real.sqrt (gammaBrick 2) := Real.sqrt_nonneg _
  have hhalf := star_kappa_halfDrift ht0 htpi hcov
  have hκ0 : (0 : ℝ) ≤ 4 * Real.sqrt 2 * frobSupBond (spikeU (torus t)) :=
    mul_nonneg (by positivity) (frobSupBond_nonneg _)
  have hgap : Real.sqrt (gammaBrick 2) / 2
      ≤ Real.sqrt (gammaBrick 2) - 4 * Real.sqrt 2 * frobSupBond (spikeU (torus t)) := by
    linarith
  have hquart : gammaBrick 2 / 4
      ≤ (Real.sqrt (gammaBrick 2) - 4 * Real.sqrt 2 * frobSupBond (spikeU (torus t))) ^ 2 := by
    nlinarith [hgap, hs, hs0]
  show gammaBrick 2 / 2
    ≤ ((Real.sqrt (gammaBrick 2) - 4 * Real.sqrt 2 * frobSupBond (spikeU (torus t)))
        / rawSigmaZero 2) ^ 2
  rw [div_pow, rawSigmaZero_two_sq]
  linarith

/-- **THE COLLAPSED VALUE, FOR COMPARISON**: at `σ₀ = 1`, `κ = 0` the floor constant is
`gammaBrick 2` exactly (`sharpFloorConst_eq_at_zero`, REUSED). -/
theorem collapsed_floorConst : sharpFloorConst (gammaBrick 2) 0 1 = gammaBrick 2 := by
  rw [AdalyFormal.Balaban.TerminalAssembly.sharpFloorConst_eq_at_zero (by norm_num : 0 < 2) 1]
  norm_num

/-- **THE SMALLNESS CLASS: `1/1488 → 1/53344`**, a factor `6668/186` and no power of `ell₀`
(`sixSixSixEight_strictly_smaller`, `threshold_ratio_is_ell_free`, both CITED). -/
theorem class_tightening : (1 : ℝ) / 53344 < 1 / 1488 ∧ (1 / 1488 : ℝ) / (1 / 53344) = 6668 / 186 := by
  constructor
  · norm_num
  · norm_num

/-- **THE DIMENSION COUNT THAT MAKES `ker Q ≠ ⊥` UNAVOIDABLE**, exhibited rather than cited:
`|Bond fineL| = 2³·|Bond witnessL|` (`card_bond_scale`, REUSED).  No linear map from the fine
carrier to the coarse one is injective, whatever `Q` is. -/
theorem card_fine_eq : Fintype.card (Bond fineL) = 2 ^ 3 * Fintype.card (Bond witnessL) :=
  AdalyFormal.HrawCarriers.card_bond_scale starScale

/-! ## §6 — CONTROLS: WHAT WOULD MAKE §4 EMPTY, AND WHY IT DOES NOT

Four ways the row could be content-free.  Each is excluded by a theorem. -/

/-- **§6a — THE SOURCE TERM IS NOT ALGEBRAICALLY FORCED POSITIVE (S82).**  At `t = 0` the SAME
expression, at the SAME datum, with the SAME `Q*`-carried source, is `0`: the background is flat
(`spike_at_zero_is_flat`, CITED) and `J = 0` there.  So `sourceTerm_Qstar_pos`'s conclusion is
bought by the curvature and by nothing structural. -/
theorem sourceTerm_vanishes_at_flat (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (B : BondFnL2 witnessL) :
    sourceTerm (starDatum bc heps) (bondQext (JsuTwo (spikeU (torus 0))))
        ((starDatum bc heps).Qstar (JsuTwo (spikeU (torus 0)))) B = 0 := by
  rw [sourceTerm_Qstar_eq]
  have hJ : JsuTwo (spikeU (torus (0 : ℝ))) = 0 := by
    rw [spike_at_zero_is_flat]
    exact AdalyFormal.Balaban.SourceWiredJ.JsuTwo_trivialU
  rw [hJ, norm_zero]
  ring

/-- **§6b — THE CLOSED FORM `‖B‖²‖v‖²` IS NOT AN IDENTITY IN `J`.**  Replace the `Q*`-carried source
by `J = 0` and the same source term is `0`, while `‖B‖²‖v‖² > 0`.  So `sourceTerm_Qstar_eq` records
a property of `J = Q*v`, not a tautology about `bondQext`. -/
theorem sourceTerm_not_forced (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (v B : BondFnL2 witnessL) (hv : v ≠ 0) (hB : B ≠ 0) :
    sourceTerm (starDatum bc heps) (bondQext v) 0 B = 0
    ∧ sourceTerm (starDatum bc heps) (bondQext v) ((starDatum bc heps).Qstar v) B ≠ 0 := by
  refine ⟨AdalyFormal.Balaban.DeltaKWiring.sourceTerm_zero_J _ _ B, ?_⟩
  exact ne_of_gt (sourceTerm_Qstar_pos (starDatum bc heps) v B hv hB)

/-- **§6c — THE POSITIVITY IS NOT READ OFF A ZERO VECTOR.**  `‖C₀B̃‖ > 0` at every `B̃ ≠ 0`
(`norm_cZero_pos`, REUSED), and the floor constant is strictly positive inside the class. -/
theorem star_nondegenerate_at_cZero {t : ℝ} (ht0 : 0 ≤ t) (htpi : t ≤ Real.pi)
    (hcov : Real.sqrt 2 * t ≤ 1 / 53344) (w : TildeFn witnessL 2) (hw : w ≠ 0) :
    0 < ‖cZero (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w‖
    ∧ 0 < sharpFloorConst (gammaBrick 2) (4 * Real.sqrt 2 * frobSupBond (spikeU (torus t)))
        (rawSigmaZero 2) := by
  refine ⟨norm_cZero_pos (spikeU (torus t)) (dinvC (spikeU (torus t)) 2) w hw, ?_⟩
  have h := starFloorConst_lower ht0 htpi hcov
  have hγ : 0 < gammaBrick 2 := gammaBrick_pos (by norm_num)
  linarith

/-- **§6d — THE REGULATOR `ε` IS NOT DOING THE WORK.**  The conclusion of §4 holds for EVERY
`ε > 0`, and the three covariance-side constants `σ₀ = ℓ^{-1/2}`, `κ = 4√2·α₁(U)` and
`γ₁ = sharpFloorConst(gammaBrick 2, κ, σ₀)` do not mention `ε` at all — visible in the statements of
`rawSigmaZero_two_sq`, `star_kappa_halfDrift` and `starFloorConst_lower`, none of which takes an
`ε`.  `ε` enters only through `‖H₁‖`, i.e. through the admissible `t`. -/
theorem star_holds_for_every_eps (bc : BaseConstant) (w : TildeFn witnessL 2) (hw : w ≠ 0)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1
      ∧ 0 < cdcFormTrue (starDatum bc heps) bc
            (bondQext (JsuTwo (spikeU (torus t))))
            ((starDatum bc heps).Qstar (JsuTwo (spikeU (torus t))))
            (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w := by
  obtain ⟨t, ht, ht1, hcov, hsrc⟩ := window_tight (starC bc heps) (starC_nonneg bc heps)
  exact ⟨t, ht, ht1, terminal_posDef_at_star_datum bc heps ht ht1 hcov hsrc w hw⟩

/-! ## §7 — `‖H₁‖` AT `D*`: THE COERCIVITY HALF, CLOSED

§4 uses `‖H₁‖` only through `0 < ‖H₁‖`, so the theorem is unconditional; but the admissible `t` is
then explicit only as a function of an unbounded quantity.  §7 removes half of that.

`TerminalAssembly.norm_solutionOperator_le_of_lift` (REUSED) wants a coercivity modulus `Cm` with
`‖A‖² ≤ Cm·⟨A,G₁⁻¹A⟩` and a lift `Rq` of the constraint.  At `D*` the modulus is **exactly `1/ε`**,
read straight off `inner_feedGinv` — strictly better than §4b's generic `‖G₁‖²‖G₁⁻¹‖`, which needs
the inverse's norm.  What remains for a fully numeric `t` is a lift and its norm; that is R1 of
`SCOPE.md` §5, with the route named there. -/

/-- **THE `ε`-COERCIVITY OF `G₁⁻¹` AT `D*`, EXACTLY.**  `⟨A,G₁⁻¹A⟩ = ‖∂₁A‖² + ε‖A‖² + a‖QA‖² ≥
ε‖A‖²`: the two dropped summands are a squared norm and `a > 0` times one.  This is the fact that
the regulator `ε` — and nothing about the curl or about `Q` — is what makes `G₁⁻¹` invertible. -/
theorem starDatum_eps_coercive (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (A : BondFnL2 fineL) :
    eps * ‖A‖ ^ 2 ≤ (inner ℝ A ((starDatum bc heps).Ginv A) : ℝ) := by
  show eps * ‖A‖ ^ 2
    ≤ (inner ℝ A ((feedDatum starScale heps (le_of_lt bc.a_pos)).Ginv A) : ℝ)
  rw [AdalyFormal.HrawCarriers.feedDatum_Ginv starScale heps (le_of_lt bc.a_pos),
    AdalyFormal.HrawCarriers.inner_feedGinv]
  have h1 : (0 : ℝ) ≤ ‖AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2
      (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU fineL) A‖ ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ bc.a * ‖composedQ starScale
      (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU fineL) A‖ ^ 2 :=
    mul_nonneg (le_of_lt bc.a_pos) (sq_nonneg _)
  linarith

/-- **`‖H₁‖ ≤ √((1/ε)·‖G₁⁻¹‖‖Rq‖²)` FOR ANY LIFT, AT ANY DATUM WITH AN `ε`-COERCIVE `G₁⁻¹`.**  The
lift's energy is bounded by Cauchy-Schwarz and two operator norms, so no property of `Rq` beyond
`Q∘Rq = id` is used. -/
theorem norm_H1_le_of_eps_coercive {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (D : BalabanCovarianceData H K) {eps : ℝ} (heps : 0 < eps)
    (hcoer : ∀ A : H, eps * ‖A‖ ^ 2 ≤ (inner ℝ A (D.Ginv A) : ℝ))
    (Rq : K →L[ℝ] H) (hRq : ∀ B : K, D.Q (Rq B) = B) :
    ‖solutionOperator D‖ ≤ Real.sqrt ((1 / eps) * (‖D.Ginv‖ * ‖Rq‖ ^ 2)) := by
  refine AdalyFormal.Balaban.TerminalAssembly.norm_solutionOperator_le_of_lift D (1 / eps)
    (‖D.Ginv‖ * ‖Rq‖ ^ 2) (by positivity) (by positivity) (fun A => ?_) Rq hRq (fun B => ?_)
  · have h := mul_le_mul_of_nonneg_left (hcoer A) (le_of_lt (one_div_pos.mpr heps))
    have hid : (1 / eps) * (eps * ‖A‖ ^ 2) = ‖A‖ ^ 2 := by
      field_simp
    rw [hid] at h
    exact h
  · have h2 : ‖D.Ginv (Rq B)‖ ≤ ‖D.Ginv‖ * ‖Rq B‖ := D.Ginv.le_opNorm _
    have h3 : ‖Rq B‖ ≤ ‖Rq‖ * ‖B‖ := Rq.le_opNorm B
    calc (inner ℝ (Rq B) (D.Ginv (Rq B)) : ℝ)
        ≤ ‖Rq B‖ * ‖D.Ginv (Rq B)‖ := real_inner_le_norm _ _
      _ ≤ ‖Rq B‖ * (‖D.Ginv‖ * ‖Rq B‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ‖D.Ginv‖ * ‖Rq B‖ ^ 2 := by ring
      _ ≤ ‖D.Ginv‖ * (‖Rq‖ * ‖B‖) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          nlinarith [h3, norm_nonneg (Rq B), norm_nonneg B, norm_nonneg Rq]
      _ = (‖D.Ginv‖ * ‖Rq‖ ^ 2) * ‖B‖ ^ 2 := by ring

/-- **THE TWO COMPOSED AT `D*`.**  Every factor on the right is elementary: `ε` is the lane's own
regulator, `‖G₁⁻¹‖` is the norm of an explicitly written sum, `‖Rq‖` is the norm of a section of the
block average (`compute/qsurj_rinverse/`'s `rInv` has `‖rInv‖ = ell³`, CITED, not imported here). -/
theorem starDatum_norm_H1_le (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (Rq : BondFnL2 witnessL →L[ℝ] BondFnL2 fineL)
    (hRq : ∀ B : BondFnL2 witnessL, (starDatum bc heps).Q (Rq B) = B) :
    ‖solutionOperator (starDatum bc heps)‖
      ≤ Real.sqrt ((1 / eps) * (‖(starDatum bc heps).Ginv‖ * ‖Rq‖ ^ 2)) :=
  norm_H1_le_of_eps_coercive (starDatum bc heps) heps (starDatum_eps_coercive bc heps) Rq hRq

/-- The lift binder of §7 is INHABITED at `D*` — `Q` is surjective there, so a right inverse exists;
`solutionOperator` itself is one (`lift_binder_inhabited`, REUSED).  Stated so that
`starDatum_norm_H1_le` cannot be read as conditional on something nothing meets.  (Using `H₁` itself
gives a circular constant; the bound's value comes from a CHEAPER lift.) -/
theorem starDatum_lift_inhabited (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) :
    ∃ Rq : BondFnL2 witnessL →L[ℝ] BondFnL2 fineL,
      ∀ B : BondFnL2 witnessL, (starDatum bc heps).Q (Rq B) = B :=
  ⟨solutionOperator (starDatum bc heps), interpolates (starDatum bc heps)⟩

/-! ## §8 — AXIOM AUDIT: TOTAL COVERAGE (every declaration in this file) -/

#print axioms fiber_singleton_of_Q_injective
#print axioms equal_carrier_fiber_singleton
#print axioms exists_kernel_vector_of_not_injective
#print axioms minimiser_strictly_beats
#print axioms norm_solutionOperator_pos
#print axioms norm_Qstar_pos
#print axioms sourceTerm_Qstar_eq
#print axioms isSourceOperator_Qstar
#print axioms sourceTerm_Qstar_pos
#print axioms Qstar_source_ne_zero
#print axioms fineL
#print axioms starScale
#print axioms starDatum
#print axioms starDatum_Q
#print axioms starDatum_Q_not_injective
#print axioms starDatum_kernel_nonzero
#print axioms starDatum_Ginv_definite
#print axioms starDatum_minimisation_nondegenerate
#print axioms window_tight
#print axioms starC
#print axioms starC_nonneg
#print axioms terminal_posDef_at_star_datum
#print axioms curved_source_bearing_witness_at_noncollapsed_datum
#print axioms rawSigmaZero_two_sq
#print axioms star_kappa_halfDrift
#print axioms starFloorConst_lower
#print axioms collapsed_floorConst
#print axioms class_tightening
#print axioms card_fine_eq
#print axioms sourceTerm_vanishes_at_flat
#print axioms sourceTerm_not_forced
#print axioms star_nondegenerate_at_cZero
#print axioms star_holds_for_every_eps
#print axioms starDatum_eps_coercive
#print axioms norm_H1_le_of_eps_coercive
#print axioms starDatum_norm_H1_le
#print axioms starDatum_lift_inhabited

end AdalyFormal.DatumWitness
