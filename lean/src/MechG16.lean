/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import StokesHraw
import StokesRestricted
import AdalyFormal.Balaban.BridgeInverseCarrier
import AdalyFormal.Balaban.DeltaKFull
import AdalyFormal.Balaban.QCLMNorm

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# G16 — THE OPERATOR-LEVEL PROMOTION OF `hraw_lattice`

`compute/terminal_compose/DAG.md` row **G16** (class MECH): *"the OPERATOR-LEVEL PROMOTION of
`stokes_hraw`'s `hraw_lattice` — the scalar-to-abstract join of the Stokes chain."*

## What the consumer asks for, transcribed FROM THE CONSUMER

`compute/stokes_commu/stage/StokesRestricted.lean:159-162` (`perturbed_chain_at_minimizer`) and
`:186-193` (`gamma_floor_at_minimizer`) take, as an undischarged hypothesis, over
`{Hs Ks P₁ P₂ : Type*}` each `[NormedAddCommGroup _] [InnerProductSpace ℝ _]`:

```
(D  : BalabanCovarianceData Hs Ks)          -- D.Q : Hs →L[ℝ] Ks
(d  : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂) (σ₀ c : ℝ) (hc : 0 ≤ c)
(hraw : ∀ A : Hs, ‖d₁ (D.Q A)‖ ≤ σ₀ * ‖d A‖ + c * ‖A‖)
```

**The quantifier prefix is the consumer's, not prose's:** `hraw` is `∀ A : Hs` — universal over the
FINE carrier — and `d`, `d₁`, `D.Q` are `ContinuousLinearMap`s, so every `‖·‖` in it is an
inner-product-space norm, never a `Real.sqrt` of an explicit sum.

`compute/stokes_hraw/stage/StokesHraw.lean:384-390` (`hraw_lattice`) delivers the same inequality
with explicit sums on the bare function types. §2 below is the join.

## The four carriers, and which existed

| abstract | lattice object | where it came from |
|---|---|---|
| `Hs` | `CovariantOperators.BondFnL2 L` | **existed** |
| `Ks` | `BridgeInverse.CoarseFnL2 L ell` | **existed** |
| `P₁` | `CovariantHjMinimizer.PlaqFnL2 L` | **existed** |
| `P₂` | `CoarsePlaqFnL2 L ell` (§0) | **did not exist anywhere in the tree** |
| `D.Q` | `BridgeInverse.qCLM U ell` | **existed** |
| `d` | `DeltaKFull.curlCovariantCLM_L2 U` | **existed** |
| `d₁` | `coarseCurlCLM_L2 hdvd` (§0) | **did not exist anywhere in the tree** |

Grepped before building (LAW-19): the only `PiLp 2` carriers over `CoarsePlaquette` in
`formal/AdalyFormal/` are `CoarseCurl.CoarsePlaquetteSpace = EuclideanSpace ℝ (CoarsePlaquette L
ell)` — **ℝ-valued, not `𝔰𝔲(2)`-valued** — so it cannot receive `coarseCurlSuTwo`. The two objects
built in §0 are the whole of what was missing.

## THE STANDING CAUTION, OBEYED

`formal/AdalyFormal/AdalyFormal/Balaban/CovariantOperators.lean:674-680`, verbatim: *"`BondFnL2 L`
keeps its `NormedAddCommGroup` by ordinary search (`PiLp.normedAddCommGroup` at the HS fibre); **do
NOT re-register one here.** The regression pin that fails the moment anyone does is
`SuTwoInner.bondFnL2_norm_is_the_registered_norm`."*

**This module registers NO instance on any carrier.** `CoarsePlaqFnL2` is an `abbrev` of `PiLp 2`,
so every structure on it is found by ordinary anonymous search, exactly as `BondFnL2`,
`CoarseFnL2` and `PlaqFnL2` are. Grep-checkable: this file contains no `instance` and no
`letI`/`haveI` for a normed or inner-product structure.

## What §8 of `compute/stokes_hraw/SCOPE.md` stopped on, and why the stop is spent

That section stops on *"Feeding it literally needs an `InnerProductSpace ℝ` on a BOND-level
carrier"* plus *"registering `InnerProductSpace ℝ` on either would create a genuine diamond"*.
Neither is needed here: **no registration happens.** `BondFnL2 L` already carries
`InnerProductSpace ℝ` by ordinary search — the same instance `qCLM`, `qstarCLM` and
`curlCovariantCLM_L2` have been elaborating through for the whole campaign — and §1 below simply
uses it. The bond-level carrier was never the obstacle; the missing object was the COARSE-PLAQUETTE
one.

Nothing here is installed in `formal/`; nothing enters `Spine.lean`'s import cone.
Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.
-/

namespace AdalyFormal.MechEdges.G16

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo curlValueCovariant suTwoWitness
  suTwoWitness_ne_zero)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM)
open AdalyFormal.Balaban.CoarseCurl (CoarsePlaquette coarseShift coarseShift_val_eq
  coarseShift_apply_ne)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo coarseCurlSuTwo_add coarseCurlSuTwo_smul)
open AdalyFormal.Balaban.BridgeInverse (CoarseFnL2 qCLM qCLM_apply)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.QCLMNorm (norm_sq_pilp)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy frobSupBond
  frobSupBond_nonneg)
open AdalyFormal.StokesHraw (hraw_lattice)

variable {L : PeriodicLatticeExtent}

/-! ## §0 — THE TWO OBJECTS THE TREE DID NOT HAVE -/

/-- **`P₂`: the `L²` carrier of `𝔰𝔲(2)`-valued COARSE-PLAQUETTE fields.**  `abbrev` of `PiLp 2`
(reducible), so every instance — `NormedAddCommGroup`, `InnerProductSpace ℝ`, `FiniteDimensional` —
is found by ordinary anonymous search, and NOTHING is registered here (the `CovariantOperators.lean`
:674-680 caution).  This mirrors `BridgeInverse.CoarseFnL2` and
`CovariantHjMinimizer.PlaqFnL2` letter for letter (LAW-19); the only difference is the index type. -/
abbrev CoarsePlaqFnL2 (L : PeriodicLatticeExtent) (ell : ℕ) : Type :=
  PiLp 2 (fun _ : CoarsePlaquette L ell => SuTwo)

/-- `∂₁'` as a bare `LinearMap` on the FUNCTION types.  Both fields are `ThirdLevelStokes`'
(`coarseCurlSuTwo_add`, `coarseCurlSuTwo_smul`) — reused, not reproved. -/
noncomputable def coarseCurlLM {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    (CoarseBond L ell → SuTwo) →ₗ[ℝ] (CoarsePlaquette L ell → SuTwo) where
  toFun := coarseCurlSuTwo hdvd
  map_add' B1 B2 := funext (fun p => coarseCurlSuTwo_add hdvd B1 B2 p)
  map_smul' c B := funext (fun p => coarseCurlSuTwo_smul hdvd c B p)

/-- **`d₁`: `∂₁' : CoarseFnL2 L ell →L[ℝ] CoarsePlaqFnL2 L ell`.**  Built by exactly the recipe
`BridgeInverse.qCLM` uses for `Q` (LAW-19): sandwich the bare `LinearMap` between the two
`WithLp.linearEquiv`s, then `LinearMap.toContinuousLinearMap` (finite dimensions). -/
noncomputable def coarseCurlCLM_L2 {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    CoarseFnL2 L ell →L[ℝ] CoarsePlaqFnL2 L ell :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (CoarsePlaquette L ell → SuTwo)).symm.toLinearMap.comp
      ((coarseCurlLM hdvd).comp
        (WithLp.linearEquiv 2 ℝ (CoarseBond L ell → SuTwo)).toLinearMap))

/-- The defining pointwise value of `d₁` — `rfl`, so no transport lemma is ever needed downstream. -/
theorem coarseCurlCLM_L2_apply {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseFnL2 L ell) (p : CoarsePlaquette L ell) :
    WithLp.ofLp (coarseCurlCLM_L2 hdvd B) p = coarseCurlSuTwo hdvd (WithLp.ofLp B) p := rfl

/-! ## §1 — THE THREE NORM IDENTITIES

Each is the SAME lemma (`QCLMNorm.norm_sq_pilp`, CITED) at a different index type.  That one lemma
serves all four carriers is not a coincidence: all four are `PiLp 2 (fun _ : ι => SuTwo)`. -/

/-- `‖x‖ = √(∑ ‖x i‖²)` on any `PiLp 2` over `𝔰𝔲(2)`.  The `sqrt` form is what `hraw_lattice`
speaks in; `norm_sq_pilp` is the squared form. -/
theorem pilp_norm_eq_sqrt_sum {ι : Type} [Fintype ι] (x : PiLp 2 (fun _ : ι => SuTwo)) :
    ‖x‖ = Real.sqrt (∑ i : ι, ‖WithLp.ofLp x i‖ ^ 2) := by
  rw [← norm_sq_pilp x, Real.sqrt_sq (norm_nonneg _)]

/-- **`‖A‖_{Hs} = √(bondEnergy A)`.** -/
theorem norm_bondFnL2 (A : Bond L → SuTwo) :
    ‖(WithLp.toLp 2 A : BondFnL2 L)‖ = Real.sqrt (bondEnergy A) := by
  rw [pilp_norm_eq_sqrt_sum]
  rfl

/-- **`‖d A‖_{P₁} = √(plaqEnergy (D_U A))`.**  Uses `DeltaKFull.curlCovariantCLM_L2_toLp` (CITED). -/
theorem norm_curlCLM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    ‖curlCovariantCLM_L2 U (WithLp.toLp 2 A)‖
      = Real.sqrt (plaqEnergy (curlValueCovariant U A)) := by
  rw [pilp_norm_eq_sqrt_sum, curlCovariantCLM_L2_toLp]
  rfl

/-- `Q` on the `L²` carrier IS `lineCoarseRestrictCovLM` on the function type. -/
theorem ofLp_qCLM {ell : ℕ} (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    WithLp.ofLp (qCLM U ell (WithLp.toLp 2 A)) = lineCoarseRestrictCovLM U ell A :=
  funext (fun b => qCLM_apply U ell (WithLp.toLp 2 A) b)

/-- **`‖d₁ (Q A)‖_{P₂} = √(∑_P ‖∂₁'(Q_ℓ(U)A)(P)‖²)`** — the LEFT side of `hraw_lattice`. -/
theorem norm_coarseCurl_qCLM {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    ‖coarseCurlCLM_L2 hdvd (qCLM U ell (WithLp.toLp 2 A))‖
      = Real.sqrt (∑ P : CoarsePlaquette L ell,
          ‖coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM U ell A) P‖ ^ 2) := by
  -- the two summands are the SAME term (`coarseCurlCLM_L2_apply` and `ofLp_qCLM` are both `rfl`
  -- by construction), so `congr 1` discharges the sum outright; the two named lemmas above are
  -- what make that true and are stated separately so a reader never has to trust `congr`.
  rw [pilp_norm_eq_sqrt_sum]
  congr 1

/-! ## §2 — **THE PROMOTION.**  `hraw` in EXACTLY the shape `StokesRestricted` consumes -/

/-- **`c`, the error coefficient, as a single real** — the consumer's `hraw` reads `c * ‖A‖` with
`c : ℝ`, so the three factors `36√2`, `ℓ^{-1/2}`, `α₁` are packaged here and NOT re-associated at the
call site.  `36√2` is `stokes_hraw`'s own counted constant (`4√2` fine + `32√2` coarse), CITED. -/
noncomputable def rawErrorCoeff (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : ℝ :=
  (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * frobSupBond U

/-- `σ₀ = ℓ^{-1/2}`, named for the same reason. -/
noncomputable def rawSigmaZero (ell : ℕ) : ℝ := 1 / Real.sqrt (ell : ℝ)

theorem rawErrorCoeff_nonneg (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    0 ≤ rawErrorCoeff ell U :=
  mul_nonneg (by positivity) (frobSupBond_nonneg U)

theorem rawSigmaZero_pos {ell : ℕ} (hell : 0 < ell) : 0 < rawSigmaZero ell := by
  have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  unfold rawSigmaZero
  positivity

/-- **`0 < ell` FROM `hdvd` ALONE.**  If `ell = 0` then `0 ∣ (L μ + 1)` forces `L μ + 1 = 0`, which
`Nat.succ_ne_zero` refutes.  This duplicates `StokesHrawWitness.ell_pos_of_dvd` (a two-line fact in a
module this lane does not import); the duplication is DISCLOSED rather than hidden (LAW-19). -/
theorem ell_pos_of_dvd {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) : 0 < ell := by
  rcases Nat.eq_zero_or_pos ell with h | h
  · exact absurd (Nat.eq_zero_of_zero_dvd (h ▸ hdvd 0)) (Nat.succ_ne_zero (L 0))
  · exact h

/-- **THE G16 DELIVERABLE.**  `hraw_lattice` as a statement about CONTINUOUS LINEAR MAPS on the
`PiLp` carriers, in exactly the shape `StokesRestricted.perturbed_chain_at_minimizer` /
`gamma_floor_at_minimizer` consume:

```
∀ A : BondFnL2 L,  ‖d₁ (Q A)‖  ≤  σ₀ · ‖d A‖  +  c · ‖A‖
```

with `d₁ = coarseCurlCLM_L2 hdvd`, `Q = qCLM U ell`, `d = curlCovariantCLM_L2 U`,
`σ₀ = rawSigmaZero ell = ℓ^{-1/2}`, `c = rawErrorCoeff ell U = 36√2·ℓ^{-1/2}·α₁`.

**Hypothesis: `hdvd` ONLY.**  `hraw_lattice` also carries `hell : 0 < ell`; `ell_pos_of_dvd` shows it
is redundant in the presence of `hdvd` (this is `stokes_hraw` §10.2's `hraw_lattice_of_dvd` reading,
independently reproved here).  So the promoted statement's hypothesis set is the smallest one the
lattice bound admits.

Every `‖·‖` here is the norm of the registered `NormedAddCommGroup` on a `PiLp 2` carrier found by
ordinary instance search.  No instance is registered by this module. -/
theorem hraw_op {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : BondFnL2 L) :
    ‖coarseCurlCLM_L2 hdvd (qCLM U ell A)‖
      ≤ rawSigmaZero ell * ‖curlCovariantCLM_L2 U A‖ + rawErrorCoeff ell U * ‖A‖ := by
  have hell : 0 < ell := ell_pos_of_dvd hdvd
  have hA : (WithLp.toLp 2 (WithLp.ofLp A) : BondFnL2 L) = A := rfl
  have hlat := hraw_lattice hell hdvd U (WithLp.ofLp A)
  rw [← norm_coarseCurl_qCLM hdvd U (WithLp.ofLp A), ← norm_curlCLM U (WithLp.ofLp A),
    ← norm_bondFnL2 (WithLp.ofLp A)] at hlat
  rw [hA] at hlat
  unfold rawSigmaZero rawErrorCoeff
  linarith [hlat]

/-! ## §3 — `hK`, DISCHARGED AT THE LATTICE

`gamma_floor_at_minimizer` also takes `hK : ∀ A, ‖d A‖² ≤ ⟪A, Kop A⟫`.  At the lattice this is not a
hypothesis at all: take `Kop := d* ∘ d` and the inequality is an EQUALITY.  Nothing is assumed. -/

/-- **`Kop := D_U^{1*} D_U^1`**, the honest curl-energy operator on the fine `L²` carrier. -/
noncomputable def curlGram (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  (ContinuousLinearMap.adjoint (curlCovariantCLM_L2 U)).comp (curlCovariantCLM_L2 U)

/-- **`⟪A, Kop A⟫ = ‖d A‖²` — an EQUALITY**, so `hK` is discharged with no slack. -/
theorem inner_curlGram (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : BondFnL2 L) :
    (inner ℝ A (curlGram U A) : ℝ) = ‖curlCovariantCLM_L2 U A‖ ^ 2 := by
  show (inner ℝ A (ContinuousLinearMap.adjoint (curlCovariantCLM_L2 U)
    (curlCovariantCLM_L2 U A)) : ℝ) = _
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

theorem hK_lattice (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : BondFnL2 L) : ‖curlCovariantCLM_L2 U A‖ ^ 2 ≤ (inner ℝ A (curlGram U A) : ℝ) :=
  le_of_eq (inner_curlGram U A).symm

/-! ## §4 — COMPOSITION A: the perturbed chain bound AT THE OPERATOR LEVEL

`StokesRestricted.perturbed_chain_at_minimizer` needs `hraw`, `hc`, and a covariance datum `D`.
`hraw` and `hc` are now theorems; `D` is carried, with its `Q` field PINNED to the lattice `Q`.
The pin `hQ` is what makes this a statement about Bałaban's operators rather than about an arbitrary
abstract datum — without it the composition would be a re-statement of the abstract theorem. -/

/-- **THE CHAIN BOUND ON THE PRINTED OPERATORS.**  For any covariance datum `D` on the lattice
carriers whose constraint operator IS `qCLM U ell`:

```
‖∂₁' B‖  ≤  ℓ^{-1/2}·‖D_U^1 (H₁B)‖  +  (36√2·ℓ^{-1/2}·α₁·‖H₁‖)·‖B‖      for every B : CoarseFnL2
```

`H₁ = solutionOperator D`.  Only `hdvd` and `D`+`hQ` are hypotheses; the drift constant is
discharged from `hraw_op`. -/
theorem perturbed_chain_op {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (D : AdalyFormal.Balaban.VariationalProjectorH1.BalabanCovarianceData
          (BondFnL2 L) (CoarseFnL2 L ell))
    (hQ : D.Q = qCLM U ell) (B : CoarseFnL2 L ell) :
    ‖coarseCurlCLM_L2 hdvd B‖
      ≤ rawSigmaZero ell *
          ‖curlCovariantCLM_L2 U
            (AdalyFormal.Balaban.VariationalProjectorH1.solutionOperator D B)‖
        + (rawErrorCoeff ell U *
            ‖AdalyFormal.Balaban.VariationalProjectorH1.solutionOperator D‖) * ‖B‖ := by
  refine AdalyFormal.StokesCommu.Restricted.perturbed_chain_at_minimizer D
    (curlCovariantCLM_L2 U) (coarseCurlCLM_L2 hdvd) (rawSigmaZero ell)
    (rawErrorCoeff ell U) (rawErrorCoeff_nonneg ell U) ?_ B
  intro A
  rw [hQ]
  exact hraw_op hdvd U A

#print axioms CoarsePlaqFnL2
#print axioms coarseCurlLM
#print axioms coarseCurlCLM_L2
#print axioms coarseCurlCLM_L2_apply
#print axioms pilp_norm_eq_sqrt_sum
#print axioms norm_bondFnL2
#print axioms norm_curlCLM
#print axioms ofLp_qCLM
#print axioms norm_coarseCurl_qCLM
#print axioms rawErrorCoeff
#print axioms rawSigmaZero
#print axioms rawErrorCoeff_nonneg
#print axioms rawSigmaZero_pos
#print axioms ell_pos_of_dvd
#print axioms hraw_op
#print axioms curlGram
#print axioms inner_curlGram
#print axioms hK_lattice
#print axioms perturbed_chain_op

end AdalyFormal.MechEdges.G16
