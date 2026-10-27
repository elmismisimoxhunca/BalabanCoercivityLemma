/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import StokesLattice

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `hraw` AT THE LATTICE — the general-`U` raw drift bound, assembled

`compute/stokes_commu/stage/StokesRestricted.lean` §4/§5 take, as a HYPOTHESIS they never discharge:

```
(hraw : ∀ A : Hs, ‖d₁ (D.Q A)‖ ≤ σ₀ * ‖d A‖ + c * ‖A‖)
```

Its own docstring: *"`hraw` is the general-`U` bound the drift estimates deliver: the error measured
against `‖A‖` (`√bondEnergy`)."*  That lane recorded that combining the tree's ingredients into
`hraw` "needs three elementary, `U`-free lemmas the tree does not have", and stopped for compile
budget.  This file builds the three lemmas and performs the assembly.

**The lattice reading of the four abstract objects** (`d₁ ∘ Q` on the left, `d` and `‖·‖` on the
right):

| abstract | lattice object |
|---|---|
| `A` | `A : Bond L → SuTwo` |
| `Q` | `lineCoarseRestrictCovLM U ell` |
| `d` | `curlValueCovariant U` |
| `d₁` | `ThirdLevelStokes.coarseCurlSuTwo hdvd` |
| `‖d A‖` | `√ (plaqEnergy (curlValueCovariant U A))` |
| `‖A‖` | `√ (bondEnergy A)` |

**THE RESULT** (§3, `hraw_lattice`), with `α₁ := frobSupBond U`:

```
√(∑_{P coarse} ‖∂₁'(Q_ℓ(U)A)(P)‖²)
    ≤  (1/√ℓ)·√(plaqEnergy (d_U A))  +  (36√2/√ℓ)·α₁·√(bondEnergy A)
```

so `σ₀ = ℓ^{-1/2}` and `c = 36√2·α₁·ℓ^{-1/2}`.

**EVERY FACTOR OF `36√2`, COUNTED** (nothing fitted; §3's docstring repeats this next to the proof):

* `4√2` — the fine curl-drift `L²` constant `√32` of `RegularUPerturbation.norm_curlDrift_L2_le_sup`
  (its own `32 = 8·(2+2)`), entering multiplied by the flat `σ₀ = 1/√ℓ` because it is a correction to
  the RIGHT-hand side of the flat bound;
* `32√2 = 4√2 · 8` — the coarse-curl operator norm `√32 = 4√2` (§2 here, `32 = 4 · (4·2)`: `4` from
  Cauchy–Schwarz over the four terms of the DEFINING four-term coarse curl, `4` terms, `2` the
  maximal direction-pair incidence `d−1` at `d = 3`) times the coarse-drift `L²` constant
  `√(64/ℓ) = 8/√ℓ` of `RegularUQChain.coarseDriftEnergy_le`;
* `4√2 + 32√2 = 36√2`, and both terms carry the same `ℓ^{-1/2}`.

**The three lemmas the predecessor named, as built here:**

1. §1 `sqrt_sum_sq_add_le` — the `L²` (Minkowski) triangle inequality on `Fintype`-indexed sums of
   normed-group-valued fields.  Configuration-free, `U`-free, lattice-free.
2. §1, the SAME lemma at the second application site (`sqrt_sum_sq_sub_le`, its `−` form): once on
   the COARSE-plaquette index (`coarseCurl(Q_U) = coarseCurl(Q_1) + coarseCurl(Q_U − Q_1)`), once on
   the FINE-plaquette index (`d_1 = d_U − curlDrift`).
3. §2 `coarseCurl_energy_le` — the operator-norm bound `∑_P ‖∂₁'B(P)‖² ≤ 32·coarseBondEnergy B`, via
   the coarse-plaquette incidence count, in the style of `StokesLattice.sum_window_incidence` and
   reusing `RegularUPerturbation`'s already-proved direction-fibre counts (LAW-19).

The vacuity guards, the witnesses and the junk substitutions are in the companion file
`StokesHrawWitness.lean` (split off so this file's import cone is exactly `StokesLattice`'s).

Nothing here is installed in `formal/`; nothing enters `Spine.lean`'s import cone.
-/

namespace AdalyFormal.StokesHraw

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM)
open AdalyFormal.Balaban.CoarseCurl (CoarsePlaquette coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.CoarseShiftCovariance (coarseShift_injective)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy frobSupBond curlDrift
  curlDrift_apply norm_curlDrift_L2_le_sup frobSupBond_nonneg bondEnergy_nonneg plaqEnergy_nonneg
  sum_dir_proj1_le sum_dir_proj2_le)
open AdalyFormal.Balaban.RegularUQChain (coarseDriftEnergy_le)
open AdalyFormal.StokesCommu.Lattice (coarseCurl_energy_le_flat)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE `L²` TRIANGLE INEQUALITY ON `Fintype` SUMS (missing lemmas 1 and 2)

Configuration-free, `U`-free, lattice-free: a statement about an arbitrary finite index type and an
arbitrary normed additive group.  It is Minkowski, obtained by transporting the sum into Mathlib's
`PiLp 2` carrier — the SAME carrier `RegularUPerturbation.PlaqL2` already uses for plaquettes
(LAW-19: the promotion idiom is reused, not re-invented). -/

/-- `√(∑ ‖f i‖²) = ‖f‖` in the `PiLp 2` carrier — the transport step, isolated. -/
theorem sqrt_sum_sq_eq_norm {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    (f : ι → E) :
    Real.sqrt (∑ i, ‖f i‖ ^ 2) = ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : ι => E))‖ :=
  (PiLp.norm_eq_of_L2 (WithLp.toLp 2 f)).symm

/-- **MISSING LEMMA 1 — the `L²` triangle inequality on `Finset` sums.**
`√(∑ ‖f i + g i‖²) ≤ √(∑ ‖f i‖²) + √(∑ ‖g i‖²)`.  No configuration, no `U`, no lattice. -/
theorem sqrt_sum_sq_add_le {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    (f g : ι → E) :
    Real.sqrt (∑ i, ‖f i + g i‖ ^ 2)
      ≤ Real.sqrt (∑ i, ‖f i‖ ^ 2) + Real.sqrt (∑ i, ‖g i‖ ^ 2) := by
  have heq : (WithLp.toLp 2 (fun i => f i + g i) : PiLp 2 (fun _ : ι => E))
      = WithLp.toLp 2 f + WithLp.toLp 2 g := rfl
  rw [sqrt_sum_sq_eq_norm (fun i => f i + g i), sqrt_sum_sq_eq_norm f, sqrt_sum_sq_eq_norm g, heq]
  exact norm_add_le _ _

/-- **MISSING LEMMA 2 — the same at the second application site**, in the `−` form the fine-plaquette
application needs (`d_1 A = d_U A − curlDrift U A`). -/
theorem sqrt_sum_sq_sub_le {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    (f g : ι → E) :
    Real.sqrt (∑ i, ‖f i - g i‖ ^ 2)
      ≤ Real.sqrt (∑ i, ‖f i‖ ^ 2) + Real.sqrt (∑ i, ‖g i‖ ^ 2) := by
  have h := sqrt_sum_sq_add_le f (fun i => -g i)
  calc Real.sqrt (∑ i, ‖f i - g i‖ ^ 2)
      = Real.sqrt (∑ i, ‖f i + (-g i)‖ ^ 2) := by
        congr 1
        exact Finset.sum_congr rfl (fun i _ => by rw [sub_eq_add_neg])
    _ ≤ Real.sqrt (∑ i, ‖f i‖ ^ 2) + Real.sqrt (∑ i, ‖(-g i)‖ ^ 2) := h
    _ = Real.sqrt (∑ i, ‖f i‖ ^ 2) + Real.sqrt (∑ i, ‖g i‖ ^ 2) := by
        congr 2
        exact Finset.sum_congr rfl (fun i _ => by rw [norm_neg])

/-! ## §2 — THE COARSE-CURL OPERATOR NORM (missing lemma 3)

`∑_{P coarse} ‖∂₁'B(P)‖² ≤ 32 · ∑_{b coarse} ‖B b‖²`, i.e. `‖∂₁'‖ ≤ √32 = 4√2`.

The count, stated before the code and re-derived in it:

* the DEFINING object is `ThirdLevelStokes.coarseCurlSuTwo`, whose body is exactly the four-term
  signed combination `B(y,μ) + B(y+ℓe_μ,ν) − B(y+ℓe_ν,μ) − B(y,ν)` — **four** terms, and the
  enumeration below runs over exactly those four, read off the definition;
* Cauchy–Schwarz on four terms costs a factor **4**;
* each of the four term-sums is `≤ 2 · coarseBondEnergy B`, the **2** being the direction-pair
  incidence `#{ν : μ < ν} ≤ d−1 = 2` (resp. `#{μ : μ < ν} ≤ 2`) already proved in
  `RegularUPerturbation.sum_dir_proj1_le`/`sum_dir_proj2_le` — reused, not rebuilt (LAW-19);
* the two SHIFTED term-sums additionally need that `coarseShift (·) ℓ μ` is a bijection OF THE
  COARSE SITE SUBTYPE, which §2a proves from `coarseShift_injective` plus finiteness;
* `4 · (4 · 2) = 32`. -/

/-- **Coarse-bond `L²` energy**, general `ell`.  (`ExtentUniformCoercivity.coarseEnergy` is the same
sum but is fixed at `ell = 2`; §4 records that the two agree there, so this is a generalisation and
not a second object.) -/
noncomputable def coarseBondEnergy {ell : ℕ} (B : CoarseBond L ell → SuTwo) : ℝ :=
  ∑ b : CoarseBond L ell, ‖B b‖ ^ 2

theorem coarseBondEnergy_nonneg {ell : ℕ} (B : CoarseBond L ell → SuTwo) :
    0 ≤ coarseBondEnergy B :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Slice decomposition of the coarse-bond energy by direction. -/
theorem coarseBondEnergy_eq_slices {ell : ℕ} (B : CoarseBond L ell → SuTwo) :
    coarseBondEnergy B
      = ∑ ρ : Fin 3, ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}, ‖B (y, ρ)‖ ^ 2 := by
  unfold coarseBondEnergy
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-! ### §2a — the coarse shift is a bijection of the coarse-site subtype -/

/-- `coarseShift` lifted to the coarse-site subtype (the membership proof is exactly the one
`coarseCurlSuTwo`'s body uses, so the two are definitionally the same site). -/
noncomputable def coarseShiftSub {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (μ : Fin 3)
    (y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) :
    {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell} :=
  ⟨coarseShift y.1 ell μ, coarseShift_mem_coarseLattice hdvd y.2 μ⟩

theorem coarseShiftSub_injective {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (μ : Fin 3) :
    Function.Injective (coarseShiftSub (L := L) hdvd μ) := by
  intro a b h
  exact Subtype.ext (coarseShift_injective ell μ (congrArg Subtype.val h))

theorem coarseShiftSub_bijective {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (μ : Fin 3) :
    Function.Bijective (coarseShiftSub (L := L) hdvd μ) :=
  Finite.injective_iff_bijective.mp (coarseShiftSub_injective hdvd μ)

/-- Reindexing the coarse-site sum along the shift — the coarse analogue of the
`periodicLatticeShiftEquiv` step inside `RegularUPerturbation.sum_nbr1_sq_le`. -/
theorem sum_coarseShiftSub {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (μ : Fin 3)
    (w : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell} → ℝ) :
    ∑ y, w (coarseShiftSub hdvd μ y) = ∑ y, w y :=
  (coarseShiftSub_bijective hdvd μ).sum_comp w

/-! ### §2b — the four term-sums, one per term of the DEFINING four-term body -/

/-- Term 1 of the definition, `B(y, μ)`: `∑_P ‖B(P.1, μ(P))‖² ≤ 2 · coarseBondEnergy B`. -/
theorem sum_term_base_dir1_le {ell : ℕ} (B : CoarseBond L ell → SuTwo) :
    (∑ P : CoarsePlaquette L ell, ‖B (P.1, P.2.1.1)‖ ^ 2) ≤ 2 * coarseBondEnergy B := by
  have key : (∑ P : CoarsePlaquette L ell, ‖B (P.1, P.2.1.1)‖ ^ 2)
      = ∑ dir : PeriodicPlaquetteDirections,
          ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}, ‖B (y, dir.1.1)‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [key, coarseBondEnergy_eq_slices B]
  refine le_trans (sum_dir_proj1_le
    (fun ρ => ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}, ‖B (y, ρ)‖ ^ 2)
    (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) ?_
  have hnn : (0 : ℝ)
      ≤ ∑ ρ : Fin 3, ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
          ‖B (y, ρ)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  linarith

/-- Term 4 of the definition, `B(y, ν)`: `∑_P ‖B(P.1, ν(P))‖² ≤ 2 · coarseBondEnergy B`. -/
theorem sum_term_base_dir2_le {ell : ℕ} (B : CoarseBond L ell → SuTwo) :
    (∑ P : CoarsePlaquette L ell, ‖B (P.1, P.2.1.2)‖ ^ 2) ≤ 2 * coarseBondEnergy B := by
  have key : (∑ P : CoarsePlaquette L ell, ‖B (P.1, P.2.1.2)‖ ^ 2)
      = ∑ dir : PeriodicPlaquetteDirections,
          ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}, ‖B (y, dir.1.2)‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [key, coarseBondEnergy_eq_slices B]
  refine le_trans (sum_dir_proj2_le
    (fun ρ => ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}, ‖B (y, ρ)‖ ^ 2)
    (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) ?_
  have hnn : (0 : ℝ)
      ≤ ∑ ρ : Fin 3, ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
          ‖B (y, ρ)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  linarith

/-- Term 2 of the definition, `B(y + ℓe_μ, ν)`: the shift is absorbed by §2a's bijection, then the
`ν`-fibre count applies. -/
theorem sum_term_shift1_le {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) :
    (∑ P : CoarsePlaquette L ell, ‖B (coarseShiftSub hdvd P.2.1.1 P.1, P.2.1.2)‖ ^ 2)
      ≤ 2 * coarseBondEnergy B := by
  have key : (∑ P : CoarsePlaquette L ell, ‖B (coarseShiftSub hdvd P.2.1.1 P.1, P.2.1.2)‖ ^ 2)
      = ∑ dir : PeriodicPlaquetteDirections,
          ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}, ‖B (y, dir.1.2)‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun dir _ => ?_)
    exact sum_coarseShiftSub hdvd dir.1.1 (fun y => ‖B (y, dir.1.2)‖ ^ 2)
  rw [key, coarseBondEnergy_eq_slices B]
  refine le_trans (sum_dir_proj2_le
    (fun ρ => ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}, ‖B (y, ρ)‖ ^ 2)
    (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) ?_
  have hnn : (0 : ℝ)
      ≤ ∑ ρ : Fin 3, ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
          ‖B (y, ρ)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  linarith

/-- Term 3 of the definition, `B(y + ℓe_ν, μ)`. -/
theorem sum_term_shift2_le {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) :
    (∑ P : CoarsePlaquette L ell, ‖B (coarseShiftSub hdvd P.2.1.2 P.1, P.2.1.1)‖ ^ 2)
      ≤ 2 * coarseBondEnergy B := by
  have key : (∑ P : CoarsePlaquette L ell, ‖B (coarseShiftSub hdvd P.2.1.2 P.1, P.2.1.1)‖ ^ 2)
      = ∑ dir : PeriodicPlaquetteDirections,
          ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}, ‖B (y, dir.1.1)‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun dir _ => ?_)
    exact sum_coarseShiftSub hdvd dir.1.2 (fun y => ‖B (y, dir.1.1)‖ ^ 2)
  rw [key, coarseBondEnergy_eq_slices B]
  refine le_trans (sum_dir_proj1_le
    (fun ρ => ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}, ‖B (y, ρ)‖ ^ 2)
    (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) ?_
  have hnn : (0 : ℝ)
      ≤ ∑ ρ : Fin 3, ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
          ‖B (y, ρ)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  linarith

/-- Cauchy–Schwarz on the four terms: `‖a+b−c−d‖² ≤ 4(‖a‖²+‖b‖²+‖c‖²+‖d‖²)`.  The `4` is the number
of terms in the defining body, not a fitted constant. -/
theorem norm_four_term_sq_le (a b c d : SuTwo) :
    ‖a + b - c - d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have htri : ‖a + b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    calc ‖a + b - c - d‖ ≤ ‖a + b - c‖ + ‖d‖ := norm_sub_le _ _
      _ ≤ (‖a + b‖ + ‖c‖) + ‖d‖ := by
          have := norm_sub_le (a + b) c
          linarith
      _ ≤ ((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖ := by
          have := norm_add_le a b
          linarith
  -- Cauchy-Schwarz on the four scalars: (A+B+C+D)^2 <= 4(A^2+B^2+C^2+D^2)
  have hCS : (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) ^ 2
      ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖a‖ - ‖d‖),
      sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖b‖ - ‖d‖), sq_nonneg (‖c‖ - ‖d‖)]
  have hmono : ‖a + b - c - d‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hnn : (0 : ℝ) ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 := by positivity
  linarith

/-- **MISSING LEMMA 3 — THE COARSE-CURL OPERATOR NORM.**
`∑_{P coarse} ‖∂₁'B(P)‖² ≤ 32 · coarseBondEnergy B`, i.e. `‖∂₁'‖ ≤ 4√2`.
`32 = 4 · (4 · 2)`: Cauchy–Schwarz over the four terms of the defining body (`4`), four term-sums
(`4`), each at direction-incidence `≤ d − 1 = 2`.  Configuration-free and `U`-free; `ell` does not
appear in the constant. -/
theorem coarseCurl_energy_le {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) :
    (∑ P : CoarsePlaquette L ell, ‖coarseCurlSuTwo hdvd B P‖ ^ 2) ≤ 32 * coarseBondEnergy B := by
  have hstep : (∑ P : CoarsePlaquette L ell, ‖coarseCurlSuTwo hdvd B P‖ ^ 2)
      ≤ ∑ P : CoarsePlaquette L ell,
          4 * (‖B (P.1, P.2.1.1)‖ ^ 2
             + ‖B (coarseShiftSub hdvd P.2.1.1 P.1, P.2.1.2)‖ ^ 2
             + ‖B (coarseShiftSub hdvd P.2.1.2 P.1, P.2.1.1)‖ ^ 2
             + ‖B (P.1, P.2.1.2)‖ ^ 2) := by
    refine Finset.sum_le_sum (fun P _ => ?_)
    exact norm_four_term_sq_le _ _ _ _
  refine hstep.trans ?_
  rw [← Finset.mul_sum]
  have hsplit : (∑ P : CoarsePlaquette L ell,
        (‖B (P.1, P.2.1.1)‖ ^ 2
       + ‖B (coarseShiftSub hdvd P.2.1.1 P.1, P.2.1.2)‖ ^ 2
       + ‖B (coarseShiftSub hdvd P.2.1.2 P.1, P.2.1.1)‖ ^ 2
       + ‖B (P.1, P.2.1.2)‖ ^ 2))
      = ((∑ P : CoarsePlaquette L ell, ‖B (P.1, P.2.1.1)‖ ^ 2)
       + (∑ P : CoarsePlaquette L ell, ‖B (coarseShiftSub hdvd P.2.1.1 P.1, P.2.1.2)‖ ^ 2))
       + ((∑ P : CoarsePlaquette L ell, ‖B (coarseShiftSub hdvd P.2.1.2 P.1, P.2.1.1)‖ ^ 2)
       + (∑ P : CoarsePlaquette L ell, ‖B (P.1, P.2.1.2)‖ ^ 2)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun P _ => by ring)
  rw [hsplit]
  have h1 := sum_term_base_dir1_le (L := L) (ell := ell) B
  have h2 := sum_term_shift1_le (L := L) (ell := ell) hdvd B
  have h3 := sum_term_shift2_le (L := L) (ell := ell) hdvd B
  have h4 := sum_term_base_dir2_le (L := L) (ell := ell) B
  have hnn : (0 : ℝ) ≤ coarseBondEnergy B := coarseBondEnergy_nonneg B
  linarith

/-- The `−`-form used in §3: the coarse curl of a DIFFERENCE of coarse bond fields. -/
theorem coarseCurlSuTwo_sub {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B1 B2 : CoarseBond L ell → SuTwo) (p : CoarsePlaquette L ell) :
    coarseCurlSuTwo hdvd (fun b => B1 b - B2 b) p
      = coarseCurlSuTwo hdvd B1 p - coarseCurlSuTwo hdvd B2 p := by
  simp only [coarseCurlSuTwo]
  abel

/-! ## §3 — THE ASSEMBLY: `hraw` AT THE LATTICE -/

/-- The coarse-bond drift energy, with the sign order of `coarseDriftEnergy_le` reversed to the one
§3 needs (`Q_U − Q_1` rather than `Q_1 − Q_U`).  `norm_sub_rev`, applied under the sum: the two
orders are NOT assumed equal, they are proved equal termwise. -/
theorem coarseBondEnergy_drift_le {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    coarseBondEnergy (fun b : CoarseBond L ell =>
        lineCoarseRestrictCovLM U ell A b - lineCoarseRestrictCovLM (trivialU L) ell A b)
      ≤ (64 / (ell : ℝ)) * frobSupBond U ^ 2 * bondEnergy A := by
  have hrev : coarseBondEnergy (fun b : CoarseBond L ell =>
        lineCoarseRestrictCovLM U ell A b - lineCoarseRestrictCovLM (trivialU L) ell A b)
      = ∑ b : CoarseBond L ell,
          ‖lineCoarseRestrictCov (trivialU L) ell A b - lineCoarseRestrictCov U ell A b‖ ^ 2 := by
    unfold coarseBondEnergy
    exact Finset.sum_congr rfl (fun b _ => by rw [norm_sub_rev]; rfl)
  rw [hrev]
  refine le_trans (coarseDriftEnergy_le U hell hdvd A) ?_
  have hnn : (0 : ℝ) ≤ (1 / (ell : ℝ)) * (frobSupBond U ^ 2 * bondEnergy A) :=
    mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (bondEnergy_nonneg A))
  -- `ring_nf` first: `linarith` treats `K / ell * α₁^2 * bondEnergy A` as a SINGLE atom (the
  -- numeral sits inside the division).  Normalising factors it out, so a WEAKENING of the stated
  -- constant closes from `hnn` alone and the `64 -> 65` mutation is a genuine must-not-fire control.
  ring_nf at hnn ⊢
  linarith [hnn]

/-- **`hraw` AT THE LATTICE — THE DELIVERABLE.**

`√(∑_P ‖∂₁'(Q_ℓ(U)A)(P)‖²) ≤ (1/√ℓ)·√(plaqEnergy (d_U A)) + (36√2/√ℓ)·α₁·√(bondEnergy A)`,
`α₁ = frobSupBond U`.

This is exactly `StokesRestricted.perturbed_chain_at_minimizer`'s and
`gamma_floor_at_minimizer`'s hypothesis `hraw : ‖d₁(Q A)‖ ≤ σ₀‖d A‖ + c‖A‖`, with

  `σ₀ = ℓ^{-1/2}`  and  `c = 36√2 · α₁ · ℓ^{-1/2}` .

**Every factor, counted.**  `4√2 = √32` is `norm_curlDrift_L2_le_sup`'s fine curl-drift constant and
enters against the flat `σ₀ = 1/√ℓ`.  `32√2 = (4√2)·8` is §2's coarse-curl operator norm `√32 = 4√2`
times `coarseDriftEnergy_le`'s `√(64/ℓ) = 8/√ℓ`.  `4√2 + 32√2 = 36√2`.  No constant is fitted; the
uniform-rescale test is §4's `hraw_lattice_rescale_flat` / the `M` battery.

The bound is uniform in the extent `L`, carries no RG step `k`, is uniform over ALL background
configurations `U` (the `U`-dependence is entirely in `α₁`), and IMPROVES as `ℓ` grows. -/
theorem hraw_lattice {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    Real.sqrt (∑ P : CoarsePlaquette L ell,
        ‖coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM U ell A) P‖ ^ 2)
      ≤ (1 / Real.sqrt (ell : ℝ)) * Real.sqrt (plaqEnergy (curlValueCovariant U A))
        + (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * frobSupBond U * Real.sqrt (bondEnergy A) := by
  classical
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hsq : (0 : ℝ) < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr hellR
  set α : ℝ := frobSupBond U with hα
  have hα0 : 0 ≤ α := frobSupBond_nonneg U
  set EA : ℝ := Real.sqrt (bondEnergy A) with hEA
  have hEA0 : 0 ≤ EA := Real.sqrt_nonneg _
  -- abbreviations for the three coarse bond fields
  set Bu : CoarseBond L ell → SuTwo := fun b => lineCoarseRestrictCovLM U ell A b with hBu
  set B1 : CoarseBond L ell → SuTwo :=
    fun b => lineCoarseRestrictCovLM (trivialU L) ell A b with hB1
  set Dq : CoarseBond L ell → SuTwo := fun b => Bu b - B1 b with hDq
  -- (A) split the coarse curl of `Q_U` into flat + coarse drift, then Minkowski (§1)
  have hptwise : ∀ P : CoarsePlaquette L ell,
      coarseCurlSuTwo hdvd Bu P = coarseCurlSuTwo hdvd B1 P + coarseCurlSuTwo hdvd Dq P := by
    intro P
    rw [hDq, coarseCurlSuTwo_sub hdvd Bu B1 P]
    abel
  have hA : Real.sqrt (∑ P : CoarsePlaquette L ell, ‖coarseCurlSuTwo hdvd Bu P‖ ^ 2)
      ≤ Real.sqrt (∑ P : CoarsePlaquette L ell, ‖coarseCurlSuTwo hdvd B1 P‖ ^ 2)
        + Real.sqrt (∑ P : CoarsePlaquette L ell, ‖coarseCurlSuTwo hdvd Dq P‖ ^ 2) := by
    have := sqrt_sum_sq_add_le (fun P : CoarsePlaquette L ell => coarseCurlSuTwo hdvd B1 P)
      (fun P : CoarsePlaquette L ell => coarseCurlSuTwo hdvd Dq P)
    rw [Finset.sum_congr rfl (fun P _ => by rw [hptwise P] :
      ∀ P ∈ (Finset.univ : Finset (CoarsePlaquette L ell)),
        ‖coarseCurlSuTwo hdvd Bu P‖ ^ 2 = ‖coarseCurlSuTwo hdvd B1 P + coarseCurlSuTwo hdvd Dq P‖ ^ 2)]
    exact this
  -- (B) the flat term: `coarseCurl_energy_le_flat`, under a square root
  have hB : Real.sqrt (∑ P : CoarsePlaquette L ell, ‖coarseCurlSuTwo hdvd B1 P‖ ^ 2)
      ≤ (1 / Real.sqrt (ell : ℝ))
          * Real.sqrt (plaqEnergy (curlValueCovariant (trivialU L) A)) := by
    have hflat := coarseCurl_energy_le_flat (L := L) (ell := ell) hell hdvd A
    have h := Real.sqrt_le_sqrt hflat
    refine h.trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity)]
    congr 1
    rw [one_div, one_div, ← Real.sqrt_inv]
  -- (C) the fine curl at `U = 1` against the fine curl at `U`, via §1's `−` form
  have hCptwise : ∀ p : PeriodicLatticePlaquette L,
      curlValueCovariant (trivialU L) A p = curlValueCovariant U A p - curlDrift U A p := by
    intro p
    rw [curlDrift]
    simp only [Pi.sub_apply]
    abel
  have hC : Real.sqrt (plaqEnergy (curlValueCovariant (trivialU L) A))
      ≤ Real.sqrt (plaqEnergy (curlValueCovariant U A))
        + Real.sqrt (plaqEnergy (curlDrift U A)) := by
    have := sqrt_sum_sq_sub_le (fun p : PeriodicLatticePlaquette L => curlValueCovariant U A p)
      (fun p : PeriodicLatticePlaquette L => curlDrift U A p)
    unfold plaqEnergy
    rw [Finset.sum_congr rfl (fun p _ => by rw [hCptwise p] :
      ∀ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette L)),
        ‖curlValueCovariant (trivialU L) A p‖ ^ 2
          = ‖curlValueCovariant U A p - curlDrift U A p‖ ^ 2)]
    exact this
  -- (D) the fine drift bound
  have hD : Real.sqrt (plaqEnergy (curlDrift U A)) ≤ 4 * Real.sqrt 2 * α * EA :=
    norm_curlDrift_L2_le_sup U A
  -- (E) the coarse drift term: §2's operator norm, then `coarseDriftEnergy_le`
  have hE : Real.sqrt (∑ P : CoarsePlaquette L ell, ‖coarseCurlSuTwo hdvd Dq P‖ ^ 2)
      ≤ (32 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * α * EA := by
    have hop := coarseCurl_energy_le (L := L) (ell := ell) hdvd Dq
    have hdr := coarseBondEnergy_drift_le (L := L) (ell := ell) hell hdvd U A
    have hchain : (∑ P : CoarsePlaquette L ell, ‖coarseCurlSuTwo hdvd Dq P‖ ^ 2)
        ≤ 32 * ((64 / (ell : ℝ)) * α ^ 2 * bondEnergy A) := by
      refine hop.trans ?_
      exact mul_le_mul_of_nonneg_left hdr (by norm_num)
    have h := Real.sqrt_le_sqrt hchain
    refine h.trans (le_of_eq ?_)
    have hval : (32 : ℝ) * ((64 / (ell : ℝ)) * α ^ 2 * bondEnergy A)
        = ((32 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * α) ^ 2 * bondEnergy A := by
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hs : Real.sqrt (ell : ℝ) ^ 2 = (ell : ℝ) := Real.sq_sqrt (le_of_lt hellR)
      have hexp : ((32 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * α) ^ 2
          = (1024 * (Real.sqrt 2 ^ 2) / (Real.sqrt (ell : ℝ) ^ 2)) * α ^ 2 := by
        field_simp; ring
      rw [hexp, h2, hs]
      field_simp
      ring
    rw [hval, Real.sqrt_mul (by positivity), hEA]
    congr 1
    exact Real.sqrt_sq (by positivity)
  -- assemble
  have hinv : (1 / Real.sqrt (ell : ℝ)) * (4 * Real.sqrt 2 * α * EA)
      + (32 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * α * EA
      = 36 * Real.sqrt 2 / Real.sqrt (ell : ℝ) * α * EA := by
    field_simp
    ring
  -- the monomial `m = √2·(√ell)⁻¹·α·EA` is nonnegative; supplied so that a WEAKENING of the
  -- stated constant (36 -> anything larger) still closes, making that mutation a genuine control
  have hmono : (0 : ℝ) ≤ Real.sqrt 2 / Real.sqrt (ell : ℝ) * α * EA := by positivity
  have hstep : Real.sqrt (∑ P : CoarsePlaquette L ell, ‖coarseCurlSuTwo hdvd B1 P‖ ^ 2)
      ≤ (1 / Real.sqrt (ell : ℝ)) * Real.sqrt (plaqEnergy (curlValueCovariant U A))
        + (1 / Real.sqrt (ell : ℝ)) * (4 * Real.sqrt 2 * α * EA) := by
    refine hB.trans ?_
    have hpos : (0 : ℝ) ≤ 1 / Real.sqrt (ell : ℝ) := by positivity
    calc (1 / Real.sqrt (ell : ℝ)) * Real.sqrt (plaqEnergy (curlValueCovariant (trivialU L) A))
        ≤ (1 / Real.sqrt (ell : ℝ)) * (Real.sqrt (plaqEnergy (curlValueCovariant U A))
            + 4 * Real.sqrt 2 * α * EA) := by
          exact mul_le_mul_of_nonneg_left (hC.trans (by linarith [hD])) hpos
      _ = (1 / Real.sqrt (ell : ℝ)) * Real.sqrt (plaqEnergy (curlValueCovariant U A))
            + (1 / Real.sqrt (ell : ℝ)) * (4 * Real.sqrt 2 * α * EA) := by ring
  -- `ring_nf` first: `linarith` treats `K * √2 / √ell * α * EA` as a SINGLE atom (the numeral is
  -- buried inside the division), so without normalisation it cannot relate two different `K`.
  -- Normalising factors the numeral out and makes the step linear in the monomial
  -- `m = √2·(√ell)⁻¹·α·EA`, which `hmono` bounds below by `0`.
  ring_nf at hA hstep hE hinv hmono ⊢
  linarith [hA, hstep, hE, hinv, hmono]

#print axioms coarseBondEnergy
#print axioms coarseShiftSub
#print axioms coarseBondEnergy_nonneg
#print axioms coarseBondEnergy_eq_slices
#print axioms coarseShiftSub_injective
#print axioms sqrt_sum_sq_eq_norm
#print axioms sqrt_sum_sq_add_le
#print axioms sqrt_sum_sq_sub_le
#print axioms coarseShiftSub_bijective
#print axioms sum_coarseShiftSub
#print axioms sum_term_base_dir1_le
#print axioms sum_term_base_dir2_le
#print axioms sum_term_shift1_le
#print axioms sum_term_shift2_le
#print axioms norm_four_term_sq_le
#print axioms coarseCurl_energy_le
#print axioms coarseCurlSuTwo_sub
#print axioms coarseBondEnergy_drift_le
#print axioms hraw_lattice

end AdalyFormal.StokesHraw
