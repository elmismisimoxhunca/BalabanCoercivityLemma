/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.Lemma24GeneralEll

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
# THE LOCALIZED (per-cube) FLAT CMP96 LEMMA 2.4.

`Lemma24GeneralEll.lemma24_general_ell` is a floor whose three sums run over the WHOLE torus. The
summation step `GaugeInvLocalize.localized_floor_sums_of_gauged` consumes a floor whose three sums
run over ONE CUBE. This module supplies the flat (`U = 1`, real-fibre) half of that per-cube floor.

## What a "cube" is here

A cube is a `Finset Y` of COARSE SITES (block centres, `CoarseLattice L ell` members). Everything
else is derived from `Y` by the geometry, never posited:

* `bondsOn Y`  — the fine bonds whose BASE site lies in a block of `Y` (`GeomScratch.bondsBasedIn`);
* `coarseOn Y` — the coarse bonds based in `Y`, i.e. `Y ×ˢ univ`;
* `plaqsOn Y`  — the fine plaquettes whose BASE site lies in a block of `Y`.

Each of these families is PAIRWISE DISJOINT in `Y` and, at `Y = univ`, is the whole index type
(`bondsOn_univ`, `coarseOn_univ`, `plaqsOn_univ`), so nothing can drift between the localized and
the global statements.

## THE RESULT, and the exact price of localization

`local_lemma24_flat`: for every `ell ≥ 2`, compatible torus, `(2.121)`-admissible `B`, and EVERY
`Y : Finset (CSite L ell)`,

>  `(1/180)·ell⁻⁵·∑_{b ∈ bondsOn Y} B(b)²
>       ≤ ell·∑_{c ∈ coarseOn Y} (Q₁B)(c)² + ∑_{p ∈ plaqsOn (tilde Y)} (∂₁B)(p)²`

with **the SAME constant `1/180` as the global theorem** — nothing is lost to localization except
the index set on the LAST term, where `tilde Y = Y ∪ {y + ell·e_μ : y ∈ Y, μ}` is the source's own
enlarged cube `□̃`, here PROVED to be exactly ONE BLOCK LAYER in each of the three POSITIVE
directions and no more.

At `Y = univ` the statement is the global theorem (`local_lemma24_flat_univ`), so the localization
is a genuine strengthening rather than a differently-scaled restatement.

## WHERE THE ENLARGEMENT COMES FROM (it is one term, not an atmosphere)

Of the five ingredients, four are exactly local:

| ingredient | localized form | leakage |
|---|---|---|
| `Lemma24GeneralEll.perC_bond` | already per-coarse-bond | NONE |
| FACT 1 (`GeomScratch.bondsBasedIn_split`) | already per-block, an EQUALITY | NONE |
| FACT 4 (region curl) | `local_fact4`, per-block, multiplicity `3` | NONE |
| `BlockPoincare.block_poincare` (`(2.123)`) | already per-block | NONE |
| FACT 2 (`boundaryCorr`) | `local_fact2` | **ONE block layer**: `boundaryCorr(y,μ)` reads the block at `y + ell·e_μ` |

`boundaryCorr B y ell μ = blockBondEnergy(y) + blockBondEnergy(coarseShift y ell μ)` — the second
summand is the whole leak, and it is why `□̃` exists in the source. Everything else is bookkeeping.

**Multiplicity `3` instead of the global `2`.** The global FACT 4 routes through
`Lemma24Assembly.slabCurlEnergy` and gets `∑_c regionCurl ≤ 2·P`. The localized route here bounds
each `regionCurlEnergy(y,μ)` by the FULL block-based plaquette energy and then sums the three `μ`,
giving `3` rather than `2`. **The constant `1/180` survives that loss**: the assembly needs
`9·t² + 3·t³ ≤ 18·t⁵` where the global proof needed `6·t² + 3·t³ ≤ 18·t⁵`, and both hold at
`t ≥ 2` with room (`60 ≤ 576` at `t = 2`). `flat_slack_at_two` pins that arithmetic.
-/

namespace AdalyFormal.Balaban.LocalizedEstimates

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.BlockPoincare
open AdalyFormal.Balaban.BlockPoincareLemma24
open AdalyFormal.Balaban.CrossSectionField
open AdalyFormal.Balaban.CoarseCurl
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.Lemma24GeneralEll
open GeomScratch

variable {L : PeriodicLatticeExtent} {ell : ℕ}

/-! ## §1 — CUBES, AND THE THREE INDEX FAMILIES THEY DETERMINE -/

/-- A COARSE SITE: a block centre. `CoarseBond L ell = CSite L ell × Fin 3` definitionally
(`LatticeOperators.CoarseBond`), which is what makes `coarseOn` a plain product. -/
abbrev CSite (L : PeriodicLatticeExtent) (ell : ℕ) :=
  {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}

/-- The plaquettes whose BASE site lies in the block `B(y)`. The base-site convention is forced:
`CrossSectionField.regionCurlEnergy` and `BlockPoincare.plaqsInBlock` both read plaquettes based in
the block, so this is the smallest family containing both. -/
def plaqsBasedIn (y : PeriodicLatticeSite L) (ell : ℕ) : Finset (PeriodicLatticePlaquette L) :=
  Finset.univ.filter (fun p => p.1 ∈ blockOf y ell)

theorem mem_plaqsBasedIn {y : PeriodicLatticeSite L} {p : PeriodicLatticePlaquette L} :
    p ∈ plaqsBasedIn y ell ↔ p.1 ∈ blockOf y ell := by
  simp [plaqsBasedIn]

/-- `{p ⊂ B(y)} ⊆ {p based in B(y)}`. -/
theorem plaqsInBlock_subset_basedIn (y : PeriodicLatticeSite L) (ell : ℕ) :
    plaqsInBlock y ell ⊆ plaqsBasedIn y ell := by
  intro p hp
  rw [mem_plaqsBasedIn]
  exact (mem_plaqsInBlock.mp hp).1

/-- The fine bonds of the cube `Y`. -/
def bondsOn (Y : Finset (CSite L ell)) : Finset (Bond L) :=
  Y.biUnion (fun y => bondsBasedIn y.1 ell)

/-- The fine plaquettes of the cube `Y`. -/
def plaqsOn (Y : Finset (CSite L ell)) : Finset (PeriodicLatticePlaquette L) :=
  Y.biUnion (fun y => plaqsBasedIn y.1 ell)

/-- The coarse bonds of the cube `Y`. -/
def coarseOn (Y : Finset (CSite L ell)) : Finset (CoarseBond L ell) :=
  Y ×ˢ (Finset.univ : Finset (Fin 3))

theorem mem_coarseOn {Y : Finset (CSite L ell)} {c : CoarseBond L ell} :
    c ∈ coarseOn Y ↔ c.1 ∈ Y := by
  simp [coarseOn]

/-! ### The three families are pairwise disjoint in `Y`, and exhaust at `Y = univ`. -/

theorem bondsBasedIn_disj (Y : Finset (CSite L ell)) :
    (Y : Set (CSite L ell)).PairwiseDisjoint (fun y => bondsBasedIn y.1 ell) := by
  intro y _ y' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro b hby hby'
  simp only [bondsBasedIn, Finset.mem_filter, Finset.mem_univ, true_and] at hby hby'
  exact hne (Subtype.ext (coarseLattice_unique ell y.2 y'.2 hby hby'))

theorem plaqsBasedIn_disj (Y : Finset (CSite L ell)) :
    (Y : Set (CSite L ell)).PairwiseDisjoint (fun y => plaqsBasedIn y.1 ell) := by
  intro y _ y' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro p hpy hpy'
  rw [mem_plaqsBasedIn] at hpy hpy'
  exact hne (Subtype.ext (coarseLattice_unique ell y.2 y'.2 hpy hpy'))

theorem bondsOn_univ (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    bondsOn (Finset.univ : Finset (CSite L ell)) = (Finset.univ : Finset (Bond L)) := by
  refine Finset.eq_univ_of_forall (fun b => ?_)
  obtain ⟨y, hymem, hyblk⟩ := coarseLattice_exists ell hell hdvd b.1
  simp only [bondsOn, Finset.mem_biUnion]
  exact ⟨⟨y, hymem⟩, Finset.mem_univ _, by
    simp only [bondsBasedIn, Finset.mem_filter, Finset.mem_univ, true_and]; exact hyblk⟩

theorem plaqsOn_univ (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    plaqsOn (Finset.univ : Finset (CSite L ell))
      = (Finset.univ : Finset (PeriodicLatticePlaquette L)) := by
  refine Finset.eq_univ_of_forall (fun p => ?_)
  obtain ⟨y, hymem, hyblk⟩ := coarseLattice_exists ell hell hdvd p.1
  simp only [plaqsOn, Finset.mem_biUnion]
  exact ⟨⟨y, hymem⟩, Finset.mem_univ _, by rw [mem_plaqsBasedIn]; exact hyblk⟩

theorem coarseOn_univ :
    coarseOn (Finset.univ : Finset (CSite L ell)) = (Finset.univ : Finset (CoarseBond L ell)) := by
  ext c; simp [coarseOn]

/-! ## §2 — THE ENLARGED CUBE `□̃`, AND WHY IT IS EXACTLY ONE BLOCK LAYER -/

/-- The coarse shift, on coarse SITES. Well-typed by `coarseShift_mem_coarseLattice`. -/
def shiftC (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (y : CSite L ell) (μ : Fin 3) : CSite L ell :=
  ⟨coarseShift y.1 ell μ, coarseShift_mem_coarseLattice hdvd y.2 μ⟩

theorem shiftC_injective (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (μ : Fin 3) :
    Function.Injective (fun y : CSite L ell => shiftC hdvd y μ) := by
  intro y y' h
  have h1 : coarseShift y.1 ell μ = coarseShift y'.1 ell μ := congrArg Subtype.val h
  exact Subtype.ext (coarseShift_injective (L := L) (ell := ell) μ h1)

/-- **`□̃` — the enlarged cube.** `Y` together with the ONE block layer `Y + ell·e_μ` in each of the
three POSITIVE lattice directions. Nothing else is added: the negative directions are NOT needed,
because `boundaryCorr` reads only the forward neighbour. -/
def tilde (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (Y : Finset (CSite L ell)) : Finset (CSite L ell) :=
  Y ∪ (Finset.univ : Finset (Fin 3)).biUnion (fun μ => Y.image (fun y => shiftC hdvd y μ))

theorem subset_tilde (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (Y : Finset (CSite L ell)) :
    Y ⊆ tilde hdvd Y := Finset.subset_union_left

theorem shiftC_mem_tilde (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {Y : Finset (CSite L ell)}
    {y : CSite L ell} (hy : y ∈ Y) (μ : Fin 3) : shiftC hdvd y μ ∈ tilde hdvd Y := by
  refine Finset.mem_union_right _ ?_
  exact Finset.mem_biUnion.mpr ⟨μ, Finset.mem_univ _, Finset.mem_image_of_mem _ hy⟩

/-- **The enlargement is trivial at `Y = univ`** — the tilde operation adds nothing there, which is
why `local_lemma24_flat_univ` recovers the global theorem verbatim. -/
theorem tilde_univ (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    tilde hdvd (Finset.univ : Finset (CSite L ell)) = Finset.univ :=
  Finset.eq_univ_of_forall (fun y => subset_tilde hdvd _ (Finset.mem_univ y))

/-! ## §3 — THE LOCALIZED ENERGIES -/

/-- `∑_{b ∈ S} B(b)²`. -/
noncomputable def bondEnergyR (S : Finset (Bond L)) (B : Bond L → ℝ) : ℝ :=
  ∑ b ∈ S, (B b) ^ 2

/-- `∑_{p ∈ S} (∂₁B)(p)²`. -/
noncomputable def curlEnergyR (S : Finset (PeriodicLatticePlaquette L)) (B : Bond L → ℝ) : ℝ :=
  ∑ p ∈ S, (curlValue B p) ^ 2

/-- `∑_{c ∈ S} (Q₁B)(c)²`. -/
noncomputable def coarseQEnergyR (S : Finset (CoarseBond L ell)) (B : Bond L → ℝ) : ℝ :=
  ∑ c ∈ S, (lineCoarseRestrict ell B c) ^ 2

/-- `∑_{y ∈ Y} ∑_{b ⊂ B(y)} B(b)²` — the cube's in-block bond energy. -/
noncomputable def blockEnergyR (Y : Finset (CSite L ell)) (B : Bond L → ℝ) : ℝ :=
  ∑ y ∈ Y, blockBondEnergy B y.1 ell

theorem bondEnergyR_nonneg (S : Finset (Bond L)) (B : Bond L → ℝ) : 0 ≤ bondEnergyR S B :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem curlEnergyR_nonneg (S : Finset (PeriodicLatticePlaquette L)) (B : Bond L → ℝ) :
    0 ≤ curlEnergyR S B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem coarseQEnergyR_nonneg (S : Finset (CoarseBond L ell)) (B : Bond L → ℝ) :
    0 ≤ coarseQEnergyR S B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem blockEnergyR_nonneg (Y : Finset (CSite L ell)) (B : Bond L → ℝ) :
    0 ≤ blockEnergyR Y B :=
  Finset.sum_nonneg (fun _ _ => blockBondEnergy_nonneg _ _ _)

theorem curlEnergyR_mono {S T : Finset (PeriodicLatticePlaquette L)} (h : S ⊆ T) (B : Bond L → ℝ) :
    curlEnergyR S B ≤ curlEnergyR T B :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sq_nonneg _)

theorem blockEnergyR_mono {Y Z : Finset (CSite L ell)} (h : Y ⊆ Z) (B : Bond L → ℝ) :
    blockEnergyR Y B ≤ blockEnergyR Z B :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => blockBondEnergy_nonneg _ _ _)

theorem plaqsOn_mono {Y Z : Finset (CSite L ell)} (h : Y ⊆ Z) : plaqsOn Y ⊆ plaqsOn Z :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

/-! ### The `univ` pins: at `Y = univ` every localized energy IS the global one. -/

theorem bondEnergyR_univ (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : Bond L → ℝ) :
    bondEnergyR (bondsOn (Finset.univ : Finset (CSite L ell))) B = bondNormSq B := by
  rw [bondEnergyR, bondsOn_univ hell hdvd]; rfl

theorem curlEnergyR_univ (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : Bond L → ℝ) :
    curlEnergyR (plaqsOn (Finset.univ : Finset (CSite L ell))) B = totalCurlEnergy B := by
  rw [curlEnergyR, plaqsOn_univ hell hdvd]; rfl

theorem coarseQEnergyR_univ (B : Bond L → ℝ) :
    coarseQEnergyR (coarseOn (Finset.univ : Finset (CSite L ell))) B = coarseQEnergy ell B := by
  rw [coarseQEnergyR, coarseOn_univ]; rfl

theorem blockEnergyR_univ (B : Bond L → ℝ) :
    blockEnergyR (Finset.univ : Finset (CSite L ell)) B = inBlockBondEnergy ell B := by
  rw [blockEnergyR, inBlockBondEnergy_eq_sum]
  exact (Finset.sum_subtype (CoarseLattice L ell) (fun _ => Iff.rfl)
    (fun z => blockBondEnergy B z ell)).symm

/-! ## §4 — FACT 1, LOCALIZED: an EQUALITY, with no leakage whatever. -/

/-- **FACT 1 on a cube.** The cube's bond energy splits EXACTLY into its in-block energy and its
top-face energy. No inequality, no enlargement: `GeomScratch.bondsBasedIn_split` is already
per-block, and the blocks of `Y` are disjoint. -/
theorem local_fact1 (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hstrict : ∀ μ : Fin 3, ell < L μ + 1) (B : Bond L → ℝ) (Y : Finset (CSite L ell)) :
    bondEnergyR (bondsOn Y) B
      = blockEnergyR Y B + ∑ c ∈ coarseOn Y, topFaceEnergy B c.1.1 ell c.2 := by
  rw [bondEnergyR, bondsOn, Finset.sum_biUnion (bondsBasedIn_disj Y)]
  rw [Finset.sum_congr rfl (fun y _ => bondsBasedIn_split hell hdvd hstrict B y.2)]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [coarseOn, Finset.sum_product]

/-! ## §5 — FACT 2, LOCALIZED: the ONE place the enlarged cube is needed. -/

/-- **FACT 2 on a cube.** `∑_{c ∈ coarseOn Y} boundaryCorr(c) ≤ 6·blockEnergyR (tilde Y)`.
The `6 = 3 + 3` is the same count as globally (each block is `c₋` for `3` coarse bonds and `c₊` for
`3`); **the only change is that the `c₊` blocks are read on `□̃`, not on `□`** — that is the entire
content of the tilde operation. -/
theorem local_fact2 (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : Bond L → ℝ)
    (Y : Finset (CSite L ell)) :
    ∑ c ∈ coarseOn Y, boundaryCorr B c.1.1 ell c.2 ≤ 6 * blockEnergyR (tilde hdvd Y) B := by
  rw [coarseOn, Finset.sum_product]
  have hsplit : ∀ y : CSite L ell,
      ∑ μ : Fin 3, boundaryCorr B y.1 ell μ
        = 3 * blockBondEnergy B y.1 ell
          + ∑ μ : Fin 3, blockBondEnergy B (coarseShift y.1 ell μ) ell := by
    intro y
    simp only [boundaryCorr]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [Finset.sum_congr rfl (fun y _ => hsplit y), Finset.sum_add_distrib]
  have hA : ∑ y ∈ Y, 3 * blockBondEnergy B y.1 ell ≤ 3 * blockEnergyR (tilde hdvd Y) B := by
    rw [← Finset.mul_sum]
    have : blockEnergyR Y B ≤ blockEnergyR (tilde hdvd Y) B :=
      blockEnergyR_mono (subset_tilde hdvd Y) B
    have h3 : (0 : ℝ) ≤ 3 := by norm_num
    exact mul_le_mul_of_nonneg_left this h3
  have hB : ∑ y ∈ Y, ∑ μ : Fin 3, blockBondEnergy B (coarseShift y.1 ell μ) ell
      ≤ 3 * blockEnergyR (tilde hdvd Y) B := by
    rw [Finset.sum_comm]
    have hper : ∀ μ : Fin 3, ∑ y ∈ Y, blockBondEnergy B (coarseShift y.1 ell μ) ell
        ≤ blockEnergyR (tilde hdvd Y) B := by
      intro μ
      have hrw : ∑ y ∈ Y, blockBondEnergy B (coarseShift y.1 ell μ) ell
          = ∑ z ∈ Y.image (fun y : CSite L ell => shiftC hdvd y μ),
              blockBondEnergy B z.1 ell := by
        rw [Finset.sum_image
          (fun a _ b _ h => shiftC_injective hdvd μ h)]
        rfl
      rw [hrw, blockEnergyR]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => blockBondEnergy_nonneg _ _ _)
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact shiftC_mem_tilde hdvd hy μ
    calc ∑ μ : Fin 3, ∑ y ∈ Y, blockBondEnergy B (coarseShift y.1 ell μ) ell
        ≤ ∑ _μ : Fin 3, blockEnergyR (tilde hdvd Y) B := Finset.sum_le_sum (fun μ _ => hper μ)
      _ = 3 * blockEnergyR (tilde hdvd Y) B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  linarith [hA, hB]

/-! ## §6 — FACT 4, LOCALIZED: the region curl, with multiplicity `3` and NO enlargement. -/

/-- The map `(x, ν) ↦ xsecPlaq x μ ν` is injective for `ν ≠ μ` — the base site recovers `x`, and the
ORDERED pair recovers `ν` given `μ`. Four cases on the two `<`-tests inside `xsecPlaq`. -/
theorem xsecPlaq_val (z : PeriodicLatticeSite L) {a b : Fin 3} (h : a < b) :
    (xsecPlaq z a b).2.1 = (a, b) := by
  unfold xsecPlaq; rw [dif_pos h]

theorem xsecPlaq_val_rev (z : PeriodicLatticeSite L) {a b : Fin 3} (h : b < a) :
    (xsecPlaq z a b).2.1 = (b, a) := by
  unfold xsecPlaq; rw [dif_neg (not_lt.mpr (le_of_lt h)), dif_pos h]

theorem xsecPlaq_inj {x x' : PeriodicLatticeSite L} {μ ν ν' : Fin 3}
    (hν : ν ≠ μ) (hν' : ν' ≠ μ)
    (heq : xsecPlaq x μ ν = xsecPlaq (L := L) x' μ ν') : x = x' ∧ ν = ν' := by
  have hbase : x = x' := by
    have h := congrArg Prod.fst heq
    rwa [xsecPlaq_base, xsecPlaq_base] at h
  refine ⟨hbase, ?_⟩
  have hsnd : (xsecPlaq x μ ν).2.1 = (xsecPlaq x' μ ν').2.1 := by rw [heq]
  rcases lt_or_gt_of_ne hν with h1 | h1
  · rw [xsecPlaq_val_rev x h1] at hsnd
    rcases lt_or_gt_of_ne hν' with h2 | h2
    · rw [xsecPlaq_val_rev x' h2] at hsnd
      exact congrArg Prod.fst hsnd
    · rw [xsecPlaq_val x' h2] at hsnd
      exact absurd (congrArg Prod.fst hsnd) hν
  · rw [xsecPlaq_val x h1] at hsnd
    rcases lt_or_gt_of_ne hν' with h2 | h2
    · rw [xsecPlaq_val_rev x' h2] at hsnd
      exact absurd (congrArg Prod.snd hsnd) hν
    · rw [xsecPlaq_val x' h2] at hsnd
      exact congrArg Prod.snd hsnd

/-- **Per coarse bond**: the region curl energy of `(y, μ)` is at most the FULL block-based
plaquette energy of `B(y)`. No enlargement — `crossSectionTop y ell μ ⊆ blockOf y ell`, so every
plaquette `xsecPlaq` reads is based inside the SAME block. -/
theorem regionCurl_le_plaqsBasedIn (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ)
    (μ : Fin 3) :
    regionCurlEnergy B y ell μ ≤ curlEnergyR (plaqsBasedIn y ell) B := by
  rw [regionCurlEnergy]
  have hstep : ∀ x ∈ crossSectionTop y ell μ,
      ∑ ν ∈ transDirs μ, xsecCurl B x μ ν ^ 2
        = ∑ ν ∈ transDirs μ, (curlValue B (xsecPlaq x μ ν)) ^ 2 := by
    intro x _
    exact Finset.sum_congr rfl (fun ν hν => xsecPlaq_sq B x μ ν ((mem_transDirs.mp hν).symm))
  rw [Finset.sum_congr rfl hstep]
  rw [← Finset.sum_product']
  rw [← Finset.sum_image (f := fun q : PeriodicLatticePlaquette L => (curlValue B q) ^ 2)
    (g := fun w : PeriodicLatticeSite L × Fin 3 => xsecPlaq w.1 μ w.2)
    (s := crossSectionTop y ell μ ×ˢ transDirs μ) ?_]
  · rw [curlEnergyR]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    rw [Finset.mem_product] at hw
    rw [mem_plaqsBasedIn, xsecPlaq_base]
    exact (mem_crossSectionTop.mp hw.1).1
  · intro w hw w' hw' h
    have hw2 := Finset.mem_product.mp (Finset.mem_coe.mp hw)
    have hw2' := Finset.mem_product.mp (Finset.mem_coe.mp hw')
    obtain ⟨he1, he2⟩ := xsecPlaq_inj (mem_transDirs.mp hw2.2) (mem_transDirs.mp hw2'.2) h
    exact Prod.ext he1 he2

/-- **FACT 4 on a cube**, multiplicity `3`, NO enlargement. -/
theorem local_fact4 (B : Bond L → ℝ) (Y : Finset (CSite L ell)) :
    ∑ c ∈ coarseOn Y, regionCurlEnergy B c.1.1 ell c.2 ≤ 3 * curlEnergyR (plaqsOn Y) B := by
  rw [coarseOn, Finset.sum_product]
  have hper : ∀ y ∈ Y, ∑ μ : Fin 3, regionCurlEnergy B y.1 ell μ
      ≤ 3 * curlEnergyR (plaqsBasedIn y.1 ell) B := by
    intro y _
    calc ∑ μ : Fin 3, regionCurlEnergy B y.1 ell μ
        ≤ ∑ _μ : Fin 3, curlEnergyR (plaqsBasedIn y.1 ell) B :=
          Finset.sum_le_sum (fun μ _ => regionCurl_le_plaqsBasedIn B y.1 ell μ)
      _ = 3 * curlEnergyR (plaqsBasedIn y.1 ell) B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  refine (Finset.sum_le_sum hper).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, curlEnergyR, plaqsOn, Finset.sum_biUnion (plaqsBasedIn_disj Y)]
  rfl

/-! ## §7 — `(2.123)` LOCALIZED: `BlockPoincare.block_poincare` is ALREADY per-block. -/

/-- **CMP96 `(2.123)` on a cube.** The cube's in-block bond energy is bounded by `3·ell³` times its
block-based curl energy. Summed from the per-block `block_poincare`; the admissibility hypothesis
`hB` is the SAME global subspace membership the global theorem uses, and it is consumed only
per-block. -/
theorem local_2123 (hstrict : ∀ μ : Fin 3, ell < L μ + 1) (B : Bond L → ℝ)
    (hB : B ∈ admissibleSubspaceInter L ell) (Y : Finset (CSite L ell)) :
    blockEnergyR Y B ≤ 3 * (ell : ℝ) ^ 3 * curlEnergyR (plaqsOn Y) B := by
  have hstep : blockEnergyR Y B
      ≤ ∑ y ∈ Y, 3 * (ell : ℝ) ^ 3 * curlEnergyR (plaqsBasedIn y.1 ell) B := by
    rw [blockEnergyR]
    refine Finset.sum_le_sum (fun y _ => ?_)
    refine (block_poincare (hstrict 0) (hstrict 1) (hstrict 2) B hB y.1 y.2).trans ?_
    have hc : (0 : ℝ) ≤ 3 * (ell : ℝ) ^ 3 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hc
    exact Finset.sum_le_sum_of_subset_of_nonneg (plaqsInBlock_subset_basedIn y.1 ell)
      (fun _ _ _ => sq_nonneg _)
  refine hstep.trans (le_of_eq ?_)
  rw [← Finset.mul_sum, curlEnergyR, plaqsOn, Finset.sum_biUnion (plaqsBasedIn_disj Y)]
  rfl

/-! ## §8 — THE LOCALIZED FLAT LEMMA 2.4 -/

/-- The arithmetic slack the localized assembly needs, pinned at the binding point `t = 2`:
`9·t² + 3·t³ ≤ 18·t⁵` (localized, multiplicity `3`) where the global proof needed
`6·t² + 3·t³ ≤ 18·t⁵`. **Both hold, so the constant `1/180` is not degraded by localization.** -/
theorem flat_slack_at_two :
    9 * (2 : ℝ) ^ 2 + 3 * (2 : ℝ) ^ 3 ≤ 18 * (2 : ℝ) ^ 5
    ∧ 6 * (2 : ℝ) ^ 2 + 3 * (2 : ℝ) ^ 3 ≤ 18 * (2 : ℝ) ^ 5 := by
  norm_num

/-- **THE LOCALIZED FLAT CMP96 LEMMA 2.4.**

For every `ell ≥ 2`, every compatible torus, every `(2.121)`-admissible `B`, and EVERY cube
`Y : Finset (CSite L ell)`:

`(1/180)·ell⁻⁵·∑_{b ∈ bondsOn Y} B(b)² ≤ ell·∑_{c ∈ coarseOn Y} (Q₁B)(c)²
    + ∑_{p ∈ plaqsOn (tilde Y)} (∂₁B)(p)²`

with the SAME constant as `Lemma24GeneralEll.lemma24_general_ell`. The curl term — and ONLY the
curl term — is read on the enlarged cube `□̃`. -/
theorem local_lemma24_flat (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell) (Y : Finset (CSite L ell)) :
    (1 / 180) * (1 / (ell : ℝ) ^ 5) * bondEnergyR (bondsOn Y) B
      ≤ (ell : ℝ) * coarseQEnergyR (coarseOn Y) B
        + curlEnergyR (plaqsOn (tilde hdvd Y)) B := by
  have hell : 0 < ell := by omega
  set t : ℝ := (ell : ℝ) with hT
  have ht0 : (0 : ℝ) < t := by rw [hT]; exact_mod_cast hell
  have ht2 : (2 : ℝ) ≤ t := by rw [hT]; exact_mod_cast hell2
  set Nloc := bondEnergyR (bondsOn Y) B with hNloc
  set Qloc := coarseQEnergyR (coarseOn Y) B with hQloc
  set Ploc := curlEnergyR (plaqsOn (tilde hdvd Y)) B with hPloc
  set SinT := blockEnergyR (tilde hdvd Y) B with hSinT
  have hQnn : (0 : ℝ) ≤ Qloc := coarseQEnergyR_nonneg _ _
  have hPnn : (0 : ℝ) ≤ Ploc := curlEnergyR_nonneg _ _
  have hSnn : (0 : ℝ) ≤ SinT := blockEnergyR_nonneg _ _
  -- the localized curl energy on `Y` is at most the one on `tilde Y`
  have hPY : curlEnergyR (plaqsOn Y) B ≤ Ploc :=
    curlEnergyR_mono (plaqsOn_mono (subset_tilde hdvd Y)) B
  -- sum the per-c bound over the cube
  have hsum := Finset.sum_le_sum
    (fun c (_ : c ∈ coarseOn Y) => perC_bond (L := L) (ell := ell) hell hdvd B c)
  have hLHS : ∑ c ∈ coarseOn Y, (1 / 3) * (1 / t ^ 4) * topFaceEnergy B c.1.1 ell c.2
      = (1 / 3) * (1 / t ^ 4) * ∑ c ∈ coarseOn Y, topFaceEnergy B c.1.1 ell c.2 := by
    rw [← Finset.mul_sum]
  have hRHS : ∑ c ∈ coarseOn Y,
        ((t * (lineCoarseRestrict ell B c) ^ 2
          + (1 / t ^ 2) * regionCurlEnergy B c.1.1 ell c.2)
          + 3 * (1 / t ^ 2) * boundaryCorr B c.1.1 ell c.2)
      = t * Qloc + (1 / t ^ 2) * (∑ c ∈ coarseOn Y, regionCurlEnergy B c.1.1 ell c.2)
        + 3 * (1 / t ^ 2) * (∑ c ∈ coarseOn Y, boundaryCorr B c.1.1 ell c.2) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hQloc, coarseQEnergyR]
  rw [hLHS, hRHS] at hsum
  -- the four localized facts
  have hF1 := local_fact1 (L := L) (ell := ell) hell hdvd hstrict B Y
  have hF2 := local_fact2 (L := L) (ell := ell) hdvd B Y
  have hF4 := local_fact4 (L := L) (ell := ell) B Y
  have hF5 := local_2123 (L := L) (ell := ell) hstrict B hB (tilde hdvd Y)
  have hSinY : blockEnergyR Y B ≤ SinT := blockEnergyR_mono (subset_tilde hdvd Y) B
  rw [← hNloc] at hF1
  -- clear denominators
  have hid : ∀ X : ℝ, 3 * t ^ 4 * ((1 / 3) * (1 / t ^ 4) * X) = X := by
    intro X; field_simp
  have hbig := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 3 * t ^ 4 by positivity)
  rw [hid] at hbig
  have hexpand : 3 * t ^ 4 * (t * Qloc
        + (1 / t ^ 2) * (∑ c ∈ coarseOn Y, regionCurlEnergy B c.1.1 ell c.2)
        + 3 * (1 / t ^ 2) * (∑ c ∈ coarseOn Y, boundaryCorr B c.1.1 ell c.2))
      = 3 * t ^ 5 * Qloc
        + 3 * t ^ 2 * (∑ c ∈ coarseOn Y, regionCurlEnergy B c.1.1 ell c.2)
        + 9 * t ^ 2 * (∑ c ∈ coarseOn Y, boundaryCorr B c.1.1 ell c.2) := by
    field_simp <;> ring
  rw [hexpand] at hbig
  have hA : 3 * t ^ 2 * (∑ c ∈ coarseOn Y, regionCurlEnergy B c.1.1 ell c.2)
      ≤ 3 * t ^ 2 * (3 * Ploc) := by
    have h1 : (∑ c ∈ coarseOn Y, regionCurlEnergy B c.1.1 ell c.2) ≤ 3 * Ploc := by
      linarith [hF4, hPY]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hBc : 9 * t ^ 2 * (∑ c ∈ coarseOn Y, boundaryCorr B c.1.1 ell c.2)
      ≤ 9 * t ^ 2 * (6 * SinT) :=
    mul_le_mul_of_nonneg_left hF2 (by positivity)
  have hSinP : 54 * t ^ 2 * SinT ≤ 54 * t ^ 2 * (3 * t ^ 3 * Ploc) :=
    mul_le_mul_of_nonneg_left hF5 (by positivity)
  -- the main size bound
  have hMain : Nloc ≤ 3 * t ^ 5 * Qloc + (3 * t ^ 3 + 9 * t ^ 2 + 162 * t ^ 5) * Ploc := by
    nlinarith [hbig, hF1, hA, hBc, hSinP, hF5, hSinY, hPnn, hSnn]
  -- conclude, exactly as the global theorem does
  rw [← sub_nonneg]
  have hkey : t * Qloc + Ploc - (1 / 180) * (1 / t ^ 5) * Nloc
      = (180 * t ^ 5 * (t * Qloc + Ploc) - Nloc) / (180 * t ^ 5) := by
    field_simp <;> ring
  rw [hkey]
  refine div_nonneg ?_ (by positivity)
  have hc1 : (0 : ℝ) ≤ 180 * t ^ 6 - 3 * t ^ 5 := by nlinarith [ht2, pow_pos ht0 5]
  have hc2' : (0 : ℝ) ≤ 18 * t ^ 5 - 3 * t ^ 3 - 9 * t ^ 2 := by
    have hq1 : (0 : ℝ) ≤ t ^ 2 - 1 := by nlinarith [ht2, sq_nonneg (t - 2)]
    have hq2 : (0 : ℝ) ≤ t ^ 3 - 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht2) hq1, hq1, ht2]
    have h3 : t ^ 3 ≤ t ^ 5 := by
      nlinarith [mul_nonneg (le_of_lt (pow_pos ht0 3)) hq1]
    have h2' : t ^ 2 ≤ t ^ 5 := by
      nlinarith [mul_nonneg (le_of_lt (pow_pos ht0 2)) hq2]
    nlinarith [h3, h2', pow_pos ht0 5]
  nlinarith [hMain, mul_nonneg hc1 hQnn, mul_nonneg hc2' hPnn]

/-- **The localization is a genuine STRENGTHENING, not a rescaling**: at `Y = univ` the localized
statement coincides with `Lemma24GeneralEll.Lemma24ConclusionCorrected`, verbatim, same constant. -/
theorem local_lemma24_flat_univ (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell) :
    Lemma24ConclusionCorrected ell B := by
  have hell : 0 < ell := by omega
  have h := local_lemma24_flat (L := L) (ell := ell) hell2 hstrict hdvd B hB Finset.univ
  rw [tilde_univ hdvd] at h
  rw [bondEnergyR_univ hell hdvd, coarseQEnergyR_univ, curlEnergyR_univ hell hdvd] at h
  rw [Lemma24ConclusionCorrected, ge_iff_le]
  exact h

#print axioms plaqsBasedIn
#print axioms CSite
#print axioms mem_plaqsBasedIn
#print axioms plaqsInBlock_subset_basedIn
#print axioms mem_coarseOn
#print axioms bondsBasedIn_disj
#print axioms plaqsBasedIn_disj
#print axioms shiftC_injective
#print axioms subset_tilde
#print axioms shiftC_mem_tilde
#print axioms bondEnergyR
#print axioms curlEnergyR
#print axioms coarseQEnergyR
#print axioms blockEnergyR
#print axioms bondEnergyR_nonneg
#print axioms curlEnergyR_nonneg
#print axioms coarseQEnergyR_nonneg
#print axioms blockEnergyR_nonneg
#print axioms curlEnergyR_mono
#print axioms blockEnergyR_mono
#print axioms plaqsOn_mono
#print axioms bondsOn
#print axioms plaqsOn
#print axioms coarseOn
#print axioms shiftC
#print axioms tilde
#print axioms bondsOn_univ
#print axioms plaqsOn_univ
#print axioms coarseOn_univ
#print axioms tilde_univ
#print axioms bondEnergyR_univ
#print axioms curlEnergyR_univ
#print axioms coarseQEnergyR_univ
#print axioms blockEnergyR_univ
#print axioms local_fact1
#print axioms local_fact2
#print axioms xsecPlaq_val
#print axioms xsecPlaq_val_rev
#print axioms xsecPlaq_inj
#print axioms regionCurl_le_plaqsBasedIn
#print axioms local_fact4
#print axioms local_2123
#print axioms flat_slack_at_two
#print axioms local_lemma24_flat
#print axioms local_lemma24_flat_univ

end AdalyFormal.Balaban.LocalizedEstimates
