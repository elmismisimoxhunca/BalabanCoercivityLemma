/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import LocCov

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
# THE TRANSPORT HOLONOMY IS LOCAL — closing `LocCov`'s named residual.

`LocCov.holonomy_locality_statement` named the one thing `LocDrift`/`LocCov` could not localize: the
coarse drift's smallness parameter stayed the GLOBAL `frobSupBond U`, because
`LineIntegralCovariant.lineCoarseRestrictCov` reads `U` through a HOLONOMY
(`Q1Real.periodicPathHolonomy U c₋ (Q1Real.transportPath c₋ x μ i)`) whose visited bonds this lane
had not bounded.

**This module proves that containment and discharges the residual.**

## What is proved

1. `holonomy_replicate_congr` — the holonomy along a run of FORWARD steps depends on `U` only at the
   bonds `(pathSite z μ j, μ)`, `j < n`. Induction on the run length; the definition
   (`Target.ClayStatement.periodicPathHolonomy`) reads exactly `U (x, μ)` at a forward step.
2. `coordSteps_pathSite` — the forward step count from `x` to `x + i·e_μ` is EXACTLY `i` (`i < L μ+1`),
   so a `straightSegment` cannot secretly wrap the torus and read far-away bonds.
3. `holonomy_GammaPath_congr` — CMP95 (1.7)'s staircase `Γ_{y,x}` from a block centre `y` to a block
   site `x` visits ONLY bonds based in the block `B(y)`. Each of its three legs is forward and
   travels from `y_ρ` to `x_ρ < y_ρ + ell`.
4. `holonomy_transportPath_congr` — hence CMP98 pp.27–28's `transportPath` visits only bonds based in
   `B(y) ∪ B(y + ell·e_μ)`, i.e. in `bondsOn (tilde Y)`.
5. `lineCoarseRestrictCov_cutU` — so cutting `U` to `bondsOn (tilde Y)` does not change `Q(U)A` on
   the cube's coarse bonds; `holonomy_locality` is then `LocCov.holonomy_locality_statement`, PROVED.
6. `local_coarseDrift_le_local` — the coarse drift with the cube's OWN `α`, and
   `local_covariant_lemma24_local` — the per-cube covariant floor with a SINGLE LOCAL `α` and no
   global smallness anywhere.

## The bond set does not grow

The cut is to `bondsOn (tilde Y)` — the SAME enlarged cube the flat lemma and the curl drift already
use. The transport path never leaves it, so `local_covariant_lemma24_local` reads its drift on
`bondsOn (tilde (tilde Y))` only because the CURL drift does (`LocCov.local_curl_flat_le`); the
coarse drift needs only one tilde.
-/

namespace AdalyFormal.Balaban.LocalizedEstimates

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CoarseCurl
open GeomScratch
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.Q1Real
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.RegularUQChain
open AdalyFormal.Balaban.CovariantLemma24

variable {L : PeriodicLatticeExtent} {ell : ℕ}

/-! ## §1 — A FORWARD STEP READS ONE BOND -/

/-- The holonomy of a forward step: `U` is read at the bond BASED AT the current site. Definitional;
isolated so the induction below never unfolds `periodicPathHolonomy` again. -/
theorem holonomy_cons_fwd {G : Type*} [Group G] (U : PeriodicLinkConfiguration G L)
    (x : PeriodicLatticeSite L) (μ : Fin 3) (rest : List (Fin 3 × Bool)) :
    periodicPathHolonomy U x ((μ, true) :: rest)
      = U (x, μ) * periodicPathHolonomy U (periodicLatticeShift x μ) rest := rfl

/-- **THE RUN LOCALITY.** The holonomy along `n` forward `μ`-steps from `z` depends on `U` only at
the `n` bonds `(pathSite z μ j, μ)`, `j < n`. -/
theorem holonomy_replicate_congr {G : Type*} [Group G] (U U' : PeriodicLinkConfiguration G L)
    (μ : Fin 3) (n : ℕ) :
    ∀ (z : PeriodicLatticeSite L),
      (∀ j < n, U (pathSite z μ j, μ) = U' (pathSite z μ j, μ)) →
      periodicPathHolonomy U z (List.replicate n (μ, true))
        = periodicPathHolonomy U' z (List.replicate n (μ, true)) := by
  induction n with
  | zero => intro z _; rfl
  | succ m ih =>
    intro z h
    rw [List.replicate_succ, holonomy_cons_fwd, holonomy_cons_fwd]
    have h0 : U (z, μ) = U' (z, μ) := by
      have hz := h 0 (Nat.succ_pos m)
      rwa [pathSite_zero] at hz
    rw [h0]
    congr 1
    refine ih (periodicLatticeShift z μ) (fun j hj => ?_)
    have hs : pathSite (periodicLatticeShift z μ) μ j = pathSite z μ (j + 1) :=
      (Function.iterate_succ_apply (fun w : PeriodicLatticeSite L => periodicLatticeShift w μ)
        j z).symm
    rw [hs]
    exact h (j + 1) (by omega)

/-- The same for a `straightSegment`, which is by definition a forward run. -/
theorem holonomy_straight_congr {G : Type*} [Group G] (U U' : PeriodicLinkConfiguration G L)
    (a b : PeriodicLatticeSite L) (μ : Fin 3)
    (h : ∀ j < coordSteps a b μ, U (pathSite a μ j, μ) = U' (pathSite a μ j, μ)) :
    periodicPathHolonomy U a (straightSegment a b μ)
      = periodicPathHolonomy U' a (straightSegment a b μ) := by
  unfold straightSegment
  exact holonomy_replicate_congr U U' μ (coordSteps a b μ) a h

/-! ## §2 — THE STEP COUNTS ARE EXACT (no hidden wrap) -/

/-- The `μ`-coordinate of a path site, in the additive group `Fin (L μ + 1)`. -/
theorem pathSite_coord_mu (x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    (pathSite x μ i) μ = x μ + i • (1 : Fin (L μ + 1)) := by
  induction i with
  | zero => simp [pathSite]
  | succ k ih =>
    rw [pathSite_succ, periodicLatticeShift_self, ih, succ_nsmul]
    abel

/-- **The forward step count from `x` to `x + i·e_μ` is EXACTLY `i`** when `i < L μ + 1`. So a
`straightSegment` of the transport path takes exactly the steps it looks like it takes: it cannot
wrap the torus and read bonds outside the block. -/
theorem coordSteps_pathSite (x : PeriodicLatticeSite L) (μ : Fin 3) {i : ℕ} (hi : i < L μ + 1) :
    coordSteps x (pathSite x μ i) μ = i := by
  unfold coordSteps
  rw [pathSite_coord_mu, add_sub_cancel_left, nsmul_one_val, Nat.mod_eq_of_lt hi]

/-- The forward step count between two sites whose `μ`-coordinates are ordered. -/
theorem coordSteps_val {a b : PeriodicLatticeSite L} (μ : Fin 3) (h : (a μ).val ≤ (b μ).val) :
    coordSteps a b μ = (b μ).val - (a μ).val := by
  unfold coordSteps
  exact Fin.sub_val_of_le (Fin.le_def.mpr h)

/-! ## §3 — PATH SITES STAY IN THE BLOCK -/

/-- The sharp form of `LocDrift.pathSite_mem_block_or_next`: when the offset does not reach the far
face, the path site is in the SAME block. -/
theorem pathSite_mem_block_sharp (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y x : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (hx : x ∈ blockOf y ell)
    (μ : Fin 3) {i : ℕ} (hlt : (x μ).val + i < (y μ).val + ell) :
    pathSite x μ i ∈ blockOf y ell := by
  have hxb := mem_blockOf.mp hx
  have hfit := coarseLattice_mem_fits hdvd hy μ
  rw [mem_blockOf]
  intro ρ
  by_cases hρ : ρ = μ
  · subst hρ
    have hval : ((pathSite x ρ i) ρ).val = ((x ρ).val + i) % (L ρ + 1) := by
      rw [pathSite_eq_coarseShift]; exact coarseShift_val_eq x i ρ
    rw [hval, Nat.mod_eq_of_lt (by omega)]
    have := hxb ρ
    omega
  · have hval : (pathSite x μ i) ρ = x ρ := by
      rw [pathSite_eq_coarseShift]; exact coarseShift_apply_ne x i μ ρ hρ
    rw [hval]
    exact hxb ρ

/-- A coarse centre lies in its own block. -/
theorem self_mem_blockOf (hell : 0 < ell) (y : PeriodicLatticeSite L) : y ∈ blockOf y ell := by
  rw [mem_blockOf]; intro ρ; exact ⟨le_rfl, by omega⟩

/-- Updating ONE coordinate of a block site to another block site's value stays in the block. -/
theorem update_mem_blockOf {y a x : PeriodicLatticeSite L} (ha : a ∈ blockOf y ell)
    (hx : x ∈ blockOf y ell) (ρ : Fin 3) :
    Function.update a ρ (x ρ) ∈ blockOf y ell := by
  rw [mem_blockOf]
  intro σ
  by_cases hσ : σ = ρ
  · subst hσ
    rw [Function.update_self]
    exact (mem_blockOf.mp hx) σ
  · rw [Function.update_of_ne hσ]
    exact (mem_blockOf.mp ha) σ

/-! ## §4 — `Γ_{y,x}` VISITS ONLY BONDS OF THE BLOCK -/

/-- **The staircase is block-local.** `Q1Real.GammaPath y x` from a coarse centre `y` to a site `x`
of its block reads `U` only at bonds based in `B(y)`. Its three legs are forward and each travels
from `y_ρ` to `x_ρ < y_ρ + ell`. -/
theorem holonomy_GammaPath_congr {G : Type*} [Group G] (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (U U' : PeriodicLinkConfiguration G L)
    {y x : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (hx : x ∈ blockOf y ell)
    (h : ∀ z ∈ blockOf y ell, ∀ ρ : Fin 3, U (z, ρ) = U' (z, ρ)) :
    periodicPathHolonomy U y (GammaPath y x) = periodicPathHolonomy U' y (GammaPath y x) := by
  have hyy : y ∈ blockOf y ell := self_mem_blockOf hell y
  have hxb := mem_blockOf.mp hx
  have he1 : Function.update y 2 (x 2) ∈ blockOf y ell := update_mem_blockOf hyy hx 2
  have he2 : Function.update (Function.update y 2 (x 2)) 1 (x 1) ∈ blockOf y ell :=
    update_mem_blockOf he1 hx 1
  -- a leg's sites stay in the block whenever its base does and its start coordinate is `y`'s
  have hleg : ∀ (a : PeriodicLatticeSite L), a ∈ blockOf y ell → ∀ (ρ : Fin 3),
      (a ρ).val = (y ρ).val →
      ∀ j < coordSteps a x ρ, U (pathSite a ρ j, ρ) = U' (pathSite a ρ j, ρ) := by
    intro a ha ρ haρ j hj
    have hle : (a ρ).val ≤ (x ρ).val := by have := hxb ρ; omega
    rw [coordSteps_val ρ hle] at hj
    have hlt : (a ρ).val + j < (y ρ).val + ell := by have := hxb ρ; omega
    exact h _ (pathSite_mem_block_sharp hdvd hy ha ρ hlt) ρ
  have hA : periodicPathHolonomy U y (straightSegment y x 2)
      = periodicPathHolonomy U' y (straightSegment y x 2) :=
    holonomy_straight_congr U U' y x 2 (hleg y hyy 2 rfl)
  have hB : periodicPathHolonomy U (Function.update y 2 (x 2))
        (straightSegment (Function.update y 2 (x 2)) x 1)
      = periodicPathHolonomy U' (Function.update y 2 (x 2))
        (straightSegment (Function.update y 2 (x 2)) x 1) := by
    refine holonomy_straight_congr U U' _ x 1 (hleg _ he1 1 ?_)
    rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2)]
  have hC : periodicPathHolonomy U (Function.update (Function.update y 2 (x 2)) 1 (x 1))
        (straightSegment (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0)
      = periodicPathHolonomy U' (Function.update (Function.update y 2 (x 2)) 1 (x 1))
        (straightSegment (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0) := by
    refine holonomy_straight_congr U U' _ x 0 (hleg _ he2 0 ?_)
    rw [Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1),
      Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2)]
  simp only [GammaPath, periodicPathHolonomy_append, periodicPathEndpoint_append,
    straightSegment_endpoint]
  rw [hA, hB, hC]

/-! ## §5 — THE TRANSPORT PATH, AND THE RESIDUAL DISCHARGED -/

/-- **THE TRANSPORT HOLONOMY IS LOCAL.** `Q1Real.transportPath y x μ i` reads `U` only at bonds based
in `B(y) ∪ B(y + ell·e_μ)`. -/
theorem holonomy_transportPath_congr {G : Type*} [Group G] (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (U U' : PeriodicLinkConfiguration G L)
    {y x : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (hx : x ∈ blockOf y ell)
    (μ : Fin 3) {i : ℕ} (hi : i < ell)
    (h : ∀ z, (z ∈ blockOf y ell ∨ z ∈ blockOf (coarseShift y ell μ) ell) →
      ∀ ρ : Fin 3, U (z, ρ) = U' (z, ρ)) :
    periodicPathHolonomy U y (transportPath y x μ i)
      = periodicPathHolonomy U' y (transportPath y x μ i) := by
  have hfit := coarseLattice_mem_fits hdvd hy μ
  have hiL : i < L μ + 1 := by omega
  unfold transportPath
  rw [periodicPathHolonomy_append, periodicPathHolonomy_append, GammaPath_endpoint]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact holonomy_GammaPath_congr hell hdvd U U' hy hx (fun z hz ρ => h z (Or.inl hz) ρ)
  · refine holonomy_straight_congr U U' x (pathSite x μ i) μ (fun j hj => ?_)
    rw [coordSteps_pathSite x μ hiL] at hj
    exact h _ (pathSite_mem_block_or_next hdvd hy hx μ (by omega)) μ

/-- **`Q(U)A` depends on `U` only through the transport holonomies.** Generic in the second
background, so no `Finset`-membership decision procedure is ever forced open. -/
theorem lineCoarseRestrictCov_congrU
    (U U' : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (c : CoarseBond L ell)
    (h : ∀ x ∈ blockOf c.1.1 ell, ∀ i ∈ Finset.range ell,
      periodicPathHolonomy U c.1.1 (transportPath c.1.1 x c.2 i)
        = periodicPathHolonomy U' c.1.1 (transportPath c.1.1 x c.2 i)) :
    lineCoarseRestrictCov U ell A c = lineCoarseRestrictCov U' ell A c := by
  unfold lineCoarseRestrictCov
  refine congrArg (fun s : SuTwo => (1 / (ell : ℝ) ^ 4) • s)
    (Finset.sum_congr rfl (fun x hx => ?_))
  unfold rZeroA
  exact Finset.sum_congr rfl (fun i hi => by rw [h x hx i hi])

/-- The cube's own bonds, as a membership fact usable inside the holonomy congruence. -/
theorem block_or_next_bond_mem (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {Y : Finset (CSite L ell)} {c : CoarseBond L ell} (hcY : c.1 ∈ Y)
    {z : PeriodicLatticeSite L}
    (hz : z ∈ blockOf c.1.1 ell ∨ z ∈ blockOf (coarseShift c.1.1 ell c.2) ell) (ρ : Fin 3) :
    (z, ρ) ∈ bondsOn (tilde hdvd Y) := by
  rcases hz with h1 | h1
  · exact Finset.mem_biUnion.mpr ⟨c.1, subset_tilde hdvd Y hcY, by
      simp only [bondsBasedIn, Finset.mem_filter, Finset.mem_univ, true_and]; exact h1⟩
  · exact Finset.mem_biUnion.mpr ⟨shiftC hdvd c.1 c.2, shiftC_mem_tilde hdvd hcY c.2, by
      simp only [bondsBasedIn, Finset.mem_filter, Finset.mem_univ, true_and]; exact h1⟩

/-- **`Q(U)A` on a cube's coarse bonds does not see `U` outside the enlarged cube.** -/
theorem lineCoarseRestrictCov_cutU (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) {Y : Finset (CSite L ell)} {c : CoarseBond L ell} (hc : c ∈ coarseOn Y) :
    lineCoarseRestrictCov U ell A c
      = lineCoarseRestrictCov (linkCut (bondsOn (tilde hdvd Y)) U) ell A c := by
  have hcY : c.1 ∈ Y := mem_coarseOn.mp hc
  refine lineCoarseRestrictCov_congrU U _ A c (fun x hx i hi => ?_)
  refine holonomy_transportPath_congr hell hdvd U (linkCut (bondsOn (tilde hdvd Y)) U)
    c.1.2 hx c.2 (Finset.mem_range.mp hi) (fun z hz ρ => ?_)
  exact (linkCut_mem (block_or_next_bond_mem hdvd hcY hz ρ)).symm

/-- **`LocCov.holonomy_locality_statement`, PROVED.** The residual named in `LocCov` §6 is
discharged; nothing in this chain depends on it as a hypothesis any more. -/
theorem holonomy_locality (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    holonomy_locality_statement L ell hdvd := by
  intro U Y c hc x hx i hi
  have hcY : c.1 ∈ Y := mem_coarseOn.mp hc
  refine holonomy_transportPath_congr hell hdvd U (linkCut (bondsOn (tilde hdvd Y)) U)
    c.1.2 hx c.2 (Finset.mem_range.mp hi) (fun z hz ρ => ?_)
  exact (linkCut_mem (block_or_next_bond_mem hdvd hcY hz ρ)).symm

/-! ## §6 — THE COARSE DRIFT WITH THE CUBE'S OWN `α` -/

/-- `frobSupBond` of a cut link configuration is bounded by the cube's own deviation bound. -/
theorem frobSupBond_linkCut_bound (S : Finset (Bond L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {α : ℝ}
    (hα0 : 0 ≤ α)
    (hα : ∀ b ∈ S, RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    frobSupBond (linkCut S U) ≤ α := by
  unfold frobSupBond
  exact Finset.sup'_le _ _ (fun b _ => frobSupBond_linkCut_le S U hα0 hα b)

/-- **THE COARSE DRIFT, FULLY LOCALIZED.** Index sets on the cube, and the smallness parameter is
the cube's own. This is `LocDrift.local_coarseDrift_le` with `frobSupBond U` replaced by `α`. -/
theorem local_coarseDrift_le_local (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (α : ℝ) (hα0 : 0 ≤ α) (Y : Finset (CSite L ell))
    (hα : ∀ b ∈ bondsOn (tilde hdvd Y),
      RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    ∑ c ∈ coarseOn Y,
        ‖lineCoarseRestrictCov (trivialU L) ell A c - lineCoarseRestrictCov U ell A c‖ ^ 2
      ≤ (64 / (ell : ℝ)) * α ^ 2 * ∑ b ∈ bondsOn (tilde hdvd Y), ‖A b‖ ^ 2 := by
  set V := linkCut (bondsOn (tilde hdvd Y)) U with hV
  have hswap : ∀ c ∈ coarseOn Y,
      ‖lineCoarseRestrictCov (trivialU L) ell A c - lineCoarseRestrictCov U ell A c‖ ^ 2
        = ‖lineCoarseRestrictCov (trivialU L) ell A c - lineCoarseRestrictCov V ell A c‖ ^ 2 := by
    intro c hc
    rw [← lineCoarseRestrictCov_cutU hell hdvd U A hc]
  rw [Finset.sum_congr rfl hswap]
  have hbase := local_coarseDrift_le hell hdvd V A Y
  have hsup : frobSupBond V ≤ α := frobSupBond_linkCut_bound _ U hα0 hα
  have hsq : frobSupBond V ^ 2 ≤ α ^ 2 := by
    have h0 := frobSupBond_nonneg V
    nlinarith [hsup, h0]
  have hE : (0 : ℝ) ≤ ∑ b ∈ bondsOn (tilde hdvd Y), ‖A b‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc0 : (0 : ℝ) ≤ 64 / (ell : ℝ) := by positivity
  refine hbase.trans ?_
  have := mul_le_mul_of_nonneg_left hsq hc0
  nlinarith [this, hE]

/-! ## §7 — THE PER-CUBE COVARIANT FLOOR AT ONE LOCAL `α` -/

/-- The flat coarse energy on the cube, with the cube's own `α`. -/
theorem local_coarseQ_flat_le_local (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (α : ℝ) (hα0 : 0 ≤ α) (Y : Finset (CSite L ell))
    (hα : ∀ b ∈ bondsOn (tilde hdvd Y),
      RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    coarseQS (coarseOn Y) (trivialU L) A
      ≤ 2 * coarseQS (coarseOn Y) U A
        + 2 * ((64 / (ell : ℝ)) * α ^ 2 * bondEnergyS (bondsOn (tilde hdvd Y)) A) := by
  have hpt : coarseQS (coarseOn Y) (trivialU L) A
      ≤ 2 * coarseQS (coarseOn Y) U A
        + 2 * ∑ c ∈ coarseOn Y,
            ‖lineCoarseRestrictCov (trivialU L) ell A c - lineCoarseRestrictCov U ell A c‖ ^ 2 := by
    unfold coarseQS
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun c _ =>
      sq_le_two_add_two (lineCoarseRestrictCov (trivialU L) ell A c)
        (lineCoarseRestrictCov U ell A c))
  have hd := local_coarseDrift_le_local hell hdvd U A α hα0 Y hα
  unfold bondEnergyS
  linarith [hpt, hd]

/-- **THE PER-CUBE COVARIANT CMP96 LEMMA 2.4, AT A SINGLE LOCAL SMALLNESS PARAMETER.**

No global smallness anywhere: `α` bounds the holonomy deviations only on the DOUBLY enlarged cube's
bonds, and the coefficient is `covariant_lemma24`'s own `96 = 64 + 32`. -/
theorem local_covariant_lemma24_local (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) (α : ℝ) (hα0 : 0 ≤ α)
    (Y : Finset (CSite L ell))
    (hα : ∀ b ∈ bondsOn (tilde hdvd (tilde hdvd Y)),
      RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    (1 / 360) * (1 / (ell : ℝ) ^ 5) * bondEnergyS (bondsOn Y) A
        - 96 * α ^ 2 * bondEnergyS (bondsOn (tilde hdvd (tilde hdvd Y))) A
      ≤ (ell : ℝ) * coarseQS (coarseOn Y) U A + curlS (plaqsOn (tilde hdvd Y)) U A := by
  have hell : 0 < ell := by omega
  have ht : (0 : ℝ) ≤ (ell : ℝ) := by positivity
  have hsubT : bondsOn (tilde hdvd Y) ⊆ bondsOn (tilde hdvd (tilde hdvd Y)) :=
    Finset.biUnion_subset_biUnion_of_subset_left _ (subset_tilde hdvd (tilde hdvd Y))
  have hαT : ∀ b ∈ bondsOn (tilde hdvd Y),
      RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α :=
    fun b hb => hα b (hsubT hb)
  have hfloor := local_suTwo_flat hell2 hstrict hdvd A hadm Y
  have hQ := local_coarseQ_flat_le_local hell hdvd U A α hα0 Y hαT
  have hP := local_curl_flat_le hell2 hdvd U A α hα0 Y hαT
  have hmain := transfer_abstract (t := (ell : ℝ)) (gam := (1 / 180) * (1 / (ell : ℝ) ^ 5))
    (N := bondEnergyS (bondsOn Y) A)
    (Qf := coarseQS (coarseOn Y) (trivialU L) A)
    (Pf := curlS (plaqsOn (tilde hdvd Y)) (trivialU L) A)
    (Qc := coarseQS (coarseOn Y) U A)
    (Pc := curlS (plaqsOn (tilde hdvd Y)) U A)
    (dQ := (64 / (ell : ℝ)) * α ^ 2 * bondEnergyS (bondsOn (tilde hdvd Y)) A)
    (dP := 32 * α ^ 2 * bondEnergyS (bondsOn (tilde hdvd (tilde hdvd Y))) A)
    ht hfloor hQ hP
  have hid : (ell : ℝ) * ((64 / (ell : ℝ)) * α ^ 2 * bondEnergyS (bondsOn (tilde hdvd Y)) A)
      = 64 * α ^ 2 * bondEnergyS (bondsOn (tilde hdvd Y)) A := by
    have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
    field_simp
  have hgam : ((1 / 180) * (1 / (ell : ℝ) ^ 5)) / 2 * bondEnergyS (bondsOn Y) A
      = (1 / 360) * (1 / (ell : ℝ) ^ 5) * bondEnergyS (bondsOn Y) A := by ring
  rw [hid, hgam] at hmain
  have hmono : bondEnergyS (bondsOn (tilde hdvd Y)) A
      ≤ bondEnergyS (bondsOn (tilde hdvd (tilde hdvd Y))) A := bondEnergyS_mono hsubT A
  have hα2 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  nlinarith [hmain, hmono, hα2]

/-! ## §8 — CONTROL: the locality is not vacuous. -/

/-- **The transport path is NOT empty in general**, so `holonomy_transportPath_congr` is not a
statement about the identity: at `i = 1` the trailing `straightSegment` has exactly one step
(`coordSteps_pathSite`), so the holonomy genuinely reads a bond. -/
theorem transport_reads_a_bond (x : PeriodicLatticeSite L) (μ : Fin 3) (hL : 1 < L μ + 1) :
    coordSteps x (pathSite x μ 1) μ = 1 :=
  coordSteps_pathSite x μ hL

#print axioms holonomy_cons_fwd
#print axioms holonomy_replicate_congr
#print axioms holonomy_straight_congr
#print axioms pathSite_coord_mu
#print axioms coordSteps_pathSite
#print axioms coordSteps_val
#print axioms pathSite_mem_block_sharp
#print axioms self_mem_blockOf
#print axioms update_mem_blockOf
#print axioms holonomy_GammaPath_congr
#print axioms holonomy_transportPath_congr
#print axioms lineCoarseRestrictCov_congrU
#print axioms block_or_next_bond_mem
#print axioms lineCoarseRestrictCov_cutU
#print axioms holonomy_locality
#print axioms frobSupBond_linkCut_bound
#print axioms local_coarseDrift_le_local
#print axioms local_coarseQ_flat_le_local
#print axioms local_covariant_lemma24_local
#print axioms transport_reads_a_bond

end AdalyFormal.Balaban.LocalizedEstimates
