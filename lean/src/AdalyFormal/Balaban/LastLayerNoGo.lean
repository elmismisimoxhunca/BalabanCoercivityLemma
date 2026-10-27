/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.KimiRGLadderScratch

set_option autoImplicit false
set_option maxRecDepth 8192

/-!
# `LastLayerNoGo` — the staircase-free bond set, exactly; and the RG-ladder no-go at every `ell`

This file generalizes `KimiRGLadderScratch.kimi_no_coercivityHypothesis_rgLadder_at_ell_two`
(a single witness, at `ell = 2`, on the single lattice `Lat4`) in two directions at once.

## §A — what `anchoredVInter ell` actually is: a COORDINATE subspace, computed exactly

`Anchoring.anchoredVInter ell` is the transport of
`admissibleSubspaceInter L ell = {B | ∀ y ∈ Λ', ∀ x ∈ B(y), ∀ b ∈ Γ_{y,x}, B b = 0}`.
The union `S(ell) := ⋃_{y ∈ Λ'} ⋃_{x ∈ B(y)} Γ_{y,x}` is therefore the ONLY datum: `V` is the
coordinate subspace of fields vanishing on `S(ell)` (`mem_anchoredVInter_iff_vanish`).

`S(ell)` is computed here EXACTLY, direction by direction (`onSomeStaircase_dir0_iff`,
`onSomeStaircase_dir1_iff`, `onSomeStaircase_dir2_iff`): for `0 < ell`,

* `(s, 0) ∈ S(ell) ↔ (s 0).val % ell ≠ ell - 1 ∧ (s 0).val < Lat 0`
* `(s, 1) ∈ S(ell) ↔ (s 0).val % ell = 0 ∧ (s 1).val % ell ≠ ell - 1 ∧ (s 1).val < Lat 1`
* `(s, 2) ∈ S(ell) ↔ (s 0).val % ell = 0 ∧ (s 1).val % ell = 0 ∧ (s 2).val % ell ≠ ell - 1
    ∧ (s 2).val < Lat 2`

Each has TWO independent escape clauses, and they are of different natures:

* the **modular** clause (`% ell = ell - 1`, the LAST LAYER of a block) is intrinsic — it says the
  bond points out of its own block, so no in-block staircase segment can sweep across it;
* the **extent** clause (`Lat μ ≤ (s μ).val`, the TOP LAYER of the coordinate box) is a
  BOUNDARY/TRUNCATION effect of this encoding: `axisSegment` compares raw `ℕ` coordinates with `<`
  and never wraps, so the periodic lattice is modelled as a box and its top face carries no
  staircase at all. **Results driven by the extent clause are flagged as such below and are NOT
  used in the headline no-go.**

## §B — the no-go, generalized

`no_coercivityHypothesis_of_free_pair` is the engine: ANY two distinct bonds outside `S(ell)`
sharing a `blockRepBond n`-fibre refute `CoercivityHypothesis` at `V = anchoredVInter ell`,
`Δ k₀ U₀ = rgDelta n`. Three witness families supply such pairs:

* `no_coercivityHypothesis_lastLayer` — **the generalization asked for**: direction-`0` bonds based
  in the last layer `(s 0).val = ell - 1` of the origin block, split along a second axis. Uses only
  the MODULAR clause, so it is truncation-free. Hypotheses: `n ≠ 1`, `ell - 1 ≤ Lat 0`,
  and `1 ≤ Lat ν` for one `ν ≠ 0`. NO hypothesis on `ell` itself, and no divisibility.
* `no_coercivityHypothesis_offCorner` — direction-`1` bonds based off the coarse corner
  (`(s 0).val % ell ≠ 0`). Also truncation-free. Hypotheses: `n ≠ 1`, `2 ≤ ell`, `1 ≤ Lat 0`,
  `1 ≤ Lat ν` for one `ν ≠ 0`. Cheaper in `Lat 0` than the last-layer family.
* `no_coercivityHypothesis_topLayer` — the extent-clause family. **Truncation-driven, recorded for
  completeness, not load-bearing for anything above.**

`no_coercivityHypothesis_rgLadder_general` combines them, and `hypothesis_exists_iff` turns that
into the sharp two-sided statement: for a fixed `Lat`, `ell`, `n`, a `CoercivityHypothesis`
with `V = anchoredVInter ell` and one rung equal to `rgDelta n` EXISTS **iff** `n = 1` or the
lattice has exactly one site.

## §C — the kernel, characterized (not one hand-picked witness)

`kernel_inter_ne_bot_iff`: for `0 < n`,
`∃ v ≠ 0, v ∈ anchoredVInter ell ∧ rgDelta n v = 0`
**iff** there are two distinct bonds off `S(ell)` in one `blockRepBond n`-fibre. This is an exact
characterization: the forward direction is a pigeonhole on a vanishing fibre sum, so no vector of
`ker (rgDelta n) ∩ V` can exist for any other reason. Combined with §A the criterion is decidable
arithmetic in `(ell, n, Lat)`.

## §D — controls (each is a compiled refutation, not a remark)

* `ctrl_hypothesis_exists_at_n_one` — at `n = 1` the no-go's conclusion is FALSE: an explicit
  `CoercivityHypothesis` with `V = anchoredVInter ell` and `Δ k true = rgDelta 1` is constructed.
  So `n ≠ 1` is load-bearing, on every lattice and at every `ell`.
* `ctrl_hypothesis_exists_on_point_lattice` — on the one-site lattice `LatPt = fun _ => 0` the
  no-go's conclusion is FALSE at EVERY `n` and EVERY `ell`. So "some direction has ≥ 2 sites" is
  load-bearing. This is also the `(ell, Lat)` where the last layer is empty for `ell ≥ 2`.
* `ctrl_kimi_at_ell_two` — the compiled `ell = 2` theorem of `KimiRGLadderScratch` is re-derived as
  an instance of the general one, so the generalization provably covers the case it generalizes.
* `ctrl_originBond_onSomeStaircase` — the must-NOT-fire direction: at `ell = 2` on `Lat4` the
  ORIGIN-anchored bond `(originSite, 0)` IS in `S(2)`, so the exclusion machinery does not accept
  every bond. (This is `kimi_kerBondA_mem_staircase` re-expressed through `OnSomeStaircase`.)
  `ctrl_layerOne_bond_free` is its must-FIRE twin on the same lattice, same `ell`, same direction:
  shifting the base site by one in coordinate `0` flips the verdict.
* `ctrl_blockRepSite_update_ne_at_one` and `ctrl_onSomeStaircase_ell_zero` /
  `ctrl_dir0_iff_false_at_ell_zero` — the two remaining hypotheses (`n ≠ 1` at the level of the
  block map, `0 < ell` in §6b) each shown FALSE-when-dropped.
-/

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice inBlock mem_blockOf
  mem_CoarseLattice admissibleSubspaceInter mem_admissibleSubspaceInter staircasePath
  axisSegment mem_axisSegment corner1 corner2)
open AdalyFormal.Balaban.RGLadderCoarse
open scoped InnerProductSpace

namespace AdalyFormal.Balaban.LastLayerNoGo

variable {Lat : PeriodicLatticeExtent}

/-! ## §0 — the arithmetic core -/

/-- **The window lemma.** A coordinate strictly inside the half-open window `[Y, X)` of a block
based at a multiple `Y` of `ell`, with `X` still inside the block, cannot sit in the block's LAST
layer. (The hypotheses already force `0 < ell`; no positivity hypothesis is needed.) -/
theorem not_last_of_window {ell Y T X : ℕ} (hY : Y % ell = 0)
    (h1 : Y ≤ T) (h2 : T < X) (h3 : X < Y + ell) : T % ell ≠ ell - 1 := by
  intro hT
  have hell : 0 < ell := by omega
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hY
  have hTY : T - Y < ell := by omega
  have hsplit : T = ell * q + (T - Y) := by omega
  have hmod : T % ell = T - Y := by
    conv_lhs => rw [hsplit]
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hTY
  have hEq : T - Y = ell - 1 := by rw [← hmod, hT]
  omega

/-! ## §1 — the corners of the staircase, evaluated -/

theorem corner1_apply_zero (y x : PeriodicLatticeSite Lat) : corner1 y x 0 = y 0 := by
  simp [corner1]

theorem corner1_apply_one (y x : PeriodicLatticeSite Lat) : corner1 y x 1 = y 1 := by
  simp [corner1]

theorem corner1_apply_two (y x : PeriodicLatticeSite Lat) : corner1 y x 2 = x 2 := by
  simp [corner1]

theorem corner2_apply_zero (y x : PeriodicLatticeSite Lat) : corner2 y x 0 = y 0 := by
  simp [corner2, corner1]

theorem corner2_apply_one (y x : PeriodicLatticeSite Lat) : corner2 y x 1 = x 1 := by
  simp [corner2]

theorem corner2_apply_two (y x : PeriodicLatticeSite Lat) : corner2 y x 2 = x 2 := by
  simp [corner2, corner1]

/-! ## §2 — `S(ell)`, the union of all staircases: the EXCLUSION half

Every lemma here is unconditional in `ell` and needs no divisibility/tileability hypothesis. -/

/-- **`b` lies on SOME staircase of SOME valid `(y, x)` pair** — the bond set on which
`admissibleSubspaceInter L ell` forces vanishing. -/
def OnSomeStaircase (Lat : PeriodicLatticeExtent) (ell : ℕ) (b : Bond Lat) : Prop :=
  ∃ y ∈ CoarseLattice Lat ell, ∃ x ∈ blockOf y ell, b ∈ staircasePath y x

/-- **Direction 0, MODULAR exclusion.** A direction-`0` bond based in the LAST layer of its block
(`% ell = ell - 1`) lies on no staircase: the direction-`0` segment must stop strictly before the
block's far face. -/
theorem dir0_not_mem_staircase_mod {ell : ℕ} {y x : PeriodicLatticeSite Lat}
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell)
    {s : PeriodicLatticeSite Lat} (hs : (s 0).val % ell = ell - 1) :
    (s, (0 : Fin 3)) ∉ staircasePath y x := by
  intro hb
  rw [mem_CoarseLattice] at hy
  rw [mem_blockOf] at hx
  rw [staircasePath, Finset.mem_union, Finset.mem_union] at hb
  rcases hb with (h2 | h1) | h0
  · rw [mem_axisSegment] at h2
    exact absurd h2.1 (show ¬ ((0 : Fin 3) = 2) by decide)
  · rw [mem_axisSegment] at h1
    exact absurd h1.1 (show ¬ ((0 : Fin 3) = 1) by decide)
  · rw [mem_axisSegment] at h0
    obtain ⟨-, -, hlo, hhi⟩ := h0
    rw [min_eq_left (hx 0).1] at hlo
    rw [max_eq_right (hx 0).1] at hhi
    exact not_last_of_window (hy 0) hlo hhi (hx 0).2 hs

/-- **Direction 1, MODULAR exclusion.** Either the bond's `0`-coordinate is off the coarse corner
(so the direction-`1` segment, which pins coordinate `0` to `y 0`, cannot reach it), or its
`1`-coordinate is in the last layer. -/
theorem dir1_not_mem_staircase_mod {ell : ℕ} {y x : PeriodicLatticeSite Lat}
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell)
    {s : PeriodicLatticeSite Lat}
    (hs : (s 0).val % ell ≠ 0 ∨ (s 1).val % ell = ell - 1) :
    (s, (1 : Fin 3)) ∉ staircasePath y x := by
  intro hb
  rw [mem_CoarseLattice] at hy
  rw [mem_blockOf] at hx
  rw [staircasePath, Finset.mem_union, Finset.mem_union] at hb
  rcases hb with (h2 | h1) | h0
  · rw [mem_axisSegment] at h2
    exact absurd h2.1 (show ¬ ((1 : Fin 3) = 2) by decide)
  · rw [mem_axisSegment] at h1
    obtain ⟨-, hother, hlo, hhi⟩ := h1
    have h00 : s 0 = y 0 := by
      have := hother 0 (by decide)
      rwa [corner1_apply_zero] at this
    rcases hs with hs0 | hs1
    · exact hs0 (by rw [h00]; exact hy 0)
    · rw [min_eq_left (hx 1).1] at hlo
      rw [max_eq_right (hx 1).1] at hhi
      exact not_last_of_window (hy 1) hlo hhi (hx 1).2 hs1
  · rw [mem_axisSegment] at h0
    exact absurd h0.1 (show ¬ ((1 : Fin 3) = 0) by decide)

/-- **Direction 2, MODULAR exclusion.** The direction-`2` segment is based at `y` itself, so it
pins BOTH coordinates `0` and `1` to the coarse corner. -/
theorem dir2_not_mem_staircase_mod {ell : ℕ} {y x : PeriodicLatticeSite Lat}
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell)
    {s : PeriodicLatticeSite Lat}
    (hs : (s 0).val % ell ≠ 0 ∨ (s 1).val % ell ≠ 0 ∨ (s 2).val % ell = ell - 1) :
    (s, (2 : Fin 3)) ∉ staircasePath y x := by
  intro hb
  rw [mem_CoarseLattice] at hy
  rw [mem_blockOf] at hx
  rw [staircasePath, Finset.mem_union, Finset.mem_union] at hb
  rcases hb with (h2 | h1) | h0
  · rw [mem_axisSegment] at h2
    obtain ⟨-, hother, hlo, hhi⟩ := h2
    have h00 : s 0 = y 0 := hother 0 (by decide)
    have h11 : s 1 = y 1 := hother 1 (by decide)
    rcases hs with hs0 | hs1 | hs2
    · exact hs0 (by rw [h00]; exact hy 0)
    · exact hs1 (by rw [h11]; exact hy 1)
    · rw [min_eq_left (hx 2).1] at hlo
      rw [max_eq_right (hx 2).1] at hhi
      exact not_last_of_window (hy 2) hlo hhi (hx 2).2 hs2
  · rw [mem_axisSegment] at h1
    exact absurd h1.1 (show ¬ ((2 : Fin 3) = 1) by decide)
  · rw [mem_axisSegment] at h0
    exact absurd h0.1 (show ¬ ((2 : Fin 3) = 0) by decide)

/-! ### §2b — the EXTENT (truncation) exclusions

**These are boundary artifacts of the encoding**, recorded because they are true of the object
`Spine` actually pins and because they decide the degenerate lattices. `axisSegment` sweeps raw
natural coordinates with `<`; it never wraps. A bond based at the top coordinate value of an axis is
therefore on no segment in that direction, whatever `ell` is. -/

theorem dir0_not_mem_staircase_top {y x s : PeriodicLatticeSite Lat}
    (hs : Lat 0 ≤ (s 0).val) : (s, (0 : Fin 3)) ∉ staircasePath y x := by
  intro hb
  rw [staircasePath, Finset.mem_union, Finset.mem_union] at hb
  rcases hb with (h2 | h1) | h0
  · rw [mem_axisSegment] at h2
    exact absurd h2.1 (show ¬ ((0 : Fin 3) = 2) by decide)
  · rw [mem_axisSegment] at h1
    exact absurd h1.1 (show ¬ ((0 : Fin 3) = 1) by decide)
  · rw [mem_axisSegment] at h0
    obtain ⟨-, -, -, hhi⟩ := h0
    have hhi' : (s 0).val < max (y 0).val (x 0).val := hhi
    have hmax : max (y 0).val (x 0).val ≤ Lat 0 :=
      max_le (Nat.lt_succ_iff.mp (y 0).isLt) (Nat.lt_succ_iff.mp (x 0).isLt)
    omega

theorem dir1_not_mem_staircase_top {y x s : PeriodicLatticeSite Lat}
    (hs : Lat 1 ≤ (s 1).val) : (s, (1 : Fin 3)) ∉ staircasePath y x := by
  intro hb
  rw [staircasePath, Finset.mem_union, Finset.mem_union] at hb
  rcases hb with (h2 | h1) | h0
  · rw [mem_axisSegment] at h2
    exact absurd h2.1 (show ¬ ((1 : Fin 3) = 2) by decide)
  · rw [mem_axisSegment] at h1
    obtain ⟨-, -, -, hhi⟩ := h1
    have hhi' : (s 1).val < max (y 1).val (x 1).val := hhi
    have hmax : max (y 1).val (x 1).val ≤ Lat 1 :=
      max_le (Nat.lt_succ_iff.mp (y 1).isLt) (Nat.lt_succ_iff.mp (x 1).isLt)
    omega
  · rw [mem_axisSegment] at h0
    exact absurd h0.1 (show ¬ ((1 : Fin 3) = 0) by decide)

theorem dir2_not_mem_staircase_top {y x s : PeriodicLatticeSite Lat}
    (hs : Lat 2 ≤ (s 2).val) : (s, (2 : Fin 3)) ∉ staircasePath y x := by
  intro hb
  rw [staircasePath, Finset.mem_union, Finset.mem_union] at hb
  rcases hb with (h2 | h1) | h0
  · rw [mem_axisSegment] at h2
    obtain ⟨-, -, -, hhi⟩ := h2
    have hhi' : (s 2).val < max (y 2).val (x 2).val := hhi
    have hmax : max (y 2).val (x 2).val ≤ Lat 2 :=
      max_le (Nat.lt_succ_iff.mp (y 2).isLt) (Nat.lt_succ_iff.mp (x 2).isLt)
    omega
  · rw [mem_axisSegment] at h1
    exact absurd h1.1 (show ¬ ((2 : Fin 3) = 1) by decide)
  · rw [mem_axisSegment] at h0
    exact absurd h0.1 (show ¬ ((2 : Fin 3) = 0) by decide)

/-! ### §2c — `OnSomeStaircase` forms -/

theorem not_onSomeStaircase_dir0_mod {ell : ℕ} {s : PeriodicLatticeSite Lat}
    (hs : (s 0).val % ell = ell - 1) : ¬ OnSomeStaircase Lat ell (s, (0 : Fin 3)) := by
  rintro ⟨y, hy, x, hx, hb⟩
  exact dir0_not_mem_staircase_mod hy hx hs hb

theorem not_onSomeStaircase_dir1_mod {ell : ℕ} {s : PeriodicLatticeSite Lat}
    (hs : (s 0).val % ell ≠ 0 ∨ (s 1).val % ell = ell - 1) :
    ¬ OnSomeStaircase Lat ell (s, (1 : Fin 3)) := by
  rintro ⟨y, hy, x, hx, hb⟩
  exact dir1_not_mem_staircase_mod hy hx hs hb

theorem not_onSomeStaircase_dir2_mod {ell : ℕ} {s : PeriodicLatticeSite Lat}
    (hs : (s 0).val % ell ≠ 0 ∨ (s 1).val % ell ≠ 0 ∨ (s 2).val % ell = ell - 1) :
    ¬ OnSomeStaircase Lat ell (s, (2 : Fin 3)) := by
  rintro ⟨y, hy, x, hx, hb⟩
  exact dir2_not_mem_staircase_mod hy hx hs hb

theorem not_onSomeStaircase_dir0_top {ell : ℕ} {s : PeriodicLatticeSite Lat}
    (hs : Lat 0 ≤ (s 0).val) : ¬ OnSomeStaircase Lat ell (s, (0 : Fin 3)) := by
  rintro ⟨y, hy, x, hx, hb⟩
  exact dir0_not_mem_staircase_top hs hb

theorem not_onSomeStaircase_dir1_top {ell : ℕ} {s : PeriodicLatticeSite Lat}
    (hs : Lat 1 ≤ (s 1).val) : ¬ OnSomeStaircase Lat ell (s, (1 : Fin 3)) := by
  rintro ⟨y, hy, x, hx, hb⟩
  exact dir1_not_mem_staircase_top hs hb

theorem not_onSomeStaircase_dir2_top {ell : ℕ} {s : PeriodicLatticeSite Lat}
    (hs : Lat 2 ≤ (s 2).val) : ¬ OnSomeStaircase Lat ell (s, (2 : Fin 3)) := by
  rintro ⟨y, hy, x, hx, hb⟩
  exact dir2_not_mem_staircase_top hs hb

/-! ## §3 — `anchoredVInter ell` IS the coordinate subspace of fields vanishing on `S(ell)` -/

theorem mem_anchoredVInter_iff_vanish {ell : ℕ} {v : Anchoring.AnchoredBondSpace Lat} :
    v ∈ Anchoring.anchoredVInter (Lat := Lat) ell ↔
      ∀ b : Bond Lat, OnSomeStaircase Lat ell b → WithLp.ofLp v b = 0 := by
  rw [KimiRGLadderScratch.kimi_mem_anchoredVInter_iff, mem_admissibleSubspaceInter]
  constructor
  · rintro h b ⟨y, hy, x, hx, hb⟩
    exact h y hy x hx b hb
  · intro h y hy x hx b hb
    exact h b ⟨y, hy, x, hx, hb⟩

/-! ## §4 — the pair engine: two staircase-free bonds in one fibre refute the ladder -/

/-- The difference of two bond deltas. -/
noncomputable def pairVec (b₁ b₂ : Bond Lat) : Anchoring.AnchoredBondSpace Lat :=
  EuclideanSpace.single b₁ (1 : ℝ) - EuclideanSpace.single b₂ (1 : ℝ)

theorem pairVec_ofLp (b₁ b₂ b : Bond Lat) :
    WithLp.ofLp (pairVec (Lat := Lat) b₁ b₂) b
      = (if b = b₁ then (1 : ℝ) else 0) - (if b = b₂ then (1 : ℝ) else 0) := by
  simp [pairVec]

theorem pairVec_ne_zero {b₁ b₂ : Bond Lat} (hne : b₁ ≠ b₂) :
    pairVec (Lat := Lat) b₁ b₂ ≠ 0 := by
  intro hz
  have h := congrFun (congrArg WithLp.ofLp hz) b₁
  rw [pairVec_ofLp] at h
  rw [if_pos rfl, if_neg hne] at h
  norm_num at h

/-- The fibre-sum operator kills a difference of two bonds in one fibre. -/
theorem sumCLMof_pairVec {n : ℕ} {b₁ b₂ : Bond Lat}
    (hrep : blockRepBond (Lat := Lat) n b₁ = blockRepBond (Lat := Lat) n b₂) :
    sumCLMof (blockRepBond (Lat := Lat) n) (pairVec b₁ b₂) = 0 := by
  refine euclid_eq_zero ?_
  intro c
  rw [pairVec, map_sub]
  simp only [WithLp.ofLp_sub, Pi.sub_apply]
  rw [sumCLMof_single, sumCLMof_single, hrep]
  simp

theorem rgDelta_pairVec {n : ℕ} {b₁ b₂ : Bond Lat}
    (hrep : blockRepBond (Lat := Lat) n b₁ = blockRepBond (Lat := Lat) n b₂) :
    rgDelta (Lat := Lat) n (pairVec b₁ b₂) = 0 := by
  rw [rgDelta_eq_deltaOf, deltaOf]
  simp [sumCLMof_pairVec hrep]

theorem pairVec_mem_anchoredVInter {ell : ℕ} {b₁ b₂ : Bond Lat}
    (h₁ : ¬ OnSomeStaircase Lat ell b₁) (h₂ : ¬ OnSomeStaircase Lat ell b₂) :
    pairVec (Lat := Lat) b₁ b₂ ∈ Anchoring.anchoredVInter (Lat := Lat) ell := by
  rw [mem_anchoredVInter_iff_vanish]
  intro b hb
  have hb₁ : b ≠ b₁ := fun h => h₁ (h ▸ hb)
  have hb₂ : b ≠ b₂ := fun h => h₂ (h ▸ hb)
  rw [pairVec_ofLp, if_neg hb₁, if_neg hb₂, sub_zero]

/-- **THE ENGINE.** Two distinct bonds off `S(ell)` that the block map at side `n` identifies
refute every `CoercivityHypothesis` with `V = anchoredVInter ell` having `rgDelta n` at one rung. -/
theorem no_coercivityHypothesis_of_free_pair {Uconfig : Type*} [Nontrivial Uconfig]
    (cohyp : Balaban.CoercivityHypothesis (Anchoring.AnchoredBondSpace Lat) Uconfig)
    {ell n : ℕ} (hV : cohyp.V = Anchoring.anchoredVInter (Lat := Lat) ell)
    (k₀ : ℕ) (U₀ : Uconfig) (hΔ : cohyp.Δ k₀ U₀ = rgDelta (Lat := Lat) n)
    {b₁ b₂ : Bond Lat} (hne : b₁ ≠ b₂)
    (hrep : blockRepBond (Lat := Lat) n b₁ = blockRepBond (Lat := Lat) n b₂)
    (h₁ : ¬ OnSomeStaircase Lat ell b₁) (h₂ : ¬ OnSomeStaircase Lat ell b₂) : False := by
  refine RGLadderCore.no_uniform_ladder_of_one_small_rung cohyp k₀ U₀ ?_ (pairVec_ne_zero hne) ?_
  · rw [hV]; exact pairVec_mem_anchoredVInter h₁ h₂
  · rw [hΔ]; exact rgDelta_pairVec hrep

/-! ## §5 — the witnesses -/

/-- Two sites differing only at axis `ν`, with `ν`-values `0` and `1`, share their block
representative at EVERY side `n ≠ 1` (`n = 0` collapses everything; `n ≥ 2` merges `0` with `1`).
`n = 1` is exactly the excluded value: there the block map is the identity. -/
theorem blockRepSite_update_eq {n : ℕ} (hn : n ≠ 1) (s : PeriodicLatticeSite Lat) (ν : Fin 3)
    (j j' : Fin (Lat ν + 1)) (hj : (j : ℕ) ≤ 1) (hj' : (j' : ℕ) ≤ 1) :
    blockRepSite n (Function.update s ν j) = blockRepSite n (Function.update s ν j') := by
  have key : ∀ m : ℕ, m ≤ 1 → m / n * n = 0 := by
    intro m hm
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · simp [hn0]
    · have : m < n := by omega
      rw [Nat.div_eq_of_lt this, Nat.zero_mul]
  funext μ
  refine Fin.ext ?_
  rw [blockRepSite_val, blockRepSite_val]
  by_cases h : μ = ν
  · subst h
    rw [Function.update_self, Function.update_self, key _ hj, key _ hj']
  · rw [Function.update_of_ne h, Function.update_of_ne h]

/-- The two sites are genuinely distinct. -/
theorem update_ne_update {s : PeriodicLatticeSite Lat} {ν : Fin 3} {j j' : Fin (Lat ν + 1)}
    (h : j ≠ j') : Function.update s ν j ≠ Function.update s ν j' := by
  intro hEq
  have := congrFun hEq ν
  rw [Function.update_self, Function.update_self] at this
  exact h this

/-- Off-axis coordinates are untouched by the split. -/
theorem update_apply_of_ne {s : PeriodicLatticeSite Lat} {ν μ : Fin 3} (h : μ ≠ ν)
    (j : Fin (Lat ν + 1)) : Function.update s ν j μ = s μ := Function.update_of_ne h _ _

/-- The base site of the last-layer family: coordinate `0` equal to `ell - 1`, all others `0`. -/
def lastLayerBase (Lat : PeriodicLatticeExtent) (ell : ℕ) (h : ell - 1 ≤ Lat 0) :
    PeriodicLatticeSite Lat :=
  Function.update (originSite (Lat := Lat)) 0 ⟨ell - 1, by omega⟩

theorem lastLayerBase_apply_zero {ell : ℕ} (h : ell - 1 ≤ Lat 0) :
    ((lastLayerBase Lat ell h) 0).val = ell - 1 := by
  rw [lastLayerBase, Function.update_self]

/-- `(ell - 1) % ell = ell - 1`, including the degenerate `ell = 0` (where `0 % 0 = 0`). -/
theorem sub_one_mod_self (ell : ℕ) : (ell - 1) % ell = ell - 1 := by
  rcases Nat.eq_zero_or_pos ell with h | h
  · simp [h]
  · exact Nat.mod_eq_of_lt (by omega)

/-- **THE LAST-LAYER NO-GO, GENERAL `(ell, n, Lat)`.** Direction-`0` bonds based in the last layer
of the origin block, split along a second axis `ν ≠ 0`.

**Load-bearing hypotheses, exactly:** `n ≠ 1` (else `rgDelta n = id`; refuted by
`ctrl_hypothesis_exists_at_n_one`), `ell - 1 ≤ Lat 0` (the last layer must contain a site), and
`1 ≤ Lat ν` for some `ν ≠ 0` (the split axis must have two sites; refuted by
`ctrl_hypothesis_exists_on_point_lattice`).

**NOT needed:** any bound on `ell` (the theorem holds at `ell = 0` and `ell = 1` too), any
divisibility `ell ∣ Lat μ + 1`, any relation between `n` and `ell`, and `Nontrivial` beyond what
the structure already carries. The proof uses only the MODULAR exclusion, so no lattice-boundary
truncation enters. -/
theorem no_coercivityHypothesis_lastLayer {Uconfig : Type*} [Nontrivial Uconfig]
    (cohyp : Balaban.CoercivityHypothesis (Anchoring.AnchoredBondSpace Lat) Uconfig)
    {ell n : ℕ} (hV : cohyp.V = Anchoring.anchoredVInter (Lat := Lat) ell)
    (k₀ : ℕ) (U₀ : Uconfig) (hΔ : cohyp.Δ k₀ U₀ = rgDelta (Lat := Lat) n)
    (hn : n ≠ 1) (hLat0 : ell - 1 ≤ Lat 0) (ν : Fin 3) (hν : ν ≠ 0) (hLatν : 1 ≤ Lat ν) :
    False := by
  set s := lastLayerBase Lat ell hLat0 with hs
  set j0 : Fin (Lat ν + 1) := ⟨0, by omega⟩ with hj0
  set j1 : Fin (Lat ν + 1) := ⟨1, by omega⟩ with hj1
  have hcoord : ∀ j : Fin (Lat ν + 1), ((Function.update s ν j) 0).val % ell = ell - 1 := by
    intro j
    rw [update_apply_of_ne (Ne.symm hν) j, hs, lastLayerBase_apply_zero, sub_one_mod_self]
  refine no_coercivityHypothesis_of_free_pair cohyp hV k₀ U₀ hΔ
    (b₁ := (Function.update s ν j0, (0 : Fin 3))) (b₂ := (Function.update s ν j1, (0 : Fin 3)))
    ?_ ?_ (not_onSomeStaircase_dir0_mod (hcoord j0)) (not_onSomeStaircase_dir0_mod (hcoord j1))
  · intro hEq
    exact update_ne_update (by simp [hj0, hj1, Fin.ext_iff]) (congrArg Prod.fst hEq)
  · unfold blockRepBond
    rw [blockRepSite_update_eq hn s ν j0 j1 (by simp [hj0]) (by simp [hj1])]

/-- The base site of the off-corner family: coordinate `0` equal to `1`, all others `0`. -/
def offCornerBase (Lat : PeriodicLatticeExtent) (h : 1 ≤ Lat 0) : PeriodicLatticeSite Lat :=
  Function.update (originSite (Lat := Lat)) 0 ⟨1, by omega⟩

theorem offCornerBase_apply_zero (h : 1 ≤ Lat 0) : ((offCornerBase Lat h) 0).val = 1 := by
  rw [offCornerBase, Function.update_self]

/-- **THE OFF-CORNER NO-GO.** Direction-`1` bonds based at a site whose `0`-coordinate is not a
multiple of `ell`. Also truncation-free. Cheaper in `Lat 0` than the last-layer family
(`1 ≤ Lat 0` instead of `ell - 1 ≤ Lat 0`), at the cost of `2 ≤ ell`. -/
theorem no_coercivityHypothesis_offCorner {Uconfig : Type*} [Nontrivial Uconfig]
    (cohyp : Balaban.CoercivityHypothesis (Anchoring.AnchoredBondSpace Lat) Uconfig)
    {ell n : ℕ} (hV : cohyp.V = Anchoring.anchoredVInter (Lat := Lat) ell)
    (k₀ : ℕ) (U₀ : Uconfig) (hΔ : cohyp.Δ k₀ U₀ = rgDelta (Lat := Lat) n)
    (hn : n ≠ 1) (hell : 2 ≤ ell) (hLat0 : 1 ≤ Lat 0) (ν : Fin 3) (hν : ν ≠ 0)
    (hLatν : 1 ≤ Lat ν) : False := by
  set s := offCornerBase Lat hLat0 with hs
  set j0 : Fin (Lat ν + 1) := ⟨0, by omega⟩ with hj0
  set j1 : Fin (Lat ν + 1) := ⟨1, by omega⟩ with hj1
  have hcoord : ∀ j : Fin (Lat ν + 1), ((Function.update s ν j) 0).val % ell ≠ 0 := by
    intro j
    rw [update_apply_of_ne (Ne.symm hν) j, hs, offCornerBase_apply_zero,
      Nat.mod_eq_of_lt (by omega)]
    omega
  refine no_coercivityHypothesis_of_free_pair cohyp hV k₀ U₀ hΔ
    (b₁ := (Function.update s ν j0, (1 : Fin 3))) (b₂ := (Function.update s ν j1, (1 : Fin 3)))
    ?_ ?_ (not_onSomeStaircase_dir1_mod (Or.inl (hcoord j0)))
    (not_onSomeStaircase_dir1_mod (Or.inl (hcoord j1)))
  · intro hEq
    exact update_ne_update (by simp [hj0, hj1, Fin.ext_iff]) (congrArg Prod.fst hEq)
  · unfold blockRepBond
    rw [blockRepSite_update_eq hn s ν j0 j1 (by simp [hj0]) (by simp [hj1])]

/-- The top site of axis `μ₀`. -/
def topSite (Lat : PeriodicLatticeExtent) (μ₀ : Fin 3) : PeriodicLatticeSite Lat :=
  Function.update (originSite (Lat := Lat)) μ₀ ⟨Lat μ₀, Nat.lt_succ_self _⟩

theorem topSite_apply_self (μ₀ : Fin 3) : ((topSite Lat μ₀) μ₀).val = Lat μ₀ := by
  rw [topSite, Function.update_self]

/-- **THE TOP-LAYER NO-GO — TRUNCATION-DRIVEN, recorded not relied upon.** Bonds in direction `μ₀`
based at the TOP coordinate value of axis `μ₀` lie on no staircase for the trivial reason that
`axisSegment` never wraps around the periodic identification. This covers the lattices the two
interior families miss (e.g. `Lat 0 = 0` with `ell ≥ 2`), and it is the reason the sharp
characterization below needs no hypothesis on `ell` at all. -/
theorem no_coercivityHypothesis_topLayer {Uconfig : Type*} [Nontrivial Uconfig]
    (cohyp : Balaban.CoercivityHypothesis (Anchoring.AnchoredBondSpace Lat) Uconfig)
    {ell n : ℕ} (hV : cohyp.V = Anchoring.anchoredVInter (Lat := Lat) ell)
    (k₀ : ℕ) (U₀ : Uconfig) (hΔ : cohyp.Δ k₀ U₀ = rgDelta (Lat := Lat) n)
    (hn : n ≠ 1) (μ₀ ν : Fin 3) (hν : ν ≠ μ₀) (hLatν : 1 ≤ Lat ν)
    (hμ₀ : μ₀ = 0 ∨ μ₀ = 1 ∨ μ₀ = 2) : False := by
  set s := topSite Lat μ₀ with hs
  set j0 : Fin (Lat ν + 1) := ⟨0, by omega⟩ with hj0
  set j1 : Fin (Lat ν + 1) := ⟨1, by omega⟩ with hj1
  have hcoord : ∀ j : Fin (Lat ν + 1), Lat μ₀ ≤ ((Function.update s ν j) μ₀).val := by
    intro j
    rw [update_apply_of_ne (Ne.symm hν) j, hs, topSite_apply_self]
  have hfree : ∀ j : Fin (Lat ν + 1),
      ¬ OnSomeStaircase Lat ell (Function.update s ν j, μ₀) := by
    intro j
    rcases hμ₀ with h | h | h
    · subst h; exact not_onSomeStaircase_dir0_top (hcoord j)
    · subst h; exact not_onSomeStaircase_dir1_top (hcoord j)
    · subst h; exact not_onSomeStaircase_dir2_top (hcoord j)
  refine no_coercivityHypothesis_of_free_pair cohyp hV k₀ U₀ hΔ
    (b₁ := (Function.update s ν j0, μ₀)) (b₂ := (Function.update s ν j1, μ₀))
    ?_ ?_ (hfree j0) (hfree j1)
  · intro hEq
    exact update_ne_update (by simp [hj0, hj1, Fin.ext_iff]) (congrArg Prod.fst hEq)
  · unfold blockRepBond
    rw [blockRepSite_update_eq hn s ν j0 j1 (by simp [hj0]) (by simp [hj1])]

/-- **THE SHARP NO-GO.** For EVERY `ell` and every `n ≠ 1`: as soon as the lattice has two sites
(one axis `ν` with `1 ≤ Lat ν`), no `CoercivityHypothesis` with `V = anchoredVInter ell` can carry
`rgDelta n` at any rung. Proof by two cases on whether the split axis is `0`; each case uses the
top-layer family, which is the only one that needs no arithmetic side condition. -/
theorem no_coercivityHypothesis_rgLadder_general {Uconfig : Type*} [Nontrivial Uconfig]
    (cohyp : Balaban.CoercivityHypothesis (Anchoring.AnchoredBondSpace Lat) Uconfig)
    {ell n : ℕ} (hV : cohyp.V = Anchoring.anchoredVInter (Lat := Lat) ell)
    (k₀ : ℕ) (U₀ : Uconfig) (hΔ : cohyp.Δ k₀ U₀ = rgDelta (Lat := Lat) n)
    (hn : n ≠ 1) (ν : Fin 3) (hLatν : 1 ≤ Lat ν) : False := by
  by_cases h : ν = 0
  · subst h
    exact no_coercivityHypothesis_topLayer cohyp hV k₀ U₀ hΔ hn 1 0 (by decide) hLatν
      (Or.inr (Or.inl rfl))
  · exact no_coercivityHypothesis_topLayer cohyp hV k₀ U₀ hΔ hn 0 ν h hLatν (Or.inl rfl)

/-! ## §6 — the kernel of `rgDelta n` against `anchoredVInter ell`, characterized EXACTLY -/

/-- **THE CHARACTERIZATION.** The intersection of `ker (rgDelta n)` with `anchoredVInter ell` is
nontrivial **iff** two distinct bonds off `S(ell)` share a `blockRepBond n`-fibre. The forward
direction is a pigeonhole on a vanishing fibre sum: any nonzero element of the intersection
manufactures such a pair, so no kernel vector can survive in `V` for any other reason.

**No hypothesis on `n`, `ell` or `Lat`.** A `0 < n` hypothesis was carried in the first draft and
the unused-variable linter proved it decorative: the pigeonhole never inspects the block side, and
the difference witness works at `n = 0` (where every site collapses to the origin) as well. -/
theorem kernel_inter_ne_bot_iff {ell n : ℕ} :
    (∃ v : Anchoring.AnchoredBondSpace Lat, v ≠ 0 ∧
        v ∈ Anchoring.anchoredVInter (Lat := Lat) ell ∧ rgDelta (Lat := Lat) n v = 0) ↔
      (∃ b₁ b₂ : Bond Lat, b₁ ≠ b₂ ∧
        blockRepBond (Lat := Lat) n b₁ = blockRepBond (Lat := Lat) n b₂ ∧
        ¬ OnSomeStaircase Lat ell b₁ ∧ ¬ OnSomeStaircase Lat ell b₂) := by
  constructor
  · rintro ⟨v, hv0, hvV, hvK⟩
    have hA : sumCLMof (blockRepBond (Lat := Lat) n) v = 0 :=
      sumCLMof_eq_zero_of_deltaOf _ (by rwa [← rgDelta_eq_deltaOf])
    -- pick a coordinate where `v` does not vanish
    have hex : ∃ b : Bond Lat, WithLp.ofLp v b ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hv0 (euclid_eq_zero hcon)
    obtain ⟨b₁, hb₁⟩ := hex
    -- the fibre sum through `b₁` vanishes, so a second nonzero coordinate shares its fibre
    have hsum : ∑ b ∈ Finset.univ.filter
        (fun b => blockRepBond (Lat := Lat) n b = blockRepBond (Lat := Lat) n b₁),
        WithLp.ofLp v b = 0 := by
      have := congrFun (congrArg WithLp.ofLp hA) (blockRepBond (Lat := Lat) n b₁)
      rw [sumCLMof_apply] at this
      simpa using this
    have hmem₁ : b₁ ∈ Finset.univ.filter
        (fun b => blockRepBond (Lat := Lat) n b = blockRepBond (Lat := Lat) n b₁) := by
      simp
    have hex₂ : ∃ b₂ ∈ Finset.univ.filter
        (fun b => blockRepBond (Lat := Lat) n b = blockRepBond (Lat := Lat) n b₁),
        b₂ ≠ b₁ ∧ WithLp.ofLp v b₂ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have hsingle := Finset.sum_eq_single_of_mem b₁ hmem₁
        (fun b hb hbne => hcon b hb hbne)
      rw [hsingle] at hsum
      exact hb₁ hsum
    obtain ⟨b₂, hb₂mem, hb₂ne, hb₂val⟩ := hex₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb₂mem
    rw [mem_anchoredVInter_iff_vanish] at hvV
    exact ⟨b₁, b₂, Ne.symm hb₂ne, hb₂mem.symm,
      fun hst => hb₁ (hvV b₁ hst), fun hst => hb₂val (hvV b₂ hst)⟩
  · rintro ⟨b₁, b₂, hne, hrep, h₁, h₂⟩
    exact ⟨pairVec b₁ b₂, pairVec_ne_zero hne, pairVec_mem_anchoredVInter h₁ h₂,
      rgDelta_pairVec hrep⟩

/-! ### §6b — `S(ell)` computed exactly, so the criterion of §6 is decidable arithmetic

The three lemmas below are the CONVERSES of §2: they build the `(y, x)` pair explicitly. Together
with §2 they pin `S(ell)` completely. `0 < ell` is needed here (and only here): the construction
uses `blockRepSite ell` as the coarse centre, which is a valid block corner only for `0 < ell`. -/

/-- The block corner of a site is a coarse-lattice member whose block contains the site. -/
theorem corner_mem {ell : ℕ} (hell : 0 < ell) (s : PeriodicLatticeSite Lat) :
    blockRepSite ell s ∈ CoarseLattice Lat ell ∧ s ∈ blockOf (blockRepSite ell s) ell :=
  ⟨blockRepSite_mem_CoarseLattice ell s, mem_blockOf_blockRepSite hell s⟩

/-- The successor site along axis `d`, as a named object (so its coordinates are `rfl`-visible to
`omega`). -/
def succSite (s : PeriodicLatticeSite Lat) (d : Fin 3) (h : (s d).val < Lat d) :
    PeriodicLatticeSite Lat :=
  Function.update s d ⟨(s d).val + 1, by omega⟩

theorem succSite_apply_self (s : PeriodicLatticeSite Lat) (d : Fin 3) (h : (s d).val < Lat d) :
    ((succSite s d h) d).val = (s d).val + 1 := by
  rw [succSite, Function.update_self]

theorem succSite_apply_of_ne (s : PeriodicLatticeSite Lat) (d : Fin 3) (h : (s d).val < Lat d)
    {μ : Fin 3} (hμ : μ ≠ d) : succSite s d h μ = s μ := Function.update_of_ne hμ _ _

/-- Every block corner coordinate is a multiple of `ell`, and the residue of a site in its own
block is exactly the offset from the corner. -/
theorem rem_eq_offset {ell : ℕ} (hell : 0 < ell) (s : PeriodicLatticeSite Lat) (μ : Fin 3) :
    (s μ).val % ell = (s μ).val - ((blockRepSite ell s) μ).val := by
  have hb := (mem_blockOf.mp (mem_blockOf_blockRepSite hell s)) μ
  have hval : ((blockRepSite ell s) μ).val % ell = 0 := by
    rw [blockRepSite_val]; exact Nat.mul_mod_left _ _
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hval
  have hlt' : (s μ).val - ((blockRepSite ell s) μ).val < ell := by omega
  have hsplit : (s μ).val = ell * q + ((s μ).val - ((blockRepSite ell s) μ).val) := by omega
  conv_lhs => rw [hsplit]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hlt'

/-- The successor site along `d` still lies in `s`'s own block, provided `s` is not in the block's
last layer along `d`. -/
theorem succSite_mem_blockOf {ell : ℕ} (hell : 0 < ell) (s : PeriodicLatticeSite Lat) (d : Fin 3)
    (hlt : (s d).val < Lat d) (hmod : (s d).val % ell ≠ ell - 1) :
    succSite s d hlt ∈ blockOf (blockRepSite ell s) ell := by
  rw [mem_blockOf]
  intro μ
  have hb := (mem_blockOf.mp (mem_blockOf_blockRepSite hell s)) μ
  by_cases h : μ = d
  · subst h
    have hval : ((succSite s μ hlt) μ).val = (s μ).val + 1 := succSite_apply_self s μ hlt
    have hrem := rem_eq_offset hell s μ
    rw [hval]
    omega
  · rw [succSite_apply_of_ne s d hlt h]
    exact hb

theorem onSomeStaircase_dir0_of {ell : ℕ} (hell : 0 < ell) {s : PeriodicLatticeSite Lat}
    (hmod : (s 0).val % ell ≠ ell - 1) (hlt : (s 0).val < Lat 0) :
    OnSomeStaircase Lat ell (s, (0 : Fin 3)) := by
  refine ⟨blockRepSite ell s, blockRepSite_mem_CoarseLattice ell s, succSite s 0 hlt,
    succSite_mem_blockOf hell s 0 hlt hmod, ?_⟩
  have hb := (mem_blockOf.mp (mem_blockOf_blockRepSite hell s)) 0
  have hval : ((succSite s 0 hlt) 0).val = (s 0).val + 1 := succSite_apply_self s 0 hlt
  rw [staircasePath, Finset.mem_union, Finset.mem_union]
  refine Or.inr ?_
  rw [mem_axisSegment]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro ν hν
    rcases (show ν = 1 ∨ ν = 2 by fin_cases ν <;> simp_all) with h | h
    · subst h
      rw [corner2_apply_one, succSite_apply_of_ne s 0 hlt (by decide)]
    · subst h
      rw [corner2_apply_two, succSite_apply_of_ne s 0 hlt (by decide)]
  · have hmin : min ((blockRepSite ell s) 0).val ((succSite s 0 hlt) 0).val
        ≤ ((blockRepSite ell s) 0).val := min_le_left _ _
    have hgoal : min ((blockRepSite ell s) 0).val ((succSite s 0 hlt) 0).val ≤ (s 0).val := by
      omega
    exact hgoal
  · have hmax : ((succSite s 0 hlt) 0).val
        ≤ max ((blockRepSite ell s) 0).val ((succSite s 0 hlt) 0).val := le_max_right _ _
    have hgoal : (s 0).val
        < max ((blockRepSite ell s) 0).val ((succSite s 0 hlt) 0).val := by omega
    exact hgoal

/-- **Direction 0, exact.** -/
theorem onSomeStaircase_dir0_iff {ell : ℕ} (hell : 0 < ell) {s : PeriodicLatticeSite Lat} :
    OnSomeStaircase Lat ell (s, (0 : Fin 3)) ↔
      ((s 0).val % ell ≠ ell - 1 ∧ (s 0).val < Lat 0) := by
  constructor
  · intro h
    refine ⟨fun hc => not_onSomeStaircase_dir0_mod hc h, ?_⟩
    by_contra hc
    exact not_onSomeStaircase_dir0_top (by omega) h
  · rintro ⟨h1, h2⟩
    exact onSomeStaircase_dir0_of hell h1 h2


/-- A coordinate that is a multiple of `ell` is its own block corner. -/
theorem blockRepSite_apply_eq_self {ell : ℕ} {s : PeriodicLatticeSite Lat} {μ : Fin 3}
    (h : (s μ).val % ell = 0) : ((blockRepSite ell s) μ).val = (s μ).val := by
  rw [blockRepSite_val]
  exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)

theorem onSomeStaircase_dir1_of {ell : ℕ} (hell : 0 < ell) {s : PeriodicLatticeSite Lat}
    (h0 : (s 0).val % ell = 0) (hmod : (s 1).val % ell ≠ ell - 1) (hlt : (s 1).val < Lat 1) :
    OnSomeStaircase Lat ell (s, (1 : Fin 3)) := by
  refine ⟨blockRepSite ell s, blockRepSite_mem_CoarseLattice ell s, succSite s 1 hlt,
    succSite_mem_blockOf hell s 1 hlt hmod, ?_⟩
  have hb := (mem_blockOf.mp (mem_blockOf_blockRepSite hell s)) 1
  have hval : ((succSite s 1 hlt) 1).val = (s 1).val + 1 := succSite_apply_self s 1 hlt
  rw [staircasePath, Finset.mem_union, Finset.mem_union]
  refine Or.inl (Or.inr ?_)
  rw [mem_axisSegment]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro ν hν
    rcases (show ν = 0 ∨ ν = 2 by fin_cases ν <;> simp_all) with h | h
    · subst h
      rw [corner1_apply_zero]
      exact (Fin.ext (blockRepSite_apply_eq_self h0)).symm
    · subst h
      rw [corner1_apply_two, succSite_apply_of_ne s 1 hlt (by decide)]
  · have hmin : min ((blockRepSite ell s) 1).val ((succSite s 1 hlt) 1).val
        ≤ ((blockRepSite ell s) 1).val := min_le_left _ _
    have hgoal : min ((blockRepSite ell s) 1).val ((succSite s 1 hlt) 1).val ≤ (s 1).val := by
      omega
    exact hgoal
  · have hmax : ((succSite s 1 hlt) 1).val
        ≤ max ((blockRepSite ell s) 1).val ((succSite s 1 hlt) 1).val := le_max_right _ _
    have hgoal : (s 1).val
        < max ((blockRepSite ell s) 1).val ((succSite s 1 hlt) 1).val := by omega
    exact hgoal

theorem onSomeStaircase_dir2_of {ell : ℕ} (hell : 0 < ell) {s : PeriodicLatticeSite Lat}
    (h0 : (s 0).val % ell = 0) (h1 : (s 1).val % ell = 0) (hmod : (s 2).val % ell ≠ ell - 1)
    (hlt : (s 2).val < Lat 2) : OnSomeStaircase Lat ell (s, (2 : Fin 3)) := by
  refine ⟨blockRepSite ell s, blockRepSite_mem_CoarseLattice ell s, succSite s 2 hlt,
    succSite_mem_blockOf hell s 2 hlt hmod, ?_⟩
  have hb := (mem_blockOf.mp (mem_blockOf_blockRepSite hell s)) 2
  have hval : ((succSite s 2 hlt) 2).val = (s 2).val + 1 := succSite_apply_self s 2 hlt
  rw [staircasePath, Finset.mem_union, Finset.mem_union]
  refine Or.inl (Or.inl ?_)
  rw [mem_axisSegment]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro ν hν
    rcases (show ν = 0 ∨ ν = 1 by fin_cases ν <;> simp_all) with h | h
    · subst h
      exact (Fin.ext (blockRepSite_apply_eq_self h0)).symm
    · subst h
      exact (Fin.ext (blockRepSite_apply_eq_self h1)).symm
  · have hmin : min ((blockRepSite ell s) 2).val ((succSite s 2 hlt) 2).val
        ≤ ((blockRepSite ell s) 2).val := min_le_left _ _
    have hgoal : min ((blockRepSite ell s) 2).val ((succSite s 2 hlt) 2).val ≤ (s 2).val := by
      omega
    exact hgoal
  · have hmax : ((succSite s 2 hlt) 2).val
        ≤ max ((blockRepSite ell s) 2).val ((succSite s 2 hlt) 2).val := le_max_right _ _
    have hgoal : (s 2).val
        < max ((blockRepSite ell s) 2).val ((succSite s 2 hlt) 2).val := by omega
    exact hgoal

/-- **Direction 1, exact.** -/
theorem onSomeStaircase_dir1_iff {ell : ℕ} (hell : 0 < ell) {s : PeriodicLatticeSite Lat} :
    OnSomeStaircase Lat ell (s, (1 : Fin 3)) ↔
      ((s 0).val % ell = 0 ∧ (s 1).val % ell ≠ ell - 1 ∧ (s 1).val < Lat 1) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · by_contra hc
      exact not_onSomeStaircase_dir1_mod (Or.inl hc) h
    · intro hc
      exact not_onSomeStaircase_dir1_mod (Or.inr hc) h
    · by_contra hc
      exact not_onSomeStaircase_dir1_top (by omega) h
  · rintro ⟨h0, h1, h2⟩
    exact onSomeStaircase_dir1_of hell h0 h1 h2

/-- **Direction 2, exact.** -/
theorem onSomeStaircase_dir2_iff {ell : ℕ} (hell : 0 < ell) {s : PeriodicLatticeSite Lat} :
    OnSomeStaircase Lat ell (s, (2 : Fin 3)) ↔
      ((s 0).val % ell = 0 ∧ (s 1).val % ell = 0 ∧ (s 2).val % ell ≠ ell - 1
        ∧ (s 2).val < Lat 2) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra hc
      exact not_onSomeStaircase_dir2_mod (Or.inl hc) h
    · by_contra hc
      exact not_onSomeStaircase_dir2_mod (Or.inr (Or.inl hc)) h
    · intro hc
      exact not_onSomeStaircase_dir2_mod (Or.inr (Or.inr hc)) h
    · by_contra hc
      exact not_onSomeStaircase_dir2_top (by omega) h
  · rintro ⟨h0, h1, h2, h3⟩
    exact onSomeStaircase_dir2_of hell h0 h1 h2 h3

/-! ## §7 — CONTROLS

Every control below is a COMPILED refutation of the no-go's conclusion at a specific input, not a
remark. If a hypothesis of §5 were decorative, the corresponding control would not be provable. -/

/-- The control operator family: `(U ? 1 : 2) • id`. Self-adjoint, PSD, coercive with `γ'' = 1` on
every subspace, genuinely `U`-dependent — everything `CoercivityHypothesis` demands — and equal to
the IDENTITY at `U = true`. -/
noncomputable def ctrlDelta (Lat : PeriodicLatticeExtent) (_k : ℕ) (U : Bool) :
    Anchoring.AnchoredBondSpace Lat →L[ℝ] Anchoring.AnchoredBondSpace Lat :=
  (if U then (1 : ℝ) else 2) • ContinuousLinearMap.id ℝ (Anchoring.AnchoredBondSpace Lat)

theorem ctrl_scale_ge_one (U : Bool) : (1 : ℝ) ≤ (if U then (1 : ℝ) else 2) := by
  split <;> norm_num

theorem ctrlDelta_true (k : ℕ) :
    ctrlDelta Lat k true = ContinuousLinearMap.id ℝ (Anchoring.AnchoredBondSpace Lat) := by
  simp [ctrlDelta]

theorem ctrl_inner (k : ℕ) (U : Bool) (v : Anchoring.AnchoredBondSpace Lat) :
    (inner ℝ v (ctrlDelta Lat k U v) : ℝ) = (if U then (1 : ℝ) else 2) * ‖v‖ ^ 2 := by
  rw [ctrlDelta]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  rw [inner_smul_right, real_inner_self_eq_norm_sq]

theorem ctrl_coercive (k : ℕ) (U : Bool) (v : Anchoring.AnchoredBondSpace Lat) :
    (1 : ℝ) * ‖v‖ ^ 2 ≤ (inner ℝ v (ctrlDelta Lat k U v) : ℝ) := by
  rw [ctrl_inner]
  nlinarith [sq_nonneg ‖v‖, ctrl_scale_ge_one U]

theorem ctrlDelta_adjoint (k : ℕ) (U : Bool) :
    (ctrlDelta Lat k U).adjoint = ctrlDelta Lat k U := by
  have h : ctrlDelta Lat k U = (ctrlDelta Lat k U).adjoint := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [ctrlDelta]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    rw [real_inner_smul_left, real_inner_smul_right]
  exact h.symm

theorem ctrlDelta_nonconstant :
    ∃ (k : ℕ) (U₁ U₂ : Bool), U₁ ≠ U₂ ∧ ctrlDelta Lat k U₁ ≠ ctrlDelta Lat k U₂ := by
  refine ⟨0, true, false, by decide, ?_⟩
  intro hEq
  obtain ⟨b⟩ := (bondSpace_nontrivial : Nonempty (Bond Lat))
  have h1 : (inner ℝ (EuclideanSpace.single b (1 : ℝ))
        (ctrlDelta Lat 0 true (EuclideanSpace.single b (1 : ℝ))) : ℝ)
      = (inner ℝ (EuclideanSpace.single b (1 : ℝ))
        (ctrlDelta Lat 0 false (EuclideanSpace.single b (1 : ℝ))) : ℝ) := by
    rw [hEq]
  rw [ctrl_inner, ctrl_inner] at h1
  rw [PiLp.norm_single, norm_one] at h1
  norm_num at h1

/-- **CONTROL 1 — `n ≠ 1` is load-bearing.** At `n = 1` the block map is the identity, so
`rgDelta 1 = id`, and an explicit `CoercivityHypothesis` with `V = anchoredVInter ell` carrying it
at rung `(0, true)` EXISTS. Holds on EVERY lattice and at EVERY `ell`: the no-go's conclusion
`False` is therefore genuinely refuted there. -/
theorem ctrl_hypothesis_exists_at_n_one (Lat : PeriodicLatticeExtent) (ell : ℕ) :
    ∃ (cohyp : Balaban.CoercivityHypothesis (Anchoring.AnchoredBondSpace Lat) Bool)
      (k₀ : ℕ) (U₀ : Bool),
      cohyp.V = Anchoring.anchoredVInter (Lat := Lat) ell ∧
      cohyp.Δ k₀ U₀ = rgDelta (Lat := Lat) 1 ∧
      (∀ (k : ℕ) (U : Bool), (cohyp.Δ k U).adjoint = cohyp.Δ k U) := by
  refine ⟨{ Δ := ctrlDelta Lat, V := Anchoring.anchoredVInter (Lat := Lat) ell,
            V_ne_bot := Anchoring.anchoredVInter_ne_bot ell,
            Δ_nonconstant := ctrlDelta_nonconstant, γ'' := 1, γ''_pos := one_pos,
            coercive := fun k U v _ => ctrl_coercive k U v }, 0, true, rfl, ?_, ?_⟩
  · show ctrlDelta Lat 0 true = rgDelta (Lat := Lat) 1
    rw [ctrlDelta_true, rgDelta_one_eq_id]
  · intro k U
    exact ctrlDelta_adjoint k U

/-- On a one-site lattice the block map is the identity at EVERY side, so the ladder never
coarsens. -/
theorem rgDelta_eq_id_of_singleton {Lat : PeriodicLatticeExtent} (h : ∀ μ : Fin 3, Lat μ = 0)
    (n : ℕ) : rgDelta (Lat := Lat) n = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Bond Lat)) := by
  have hb : blockRepBond (Lat := Lat) n = fun b => b := by
    funext b
    unfold blockRepBond
    refine Prod.ext ?_ rfl
    funext μ
    refine Fin.ext ?_
    have hz : (b.1 μ).val = 0 := by
      have h1 := (b.1 μ).isLt
      have h2 := h μ
      omega
    rw [blockRepSite_val, hz]
    simp
  rw [rgDelta_eq_deltaOf, hb, deltaOf_id_eq_id]

/-- **CONTROL 2 — "some axis has two sites" is load-bearing.** On any lattice with a single site
the no-go's conclusion is FALSE at EVERY `n` and EVERY `ell`. This is exactly the `(ell, Lat)` at
which the last layer of `no_coercivityHypothesis_lastLayer` is EMPTY for `ell ≥ 2`
(`ell - 1 ≤ Lat 0 = 0` fails), and it shows the emptiness is not a bookkeeping artifact: the
theorem is genuinely unavailable there. -/
theorem ctrl_hypothesis_exists_on_point_lattice {Lat : PeriodicLatticeExtent}
    (h : ∀ μ : Fin 3, Lat μ = 0) (ell n : ℕ) :
    ∃ (cohyp : Balaban.CoercivityHypothesis (Anchoring.AnchoredBondSpace Lat) Bool)
      (k₀ : ℕ) (U₀ : Bool),
      cohyp.V = Anchoring.anchoredVInter (Lat := Lat) ell ∧
      cohyp.Δ k₀ U₀ = rgDelta (Lat := Lat) n := by
  refine ⟨{ Δ := ctrlDelta Lat, V := Anchoring.anchoredVInter (Lat := Lat) ell,
            V_ne_bot := Anchoring.anchoredVInter_ne_bot ell,
            Δ_nonconstant := ctrlDelta_nonconstant, γ'' := 1, γ''_pos := one_pos,
            coercive := fun k U v _ => ctrl_coercive k U v }, 0, true, rfl, ?_⟩
  show ctrlDelta Lat 0 true = rgDelta (Lat := Lat) n
  rw [ctrlDelta_true, rgDelta_eq_id_of_singleton h]

/-- The one-site lattice, named. -/
def LatPt : PeriodicLatticeExtent := fun _ => 0

theorem ctrl_hypothesis_exists_on_LatPt (ell n : ℕ) :
    ∃ (cohyp : Balaban.CoercivityHypothesis (Anchoring.AnchoredBondSpace LatPt) Bool)
      (k₀ : ℕ) (U₀ : Bool),
      cohyp.V = Anchoring.anchoredVInter (Lat := LatPt) ell ∧
      cohyp.Δ k₀ U₀ = rgDelta (Lat := LatPt) n :=
  ctrl_hypothesis_exists_on_point_lattice (fun _ => rfl) ell n

/-- **THE SHARP CHARACTERIZATION.** Combining §5 with the two controls: a `CoercivityHypothesis`
on the anchored carrier with `V = anchoredVInter ell` and one rung equal to `rgDelta n` exists
**iff** `n = 1` (no coarsening) or the lattice has a single site. Nothing about `ell` enters. -/
theorem hypothesis_exists_iff (Lat : PeriodicLatticeExtent) (ell n : ℕ) :
    (∃ (cohyp : Balaban.CoercivityHypothesis (Anchoring.AnchoredBondSpace Lat) Bool)
        (k₀ : ℕ) (U₀ : Bool),
        cohyp.V = Anchoring.anchoredVInter (Lat := Lat) ell ∧
        cohyp.Δ k₀ U₀ = rgDelta (Lat := Lat) n)
      ↔ (n = 1 ∨ ∀ μ : Fin 3, Lat μ = 0) := by
  constructor
  · rintro ⟨cohyp, k₀, U₀, hV, hΔ⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨hn, hμ⟩ := hcon
    obtain ⟨ν, hν⟩ := hμ
    exact no_coercivityHypothesis_rgLadder_general cohyp hV k₀ U₀ hΔ hn ν (by omega)
  · rintro (hn | hpt)
    · subst hn
      obtain ⟨cohyp, k₀, U₀, h1, h2, -⟩ := ctrl_hypothesis_exists_at_n_one Lat ell
      exact ⟨cohyp, k₀, U₀, h1, h2⟩
    · exact ctrl_hypothesis_exists_on_point_lattice hpt ell n

/-! ### §7b — the `ell = 2` exhibit, re-derived; and the must-NOT-fire direction -/

/-- **CONTROL 3 — the generalization covers the case it generalizes.**
`KimiRGLadderScratch.kimi_no_coercivityHypothesis_rgLadder_at_ell_two` re-derived as an INSTANCE of
`no_coercivityHypothesis_lastLayer` at `(Lat, ell, n, ν) = (Lat4, 2, 2, 1)`. -/
theorem ctrl_kimi_at_ell_two
    (cohyp : Balaban.CoercivityHypothesis
      (Anchoring.AnchoredBondSpace KimiRGLadderScratch.Lat4) Bool)
    (hV : cohyp.V = Anchoring.anchoredVInter (Lat := KimiRGLadderScratch.Lat4) 2)
    (k₀ : ℕ) (U₀ : Bool)
    (hΔ : cohyp.Δ k₀ U₀ = rgDelta (Lat := KimiRGLadderScratch.Lat4) 2) : False :=
  no_coercivityHypothesis_lastLayer cohyp hV k₀ U₀ hΔ (by decide) (by decide) 1 (by decide)
    (by decide)

/-- **CONTROL 4 — must-NOT-fire.** The exclusion machinery does NOT declare every bond
staircase-free. On `Lat4` at `ell = 2` the ORIGIN-anchored direction-`0` bond IS on a staircase
(it is `KimiRGLadderScratch`'s own `kerBondA`), so `anchoredVInter 2` genuinely forces it to
vanish. Compare with `ctrl_layerOne_bond_free` below: the two bonds differ ONLY in the modular
residue of coordinate `0`, and the machinery separates them. -/
theorem ctrl_originBond_onSomeStaircase :
    OnSomeStaircase KimiRGLadderScratch.Lat4 2
      (originSite (Lat := KimiRGLadderScratch.Lat4), (0 : Fin 3)) :=
  ⟨originSite, KimiRGLadderScratch.kimi_origin_mem_coarseLattice_two,
    unitSite 0 KimiRGLadderScratch.kimi_lat4_dir,
    KimiRGLadderScratch.kimi_unitSite_mem_blockOf_two,
    KimiRGLadderScratch.kimi_kerBondA_mem_staircase⟩

/-- **CONTROL 4' — must-fire, same lattice, same direction, same `ell`.** Shifting the base site by
ONE in coordinate `0` (residue `0 → 1 = ell - 1`) flips the verdict. -/
theorem ctrl_layerOne_bond_free :
    ¬ OnSomeStaircase KimiRGLadderScratch.Lat4 2
      (unitSite (Lat := KimiRGLadderScratch.Lat4) 0 KimiRGLadderScratch.kimi_lat4_dir,
        (0 : Fin 3)) := by
  refine not_onSomeStaircase_dir0_mod ?_
  rw [unitSite_apply_self]

/-- **The exclusion boundary, in general.** A vector fails to lie in `anchoredVInter ell` exactly
when some staircase coordinate of it is nonzero. Together with `kernel_inter_ne_bot_iff` this says
precisely which kernel vectors of `rgDelta n` the axial gauge throws away: those, and only those,
that put weight on `S(ell)`. `KimiRGLadderScratch.kimi_kerVec_not_mem_anchoredVInter_two` is the
instance of this at `(Lat4, ell = 2)` for the origin-anchored `kerVec`. -/
theorem not_mem_anchoredVInter_iff {ell : ℕ} {v : Anchoring.AnchoredBondSpace Lat} :
    v ∉ Anchoring.anchoredVInter (Lat := Lat) ell ↔
      ∃ b : Bond Lat, OnSomeStaircase Lat ell b ∧ WithLp.ofLp v b ≠ 0 := by
  rw [mem_anchoredVInter_iff_vanish]
  push_neg
  rfl

/-- **THE RG-TOWER FORM.** The ladder `k ↦ rgDelta (ell ^ k)` — the family
`RGLadderCoarse` §9 builds — cannot supply any rung `k ≥ 1` of a fixed-`V` coercivity hypothesis,
for `2 ≤ ell`, on any lattice with two sites, at any `ell'` used for the gauge subspace. -/
theorem no_coercivityHypothesis_tower {Uconfig : Type*} [Nontrivial Uconfig]
    (cohyp : Balaban.CoercivityHypothesis (Anchoring.AnchoredBondSpace Lat) Uconfig)
    {ell ellV k : ℕ} (hV : cohyp.V = Anchoring.anchoredVInter (Lat := Lat) ellV)
    (k₀ : ℕ) (U₀ : Uconfig) (hΔ : cohyp.Δ k₀ U₀ = rgDelta (Lat := Lat) (ell ^ k))
    (hell : 2 ≤ ell) (hk : 1 ≤ k) (ν : Fin 3) (hLatν : 1 ≤ Lat ν) : False := by
  refine no_coercivityHypothesis_rgLadder_general cohyp hV k₀ U₀ hΔ ?_ ν hLatν
  have h1 : 2 ^ 1 ≤ ell ^ k := Nat.pow_le_pow_left hell 1 |>.trans (Nat.pow_le_pow_right (by omega) hk)
  omega

/-- **CONTROL 5 — `n ≠ 1` fires at the level of the block map itself.** At side `1` the block map
is the identity, so the two split sites do NOT share a representative: `blockRepSite_update_eq`'s
conclusion is FALSE at `n = 1`, which is precisely why the hypothesis is there. -/
theorem ctrl_blockRepSite_update_ne_at_one {s : PeriodicLatticeSite Lat} {ν : Fin 3}
    {j j' : Fin (Lat ν + 1)} (h : j ≠ j') :
    blockRepSite 1 (Function.update s ν j) ≠ blockRepSite 1 (Function.update s ν j') := by
  rw [blockRepSite_one, blockRepSite_one]
  exact update_ne_update h

/-- **CONTROL 6 — `0 < ell` is load-bearing in §6b.** At `ell = 0` every block `B(y)` is EMPTY
(`y ≤ x < y + 0` is unsatisfiable), so no bond is on any staircase and `anchoredVInter 0 = ⊤`. -/
theorem ctrl_onSomeStaircase_ell_zero (b : Bond Lat) : ¬ OnSomeStaircase Lat 0 b := by
  rintro ⟨y, hy, x, hx, hb⟩
  rw [mem_blockOf] at hx
  have h0 := hx 0
  omega

/-- **CONTROL 6' — and the exact characterizations are FALSE without it.** At `ell = 0` on `Lat4`
the right-hand side of `onSomeStaircase_dir0_iff` HOLDS for the direction-`0` bond based at
`unitSite 0` (`1 % 0 = 1 ≠ 0 = 0 - 1`, and `1 < 3`), while the left-hand side fails by
`ctrl_onSomeStaircase_ell_zero`. So `hell` is not decoration. -/
theorem ctrl_dir0_iff_false_at_ell_zero :
    ¬ (OnSomeStaircase KimiRGLadderScratch.Lat4 0
          (unitSite (Lat := KimiRGLadderScratch.Lat4) 0 KimiRGLadderScratch.kimi_lat4_dir,
            (0 : Fin 3))
        ↔ (((unitSite (Lat := KimiRGLadderScratch.Lat4) 0
              KimiRGLadderScratch.kimi_lat4_dir) 0).val % 0 ≠ 0 - 1 ∧
            ((unitSite (Lat := KimiRGLadderScratch.Lat4) 0
              KimiRGLadderScratch.kimi_lat4_dir) 0).val < KimiRGLadderScratch.Lat4 0)) := by
  intro hiff
  refine ctrl_onSomeStaircase_ell_zero _ (hiff.mpr ⟨?_, ?_⟩)
  · rw [unitSite_apply_self]
    decide
  · rw [unitSite_apply_self]
    decide

/-- **CONTROL 1' — what the `n = 1` escape costs on the consumer's side.** The inhabitant of
`ctrl_hypothesis_exists_at_n_one` satisfies every field of `CoercivityHypothesis`, but its pinned
rung is SCALAR: `rgDelta 1 = 1 • id`. So while the no-go's own conclusion is genuinely false at
`n = 1`, `Spine.coerc_u_main`'s fourth conjunct (`∀ k U c, Δ k U ≠ c • id`) fails there for an
independent reason. The `n = 1` slice is therefore not a live escape for the consumer — it is
excluded by the consumer's own statement, not by anything proved here. -/
theorem ctrl_rgDelta_one_is_scalar :
    rgDelta (Lat := Lat) 1
      = (1 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Bond Lat)) := by
  rw [rgDelta_one_eq_id, one_smul]

/-- **CONTROL 2' — the same for the one-site lattice.** There the ladder is scalar at EVERY `n`,
so that escape is likewise closed by the consumer's non-scalarity conjunct — but note the carrier
is then only `3`-dimensional, so the one-site lattice is degenerate for independent reasons too. -/
theorem ctrl_rgDelta_scalar_on_point_lattice {Lat : PeriodicLatticeExtent}
    (h : ∀ μ : Fin 3, Lat μ = 0) (n : ℕ) :
    rgDelta (Lat := Lat) n = (1 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Bond Lat)) := by
  rw [rgDelta_eq_id_of_singleton h, one_smul]

/-! ## §8 — axiom audit: EVERY declaration of this file, no exceptions -/

#print axioms not_last_of_window
#print axioms corner1_apply_zero
#print axioms corner1_apply_one
#print axioms corner1_apply_two
#print axioms corner2_apply_zero
#print axioms corner2_apply_one
#print axioms corner2_apply_two
#print axioms OnSomeStaircase
#print axioms dir0_not_mem_staircase_mod
#print axioms dir1_not_mem_staircase_mod
#print axioms dir2_not_mem_staircase_mod
#print axioms dir0_not_mem_staircase_top
#print axioms dir1_not_mem_staircase_top
#print axioms dir2_not_mem_staircase_top
#print axioms not_onSomeStaircase_dir0_mod
#print axioms not_onSomeStaircase_dir1_mod
#print axioms not_onSomeStaircase_dir2_mod
#print axioms not_onSomeStaircase_dir0_top
#print axioms not_onSomeStaircase_dir1_top
#print axioms not_onSomeStaircase_dir2_top
#print axioms mem_anchoredVInter_iff_vanish
#print axioms pairVec
#print axioms pairVec_ofLp
#print axioms pairVec_ne_zero
#print axioms sumCLMof_pairVec
#print axioms rgDelta_pairVec
#print axioms pairVec_mem_anchoredVInter
#print axioms no_coercivityHypothesis_of_free_pair
#print axioms blockRepSite_update_eq
#print axioms update_ne_update
#print axioms update_apply_of_ne
#print axioms lastLayerBase
#print axioms lastLayerBase_apply_zero
#print axioms sub_one_mod_self
#print axioms no_coercivityHypothesis_lastLayer
#print axioms offCornerBase
#print axioms offCornerBase_apply_zero
#print axioms no_coercivityHypothesis_offCorner
#print axioms topSite
#print axioms topSite_apply_self
#print axioms no_coercivityHypothesis_topLayer
#print axioms no_coercivityHypothesis_rgLadder_general
#print axioms kernel_inter_ne_bot_iff
#print axioms corner_mem
#print axioms succSite
#print axioms succSite_apply_self
#print axioms succSite_apply_of_ne
#print axioms rem_eq_offset
#print axioms succSite_mem_blockOf
#print axioms onSomeStaircase_dir0_of
#print axioms onSomeStaircase_dir0_iff
#print axioms blockRepSite_apply_eq_self
#print axioms onSomeStaircase_dir1_of
#print axioms onSomeStaircase_dir2_of
#print axioms onSomeStaircase_dir1_iff
#print axioms onSomeStaircase_dir2_iff
#print axioms ctrlDelta
#print axioms ctrl_scale_ge_one
#print axioms ctrlDelta_true
#print axioms ctrl_inner
#print axioms ctrl_coercive
#print axioms ctrlDelta_adjoint
#print axioms ctrlDelta_nonconstant
#print axioms ctrl_hypothesis_exists_at_n_one
#print axioms rgDelta_eq_id_of_singleton
#print axioms ctrl_hypothesis_exists_on_point_lattice
#print axioms LatPt
#print axioms ctrl_hypothesis_exists_on_LatPt
#print axioms hypothesis_exists_iff
#print axioms ctrl_kimi_at_ell_two
#print axioms ctrl_originBond_onSomeStaircase
#print axioms ctrl_layerOne_bond_free
#print axioms not_mem_anchoredVInter_iff
#print axioms no_coercivityHypothesis_tower
#print axioms ctrl_blockRepSite_update_ne_at_one
#print axioms ctrl_onSomeStaircase_ell_zero
#print axioms ctrl_dir0_iff_false_at_ell_zero
#print axioms ctrl_rgDelta_one_is_scalar
#print axioms ctrl_rgDelta_scalar_on_point_lattice

end AdalyFormal.Balaban.LastLayerNoGo
