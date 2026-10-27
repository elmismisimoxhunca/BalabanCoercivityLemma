/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.RGLadderCore

set_option autoImplicit false

/-!
# `RGLadderCoarse` — a `Δ : ℕ → …` in which `k` acts through the LATTICE, and what it costs

## Why this file exists

`Spine.coerc_u_main`'s fourth conjunct demands `∃ U k₁ k₂, k₁ ≠ k₂ ∧ Δ k₁ U ≠ Δ k₂ U`. Measured
(2026-07-28) across this tree, **every** `Δ` it owns is `k`-constant: `Anchoring.anchoredΔ` is
literally `fun _ U => …`, `CoercivitySupply.deltaSupplyField_k_independent` proves its own supply
`k`-independent by `rfl`, and `DeltaKRecursive.richWitnessFamily`'s `k`-dependence is
`DeltaOp := fun k => diagCLM (k : ℝ) 0` — the scale index written into a 2×2 matrix entry, with no
lattice anywhere in the file.

This file builds a family whose `k`-dependence is a lattice identification and nothing else, and
then measures what that costs.

## The construction, and the one channel `k` may use

```
deltaOf (r : Bond Lat → Bond Lat) := (sumCLMof r)^* ∘ (sumCLMof r),
  where  ofLp (sumCLMof r v) c = ∑_{b : r b = c} ofLp v b
rgDelta n := deltaOf (blockRepBond n)
```

`rgDelta` is **definitionally** `deltaOf ∘ blockRepBond` (`rgDelta_eq_deltaOf`, `rfl`). So the scale
argument has exactly ONE way into the operator: through the bond map `blockRepBond n`. There is no
numeral, no tag, no second channel — `deltaOf_congr` turns that into a theorem
(`blockRepBond n₁ = blockRepBond n₂ → rgDelta n₁ = rgDelta n₂`).

`blockRepBond n (x, μ) = (blockRepSite n x, μ)` and `blockRepSite n x μ = ⌊x_μ/n⌋·n`, i.e. the
coordinate-wise corner of the side-`n` block containing `x`. **That this is the tree's own block
geometry and not a fresh invention is proved, not asserted** (§2):

* `blockRepSite_mem_CoarseLattice` — the representative lies in `AdmissibleSubspace.CoarseLattice
  Lat n`, the tree's `Λ'`.
* `mem_blockOf_blockRepSite` — `x` lies in `AdmissibleSubspace.blockOf (blockRepSite n x) n`, the
  tree's `B(y)`.
* `blockRepSite_eq_of_mem_blockOf` — conversely, for `y ∈ CoarseLattice Lat n` and
  `x ∈ blockOf y n`, `blockRepSite n x = y`. So `blockRepSite n` IS the map "send a site to the
  centre of its block", for the tree's own `blockOf`/`CoarseLattice`, with no freedom left.

## What is proved about the ladder (§3-§5)

* `rgDelta_adjoint` — self-adjoint (`Spine.coerc_u_main` conjunct 2).
* `rgDelta_psd` — globally positive semidefinite (conjunct 3).
* `rgDelta_not_scalar` — non-scalar for `2 ≤ n` on a lattice with a nontrivial direction
  (conjunct 4).
* `rgDelta_one_ne_rgDelta` — genuinely `k`-dependent (conjunct 5): `rgDelta 1 = id` (block side one
  is no coarsening at all) while `rgDelta n ≠ id` for `2 ≤ n`.
* `rgDelta_kerVec` — and the price: for `2 ≤ n` the operator KILLS a nonzero vector, namely
  `e_(x₀,μ₀) − e_(x₁,μ₀)` for two sites `x₀ ≠ x₁` in the same block. Coarsening is exactly the
  identification of `x₀` with `x₁`; the difference of the two bonds is what the block map cannot
  see.

## The consequence (§6), which is the point of the lane

`RGLadderCore.eq_zero_of_coercive_of_apply_eq_zero` turns that kernel vector into a refutation:
**no `Balaban.CoercivityHypothesis` on `AnchoredBondSpace Lat` can have `Δ k₀ U₀ = rgDelta n`
(`2 ≤ n`) and a `V` containing the kernel vector.** With `ell = 1` — a value `coerc_u_main` admits,
its `ell` being a free `ℕ` — `V = anchoredVInter 1 = ⊤` (`anchoredVInter_one_eq_top`, proved here)
contains everything, so the refutation is unconditional there
(`no_coercivityHypothesis_rgLadder_at_ell_one`).

Quantitatively (`finrank_V_le_card_coarse`): for `0 < n`, ANY `cohyp` with `Δ k₀ U₀ = rgDelta n`
obeys `finrank cohyp.V ≤ #{coarse bonds at side n}`, and once `n` exceeds every side length that
count is `3` (`card_coarseBondIdx_le_three`). A fixed subspace `V` must fit inside the coarse space
of every rung.

**What this does and does not say.** It does NOT say Bałaban's `k`-uniform bound is false: Bałaban
states coercivity at scale `k` on scale `k`'s own space, whose dimension shrinks with `k`, and
there is no fixed `V` in his statement.

**[STRUCK 2026-07-28 — Kimi third gate, item 2, REFUTED BY COMPILED COUNTEREXAMPLE. This is the
SECOND conviction of this same billing: Sol earlier refuted its statement as a general no-go
(it is a theorem about purely-factored coarsening operators), and this strikes what survived.]**
The struck text read: *"It says the ENCODING `Δ : ℕ → Uconfig → H →L[ℝ] H` with a single
`V : Submodule ℝ H` cannot carry a tower whose steps genuinely coarsen. Either the carrier or `V`
has to become `k`-indexed."* **That is false as stated.**

`KimiRGLadderScratch.kimi_fixedV_coarsening_tower` compiles a counterexample on this very carrier:
`V := span{const}` — fixed and proper — with `Δ k U := (U ? 2 : 1) • rgDelta (2^(k+1))`, i.e. the
SAME `rgDelta` operators this file uses. It is self-adjoint, globally PSD, non-scalar, genuinely
`k`- and `U`-dependent, has an explicit nonzero kernel vector at rung 0 (so the steps do coarsen),
and is coercive with `γ'' = 1` UNIFORM in `k` and `U` — the last from the fibre-count bound
`‖S_r(const)‖² = Σ_c f_c² ≥ Σ_c f_c = #bonds = ‖const‖²`, valid for ANY bond map `r`. Axioms:
`[propext, Classical.choice, Quot.sound]`.

**Where the reasoning went wrong, exactly.** The paragraph above derives `finrank V ≤ 3` from
`finrank_V_le_card_coarse` + `card_coarseBondIdx_le_three` — a true and useful bound — and the
prose then read `≤ 3` as *impossible*. It does not force `V = ⊥`. A one-dimensional `V` fits
inside 3 with room to spare, and that is precisely what the counterexample supplies.

**The true statement**, and all this file's THEOREMS (as opposed to its prose) ever said:
a fixed `V` cannot carry a tower that coarsens **WITHIN** `V` — which is exactly
`RGLadderCore.no_uniform_ladder_of_one_small_rung`. Coarsening that happens entirely off `V`
costs the tower nothing. So the conclusion "either the carrier or `V` has to become `k`-indexed"
is NOT established here; what is established is that `V` must avoid the rungs' kernels.

**Coverage, corrected.** `no_coercivityHypothesis_rgLadder_at_ell_one` is unconditional only
relative to three pinnings (`V = anchoredVInter 1`, the operator pinned to `rgDelta n` at one
rung, and a direction with ≥ 2 sites), and `ell = 1` is the degenerate slice where
`anchoredVInter 1 = ⊤`. At `ell ≥ 2` the conditional theorem's own witness is USELESS:
`kimi_kerVec_not_mem_anchoredVInter_two` proves `kerVec ∉ anchoredVInter 2`, because
`(originSite, 0)` lies on the staircase `Γ_{origin, unitSite}` and the axial-gauge clause
therefore forces every member of `V` to vanish exactly where `kerVec` does not. The witness this
file formalizes is gauge-fixed out of the subspace this file targets.

**But the obstruction at `ell = 2` is REAL, and is now proved** —
`KimiRGLadderScratch.kimi_no_coercivityHypothesis_rgLadder_at_ell_two`, via a LAST-LAYER witness
this file missed: `w = e_{((1,0,0),0)} − e_{((1,1,0),0)}`. Both bonds are direction-0 at base
coordinate `1 = y₀ + ell − 1` of the origin block, so they share a block representative
(hence `rgDelta 2 w = 0`) while lying on NO staircase of any valid pair (direction-0 membership
would force `y₀ = 1`, contradicting `y₀ % 2 = 0`). So the door this file intends to close IS
closeable at `ell = 2` — this file simply did not close it. The general `(ell, Lat)` form of that
argument is stated but NOT yet compiled; it is open.

## Controls (§7), both directions

* **must-fire (the `k`-dependence is not decorative):** `deltaOf_id_eq_id` +
  `flatLadder_k_constant` — replace the coarsening `blockRepBond n` by the identity bond map (i.e.
  remove the block structure, not merely change a numeral) and the whole family collapses to `id`
  at every `k`; `flatLadder_fails_rg_scale_dependence` then proves it fails
  `coerc_u_main`'s fourth conjunct. And `rgDelta_one_eq_id` shows the same collapse happens at
  block side `1`, where the lattice identification is empty — so the difference between rungs is
  traceable to which sites the lattice glues, not to the value of `k`.
* **must-not-fire (non-vacuity):** `originSite_ne_unitSite` (a named, genuinely distinct pair of
  sites), `bondSpace_nontrivial` (`Bond Lat` is never empty, so the carrier is never the
  `EuclideanSpace ℝ (Fin 0)` degenerate that has defeated guards in this tree), and
  `rgDelta_ne_zero` (the operator is not the zero operator at any `n`, so the kernel finding is not
  the trivial "everything dies").

## Degenerate points, all recorded rather than avoided (§8)

* `k = 0`, i.e. block side `ell^0 = 1`: `rgDelta_one_eq_id` — no coarsening, `Δ = id`.
* `ell = 1`: `rgDelta_pow_one_k_constant` / `rgDelta_pow_one_fails_rg_scale_dependence` — the tower
  never coarsens; every rung of `fun k => rgDelta (1 ^ k)` is the identity, so the family is
  `k`-constant and fails `coerc_u_main`'s fourth conjunct.
* `ell = 0`, i.e. block side `0` at every `k ≥ 1`: `blockRepSite_zero` — `⌊x/0⌋·0 = 0`, so ALL
  sites collapse to the origin at once. Total coarsening, kernel maximal. Recorded, not used.
* `L μ + 1 ≤ n` (the block IS the whole torus): `card_coarseBondIdx_le_three` — the coarse space
  has at most three elements, one per direction.
* `EuclideanSpace ℝ (Fin 0)`: cannot occur here — `bondSpace_nontrivial`.
-/

namespace AdalyFormal.Balaban.RGLadderCoarse

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice inBlock mem_blockOf
  mem_CoarseLattice admissibleSubspaceInter mem_admissibleSubspaceInter staircasePath axisSegment)

open Matrix

variable {Lat : PeriodicLatticeExtent}

/-! ## §1 — a `Matrix`-built CLM on the anchored bond space

Local copy of the established `matCLM` pattern (`VariationalProjectorH1.lean §4`,
`DeltaKRecursive.lean §4`), kept self-contained so this file's write-scope does not depend on a
concurrently edited sibling. -/

/-- A matrix gives a continuous linear map of Euclidean spaces. -/
noncomputable def matCLM {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

theorem matCLM_apply {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    WithLp.ofLp (matCLM M x) = M *ᵥ (WithLp.ofLp x) := by
  unfold matCLM
  simp [Matrix.toEuclideanLin, LinearMap.coe_toContinuousLinearMap']

/-! ## §2 — the block map, tied to the tree's own `blockOf` / `CoarseLattice` -/

/-- **The block representative of a site at block side `n`**: coordinate-wise, the largest multiple
of `n` not exceeding the coordinate. For `n = 0` this is the constant origin (see
`blockRepSite_zero`); for `n = 1` it is the identity (`blockRepSite_one`). -/
def blockRepSite (n : ℕ) (x : PeriodicLatticeSite Lat) : PeriodicLatticeSite Lat :=
  fun μ => ⟨(x μ).val / n * n, lt_of_le_of_lt (Nat.div_mul_le_self _ _) (x μ).isLt⟩

theorem blockRepSite_val (n : ℕ) (x : PeriodicLatticeSite Lat) (μ : Fin 3) :
    (blockRepSite n x μ).val = (x μ).val / n * n := rfl

/-- **The block map on BONDS**: coarsen the base site, keep the direction. -/
def blockRepBond (n : ℕ) (b : Bond Lat) : Bond Lat := (blockRepSite n b.1, b.2)

/-- **Faithfulness (a): the representative is a coarse-lattice site**, i.e. an element of the
tree's own `Λ' = AdmissibleSubspace.CoarseLattice Lat n`. -/
theorem blockRepSite_mem_CoarseLattice (n : ℕ) (x : PeriodicLatticeSite Lat) :
    blockRepSite n x ∈ CoarseLattice Lat n := by
  rw [mem_CoarseLattice]
  intro μ
  rw [blockRepSite_val]
  exact Nat.mul_mod_left _ _

/-- **Faithfulness (b): `x` lies in the block of its representative**, for the tree's own
`B(y) = AdmissibleSubspace.blockOf y n`. -/
theorem mem_blockOf_blockRepSite {n : ℕ} (hn : 0 < n) (x : PeriodicLatticeSite Lat) :
    x ∈ blockOf (blockRepSite n x) n := by
  rw [mem_blockOf]
  intro μ
  have hdm : (x μ).val / n * n + (x μ).val % n = (x μ).val := Nat.div_add_mod' _ _
  have hlt := Nat.mod_lt (x μ).val hn
  rw [blockRepSite_val]
  omega

/-- **Faithfulness (c), the converse**: for a coarse-lattice site `y` and `x` in `B(y)`, the
representative of `x` IS `y`. Together with (a) and (b) this pins `blockRepSite n` to be exactly
"the centre of the block containing `x`" for the tree's own block geometry. -/
theorem blockRepSite_eq_of_mem_blockOf {n : ℕ} (hn : 0 < n) {y x : PeriodicLatticeSite Lat}
    (hy : y ∈ CoarseLattice Lat n) (hx : x ∈ blockOf y n) : blockRepSite n x = y := by
  rw [mem_CoarseLattice] at hy
  rw [mem_blockOf] at hx
  funext μ
  have hy' := hy μ
  have hx' := hx μ
  -- `(y μ).val` is a multiple of `n`, say `n * q`, and `x` sits in the window `[y, y+n)`.
  obtain ⟨q, hq⟩ : n ∣ (y μ).val := Nat.dvd_of_mod_eq_zero hy'
  have hqn : q * n = (y μ).val := by rw [mul_comm]; omega
  have hlo : q * n ≤ (x μ).val := by omega
  have hhi : (x μ).val < Nat.succ q * n := by
    rw [Nat.succ_mul]
    omega
  have hdiv : (x μ).val / n = q := Nat.div_eq_of_lt_le hlo hhi
  exact Fin.ext (by rw [blockRepSite_val, hdiv, hqn])

/-- **`n = 1`: no coarsening at all.** -/
theorem blockRepSite_one (x : PeriodicLatticeSite Lat) : blockRepSite 1 x = x := by
  funext μ
  exact Fin.ext (by rw [blockRepSite_val]; omega)

theorem blockRepBond_one (b : Bond Lat) : blockRepBond 1 b = b := by
  unfold blockRepBond
  rw [blockRepSite_one]

/-- **`n = 0` (the `ell = 0` degenerate): every site collapses to the origin.** `⌊x/0⌋·0 = 0`. -/
theorem blockRepSite_zero (x : PeriodicLatticeSite Lat) (μ : Fin 3) :
    (blockRepSite 0 x μ).val = 0 := by
  rw [blockRepSite_val, Nat.mul_zero]

/-- `⌊·/n⌋·n` is monotone. -/
theorem floorMul_mono (n : ℕ) {a b : ℕ} (h : a ≤ b) : a / n * n ≤ b / n * n :=
  Nat.mul_le_mul_right n (Nat.div_le_div_right h)

theorem floorMul_le (n a : ℕ) : a / n * n ≤ a := Nat.div_mul_le_self _ _

/-- `⌊·/n⌋·n` is idempotent on ℕ, for `0 < n`. -/
theorem floorMul_idem {n : ℕ} (hn : 0 < n) (a : ℕ) : (a / n * n) / n * n = a / n * n := by
  have h : a / n * n / n = a / n := by
    conv_lhs => rw [Nat.mul_comm]
    exact Nat.mul_div_cancel_left _ hn
  rw [h]

/-- **THE TOWER LAW, at the level of the block geometry.** If `a ∣ b` then coarsening to side `a`
and then to side `b` is the same as coarsening to side `b` directly. This is what makes a sequence
of block sides a genuine RG TOWER rather than a list of unrelated operators: each level factors
through the previous one. -/
theorem floorMul_tower {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) (v : ℕ) :
    (v / a * a) / b * b = v / b * b := by
  obtain ⟨m, hm⟩ := hab
  refine le_antisymm (floorMul_mono b (floorMul_le a v)) ?_
  -- `v / b * b` is a multiple of `a` (since `a ∣ b`) and is `≤ v`, hence `≤ v / a * a`.
  have hmulA : (v / b * b) / a * a = v / b * b := by
    have hdvd : a ∣ v / b * b := Dvd.dvd.mul_left ⟨m, hm⟩ (v / b)
    obtain ⟨t, ht⟩ := hdvd
    rw [ht, Nat.mul_comm a t, Nat.mul_div_cancel _ ha]
  have hstep : v / b * b ≤ v / a * a := by
    calc v / b * b = (v / b * b) / a * a := hmulA.symm
      _ ≤ v / a * a := floorMul_mono a (floorMul_le b v)
  calc v / b * b = (v / b * b) / b * b := (floorMul_idem hb _).symm
    _ ≤ (v / a * a) / b * b := floorMul_mono b hstep

/-- **Idempotence for `0 < n`**: the representative of a representative is itself. Consequence:
only representatives have nonempty fibres, which is what makes the coarse index set of §6 the right
one. -/
theorem blockRepSite_idem {n : ℕ} (hn : 0 < n) (x : PeriodicLatticeSite Lat) :
    blockRepSite n (blockRepSite n x) = blockRepSite n x := by
  funext μ
  refine Fin.ext ?_
  rw [blockRepSite_val, blockRepSite_val, floorMul_idem hn]

theorem blockRepBond_idem {n : ℕ} (hn : 0 < n) (b : Bond Lat) :
    blockRepBond n (blockRepBond n b) = blockRepBond n b := by
  unfold blockRepBond
  simp [blockRepSite_idem hn]

/-- **The tower law on SITES.** -/
theorem blockRepSite_tower {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b)
    (x : PeriodicLatticeSite Lat) :
    blockRepSite b (blockRepSite a x) = blockRepSite b x := by
  funext μ
  exact Fin.ext (by rw [blockRepSite_val, blockRepSite_val, blockRepSite_val,
    floorMul_tower ha hb hab])

/-- **The tower law on BONDS** — `Q_b = Q_b ∘ Q_a` whenever `a ∣ b`. The level index is what
advances; there is no other moving part. -/
theorem blockRepBond_tower {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) (e : Bond Lat) :
    blockRepBond b (blockRepBond a e) = blockRepBond b e := by
  unfold blockRepBond
  rw [blockRepSite_tower ha hb hab]

/-! ## §3 — the operator family: ONE channel for `k` -/

/-- **The fibre-sum map of an arbitrary bond map.** `ofLp (sumCLMof r v) c = ∑_{b : r b = c} v b`.
`r` is the only argument; every scale dependence below enters here. -/
noncomputable def sumCLMof (r : Bond Lat → Bond Lat) :
    EuclideanSpace ℝ (Bond Lat) →L[ℝ] EuclideanSpace ℝ (Bond Lat) :=
  matCLM (fun c b => if r b = c then (1 : ℝ) else 0)

theorem sumCLMof_apply (r : Bond Lat → Bond Lat) (v : EuclideanSpace ℝ (Bond Lat))
    (c : Bond Lat) :
    WithLp.ofLp (sumCLMof r v) c
      = ∑ b ∈ Finset.univ.filter (fun b => r b = c), WithLp.ofLp v b := by
  rw [sumCLMof, matCLM_apply]
  simp [Matrix.mulVec, dotProduct, Finset.sum_filter, ite_mul]

theorem sumCLMof_single (r : Bond Lat → Bond Lat) (b c : Bond Lat) :
    WithLp.ofLp (sumCLMof r (EuclideanSpace.single b (1 : ℝ))) c
      = if r b = c then (1 : ℝ) else 0 := by
  rw [sumCLMof, matCLM_apply, PiLp.ofLp_single, Matrix.mulVec_single]
  simp

/-- **The Gram operator of a bond map.** Self-adjoint and PSD by construction. -/
noncomputable def deltaOf (r : Bond Lat → Bond Lat) :
    EuclideanSpace ℝ (Bond Lat) →L[ℝ] EuclideanSpace ℝ (Bond Lat) :=
  (ContinuousLinearMap.adjoint (sumCLMof r)).comp (sumCLMof r)

/-- **THE LADDER.** `k`'s only route into the operator is the block map. -/
noncomputable def rgDelta (n : ℕ) :
    EuclideanSpace ℝ (Bond Lat) →L[ℝ] EuclideanSpace ℝ (Bond Lat) :=
  deltaOf (blockRepBond (Lat := Lat) n)

theorem rgDelta_eq_deltaOf (n : ℕ) :
    rgDelta (Lat := Lat) n = deltaOf (blockRepBond (Lat := Lat) n) := rfl

/-- **The scale index has no second channel**, as a theorem: equal block maps give equal
operators. -/
theorem deltaOf_congr {r₁ r₂ : Bond Lat → Bond Lat} (h : r₁ = r₂) : deltaOf r₁ = deltaOf r₂ := by
  rw [h]

theorem rgDelta_congr {n₁ n₂ : ℕ} (h : blockRepBond (Lat := Lat) n₁ = blockRepBond (Lat := Lat) n₂) :
    rgDelta (Lat := Lat) n₁ = rgDelta (Lat := Lat) n₂ := deltaOf_congr h

/-! ## §4 — the `coerc_u_main` conjuncts that DO hold -/

/-- **Conjunct 2 — self-adjointness.** -/
theorem deltaOf_adjoint (r : Bond Lat → Bond Lat) :
    ContinuousLinearMap.adjoint (deltaOf r) = deltaOf r := by
  rw [deltaOf, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem rgDelta_adjoint (n : ℕ) :
    ContinuousLinearMap.adjoint (rgDelta (Lat := Lat) n) = rgDelta (Lat := Lat) n :=
  deltaOf_adjoint _

/-- The Gram identity: `⟪v, deltaOf r v⟫ = ‖sumCLMof r v‖²`. -/
theorem inner_deltaOf (r : Bond Lat → Bond Lat) (v : EuclideanSpace ℝ (Bond Lat)) :
    (inner ℝ v (deltaOf r v) : ℝ) = ‖sumCLMof r v‖ ^ 2 := by
  rw [deltaOf]
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_self_eq_norm_sq]

/-- **Conjunct 3 — global positive semidefiniteness**, on every vector, not only on `V`. -/
theorem rgDelta_psd (n : ℕ) (v : EuclideanSpace ℝ (Bond Lat)) :
    0 ≤ (inner ℝ v (rgDelta (Lat := Lat) n v) : ℝ) := by
  rw [rgDelta_eq_deltaOf, inner_deltaOf]
  positivity

/-! ## §5 — the lattice witnesses, the kernel, and genuine `k`-dependence -/

/-- The origin site. -/
def originSite : PeriodicLatticeSite Lat := fun μ => ⟨0, Nat.succ_pos _⟩

/-- A site one step from the origin in direction `μ₀` — available exactly when that direction has
at least two sites. -/
def unitSite (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀) : PeriodicLatticeSite Lat :=
  Function.update (originSite (Lat := Lat)) μ₀ ⟨1, by omega⟩

theorem unitSite_apply_self (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀) :
    ((unitSite (Lat := Lat) μ₀ h) μ₀).val = 1 := by
  unfold unitSite
  rw [Function.update_self]

theorem unitSite_apply_other {μ₀ μ : Fin 3} (h : 1 ≤ Lat μ₀) (hne : μ ≠ μ₀) :
    ((unitSite (Lat := Lat) μ₀ h) μ).val = 0 := by
  unfold unitSite
  rw [Function.update_of_ne hne]
  rfl

/-- **must-not-fire control**: the two sites are genuinely distinct. -/
theorem originSite_ne_unitSite (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀) :
    (originSite (Lat := Lat)) ≠ unitSite μ₀ h := by
  intro hEq
  have := congrFun hEq μ₀
  rw [unitSite] at this
  have h2 : ((originSite (Lat := Lat)) μ₀).val = 1 := by
    rw [this, Function.update_self]
  simp [originSite] at h2

/-- **must-not-fire control**: the carrier is never the empty-index degenerate. -/
theorem bondSpace_nontrivial : Nonempty (Bond Lat) :=
  ⟨(originSite, 0)⟩

/-- Both sites have the same block representative once the block side is at least `2`. -/
theorem blockRep_originSite (n : ℕ) : blockRepSite n (originSite (Lat := Lat)) = originSite := by
  funext μ
  exact Fin.ext (by rw [blockRepSite_val]; simp [originSite])

theorem blockRep_unitSite {n : ℕ} (hn : 2 ≤ n) (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀) :
    blockRepSite n (unitSite (Lat := Lat) μ₀ h) = originSite := by
  funext μ
  refine Fin.ext ?_
  rw [blockRepSite_val]
  by_cases hμ : μ = μ₀
  · subst hμ
    rw [unitSite_apply_self]
    have : 1 / n = 0 := Nat.div_eq_of_lt (by omega)
    simp [this, originSite]
  · rw [unitSite_apply_other h hμ]
    simp [originSite]

/-- The two bonds glued by the block map at side `n ≥ 2`. -/
def kerBondA (μ₀ : Fin 3) : Bond Lat := (originSite, μ₀)

def kerBondB (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀) : Bond Lat := (unitSite μ₀ h, μ₀)

theorem kerBond_ne (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀) :
    (kerBondA (Lat := Lat) μ₀) ≠ kerBondB μ₀ h := by
  intro hEq
  exact originSite_ne_unitSite μ₀ h (congrArg Prod.fst hEq)

theorem kerBond_same_rep {n : ℕ} (hn : 2 ≤ n) (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀) :
    blockRepBond n (kerBondA (Lat := Lat) μ₀) = blockRepBond n (kerBondB μ₀ h) := by
  unfold blockRepBond kerBondA kerBondB
  rw [blockRep_originSite, blockRep_unitSite hn]

/-- **The kernel vector of the coarsening**: the difference of two bonds the block map identifies.
This is what coarse-graining cannot see, and it is the whole cost of the ladder. -/
noncomputable def kerVec (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀) : EuclideanSpace ℝ (Bond Lat) :=
  EuclideanSpace.single (kerBondA μ₀) (1 : ℝ) - EuclideanSpace.single (kerBondB μ₀ h) (1 : ℝ)

theorem kerVec_ne_zero (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀) : kerVec (Lat := Lat) μ₀ h ≠ 0 := by
  intro hz
  have := congrFun (congrArg WithLp.ofLp hz) (kerBondA (Lat := Lat) μ₀)
  rw [kerVec] at this
  simp [(kerBond_ne (Lat := Lat) μ₀ h).symm] at this

/-- A vector of `EuclideanSpace` vanishing coordinatewise is zero. -/
theorem euclid_eq_zero {ι : Type*} [Fintype ι] {v : EuclideanSpace ℝ ι}
    (h : ∀ i, WithLp.ofLp v i = 0) : v = 0 := by
  apply WithLp.ofLp_injective 2
  funext i
  simpa using h i

theorem sumCLMof_kerVec {n : ℕ} (hn : 2 ≤ n) (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀) :
    sumCLMof (blockRepBond (Lat := Lat) n) (kerVec μ₀ h) = 0 := by
  refine euclid_eq_zero ?_
  intro c
  rw [kerVec, map_sub]
  simp only [WithLp.ofLp_sub, Pi.sub_apply]
  rw [sumCLMof_single, sumCLMof_single, kerBond_same_rep hn μ₀ h]
  simp

/-- **The ladder kills a nonzero vector at every rung with block side `≥ 2`.** -/
theorem rgDelta_kerVec {n : ℕ} (hn : 2 ≤ n) (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀) :
    rgDelta (Lat := Lat) n (kerVec μ₀ h) = 0 := by
  rw [rgDelta_eq_deltaOf, deltaOf]
  simp [sumCLMof_kerVec hn μ₀ h]

/-! ### §5b — `rgDelta 1 = id`, and hence genuine `k`-dependence -/

theorem sumCLMof_id_eq_id :
    sumCLMof (Lat := Lat) (fun b => b) = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Bond Lat)) := by
  ext v c
  show WithLp.ofLp (sumCLMof (fun b => b) v) c = _
  rw [sumCLMof_apply, Finset.filter_eq' Finset.univ c, if_pos (Finset.mem_univ c),
    Finset.sum_singleton]
  rfl

/-- **must-fire control (a)**: with the coarsening REMOVED — the identity bond map, i.e. no block
structure at all — the construction is the identity operator. -/
theorem deltaOf_id_eq_id :
    deltaOf (Lat := Lat) (fun b => b)
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Bond Lat)) := by
  rw [deltaOf, sumCLMof_id_eq_id]
  simp

/-- **must-fire control (b)**: the flat ladder — the same construction with the block map replaced
by the identity at every `k` — is `k`-CONSTANT: every rung is the identity operator. -/
theorem flatLadder_k_constant (k : ℕ) :
    (fun (_ : ℕ) => deltaOf (Lat := Lat) (fun b => b)) k
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Bond Lat)) := deltaOf_id_eq_id

/-- **must-fire control (c)**: consequently the flat ladder FAILS `coerc_u_main`'s fourth conjunct,
for every `Uconfig`. Removing the coarsening breaks the ladder — this is the control that would fail
if the `k`-dependence of `rgDelta` were decorative. -/
theorem flatLadder_fails_rg_scale_dependence {Uconfig : Type*} :
    ¬ ∃ (U : Uconfig) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧
        (fun (_ : ℕ) (_ : Uconfig) => deltaOf (Lat := Lat) (fun b => b)) k₁ U
          ≠ (fun (_ : ℕ) (_ : Uconfig) => deltaOf (Lat := Lat) (fun b => b)) k₂ U := by
  rintro ⟨U, k₁, k₂, -, hne⟩
  exact hne rfl

/-- **Degenerate `k = 0` (block side `ell^0 = 1`): the rung is the identity.** -/
theorem rgDelta_one_eq_id :
    rgDelta (Lat := Lat) 1 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Bond Lat)) := by
  rw [rgDelta_eq_deltaOf]
  have : blockRepBond (Lat := Lat) 1 = fun b => b := funext blockRepBond_one
  rw [this, deltaOf_id_eq_id]

/-- **Conjunct 5 — genuine `k`-dependence, traceable to the lattice.** Rung `1` is the identity
(the block side is one, the lattice glues nothing); rung `n ≥ 2` annihilates the difference of two
bonds the lattice glues. The two rungs therefore differ, and they differ BECAUSE of which sites the
block map identifies. -/
theorem rgDelta_one_ne_rgDelta {n : ℕ} (hn : 2 ≤ n) (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀) :
    rgDelta (Lat := Lat) 1 ≠ rgDelta (Lat := Lat) n := by
  intro hEq
  have h0 : rgDelta (Lat := Lat) 1 (kerVec μ₀ h) = 0 := by
    rw [hEq, rgDelta_kerVec hn μ₀ h]
  rw [rgDelta_one_eq_id] at h0
  exact kerVec_ne_zero μ₀ h h0

/-! ### §5c — non-scalarity, and the operator is not zero -/

theorem sumCLMof_single_ne_zero (r : Bond Lat → Bond Lat) (b : Bond Lat) :
    sumCLMof r (EuclideanSpace.single b (1 : ℝ)) ≠ 0 := by
  intro hz
  have := congrFun (congrArg WithLp.ofLp hz) (r b)
  rw [sumCLMof_single] at this
  simp at this

/-- **must-not-fire control**: the ladder is not the zero operator at any rung. -/
theorem rgDelta_ne_zero (n : ℕ) : rgDelta (Lat := Lat) n ≠ 0 := by
  intro hz
  have hb : Nonempty (Bond Lat) := bondSpace_nontrivial
  obtain ⟨b⟩ := hb
  have hin : (inner ℝ (EuclideanSpace.single b (1 : ℝ))
      (rgDelta (Lat := Lat) n (EuclideanSpace.single b (1 : ℝ))) : ℝ) = 0 := by
    rw [hz]; simp
  rw [rgDelta_eq_deltaOf, inner_deltaOf] at hin
  have : sumCLMof (blockRepBond (Lat := Lat) n) (EuclideanSpace.single b (1 : ℝ)) = 0 := by
    have hnorm : ‖sumCLMof (blockRepBond (Lat := Lat) n) (EuclideanSpace.single b (1 : ℝ))‖ = 0 := by
      nlinarith [norm_nonneg (sumCLMof (blockRepBond (Lat := Lat) n)
        (EuclideanSpace.single b (1 : ℝ)))]
    exact norm_eq_zero.mp hnorm
  exact sumCLMof_single_ne_zero _ b this

/-- **Conjunct 4 — non-scalarity**, for block side `≥ 2` on a lattice with a nontrivial
direction. -/
theorem rgDelta_not_scalar {n : ℕ} (hn : 2 ≤ n) (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀) (c : ℝ) :
    rgDelta (Lat := Lat) n ≠ c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Bond Lat)) := by
  intro hEq
  have hk : rgDelta (Lat := Lat) n (kerVec μ₀ h) = 0 := rgDelta_kerVec hn μ₀ h
  rw [hEq] at hk
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hk
  have hc : c = 0 := by
    rcases smul_eq_zero.mp hk with hc | hv
    · exact hc
    · exact absurd hv (kerVec_ne_zero μ₀ h)
  obtain ⟨b⟩ := (bondSpace_nontrivial : Nonempty (Bond Lat))
  have hb : rgDelta (Lat := Lat) n (EuclideanSpace.single b (1 : ℝ)) = 0 := by
    rw [hEq]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hc]
    exact zero_smul ℝ _
  have hin : (inner ℝ (EuclideanSpace.single b (1 : ℝ))
      (rgDelta (Lat := Lat) n (EuclideanSpace.single b (1 : ℝ))) : ℝ) = 0 := by
    rw [hb]; simp
  rw [rgDelta_eq_deltaOf, inner_deltaOf] at hin
  have hz : sumCLMof (blockRepBond (Lat := Lat) n) (EuclideanSpace.single b (1 : ℝ)) = 0 := by
    have hnorm : ‖sumCLMof (blockRepBond (Lat := Lat) n) (EuclideanSpace.single b (1 : ℝ))‖ = 0 := by
      nlinarith [norm_nonneg (sumCLMof (blockRepBond (Lat := Lat) n)
        (EuclideanSpace.single b (1 : ℝ)))]
    exact norm_eq_zero.mp hnorm
  exact sumCLMof_single_ne_zero _ b hz

/-! ## §6 — the consequence for `Spine.coerc_u_main` -/

open AdalyFormal.Balaban.RGLadderCore

variable {Uconfig : Type*} [Nontrivial Uconfig]

/-- **The ladder cannot be a rung of a fixed-`V` coercivity hypothesis whose `V` contains the
glued difference.** Coercivity on `V` with a positive constant kills no nonzero vector of `V`
(`RGLadderCore.eq_zero_of_coercive_of_apply_eq_zero`), but a coarsening rung kills `kerVec`. -/
theorem no_coercivityHypothesis_rgLadder
    (cohyp : Balaban.CoercivityHypothesis (EuclideanSpace ℝ (Bond Lat)) Uconfig)
    {n : ℕ} (hn : 2 ≤ n) (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀)
    (k₀ : ℕ) (U₀ : Uconfig) (hΔ : cohyp.Δ k₀ U₀ = rgDelta (Lat := Lat) n)
    (hmem : kerVec (Lat := Lat) μ₀ h ∈ cohyp.V) : False := by
  refine no_uniform_ladder_of_one_small_rung cohyp k₀ U₀ hmem (kerVec_ne_zero μ₀ h) ?_
  rw [hΔ]
  exact rgDelta_kerVec hn μ₀ h

/-! ### §6a — `ell = 1` makes the membership hypothesis unconditional -/

/-- At block side `1` the tree's own block is a singleton. -/
theorem blockOf_one_eq {y x : PeriodicLatticeSite Lat} (hx : x ∈ blockOf y 1) : x = y := by
  rw [mem_blockOf] at hx
  funext μ
  exact Fin.ext (by have := hx μ; omega)

/-- `Γ_{y,y}` is empty: every axis segment of the staircase has coincident endpoints. -/
theorem staircasePath_self_eq_empty (y : PeriodicLatticeSite Lat) :
    staircasePath y y = (∅ : Finset (PeriodicLatticeEdge Lat)) := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  simp only [staircasePath, Finset.mem_union, axisSegment, Finset.mem_filter, Finset.mem_univ,
    true_and, min_self, max_self] at he
  rcases he with (⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩) | ⟨-, -, h1, h2⟩ <;> omega

/-- **`admissibleSubspaceInter Lat 1 = ⊤`.** At block side `1` there is no `(y,x)` pair with a
nonempty staircase, so `(2.121)` imposes no condition. -/
theorem admissibleSubspaceInter_one_eq_top :
    admissibleSubspaceInter Lat 1 = ⊤ := by
  refine eq_top_iff.mpr ?_
  intro B _
  rw [mem_admissibleSubspaceInter]
  intro y _ x hx b hb
  rw [blockOf_one_eq hx] at hb
  rw [staircasePath_self_eq_empty] at hb
  exact absurd hb (Finset.notMem_empty b)

/-- **`anchoredVInter 1 = ⊤`** on the anchored carrier `Spine.coerc_u_main` uses. -/
theorem anchoredVInter_one_eq_top :
    Balaban.Anchoring.anchoredVInter (Lat := Lat) 1 = ⊤ := by
  unfold Balaban.Anchoring.anchoredVInter
  rw [admissibleSubspaceInter_one_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact (WithLp.linearEquiv 2 ℝ (Bond Lat → ℝ)).symm.surjective

/-- **The unconditional form.** `coerc_u_main`'s `ell` is a free natural number; at `ell = 1` its
`V` is all of the carrier, so no coarsening rung can appear in it at all. -/
theorem no_coercivityHypothesis_rgLadder_at_ell_one
    (cohyp : Balaban.CoercivityHypothesis (EuclideanSpace ℝ (Bond Lat)) Uconfig)
    (hV : cohyp.V = Balaban.Anchoring.anchoredVInter (Lat := Lat) 1)
    {n : ℕ} (hn : 2 ≤ n) (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀)
    (k₀ : ℕ) (U₀ : Uconfig) (hΔ : cohyp.Δ k₀ U₀ = rgDelta (Lat := Lat) n) : False := by
  refine no_coercivityHypothesis_rgLadder cohyp hn μ₀ h k₀ U₀ hΔ ?_
  rw [hV, anchoredVInter_one_eq_top]
  exact Submodule.mem_top

/-! ## §7 — THE TOWER LAW AT OPERATOR LEVEL, and the kernels it nests

This is the answer to "is `Q_k` the `k`-fold composite of the one-step atom, and does the `k`
dependence come from the level index?" — for the BLOCK-SUPPORT channel, in general and exactly.

`sumCLMof_tower`: for `a ∣ b`, `A_b ∘ A_a = A_b`. Coarsening to side `a` and then to side `b` IS
coarsening to side `b`. So a chain of block sides `ell^0 ∣ ell^1 ∣ ell^2 ∣ …` is a genuine tower:
each rung factors through the previous one, with the level index the only thing that advances.

`sumCLMof_ker_mono` is the immediate consequence and the sharp form of this lane's obstruction:
**the kernels are nested INCREASING along the tower.** Information lost at one rung is lost at every
later rung. A fixed `V` therefore has to avoid the kernel of the LAST rung, which is the largest
one — and that is what a `k`-independent `V` cannot do. -/

/-- Only representatives have nonempty fibres. -/
theorem eq_self_of_blockRepBond_eq {n : ℕ} (hn : 0 < n) {b c : Bond Lat}
    (h : blockRepBond n b = c) : blockRepBond n c = c := by
  rw [← h, blockRepBond_idem hn]

/-- **THE TOWER LAW, at operator level**: `A_b ∘ A_a = A_b` whenever `a ∣ b`. -/
theorem sumCLMof_tower {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) :
    (sumCLMof (blockRepBond (Lat := Lat) b)).comp (sumCLMof (blockRepBond (Lat := Lat) a))
      = sumCLMof (blockRepBond (Lat := Lat) b) := by
  ext v c
  show WithLp.ofLp (sumCLMof (blockRepBond (Lat := Lat) b)
      (sumCLMof (blockRepBond (Lat := Lat) a) v)) c
    = WithLp.ofLp (sumCLMof (blockRepBond (Lat := Lat) b) v) c
  rw [sumCLMof_apply (blockRepBond (Lat := Lat) b) (sumCLMof (blockRepBond (Lat := Lat) a) v) c]
  have hinner : ∀ d ∈ Finset.univ.filter (fun d => blockRepBond (Lat := Lat) b d = c),
      WithLp.ofLp (sumCLMof (blockRepBond (Lat := Lat) a) v) d
        = ∑ x ∈ (Finset.univ.filter (fun x => blockRepBond (Lat := Lat) b x = c)).filter
            (fun x => blockRepBond (Lat := Lat) a x = d), WithLp.ofLp v x := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    rw [sumCLMof_apply]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      exact ⟨by rw [← hd, ← hx, blockRepBond_tower ha hb hab], hx⟩
    · exact fun hh => hh.2
  rw [sumCLMof_apply (blockRepBond (Lat := Lat) b) v c, Finset.sum_congr rfl hinner]
  refine Finset.sum_fiberwise_of_maps_to ?_ _
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  rw [blockRepBond_tower ha hb hab, hx]

/-- **The kernels nest**: what a coarser rung cannot see, no finer-to-coarser step recovers. -/
theorem sumCLMof_ker_mono {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b)
    {v : EuclideanSpace ℝ (Bond Lat)} (h : sumCLMof (blockRepBond (Lat := Lat) a) v = 0) :
    sumCLMof (blockRepBond (Lat := Lat) b) v = 0 := by
  have := congrArg (fun T : EuclideanSpace ℝ (Bond Lat) →L[ℝ] EuclideanSpace ℝ (Bond Lat) => T v)
    (sumCLMof_tower (Lat := Lat) ha hb hab)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at this
  rw [h] at this
  simpa using this.symm

/-- From `deltaOf r v = 0` recover `sumCLMof r v = 0` (the Gram identity). -/
theorem sumCLMof_eq_zero_of_deltaOf (r : Bond Lat → Bond Lat)
    {v : EuclideanSpace ℝ (Bond Lat)} (h : deltaOf r v = 0) : sumCLMof r v = 0 := by
  have hin : (inner ℝ v (deltaOf r v) : ℝ) = 0 := by rw [h]; simp
  rw [inner_deltaOf] at hin
  have : ‖sumCLMof r v‖ = 0 := by nlinarith [norm_nonneg (sumCLMof r v)]
  exact norm_eq_zero.mp this

/-- **The ladder's kernels nest.** -/
theorem rgDelta_ker_mono {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b)
    {v : EuclideanSpace ℝ (Bond Lat)} (h : rgDelta (Lat := Lat) a v = 0) :
    rgDelta (Lat := Lat) b v = 0 := by
  rw [rgDelta_eq_deltaOf, deltaOf]
  simp [sumCLMof_ker_mono ha hb hab (sumCLMof_eq_zero_of_deltaOf _ h)]

/-! ## §8 — the quantitative form: `finrank V ≤ #(coarse bonds)` at EVERY rung -/

/-- The coarse index set at block side `n`: the bonds fixed by the block map. -/
def CoarseBondIdx (Lat : PeriodicLatticeExtent) (n : ℕ) : Type :=
  {c : Bond Lat // blockRepBond n c = c}

instance instFintypeCoarseBondIdx (Lat : PeriodicLatticeExtent) (n : ℕ) :
    Fintype (CoarseBondIdx Lat n) := Subtype.fintype _

/-- The coarse field of a fine field: its block sums, indexed by the coarse bonds. -/
noncomputable def coarseLM (n : ℕ) :
    (Bond Lat → ℝ) →ₗ[ℝ] (CoarseBondIdx Lat n → ℝ) where
  toFun x := fun c => ∑ b ∈ Finset.univ.filter (fun b => blockRepBond n b = c.1), x b
  map_add' x y := by
    funext c
    simp [Finset.sum_add_distrib]
  map_smul' r x := by
    funext c
    simp [Finset.mul_sum]

/-- The fibre-sum operator vanishes exactly when all coarse block sums vanish. -/
theorem sumCLMof_eq_zero_iff {n : ℕ} (hn : 0 < n) (v : EuclideanSpace ℝ (Bond Lat)) :
    sumCLMof (blockRepBond (Lat := Lat) n) v = 0 ↔ coarseLM n (WithLp.ofLp v) = 0 := by
  constructor
  · intro h
    funext c
    have := congrFun (congrArg WithLp.ofLp h) c.1
    rw [sumCLMof_apply] at this
    simpa [coarseLM] using this
  · intro h
    refine euclid_eq_zero ?_
    intro c
    rw [sumCLMof_apply]
    by_cases hne : (Finset.univ.filter (fun b => blockRepBond (Lat := Lat) n b = c)).Nonempty
    · obtain ⟨b, hb⟩ := hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hrep : blockRepBond (Lat := Lat) n c = c := eq_self_of_blockRepBond_eq hn hb
      have h2 : coarseLM (Lat := Lat) n (WithLp.ofLp v) ⟨c, hrep⟩ = 0 := by rw [h]; rfl
      simpa [coarseLM] using h2
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty]

/-- **THE QUANTITATIVE OBSTRUCTION.** A fixed `V` must inject into the coarse space of EVERY rung
it is asked to be coercive against. -/
theorem finrank_V_le_card_coarse
    (cohyp : Balaban.CoercivityHypothesis (EuclideanSpace ℝ (Bond Lat)) Uconfig)
    {n : ℕ} (hn : 0 < n) (k₀ : ℕ) (U₀ : Uconfig)
    (hΔ : cohyp.Δ k₀ U₀ = rgDelta (Lat := Lat) n) :
    Module.finrank ℝ cohyp.V ≤ Fintype.card (CoarseBondIdx Lat n) := by
  have hinj : Function.Injective
      (((coarseLM (Lat := Lat) n).comp
        ((WithLp.linearEquiv 2 ℝ (Bond Lat → ℝ)).toLinearMap.comp cohyp.V.subtype))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨v, hv⟩ hz
    have hz' : coarseLM (Lat := Lat) n (WithLp.ofLp v) = 0 := hz
    have hA : sumCLMof (blockRepBond (Lat := Lat) n) v = 0 :=
      (sumCLMof_eq_zero_iff hn v).mpr hz'
    have hΔv : cohyp.Δ k₀ U₀ v = 0 := by
      rw [hΔ, rgDelta_eq_deltaOf, deltaOf]
      simp [hA]
    exact Subtype.ext (RGLadderCore.eq_zero_of_coercive_of_apply_eq_zero (cohyp.Δ k₀ U₀) cohyp.V
      cohyp.γ'' cohyp.γ''_pos (cohyp.coercive k₀ U₀) hv hΔv)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card] at hle

/-- **The block IS the whole torus** (the `L μ + 1 ≤ n` degenerate): at most three coarse bonds,
one per direction. Combined with `finrank_V_le_card_coarse`, a fixed `V` compatible with such a
rung has `finrank V ≤ 3`. -/
theorem card_coarseBondIdx_le_three {n : ℕ} (hn : ∀ μ : Fin 3, Lat μ + 1 ≤ n) :
    Fintype.card (CoarseBondIdx Lat n) ≤ 3 := by
  have hinj : Function.Injective (fun c : CoarseBondIdx Lat n => c.1.2) := by
    rintro ⟨⟨x, μ⟩, hx⟩ ⟨⟨y, ν⟩, hy⟩ hEq
    simp only at hEq
    subst hEq
    refine Subtype.ext ?_
    have hxo : x = originSite (Lat := Lat) := by
      funext ρ
      refine Fin.ext ?_
      have hval : (x ρ).val / n * n = (x ρ).val := by
        have h0 := congrArg (fun (e : Bond Lat) => (e.1 ρ).val) hx
        simpa [blockRepBond, blockRepSite_val] using h0
      have hlt : (x ρ).val < n := lt_of_lt_of_le (x ρ).isLt (hn ρ)
      rw [Nat.div_eq_of_lt hlt] at hval
      show (x ρ).val = 0
      omega
    have hyo : y = originSite (Lat := Lat) := by
      funext ρ
      refine Fin.ext ?_
      have hval : (y ρ).val / n * n = (y ρ).val := by
        have h0 := congrArg (fun (e : Bond Lat) => (e.1 ρ).val) hy
        simpa [blockRepBond, blockRepSite_val] using h0
      have hlt : (y ρ).val < n := lt_of_lt_of_le (y ρ).isLt (hn ρ)
      rw [Nat.div_eq_of_lt hlt] at hval
      show (y ρ).val = 0
      omega
    show ((x, μ) : Bond Lat) = (y, μ)
    rw [hxo, hyo]
  have := Fintype.card_le_of_injective _ hinj
  simpa using this

/-! ## §9 — the family indexed by `k`: `n = ell ^ k`

This is where the level index actually advances. `ell ^ k ∣ ell ^ (k+1)`, so §7's tower law applies
at every step: **rung `k+1` factors through rung `k`**, which is what "`Q_k` is the `k`-fold
composite of the one-step atom" says in the block-support channel. The `ell = 1` degenerate is the
must-fire control: there the tower never coarsens and the family collapses. -/

/-- **THE TOWER, as a `k`-indexed family.** Each rung factors through the previous one. -/
theorem rgDelta_pow_tower {ell : ℕ} (hell : 0 < ell) (k : ℕ) :
    (sumCLMof (blockRepBond (Lat := Lat) (ell ^ (k + 1)))).comp
        (sumCLMof (blockRepBond (Lat := Lat) (ell ^ k)))
      = sumCLMof (blockRepBond (Lat := Lat) (ell ^ (k + 1))) :=
  sumCLMof_tower (pow_pos hell k) (pow_pos hell (k + 1)) (pow_dvd_pow ell (Nat.le_succ k))

/-- **The tower's kernels increase along `k`.** Information lost at rung `k₁` is lost at every
later rung. -/
theorem rgDelta_pow_ker_mono {ell : ℕ} (hell : 0 < ell) {k₁ k₂ : ℕ} (h : k₁ ≤ k₂)
    {v : EuclideanSpace ℝ (Bond Lat)} (hv : rgDelta (Lat := Lat) (ell ^ k₁) v = 0) :
    rgDelta (Lat := Lat) (ell ^ k₂) v = 0 :=
  rgDelta_ker_mono (pow_pos hell k₁) (pow_pos hell k₂) (pow_dvd_pow ell h) hv

/-- **Degenerate `ell = 1`**: every rung of the tower is the identity. -/
theorem rgDelta_pow_one_k_constant (k : ℕ) :
    rgDelta (Lat := Lat) (1 ^ k) = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Bond Lat)) := by
  rw [one_pow]
  exact rgDelta_one_eq_id

/-- **must-fire control (d)**: at `ell = 1` the tower is `k`-CONSTANT and therefore fails
`coerc_u_main`'s fourth conjunct — the coarsening is what carries the `k`-dependence, and with the
coarsening switched off (block side one at every rung) there is none. -/
theorem rgDelta_pow_one_fails_rg_scale_dependence {Uconfig : Type*} :
    ¬ ∃ (U : Uconfig) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧
        rgDelta (Lat := Lat) (1 ^ k₁) ≠ rgDelta (Lat := Lat) (1 ^ k₂) := by
  rintro ⟨U, k₁, k₂, -, hne⟩
  exact hne (by rw [rgDelta_pow_one_k_constant, rgDelta_pow_one_k_constant])

/-- **The tower genuinely coarsens once `2 ≤ ell`**: rung `0` is the identity and rung `1` is not,
because `ell ^ 1 = ell ≥ 2` glues two sites. -/
theorem rgDelta_pow_zero_ne_one {ell : ℕ} (hell : 2 ≤ ell) (μ₀ : Fin 3) (h : 1 ≤ Lat μ₀) :
    rgDelta (Lat := Lat) (ell ^ 0) ≠ rgDelta (Lat := Lat) (ell ^ 1) := by
  rw [pow_zero, pow_one]
  exact rgDelta_one_ne_rgDelta hell μ₀ h

#print axioms blockRepSite_val
#print axioms floorMul_le
#print axioms instFintypeCoarseBondIdx
#print axioms kerBondA
#print axioms kerBondB
#print axioms unitSite_apply_self
#print axioms unitSite_apply_other
#print axioms matCLM
#print axioms matCLM_apply
#print axioms blockRepSite
#print axioms blockRepBond
#print axioms blockRepSite_mem_CoarseLattice
#print axioms mem_blockOf_blockRepSite
#print axioms blockRepSite_one
#print axioms blockRepBond_one
#print axioms blockRepSite_zero
#print axioms floorMul_mono
#print axioms floorMul_idem
#print axioms floorMul_tower
#print axioms blockRepSite_idem
#print axioms blockRepBond_idem
#print axioms sumCLMof
#print axioms sumCLMof_apply
#print axioms sumCLMof_single
#print axioms deltaOf
#print axioms rgDelta
#print axioms rgDelta_eq_deltaOf
#print axioms deltaOf_congr
#print axioms rgDelta_congr
#print axioms deltaOf_adjoint
#print axioms inner_deltaOf
#print axioms originSite
#print axioms unitSite
#print axioms originSite_ne_unitSite
#print axioms bondSpace_nontrivial
#print axioms blockRep_originSite
#print axioms blockRep_unitSite
#print axioms kerBond_ne
#print axioms kerBond_same_rep
#print axioms kerVec
#print axioms kerVec_ne_zero
#print axioms euclid_eq_zero
#print axioms sumCLMof_kerVec
#print axioms sumCLMof_id_eq_id
#print axioms flatLadder_k_constant
#print axioms sumCLMof_single_ne_zero
#print axioms blockOf_one_eq
#print axioms eq_self_of_blockRepBond_eq
#print axioms sumCLMof_eq_zero_of_deltaOf
#print axioms CoarseBondIdx
#print axioms coarseLM
#print axioms sumCLMof_eq_zero_iff
#print axioms rgDelta_pow_tower
#print axioms rgDelta_pow_ker_mono
#print axioms rgDelta_pow_one_k_constant
#print axioms rgDelta_pow_one_fails_rg_scale_dependence
#print axioms rgDelta_pow_zero_ne_one
#print axioms blockRepSite_eq_of_mem_blockOf
#print axioms blockRepSite_tower
#print axioms blockRepBond_tower
#print axioms sumCLMof_tower
#print axioms sumCLMof_ker_mono
#print axioms rgDelta_ker_mono
#print axioms rgDelta_adjoint
#print axioms rgDelta_psd
#print axioms rgDelta_kerVec
#print axioms rgDelta_one_eq_id
#print axioms rgDelta_one_ne_rgDelta
#print axioms rgDelta_not_scalar
#print axioms rgDelta_ne_zero
#print axioms deltaOf_id_eq_id
#print axioms flatLadder_fails_rg_scale_dependence
#print axioms staircasePath_self_eq_empty
#print axioms admissibleSubspaceInter_one_eq_top
#print axioms anchoredVInter_one_eq_top
#print axioms no_coercivityHypothesis_rgLadder
#print axioms no_coercivityHypothesis_rgLadder_at_ell_one
#print axioms finrank_V_le_card_coarse
#print axioms card_coarseBondIdx_le_three

end AdalyFormal.Balaban.RGLadderCoarse
