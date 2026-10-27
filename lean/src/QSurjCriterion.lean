/-
# `QSurjCriterion.lean` — A PER-BLOCK, VOLUME-FREE SUFFICIENT CRITERION FOR SURJECTIVITY OF THE
# COVARIANT BLOCK AVERAGE `Q_ell(U)` AT GENERAL `U`.

LANE `compute/qsurj_criterion/`.  Write scope: `compute/qsurj_criterion/` only.
Read-only inputs: `compute/hkinv_seam/` (pinned in `CONSUMED_SHA.txt`) and `formal/AdalyFormal/`.

`compute/hkinv_seam/` proved that the S9 seam `hKinv` of `CurvedLegWire.gamma0_curved_leg_composed`
is — given that theorem's own package — THE SAME STATEMENT as `Function.Surjective D3.Qt`, i.e.
surjectivity of `qCLM U (L^{k+1})`, and discharged it on the flat gauge ORBIT and in a
volume-DEPENDENT `frobSupBond` neighbourhood.  Its `SCOPE.md` §5 LOCATED, and explicitly did not
build, a per-block route to general `U`.  This file builds it.

## The object, read from the definitions rather than from prose

`AdalyFormal.Balaban.BridgeInverse.qCLM U ell` is `LineIntegralCovariant.lineCoarseRestrictCov`
promoted to the `PiLp 2` carriers, and that definition is, VERBATIM:

    lineCoarseRestrictCov U ell A b = (1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf b.1.1 ell,
                                        rZeroA U b.1.1 x A b.2 ell            -- LineIntegralCovariant.lean
    rZeroA U cMinus x A μ ell = ∑ i ∈ Finset.range ell,
        RMap (periodicPathHolonomy U cMinus (transportPath cMinus x μ i)) (A (pathSite x μ i, μ))
                                                                              -- Q1Real.lean

so that, for a coarse bond `b = (y, μ)` with `y ∈ CoarseLattice L ell`,

    Q(U)A(y,μ) = (1/ell⁴) · Σ_{x ∈ B(y)} Σ_{i<ell} R(Γ_{y,x} ∪ [x, x+i·e_μ]) · A(x + i·e_μ, μ).

The index sets are `blockOf b.1.1 ell` and `Finset.range ell` — TRANSCRIBED FROM THE DEFINING
OBJECT (S83), not from a description of it.

## The mechanism

Call a fine site `z` **`μ`-top-layer** when `(z μ).val % ell = ell - 1`.  Two facts (§1):

* **single hit in a line** (`isTop_pathSite_iff`): for `x` in any block and `i < ell`, the moved
  site `pathSite x μ i` is `μ`-top-layer for EXACTLY ONE `i`, namely `i = iTop = ell-1-(x μ).val%ell`;
* **unique sight** (`coarseOf_topSite`): the coarse site of that top-layer site is `y` itself.

Hence a bond field supported on the `μ`-top-layer bonds is read by exactly one coarse bond, and `Q`
restricted to that subspace is BLOCK-DIAGONAL over coarse bonds.  Its block is `blockTopMap`, and
`Q(U)` is surjective as soon as every block is (`TopSpanning`, §3).

**Both facts are FALSE without `hdvd : ∀ μ, ell ∣ L μ + 1`.**  This is not a decorative hypothesis:
`probe_combinatorics.py` enumerates the whole construction on non-fitting extents and finds, e.g. at
`L+1 = (3,3,3)`, `ell = 2`, that `x = (0,0,2)`, `μ = 2` has `iTop = 1` and
`pathSite x 2 1 = (0,0,0)`, whose offset is `0 ≠ ell-1`: 27 of 81 `(x,μ)` pairs fail.  The mutant
`M-DVD` deletes `hdvd` and the build fails.

## What is NOT claimed

~~`TopSpanning` is SUFFICIENT, not necessary, and it is not proved for every `U`.~~
**SUPERSEDED (S75), retained struck.**  `QSurjGeneral.topSpanning_general` proves `TopSpanning U ell`
for EVERY `U`, by an argument that uses one transverse offset (the block's CORNER LINE) rather than
the span over all of them, and hence `QSurjGeneral.qCLM_surjective_general` proves surjectivity at
every background.  The struck sentence described this FILE's state and is no longer the lane's.
What remains true and unchanged: `TopSpanning` is SUFFICIENT and is not claimed necessary; §5 proves
it on the explicit class `8·ell·frobSupBond U < 1` by an independent perturbation argument —
VOLUME-FREE, which is what `hkinv_seam`'s `SCOPE.md` §5 (R-a)+(R-b) could not deliver — and §6 shows
a single top-layer transport sum CAN be singular, which is exactly why the span-over-all-offsets
route could not be pushed through.
-/
import AdalyFormal.Balaban.BridgeInverseCarrier
import AdalyFormal.Balaban.RegularUQChain
import AdalyFormal.Balaban.WitnessInequality
import AdalyFormal.Balaban.ReparamCDisjoint

open scoped InnerProductSpace RealInnerProductSpace

set_option maxHeartbeats 4000000

noncomputable section

namespace QSurjCriterion

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLinkConfiguration periodicPathHolonomy)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one suTwoWitness
  suTwoWitness_ne_zero)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf inBlock CoarseLattice
  mem_CoarseLattice coarseLattice_mem_fits card_blockOf_of_coarse unique_multiple_in_window)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero)
open AdalyFormal.Balaban.Q1Real (rZeroA transportPath periodicPathHolonomy_trivialU_eq_one)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.BridgeInverse (qCLM qCLM_apply CoarseFnL2)
open AdalyFormal.Balaban.ReparamCDisjoint (pathSite_apply_ne pathSite_apply_self_val)
open AdalyFormal.Balaban.WitnessInequality (pathSite_eq_iff)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg)
open AdalyFormal.Balaban.RegularUQChain (norm_RMap_holonomy_sub_self_le transportPath_length_le)

variable {L : PeriodicLatticeExtent}

/-- `ℕ`-scalar and real-scalar multiples agree.  Proved here rather than named, because the
Mathlib spelling of this bridge has changed more than once. -/
theorem cast_nsmul {M : Type*} [AddCommGroup M] [Module ℝ M] (n : ℕ) (v : M) :
    ((n : ℝ)) • v = n • v := by
  induction n with
  | zero => simp
  | succ k ih => push_cast; rw [add_smul, one_smul, ih, succ_nsmul]

/-! ## §0 — the top layer of a block, and the coarse site a fine site belongs to -/

/-- The `μ`-offset of a fine site inside its own block of side `ell`. -/
def muOff (ell : ℕ) (z : PeriodicLatticeSite L) (μ : Fin 3) : ℕ := (z μ).val % ell

/-- **`z` is `μ`-TOP-LAYER**: its `μ`-coordinate sits at the far end of its own block,
`(z μ).val % ell = ell - 1`.  This is the subspace on which `Q` will be block-diagonal. -/
def IsTop (ell : ℕ) (z : PeriodicLatticeSite L) (μ : Fin 3) : Prop := muOff ell z μ = ell - 1

instance instDecidableIsTop (ell : ℕ) (z : PeriodicLatticeSite L) (μ : Fin 3) :
    Decidable (IsTop ell z μ) := Nat.decEq _ _

/-- The unique step count `i < ell` that carries `x` to the top layer of its own block. -/
def iTop (ell : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) : ℕ := ell - 1 - muOff ell x μ

/-- The top-layer site of `x`'s own `μ`-line. -/
def topSite (ell : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) : PeriodicLatticeSite L :=
  pathSite x μ (iTop ell x μ)

/-- **The coarse site a fine site belongs to**: round every coordinate down to a multiple of
`ell`. -/
def coarseOf (ell : ℕ) (z : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun ν => ⟨(z ν).val - (z ν).val % ell, lt_of_le_of_lt (Nat.sub_le _ _) (z ν).isLt⟩

theorem coarseOf_val (ell : ℕ) (z : PeriodicLatticeSite L) (ν : Fin 3) :
    ((coarseOf ell z) ν).val = (z ν).val - (z ν).val % ell := rfl

theorem coarseOf_mem {ell : ℕ} (_hell : 0 < ell) (z : PeriodicLatticeSite L) :
    coarseOf ell z ∈ CoarseLattice L ell := by
  refine mem_CoarseLattice.mpr (fun ν => ?_)
  have hdm := Nat.div_add_mod (z ν).val ell
  have hrw : ((coarseOf ell z) ν).val = ell * ((z ν).val / ell) := by
    rw [coarseOf_val]; omega
  rw [hrw, Nat.mul_mod_right]

/-- A fine site lies in the block of its own coarse site. -/
theorem mem_blockOf_coarseOf {ell : ℕ} (hell : 0 < ell) (z : PeriodicLatticeSite L) :
    z ∈ blockOf (coarseOf ell z) ell := by
  refine mem_blockOf.mpr (fun ν => ?_)
  have hlt : (z ν).val % ell < ell := Nat.mod_lt _ hell
  have hle : (z ν).val % ell ≤ (z ν).val := Nat.mod_le _ _
  rw [coarseOf_val]
  omega

/-- **`coarseOf` INVERTS block membership.**  A coarse site whose block contains `x` is the coarse
site of `x`.  (`unique_multiple_in_window`, the tree's own one-multiple-per-window lemma.) -/
theorem coarseOf_eq_of_mem_blockOf {ell : ℕ} {y x : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) (hx : x ∈ blockOf y ell) :
    coarseOf ell x = y := by
  have hxb := mem_blockOf.mp hx
  have hyc := mem_CoarseLattice.mp hy
  funext ν
  apply Fin.ext
  rw [coarseOf_val]
  refine unique_multiple_in_window ell (x ν).val ((x ν).val - (x ν).val % ell) (y ν).val ?_ (hyc ν)
    (Nat.sub_le _ _) ?_ (hxb ν).1 (hxb ν).2
  · have hdm := Nat.div_add_mod (x ν).val ell
    have : (x ν).val - (x ν).val % ell = ell * ((x ν).val / ell) := by omega
    rw [this, Nat.mul_mod_right]
  · have hlt : (x ν).val % ell < ell := by
      rcases Nat.eq_zero_or_pos ell with h | h
      · exfalso; have := (hxb ν).1; have := (hxb ν).2; omega
      · exact Nat.mod_lt _ h
    have hle : (x ν).val % ell ≤ (x ν).val := Nat.mod_le _ _
    omega

/-! ## §1 — THE TWO COMBINATORIAL FACTS.  Both need `hdvd`. -/

/-- **SINGLE HIT IN A LINE.**  Among the `ell` sites `pathSite x μ i`, `i < ell`, of one line of the
block average, EXACTLY ONE is `μ`-top-layer, and it is the one with `i = iTop ell x μ`.

`hdvd` is load-bearing: it is what makes reduction modulo the periodic extent `L μ + 1` preserve the
residue modulo `ell` (`Nat.mod_mod_of_dvd`).  Without it the wrap moves a site to a DIFFERENT
offset — measured: 27 failures of 81 at `L+1 = (3,3,3)`, `ell = 2`. -/
theorem isTop_pathSite_iff {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (x : PeriodicLatticeSite L) (μ : Fin 3) {i : ℕ} (hi : i < ell) :
    IsTop ell (pathSite x μ i) μ ↔ i = iTop ell x μ := by
  have hval : ((pathSite x μ i) μ).val = ((x μ).val + i) % (L μ + 1) :=
    pathSite_apply_self_val x μ i
  have hmm : ((x μ).val + i) % (L μ + 1) % ell = ((x μ).val + i) % ell :=
    Nat.mod_mod_of_dvd _ (hdvd μ)
  have hr : (x μ).val % ell < ell := Nat.mod_lt _ hell
  have hilt : i % ell = i := Nat.mod_eq_of_lt hi
  have hsplit : ((x μ).val + i) % ell = ((x μ).val % ell + i) % ell := by
    conv_lhs => rw [Nat.add_mod, hilt]
  simp only [IsTop, muOff, iTop, hval, hmm, hsplit]
  rcases lt_or_ge ((x μ).val % ell + i) ell with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega

theorem iTop_lt {ell : ℕ} (hell : 0 < ell) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    iTop ell x μ < ell := by
  have hr : (x μ).val % ell < ell := Nat.mod_lt _ hell
  simp only [iTop, muOff]; omega

theorem isTop_topSite {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (x : PeriodicLatticeSite L) (μ : Fin 3) : IsTop ell (topSite ell x μ) μ :=
  (isTop_pathSite_iff hell hdvd x μ (iTop_lt hell x μ)).mpr rfl

/-- The `μ`-coordinate of the top-layer site, in closed form.  The periodic wrap does NOT fire:
`hdvd` + coarseness give `y μ + ell ≤ L μ + 1` (`coarseLattice_mem_fits`). -/
theorem topSite_val {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y x : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (hx : x ∈ blockOf y ell)
    (μ : Fin 3) : ((topSite ell x μ) μ).val = (y μ).val + (ell - 1) := by
  have hxb := mem_blockOf.mp hx
  have hfit : (y μ).val + ell ≤ L μ + 1 := coarseLattice_mem_fits hdvd hy μ
  have hcoarse : ((coarseOf ell x) μ).val = (y μ).val := by
    rw [coarseOf_eq_of_mem_blockOf hy hx]
  rw [coarseOf_val] at hcoarse
  have hr : (x μ).val % ell < ell := Nat.mod_lt _ hell
  have hle : (x μ).val % ell ≤ (x μ).val := Nat.mod_le _ _
  have hsum : (x μ).val + iTop ell x μ = (y μ).val + (ell - 1) := by
    simp only [iTop, muOff]; omega
  rw [topSite, pathSite_apply_self_val, hsum, Nat.mod_eq_of_lt (by omega)]

/-- **UNIQUE SIGHT.**  The top-layer site of any `x` in the block of a coarse `y` has `y` as its
own coarse site.  So a `μ`-top-layer fine bond is read by EXACTLY ONE coarse bond, and the top-layer
subspace decouples over coarse bonds. -/
theorem coarseOf_topSite {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y x : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (hx : x ∈ blockOf y ell)
    (μ : Fin 3) : coarseOf ell (topSite ell x μ) = y := by
  have hyc := mem_CoarseLattice.mp hy
  funext ν
  apply Fin.ext
  rw [coarseOf_val]
  by_cases hν : ν = μ
  · subst hν
    have hv := topSite_val hell hdvd hy hx ν
    have hmod : ((y ν).val + (ell - 1)) % ell = ell - 1 := by
      have h0 : (y ν).val % ell = 0 := hyc ν
      have h1 : (ell - 1) % ell = ell - 1 := Nat.mod_eq_of_lt (by omega)
      rw [Nat.add_mod, h0, h1, Nat.zero_add, h1]
    rw [hv, hmod]
    omega
  · have hv : ((topSite ell x μ) ν).val = (x ν).val := by
      rw [topSite]; exact congrArg Fin.val (pathSite_apply_ne x μ ν _ hν)
    have hc : ((coarseOf ell x) ν).val = (y ν).val := by
      rw [coarseOf_eq_of_mem_blockOf hy hx]
    rw [coarseOf_val] at hc
    rw [hv]; exact hc

theorem topSite_apply_ne {ell : ℕ} (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    (topSite ell x μ) ν = x ν := pathSite_apply_ne x μ ν _ h

/-! ## §2 — THE CRITERION.

`blockTopMap U ell b` reads a bond field ONLY at the `μ`-top-layer bonds of the block of `b`; its
range is therefore exactly the sum of the ranges of the `ell^{d-1}` transverse transport sums
`M_t = Σ_{s<ell} R(Γ_{y, y+t+s·e_μ} ∪ [y+t+s·e_μ, y+t+(ell-1)·e_μ])` that `hkinv_seam/SCOPE.md` §5
names — with no transverse indexing, because the sum over `x ∈ B(y)` already enumerates `(t,s)`. -/

/-- **THE PER-BLOCK MAP.**  The single-`i` restriction of `rZeroA`, summed over the block:

    blockTopMap U ell (y,μ) w = Σ_{x ∈ B(y)} R(Γ_{y,x} ∪ [x, top(x)]) · w(top(x), μ)

with `top(x) = pathSite x μ (iTop ell x μ)`.  Every index set is `Q`'s own. -/
def blockTopMap (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (b : CoarseBond L ell) : (Bond L → SuTwo) →ₗ[ℝ] SuTwo where
  toFun w := ∑ x ∈ blockOf b.1.1 ell,
    RMap (periodicPathHolonomy U b.1.1 (transportPath b.1.1 x b.2 (iTop ell x b.2)))
      (w (topSite ell x b.2, b.2))
  map_add' w1 w2 := by
    simp only [Pi.add_apply, map_add]
    rw [Finset.sum_add_distrib]
  map_smul' c w := by
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
    rw [Finset.smul_sum]

theorem blockTopMap_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (b : CoarseBond L ell) (w : Bond L → SuTwo) :
    blockTopMap U ell b w = ∑ x ∈ blockOf b.1.1 ell,
      RMap (periodicPathHolonomy U b.1.1 (transportPath b.1.1 x b.2 (iTop ell x b.2)))
        (w (topSite ell x b.2, b.2)) := rfl

/-- **THE CRITERION.**  Per coarse bond, volume-free: no sum over the lattice appears. -/
def TopSpanning (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) : Prop := ∀ b : CoarseBond L ell, Function.Surjective (blockTopMap U ell b)

/-- The coarse bond that reads a `μ`-top-layer fine bond. -/
def coarseBond {ell : ℕ} (hell : 0 < ell) (z : PeriodicLatticeSite L) (ν : Fin 3) :
    CoarseBond L ell := (⟨coarseOf ell z, coarseOf_mem hell z⟩, ν)

/-! ## §3 — CRITERION ⟹ SURJECTIVITY. -/

/-- **THE CRITERION IMPLIES SURJECTIVITY OF `Q_ell(U)`.**

The solution is assembled from per-block preimages: `A(z,ν) := g_{(coarseOf z, ν)}(z,ν)` on the
`ν`-top-layer bonds and `0` elsewhere.  `isTop_pathSite_iff` collapses each inner `i`-sum to its one
surviving term, and `coarseOf_topSite` guarantees that the term picked up at block `b` is `g_b`'s —
i.e. that the blocks do not read each other's data. -/
theorem qCLM_surjective_of_topSpanning
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (h : TopSpanning U ell) : Function.Surjective (qCLM U ell) := by
  intro F
  choose g hg using fun b : CoarseBond L ell => h b (((ell : ℝ) ^ 4) • WithLp.ofLp F b)
  set A : Bond L → SuTwo := fun bd =>
    if IsTop ell bd.1 bd.2 then g (coarseBond hell bd.1 bd.2) bd else 0 with hAdef
  have hAapply : ∀ (z : PeriodicLatticeSite L) (ν : Fin 3),
      A (z, ν) = if IsTop ell z ν then g (coarseBond hell z ν) (z, ν) else 0 := fun _ _ => rfl
  refine ⟨WithLp.toLp 2 A, ?_⟩
  refine (WithLp.linearEquiv 2 ℝ (CoarseBond L ell → SuTwo)).injective ?_
  funext b
  show lineCoarseRestrictCov U ell A b = WithLp.ofLp F b
  have key : ∀ x ∈ blockOf b.1.1 ell, rZeroA U b.1.1 x A b.2 ell
      = RMap (periodicPathHolonomy U b.1.1 (transportPath b.1.1 x b.2 (iTop ell x b.2)))
          (A (topSite ell x b.2, b.2)) := by
    intro x hx
    have hiT : iTop ell x b.2 < ell := iTop_lt hell x b.2
    show (∑ i ∈ Finset.range ell,
        RMap (periodicPathHolonomy U b.1.1 (transportPath b.1.1 x b.2 i))
          (A (pathSite x b.2 i, b.2))) = _
    refine Finset.sum_eq_single (iTop ell x b.2) ?_ ?_
    · intro i hi hne
      have hlt : i < ell := Finset.mem_range.mp hi
      have hnt : ¬ IsTop ell (pathSite x b.2 i) b.2 := fun hc =>
        hne ((isTop_pathSite_iff hell hdvd x b.2 hlt).mp hc)
      rw [hAapply, if_neg hnt, map_zero]
    · intro hnm
      exact absurd (Finset.mem_range.mpr hiT) hnm
  have hcb : ∀ x ∈ blockOf b.1.1 ell,
      A (topSite ell x b.2, b.2) = g b (topSite ell x b.2, b.2) := by
    intro x hx
    have htop : IsTop ell (topSite ell x b.2) b.2 := isTop_topSite hell hdvd x b.2
    have hbb : coarseBond hell (topSite ell x b.2) b.2 = b := by
      have hco : coarseOf ell (topSite ell x b.2) = b.1.1 :=
        coarseOf_topSite hell hdvd b.1.2 hx b.2
      show ((⟨coarseOf ell (topSite ell x b.2), _⟩ : {y : PeriodicLatticeSite L //
        y ∈ CoarseLattice L ell}), b.2) = b
      rw [Prod.ext_iff]
      exact ⟨Subtype.ext hco, rfl⟩
    rw [hAapply, if_pos htop, hbb]
  have hsum : ∑ x ∈ blockOf b.1.1 ell, rZeroA U b.1.1 x A b.2 ell = blockTopMap U ell b (g b) := by
    rw [blockTopMap_apply]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [key x hx, hcb x hx]
  rw [lineCoarseRestrictCov, hsum, hg b, smul_smul]
  have hne : ((ell : ℝ) ^ 4) ≠ 0 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  rw [one_div, inv_mul_cancel₀ hne, one_smul]

/-! ## §4 — CONTROLS.  The criterion is neither empty nor automatic. -/

/-- **MUST-PASS CONTROL: the criterion holds at the flat background.**  At `U = 1` every holonomy
is `1` and `RMap 1 = id`, so `blockTopMap` is `w ↦ Σ_{x ∈ B(y)} w(top(x), μ)`, which hits any `v`
at the constant field `(ell³)⁻¹ • v`.  Consistency with `hkinv_seam`'s discharged case. -/
theorem topSpanning_trivialU {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    TopSpanning (trivialU L) ell := by
  intro b v
  have hcard : (blockOf b.1.1 ell).card = ell ^ 3 := card_blockOf_of_coarse hdvd b.1.2
  have hcardpos : (0 : ℝ) < ((blockOf b.1.1 ell).card : ℝ) := by
    rw [hcard]; positivity
  refine ⟨fun _ => (((blockOf b.1.1 ell).card : ℝ))⁻¹ • v, ?_⟩
  rw [blockTopMap_apply]
  have hterm : ∀ x ∈ blockOf b.1.1 ell,
      RMap (periodicPathHolonomy (trivialU L) b.1.1 (transportPath b.1.1 x b.2 (iTop ell x b.2)))
        ((((blockOf b.1.1 ell).card : ℝ))⁻¹ • v) = (((blockOf b.1.1 ell).card : ℝ))⁻¹ • v := by
    intro x hx
    rw [periodicPathHolonomy_trivialU_eq_one, RMap_one, LinearMap.id_apply]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, ← cast_nsmul, smul_smul,
    mul_inv_cancel₀ (ne_of_gt hcardpos), one_smul]

/-- **MUST-FAIL CONTROL: the criterion is FALSE at `ell = 0`.**  `blockOf y 0 = ∅`, so every
`blockTopMap` is the zero map, which is not surjective onto the nontrivial `𝔰𝔲(2)`.  So
`TopSpanning` is a condition with content: it is not satisfied by every parameter. -/
theorem sum_blockOf_ell_zero {M : Type*} [AddCommMonoid M] (y : PeriodicLatticeSite L)
    (f : PeriodicLatticeSite L → M) : ∑ x ∈ blockOf y 0, f x = 0 :=
  Finset.sum_eq_zero (fun x hx => absurd ((mem_blockOf.mp hx) 0) (by omega))

theorem not_topSpanning_ell_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ¬ TopSpanning U 0 := by
  intro h
  obtain ⟨w, hw⟩ := h (Classical.arbitrary (CoarseBond L 0)) suTwoWitness
  rw [blockTopMap_apply, sum_blockOf_ell_zero] at hw
  exact suTwoWitness_ne_zero hw.symm

/-- The matching consistency check on the CONCLUSION: at `ell = 0` the operator itself is not
surjective either, so the criterion and its conclusion fail together — no vacuous implication. -/
theorem not_qCLM_surjective_ell_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ¬ Function.Surjective (qCLM U 0) := by
  intro h
  obtain ⟨A, hA⟩ := h (WithLp.toLp 2 (fun _ => suTwoWitness))
  have := congrFun (congrArg (fun u : CoarseFnL2 L 0 => WithLp.ofLp u) hA)
    (Classical.arbitrary (CoarseBond L 0))
  rw [qCLM_apply] at this
  rw [lineCoarseRestrictCov, sum_blockOf_ell_zero, smul_zero] at this
  exact suTwoWitness_ne_zero (by simpa using this.symm)

/-! ## §5 — THE CRITERION HOLDS ON A VOLUME-FREE NEIGHBOURHOOD OF THE FLAT ORBIT.

This is what `hkinv_seam/SCOPE.md` §5 records as NOT delivered: its (R-a) leaves a
`√(#coarse bonds)` in the constant and its (R-b) leaves the section norm uncontrolled.  Both
obstructions are bypassed here, because the criterion never forms an operator norm and never needs
a section: it is tested on ONE `𝔰𝔲(2)` at a time. -/

/-- The constant field, as a linear map. -/
def constLM : SuTwo →ₗ[ℝ] (Bond L → SuTwo) where
  toFun v := fun _ => v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The per-block map tested on constant fields — a single endomorphism of `𝔰𝔲(2)` per coarse
bond, which at `U = 1` is `ell³ · id`. -/
def nBlock (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (b : CoarseBond L ell) : SuTwo →ₗ[ℝ] SuTwo :=
  (blockTopMap U ell b).comp constLM

theorem nBlock_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (b : CoarseBond L ell) (v : SuTwo) :
    nBlock U ell b v = ∑ x ∈ blockOf b.1.1 ell,
      RMap (periodicPathHolonomy U b.1.1 (transportPath b.1.1 x b.2 (iTop ell x b.2))) v := rfl

/-- **THE PER-BLOCK DRIFT, WITH NO VOLUME IN IT.**  `‖N_b v − ell³·v‖ ≤ ell³·(8·ell·α)·‖v‖`,
`α = frobSupBond U`.  Composed constant `8 = 2·4`: the `2` of the `RMap` Lipschitz brick carried by
`norm_RMap_holonomy_sub_self_le`, times the `4` of `transportPath_length_le`'s `4·ell`. -/
theorem norm_nBlock_sub_card_smul
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (b : CoarseBond L ell) (v : SuTwo) :
    ‖nBlock U ell b v - ((blockOf b.1.1 ell).card : ℝ) • v‖
      ≤ ((blockOf b.1.1 ell).card : ℝ) * (8 * (ell : ℝ) * frobSupBond U) * ‖v‖ := by
  have hα : (0 : ℝ) ≤ frobSupBond U := frobSupBond_nonneg U
  have hv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hrw : nBlock U ell b v - ((blockOf b.1.1 ell).card : ℝ) • v
      = ∑ x ∈ blockOf b.1.1 ell,
        (RMap (periodicPathHolonomy U b.1.1 (transportPath b.1.1 x b.2 (iTop ell x b.2))) v
          - v) := by
    rw [nBlock_apply, Finset.sum_sub_distrib, Finset.sum_const, cast_nsmul]
  rw [hrw]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ x ∈ blockOf b.1.1 ell,
      ‖RMap (periodicPathHolonomy U b.1.1 (transportPath b.1.1 x b.2 (iTop ell x b.2))) v - v‖
        ≤ 8 * (ell : ℝ) * frobSupBond U * ‖v‖ := by
    intro x hx
    have hxb : inBlock b.1.1 ell x := mem_blockOf.mp hx
    have hiT : iTop ell x b.2 < ell := iTop_lt hell x b.2
    have hlen : (transportPath b.1.1 x b.2 (iTop ell x b.2)).length ≤ 4 * ell :=
      transportPath_length_le hxb hiT b.2
    have hlenR : ((transportPath b.1.1 x b.2 (iTop ell x b.2)).length : ℝ) ≤ 4 * (ell : ℝ) := by
      exact_mod_cast hlen
    have hlnn : (0 : ℝ) ≤ ((transportPath b.1.1 x b.2 (iTop ell x b.2)).length : ℝ) :=
      Nat.cast_nonneg _
    refine le_trans (norm_RMap_holonomy_sub_self_le U _ _ v) ?_
    nlinarith [mul_nonneg hα hv]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have : (0 : ℝ) ≤ ((blockOf b.1.1 ell).card : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hα hv]

/-- **THE VOLUME-FREE SUFFICIENT CONDITION FOR THE CRITERION.**  `8·ell·frobSupBond U < 1` forces
every `N_b` injective, hence (finite dimension) surjective, hence `blockTopMap` surjective. -/
theorem topSpanning_of_frobSup_small
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hsmall : 8 * (ell : ℝ) * frobSupBond U < 1) : TopSpanning U ell := by
  intro b
  have hcard : (blockOf b.1.1 ell).card = ell ^ 3 := card_blockOf_of_coarse hdvd b.1.2
  have hcpos : (0 : ℝ) < ((blockOf b.1.1 ell).card : ℝ) := by
    rw [hcard]
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  have hinj : Function.Injective (nBlock U ell b) := by
    refine (injective_iff_map_eq_zero _).mpr (fun v hv0 => ?_)
    have hb := norm_nBlock_sub_card_smul U hell b v
    rw [hv0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos hcpos] at hb
    have hvn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
    have : ((blockOf b.1.1 ell).card : ℝ) * ‖v‖
        ≤ ((blockOf b.1.1 ell).card : ℝ) * ((8 * (ell : ℝ) * frobSupBond U) * ‖v‖) := by
      calc ((blockOf b.1.1 ell).card : ℝ) * ‖v‖ ≤ _ := hb
        _ = ((blockOf b.1.1 ell).card : ℝ) * ((8 * (ell : ℝ) * frobSupBond U) * ‖v‖) := by ring
    have hle : ‖v‖ ≤ (8 * (ell : ℝ) * frobSupBond U) * ‖v‖ :=
      le_of_mul_le_mul_left this hcpos
    have : ‖v‖ = 0 := by nlinarith
    exact norm_eq_zero.mp this
  have hsurjN : Function.Surjective (nBlock U ell b) := LinearMap.surjective_of_injective hinj
  intro v
  obtain ⟨u, hu⟩ := hsurjN v
  exact ⟨constLM u, hu⟩

/-- **THE HEADLINE OF §5, VOLUME-FREE.**  A neighbourhood of the flat orbit whose radius does NOT
shrink with the lattice: `frobSupBond U < 1/(8·ell)` ⟹ `Q_ell(U)` surjective.

Contrast with `hkinv_seam`'s `HKinvDrift.qCLM_surjective_of_frobSup_small`, whose hypothesis carries
`√(#coarse bonds)` AND an unbounded section norm.  Neither appears here. -/
theorem qCLM_surjective_of_frobSup_small_volume_free
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hsmall : 8 * (ell : ℝ) * frobSupBond U < 1) : Function.Surjective (qCLM U ell) :=
  qCLM_surjective_of_topSpanning U hell hdvd (topSpanning_of_frobSup_small U hell hdvd hsmall)

end QSurjCriterion
