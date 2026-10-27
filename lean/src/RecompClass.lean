/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import RecompTerminal
import GaugeInvPrinted

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.longLine false

/-!
# `RecompClass.lean` — THE SUMMATION'S HYPOTHESIS, DISCHARGED FROM CMP99b (3.35) AS PRINTED

`RecompTerminal` runs the terminal chain on a per-cube gauged smallness hypothesis: a
pairwise-disjoint family of blocks covering the coarse lattice, ONE UNRELATED GAUGE PER BLOCK, and
the locally gauged holonomy deviations below `1/(744ℓ³)` on each block's doubly-enlarged bond set.

**That hypothesis is what (3.35) delivers.**  Its quantifier prefix is the printed one — p.396's
`∀□ ∃u`, one gauge per cube, nothing relating two cubes — and this is exactly the prefix that
defeated the previous composition, which needed a GLOBAL gauge
(`GaugeInvPerCube.perCube_not_implies_global`: the per-cube class does NOT imply the global one, and
the counterexample is the wrapping holonomy of `U ≡ −1`).

## THE ONE THING THAT DOES NOT COME FOR FREE: THE CUBE FAMILIES MUST MATCH

(3.35) gives a gauge on each cube `□` of ITS class.  The summation asks for a gauge on each
`bondsOn (□̃̃ (Y i))` — the doubly-enlarged block.  §1 names the exact statement that bridges them,
`CubesRefine`, and §2 proves it is all that is needed.  §5 says what it costs in the source's own
units.

**[SOURCE], p.396, image-verified at 300 dpi (`renders/CMP99b_pdf8-08.png`), VERBATIM:**

> "At first let us introduce a class of cubes. For each cube □ of this class there exists a unique
> index j, 0 ≦ j ≦ k, such that □ ⊂ B^j(Λ_j) ∪ B^{j+1}(Λ_{j+1}), □ ∩ B^j(Λ_j) ≠ ∅, and □ is a union
> of several big blocks of the lattice T_{L^{-j}}, which implies that its size in the lattice T_η is
> O(1)ML^jη. Here O(1) will mean a number ≧ 10."

and, on the same page and load-bearing for the SCOPE of the discharge:

> "Let us notice that these regularity conditions do not impose any constraints on U outside the
> domain Ω₀."

So the source's cubes have fine side `O(1)ML^j ≥ 10ML^j` LATTICE UNITS, and §4 proves our
doubly-enlarged block sits inside a fine box of side `3ℓ` — but the source's class is only
guaranteed to cover `Ω₀`.  `CubesRefine` carries BOTH requirements, and neither is hidden in prose.

## ISLAND / MERGE STATUS OF THE WHOLE CHAIN THIS MODULE COMPOSES

**Measured 2026-08-12, by `ls formal/AdalyFormal/AdalyFormal/**/<M>.lean` and
`grep -rl "^import <M>$" formal/` for every module `M` of the chain.  Result: `NO` on both counts
for all of them.**  Concretely:

* `RecompFloor`, `RecompTerminal`, `RecompClass` (this lane) — **islands**.  Nothing is installed in
  `formal/`; nothing enters `Spine.lean`'s import cone; they contribute nothing to `FULL3D.main`'s
  axiom set.  The three modules are consumed by each other and by nothing else.
* The covariance input — `LocFeed`, `LocSum`, `LocPath`, `LocCov`, `LocDrift`, `LocGeom`
  (`compute/localized_estimates/`), `GaugeInvPrinted`, `GaugeInvPerCube`, `GaugeInvClass`,
  `GaugeInvLocalize` (`compute/gauge_inv_class/`), `DeltaAlpha0Conv` (`compute/delta_alpha0/`) —
  **all islands**.
* The terminal chain — `TerminalAssembly` (`compute/terminal_assembly/`), `TerminalBinder`
  (`compute/terminal_binder/`), `SchurComposed`, `SchurFloor` (`compute/schur_floor/`),
  `HrawCarriers`, `HrawFeed`, `MechG16` (`compute/hraw_carriers/`, `compute/mech_edges/`),
  `QSurjCriterion`, `QSurjGeneralCore` — **all islands**.

So **the recomposed terminal theorem is an island result**: it is kernel-checked, and it is not
part of `FULL3D.main`.  Merging it is a separate, unattempted step (LAW-4: this lane installs
nothing in `formal/`).

**THE FOUR ENDGAME LANES THAT OWE THE DISCLOSURE.**  Measured the same day by
`grep -c -i "island\|not merged\|unreachable\|not imported\|Spine" compute/<lane>/SCOPE.md`:
`compute/localized_estimates/` (SCOPE.md line 299), `compute/gauge_inv_class/` (line 360) and
`compute/schur_floor/` (line 215) DO disclose.  These four DO NOT, and this lane cannot edit them
(LAW-4, write-scope):

1. `compute/terminal_assembly/` — 0 hits in `SCOPE.md`, 0 in `stage/TerminalAssembly.lean`;
2. `compute/terminal_binder/` — 0 hits in `SCOPE.md`, 0 in `stage/TerminalBinder.lean`;
3. `compute/hraw_carriers/` — 0 hits in `SCOPE.md`, 0 in `stage/HrawCarriers.lean`;
4. `compute/delta_alpha0/` — 0 hits in `SCOPE.md`, 0 in `stage/DeltaAlpha0Conv.lean`.

The sentence each owes is the one above: *nothing installed in `formal/`, nothing in `Spine.lean`'s
import cone, no contribution to `FULL3D.main`'s axiom set.*

**Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.**
-/

namespace AdalyFormal.Balaban.RecomposeSum

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn GaugeRegular)
open AdalyFormal.Balaban.GaugeInvPerCube (PerCubeRegular)
open AdalyFormal.Balaban.DeltaAlpha0 (PrintedCubeClassI)
open AdalyFormal.Balaban.GaugeInvPrinted (perCubeRegular_of_printedCubeClassI)
open GeomScratch
open AdalyFormal.Balaban.LocalizedEstimates (tilde bondsOn CSite actO mem_tilde_iff
  singleton_family_ok)
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (IsSourceOperator cdcFormTrue)
open AdalyFormal.Balaban.TerminalAssembly (sharpFloorConst)
open AdalyFormal.TerminalBinder (PrintedG1FormAt HrawAt OnMinimizerRange)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE GEOMETRIC INPUT, NAMED -/

/-- **[GEOM] — THE CUBE-FAMILY REFINEMENT.**

`CubesRefine hdvd 𝒞 Y 𝒞src` says: every block of the summation's family, doubly enlarged and read as
a set of fine bonds, is contained in ONE cube of the source's class.

This is the whole geometric content of matching (3.35) to the summation, and it is stated as a
hypothesis rather than proved because `𝒞src` is the SOURCE's family: an abstract parameter carried
by `PrintedCubeClassI`, whose membership is decided by p.396's conditions on the domains
`B^j(Λ_j)`, which this formalisation does not carry. §4 and §5 say exactly what it demands. -/
def CubesRefine {ι : Type*} {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell)) (𝒞src : Set (Set (Bond L))) : Prop :=
  ∀ i ∈ 𝒞, ∃ C ∈ 𝒞src, (↑(bondsOn (tilde hdvd (tilde hdvd (Y i)))) : Set (Bond L)) ⊆ C

/-! ## §2 — THE DISCHARGE: PER-CUBE GAUGES, EXTRACTED -/

/-- **THE SUMMATION'S HYPOTHESIS, FROM THE PER-CUBE ORBIT CLASS AND [GEOM].**

The gauges are extracted cube by cube; **no relation between two of them is introduced, and none is
available**.  Outside `𝒞` the choice is the identity gauge and is never used. -/
theorem exists_gauges_of_refine {ι : Type*} [DecidableEq ι] {ell : ℕ}
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (α : ℝ)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell)) (𝒞src : Set (Set (Bond L)))
    (hreg : PerCubeRegular α U 𝒞src) (href : CubesRefine hdvd 𝒞 Y 𝒞src) :
    ∃ γ : ι → GaugeFn L, ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (tilde hdvd (tilde hdvd (Y i))),
      frobNorm (((periodicGaugeTransform (γ i) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α := by
  classical
  have key : ∀ i : ι, ∃ g : GaugeFn L, i ∈ 𝒞 →
      ∀ b ∈ bondsOn (tilde hdvd (tilde hdvd (Y i))),
        frobNorm (((periodicGaugeTransform g U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α := by
    intro i
    by_cases hi : i ∈ 𝒞
    · obtain ⟨C, hC, hsub⟩ := href i hi
      obtain ⟨g, hg⟩ := hreg C hC
      exact ⟨g, fun _ b hb => hg b (hsub (Finset.mem_coe.mpr hb))⟩
    · exact ⟨fun _ => 1, fun h => absurd h hi⟩
  choose γ hγ using key
  exact ⟨γ, fun i hi => hγ i hi⟩

/-! ## §3 — THE PRINTED PARAMETER AT THE RECOMPOSED RADIUS

`GaugeInvPrinted.perCubeRegular_at_threshold_of_printed` lands the printed class at the OLD radius
`1/(186ℓ³)`.  `RecompFloor.old_radius_fails_after_swap` proves that radius does not survive the
swap, so the conversion is redone at `1/(744ℓ³)`.  The `√2` is `ThresholdVsPrinted`'s exact
`‖X‖_F = √2·|X|` and is not touched. -/

/-- `√2·s ≤ 1/(744ℓ³)` from `s ≤ 1/(744√2·ℓ³)`.  Exact-constant form; the proof is
`DeltaAlpha0Conv.covariance_class_of_alpha0_exact`'s with `186` replaced by `744`. -/
theorem sqrt2_mul_le_sumRadius {ell : ℕ} (hell : 0 < ell) (s : ℝ) (hs : 0 ≤ s)
    (h : s ≤ 1 / (744 * Real.sqrt 2 * (ell : ℝ) ^ 3)) :
    Real.sqrt 2 * s ≤ sumRadius ell := by
  have hL : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hL3 : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hden : (0 : ℝ) < 744 * Real.sqrt 2 * (ell : ℝ) ^ 3 := by positivity
  have hden' : (0 : ℝ) < 744 * (ell : ℝ) ^ 3 := by positivity
  rw [le_div_iff₀ hden] at h
  unfold sumRadius
  rw [le_div_iff₀ hden']
  nlinarith [h, h2, hL3, hsq, hs]

/-- **THE RATIONAL THRESHOLD**, `1/(1120ℓ³)`, so no `√2` appears in the hypothesis a consumer
checks.  `1120 = 4·280` with `280` `DeltaAlpha0Conv.covThreshold`'s, and it is sufficient because
`744·√2 = 1052.17… ≤ 744·1.5 = 1116 ≤ 1120`; `1120` is **not claimed least**. -/
theorem sqrt2_mul_le_sumRadius_rational {ell : ℕ} (hell : 0 < ell) (s : ℝ) (hs : 0 ≤ s)
    (h : s < 1 / (1120 * (ell : ℝ) ^ 3)) :
    Real.sqrt 2 * s ≤ sumRadius ell := by
  have hL : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hL3 : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs32 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [hsq, h2]
  have hden : (0 : ℝ) < 1120 * (ell : ℝ) ^ 3 := by positivity
  have hden' : (0 : ℝ) < 744 * (ell : ℝ) ^ 3 := by positivity
  rw [lt_div_iff₀ hden] at h
  unfold sumRadius
  rw [le_div_iff₀ hden']
  nlinarith [h, hs, h2, hs32, hL3]

/-- **THE PRINTED PER-CUBE CLASS AT THE RECOMPOSED RADIUS.**  `O(1)Mα₀ < 1/(1120ℓ³)` gives
`PerCubeRegular (1/(744ℓ³))`, which is exactly `RecompFloor.sumRadius ℓ`. -/
theorem perCubeRegular_at_sumRadius_of_printed {ell : ℕ} (hell : 0 < ell)
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hα : 0 ≤ α₀) (hthr : c * M * α₀ < 1 / (1120 * (ell : ℝ) ^ 3))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (𝒞src : Set (Set (Bond L))) (h : PrintedCubeClassI c M α₀ η Lj U 𝒞src) :
    PerCubeRegular (sumRadius ell) U 𝒞src := by
  have hs : (0 : ℝ) ≤ c * M * α₀ := by positivity
  refine fun C hC => ?_
  obtain ⟨g, hg⟩ := perCubeRegular_of_printedCubeClassI c M α₀ η Lj hη hηne hLj hc hM hα U 𝒞src h C hC
  exact ⟨g, fun b hb => le_trans (hg b hb)
    (sqrt2_mul_le_sumRadius hell (c * M * α₀) hs (le_of_lt (by
      have hL : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
      have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hs32 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [hsq, Real.sqrt_nonneg 2]
      have hL3 : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
      have hd1 : (0 : ℝ) < 1120 * (ell : ℝ) ^ 3 := by positivity
      have hd2 : (0 : ℝ) < 744 * Real.sqrt 2 * (ell : ℝ) ^ 3 := by positivity
      rw [lt_div_iff₀ hd1] at hthr
      rw [lt_div_iff₀ hd2]
      nlinarith [hthr, hs32, hL3, h2, hs])))⟩

/-! ## §4 — WHAT [GEOM] DEMANDS, IN OUR OWN OBJECTS

The doubly-enlarged block is not a mystery: `LocGeom.tilde` adds ONE block layer in each of the
three POSITIVE directions, so twice-enlarging a single block reaches only sites displaced by at most
two positive block steps per direction.  §4a proves that; §4b reads off the count. -/

/-- **THE DOUBLY-ENLARGED SINGLE BLOCK IS A SET OF AT MOST `16` DISPLACEMENTS OF ITS CENTRE.**

Every coarse site of `□̃̃({z})` is `z` displaced by at most one positive block step twice over.  The
`16` is `Fintype.card (Option (Fin 3) × Option (Fin 3))`; the true count is `10`
(`LocSum.tilde2_mult_le_sixteen`'s own docstring says `16` is not least).  In fine-lattice units the
displacement is at most `2ℓ` per direction, so the bond set lies in a box of side `3ℓ` — which is
the number §5 compares against the source's cube side. -/
theorem tilde2_singleton_subset_displacements {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (z : CSite L ell) :
    tilde hdvd (tilde hdvd ({z} : Finset (CSite L ell)))
      ⊆ (Finset.univ : Finset (Option (Fin 3) × Option (Fin 3))).image
          (fun k => actO hdvd k.1 (actO hdvd k.2 z)) := by
  intro y hy
  obtain ⟨o1, v, hv, hvy⟩ := (mem_tilde_iff hdvd (tilde hdvd ({z} : Finset (CSite L ell))) y).mp hy
  obtain ⟨o2, u, hu, huv⟩ := (mem_tilde_iff hdvd ({z} : Finset (CSite L ell)) v).mp hv
  have hz : u = z := Finset.mem_singleton.mp hu
  subst hz
  refine Finset.mem_image.mpr ⟨(o1, o2), Finset.mem_univ _, ?_⟩
  simp only []
  rw [huv]
  exact hvy

/-- **AND THE COUNT IS AT MOST `16` BLOCKS**, so [GEOM] is a demand about a bounded neighbourhood of
one block and not about a large region. -/
theorem tilde2_singleton_card_le {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (z : CSite L ell) :
    (tilde hdvd (tilde hdvd ({z} : Finset (CSite L ell)))).card ≤ 16 := by
  classical
  have hsub := tilde2_singleton_subset_displacements hdvd z
  have h1 := Finset.card_le_card hsub
  have h2 : ((Finset.univ : Finset (Option (Fin 3) × Option (Fin 3))).image
      (fun k => actO hdvd k.1 (actO hdvd k.2 z))).card
      ≤ (Finset.univ : Finset (Option (Fin 3) × Option (Fin 3))).card :=
    Finset.card_image_le
  have h3 : (Finset.univ : Finset (Option (Fin 3) × Option (Fin 3))).card = 16 := by
    simp
  omega

/-! ### §4c — THE SIDE, IN COORDINATES: `3ℓ`

`AdmissibleSubspace.inBlock` is a NON-WRAPPING coordinate box (`y_μ ≤ x_μ < y_μ + ℓ` on the raw
`Fin` values), and `CoarseCurl.coarseShift_val_eq` advances one coordinate by `ℓ` modulo the
extent.  Away from the wrap — the hypothesis `hfit` below, `z_μ + 3ℓ ≤ L_μ + 1` — the two compose
to the exact statement [GEOM] needs on OUR side:

>  every fine bond of `□̃̃({z})` has its base site in the coordinate box of side `3ℓ` at `z`.

The link itself reaches one further site in its own direction, so the source's cube must contain a
box of side `3ℓ + 1` — which is the number to compare with p.396's `O(1)ML^jη`, i.e. with
`O(1)ML^j ≥ 10ML^j` fine-lattice units. -/

/-- One displacement step moves one coordinate by at most `ℓ` and never decreases it, away from the
wrap. -/
theorem actO_val_bounds {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (o : Option (Fin 3))
    (y : CSite L ell) (μ : Fin 3) (hfit : (y.1 μ).val + ell < L μ + 1) :
    (y.1 μ).val ≤ ((actO hdvd o y).1 μ).val
      ∧ ((actO hdvd o y).1 μ).val ≤ (y.1 μ).val + ell := by
  cases o with
  | none => exact ⟨le_rfl, Nat.le_add_right ((y.1 μ).val) ell⟩
  | some ν =>
    by_cases hν : ν = μ
    · subst hν
      have h := AdalyFormal.Balaban.CoarseCurl.coarseShift_val_eq y.1 ell ν
      have hval : ((actO hdvd (some ν) y).1 ν).val = ((y.1 ν).val + ell) % (L ν + 1) := h
      rw [hval, Nat.mod_eq_of_lt hfit]
      exact ⟨by omega, le_rfl⟩
    · have h := AdalyFormal.Balaban.CoarseCurl.coarseShift_apply_ne y.1 ell ν μ (fun hc => hν hc.symm)
      have hval : ((actO hdvd (some ν) y).1 μ) = y.1 μ := h
      rw [hval]
      exact ⟨le_rfl, by omega⟩

/-- **THE DOUBLY-ENLARGED BLOCK SITS IN THE COORDINATE BOX OF SIDE `3ℓ`.**  `hfit` is the
away-from-the-wrap hypothesis; `hell` is needed because at `ell = 0` the enlargement is trivial and
the box degenerate. -/
theorem tilde2_singleton_in_box {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (z : CSite L ell) (hfit : ∀ μ : Fin 3, (z.1 μ).val + 3 * ell ≤ L μ + 1)
    (b : Bond L) (hb : b ∈ bondsOn (tilde hdvd (tilde hdvd ({z} : Finset (CSite L ell))))) :
    ∀ μ : Fin 3, (z.1 μ).val ≤ (b.1 μ).val ∧ (b.1 μ).val < (z.1 μ).val + 3 * ell := by
  intro μ
  obtain ⟨y, hy, hby⟩ := Finset.mem_biUnion.mp hb
  have hblk : b.1 ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf y.1 ell := by
    simpa only [GeomScratch.bondsBasedIn, Finset.mem_filter,
      Finset.mem_univ, true_and] using hby
  have hin := AdalyFormal.Balaban.AdmissibleSubspace.mem_blockOf.mp hblk μ
  -- `y` is at most two positive block steps from `z` in each coordinate
  obtain ⟨o1, v, hv, hvy⟩ := (mem_tilde_iff hdvd (tilde hdvd ({z} : Finset (CSite L ell))) y).mp hy
  obtain ⟨o2, u, hu, huv⟩ := (mem_tilde_iff hdvd ({z} : Finset (CSite L ell)) v).mp hv
  have hz : u = z := Finset.mem_singleton.mp hu
  rw [hz] at huv
  have hfitz : (z.1 μ).val + ell < L μ + 1 := by have := hfit μ; omega
  have hstep1 := actO_val_bounds hdvd o2 z μ hfitz
  rw [huv] at hstep1
  have hfitv : (v.1 μ).val + ell < L μ + 1 := by
    have h1 := hstep1.2
    have := hfit μ
    omega
  have hstep2 := actO_val_bounds hdvd o1 v μ hfitv
  rw [hvy] at hstep2
  constructor
  · omega
  · omega

/-! ### §4d — [GEOM] REDUCED TO A SIZE CRITERION

With §4c, the abstract containment `CubesRefine` follows from a statement about SIZE: it is enough
that the source's class contains, around every interior coarse site, a cube containing the
coordinate box of side `3ℓ`.  The wrap-around sites are carried SEPARATELY and are not absorbed
into the size statement — `AdmissibleSubspace.inBlock` is a non-wrapping box while
`CoarseCurl.coarseShift` wraps, so a block within `3ℓ` of the far edge genuinely reaches sites at
the near edge and no side comparison covers it. -/

/-- **THE SIZE CRITERION.**  `hbox` is the interior demand — in the source's units, a cube of fine
side `O(1)ML^j` must contain a box of side `3ℓ`, i.e. `3ℓ + 1 ≤ O(1)ML^j` counting the link's far
endpoint — and `hwrap` is the residual demand at the sites within `3ℓ` of the periodic seam. -/
theorem cubesRefine_of_boxes {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (𝒞src : Set (Set (Bond L)))
    (hbox : ∀ z : CSite L ell, (∀ μ : Fin 3, (z.1 μ).val + 3 * ell ≤ L μ + 1) →
      ∃ C ∈ 𝒞src, {b : Bond L | ∀ μ : Fin 3,
        (z.1 μ).val ≤ (b.1 μ).val ∧ (b.1 μ).val < (z.1 μ).val + 3 * ell} ⊆ C)
    (hwrap : ∀ z : CSite L ell, ¬ (∀ μ : Fin 3, (z.1 μ).val + 3 * ell ≤ L μ + 1) →
      ∃ C ∈ 𝒞src, (↑(bondsOn (tilde hdvd (tilde hdvd ({z} : Finset (CSite L ell)))))
        : Set (Bond L)) ⊆ C) :
    CubesRefine hdvd (Finset.univ : Finset (CSite L ell))
      (fun z => ({z} : Finset (CSite L ell))) 𝒞src := by
  intro z _
  by_cases hfit : ∀ μ : Fin 3, (z.1 μ).val + 3 * ell ≤ L μ + 1
  · obtain ⟨C, hC, hsub⟩ := hbox z hfit
    refine ⟨C, hC, fun b hb => hsub ?_⟩
    exact tilde2_singleton_in_box hell hdvd z hfit b (Finset.mem_coe.mp hb)
  · exact hwrap z hfit

/-! ## §5 — THE HEADLINE, FROM THE PRINTED CLASS

Everything composed: the printed (3.35) data at `O(1)Mα₀ < 1/(1120ℓ³)`, the geometric input, the
single-block family (whose two family hypotheses are `LocFeed.singleton_family_ok`, so they are NOT
free binders), and `RecompTerminal`'s chain. -/

/-- **THE RECOMPOSED TERMINAL THEOREM, WITH THE COVARIANCE SIDE COMING FROM (3.35) AS PRINTED.**

    ℓ ≥ 2, tiled torus, CMP99b (3.35) on a cube family 𝒞src with O(1)Mα₀ < 1/(1120·ℓ³),
    [GEOM] (every doubly-enlarged block's bond set inside one cube of 𝒞src),
    CMP99b (3.128) and the drift-priced chain bound on the minimiser range, κ ≤ √(gammaSum ℓ),
    source below the threshold
    ⟹  ⟨B̃, C*Δ_k(U) C B̃⟩ > 0  for every B̃ ≠ 0 in ℓ²(Λ̃).

**There is no `frobSupBond` hypothesis, no `GaugeRegular` hypothesis, and no global gauge anywhere
in this statement.**  The gauge quantifier is the printed `∀□ ∃u`. -/
theorem terminal_sum_posDef_from_printed {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hα0 : 0 ≤ α₀) (hthr : c * M * α₀ < 1 / (1120 * (ell : ℝ) ^ 3))
    (𝒞src : Set (Set (Bond L))) (hprinted : PrintedCubeClassI c M α₀ η Lj U 𝒞src)
    (hgeom : CubesRefine hdvd (Finset.univ : Finset (CSite L ell))
      (fun z => ({z} : Finset (CSite L ell))) 𝒞src)
    {Hs : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (bc : BaseConstant)
    (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ) (hκγ : κ ≤ Real.sqrt (gammaSum ell))
    (hformR : OnMinimizerRange D (PrintedG1FormAt D (usedAt bc 0) d pen))
    (hrawR : OnMinimizerRange D (HrawAt D U d σ₀ κ))
    (Qext : BondFnL2 L → BondFnL2 L) (J : Hs) (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hS : IsSourceOperator D Qext J S) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (R : ℝ) (hJbound : ‖J‖ ≤ R)
    (hRthr : 2 * ‖solutionOperator D‖ * c₂ * R < sharpFloorConst (gammaSum ell) κ σ₀)
    (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < cdcFormTrue D bc Qext J U ell (dinvC U ell) w := by
  classical
  have hell : 0 < ell := by omega
  have hreg : PerCubeRegular (sumRadius ell) U 𝒞src :=
    perCubeRegular_at_sumRadius_of_printed hell c M α₀ η Lj hη hηne hLj hc hM hα0 hthr U 𝒞src
      hprinted
  obtain ⟨γ, hγ⟩ := exists_gauges_of_refine hdvd U (sumRadius ell)
    (Finset.univ : Finset (CSite L ell)) (fun z => ({z} : Finset (CSite L ell))) 𝒞src hreg hgeom
  have hrad : (0 : ℝ) ≤ sumRadius ell := by
    unfold sumRadius
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  exact terminal_sum_posDef_on_range hell2 hstrict hdvd U (sumRadius ell) hrad le_rfl
    (Finset.univ : Finset (CSite L ell)) (fun z => ({z} : Finset (CSite L ell))) γ
    singleton_family_ok.1 singleton_family_ok.2 hγ D bc d pen σ₀ κ hσ₀ hκ hκγ hformR hrawR
    Qext J S hS c₂ hc₂ hD2 R hJbound hRthr w hw

/-! ## §6 — CONTROLS -/

/-- **MUST-NOT-FIRE — [GEOM] IS NOT VACUOUS AND NOT AUTOMATIC.**

1. It IS satisfiable: the family `{univ}` — a single cube containing every bond — satisfies it for
   every block family.  (That family is exactly the one
   `GaugeInvPrinted.gaugeRegular_of_perCubeRegular_univ` shows would collapse the per-cube class to
   the global one; it is admissible here only as a NON-VACUITY witness, and p.396 does not grant it,
   since a cube of side `O(1)ML^jη` is not the torus.)
2. It is NOT automatic: at `𝒞src = ∅` it fails for every nonempty index family, so the hypothesis
   has content. -/
theorem cubesRefine_inhabited_and_not_automatic {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {ι : Type*} (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell)) (i₀ : ι) (hi₀ : i₀ ∈ 𝒞) :
    CubesRefine hdvd 𝒞 Y {(Set.univ : Set (Bond L))}
    ∧ ¬ CubesRefine hdvd 𝒞 Y (∅ : Set (Set (Bond L))) := by
  constructor
  · exact fun i _ => ⟨Set.univ, Set.mem_singleton _, fun b _ => Set.mem_univ b⟩
  · intro hbad
    obtain ⟨C, hC, _⟩ := hbad i₀ hi₀
    exact hC

/-- **THE RECOMPOSED CLASS IS NOT EXOTIC, AND IS NOT UNIFORMLY WEAKER — BOTH, AS ONE ROW.**

If the ORIGINAL links already satisfy `frobSupBond U ≤ α`, the IDENTITY gauge on every cube
discharges the summation's hypothesis at `α`.  So the recomposed class contains the ungauged one at
the same radius.

**What this row must not be read as saying.**  The recomposed radius is `1/(744ℓ³)`, four times
tighter than the old chain's `1/(186ℓ³)`; `RecompFloor.old_radius_fails_after_swap` proves the
factor cannot be given back.  The trade is therefore explicit: **the printed quantifier prefix
`∀□ ∃u` in exchange for a factor `4` in the radius**, and the two hypotheses are incomparable in
general — neither implies the other.

`frobSupBond` appears in exactly TWO statements of this lane, both here: this row, and §8's
`witU_alpha_le_sumRadius`, which uses this row to put the tree's CURVED witness into the recomposed
per-cube class.  It appears in no hypothesis of the composed chain. -/
theorem hclass_of_frobSupBond {ι : Type*} {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (α : ℝ)
    (h : AdalyFormal.Balaban.RegularUPerturbation.frobSupBond U ≤ α)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell)) :
    ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (tilde hdvd (tilde hdvd (Y i))),
      frobNorm (((periodicGaugeTransform (fun _ => 1) U) b :
        Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α := by
  intro i _ b _
  have hg : ((periodicGaugeTransform (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) U) b :
      Matrix.specialUnitaryGroup (Fin 2) ℂ) = U b := by
    show (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) * U b * (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)⁻¹ = U b
    simp
  rw [hg]
  exact le_trans (AdalyFormal.Balaban.RegularUPerturbation.frobNorm_le_frobSupBond U b) h

/-- **THE PRINTED CLASS DOES NOT GIVE THE GLOBAL CLASS — RE-EXPOSED, SO THE RECOMPOSITION'S POINT
CANNOT BE MISSED.**  `GaugeInvPrinted.printed_class_does_not_reach_the_consumer` (CITED, not
rebuilt): at `U ≡ −1` on an odd torus the per-cube class holds at radius `0` while the global class
fails at every radius the campaign uses.  The recomposed theorem above consumes only the per-cube
side, which is why it is stateable at all. -/
theorem printed_class_gap_recalled {ell : ℕ} (hell : 0 < ell)
    (hbig : ∀ μ : Fin 3, 2 ≤ L μ) (hodd : ∀ μ : Fin 3, (L μ + 1) % 2 = 1)
    (hsize : ((L 0 + 1 : ℕ) : ℝ) * (1 / (186 * (ell : ℝ) ^ 3)) < 2 * Real.sqrt 2) :
    PerCubeRegular (0 : ℝ) (AdalyFormal.Balaban.AlphaAnalyticity.centerU L)
        {{b : Bond L | ¬ AdalyFormal.Balaban.GaugeInvPerCube.Wraps b}}
    ∧ ¬ GaugeRegular (1 / (186 * (ell : ℝ) ^ 3))
        (AdalyFormal.Balaban.AlphaAnalyticity.centerU L) :=
  AdalyFormal.Balaban.GaugeInvPrinted.printed_class_does_not_reach_the_consumer hell hbig hodd hsize

/-! ## §7 — NON-VACUITY OF THE RECOMPOSED HYPOTHESIS SET, END TO END

`TerminalAssembly.end_to_end_flat` discharges every binder of the OLD chain at `U = 1`.  This is
the same row on the SUMMATION chain: every binder of `RecompTerminal.terminal_sum_posDef_on_range`
discharged simultaneously, with the per-cube class supplied by the identity gauge on the
single-block family.

**⚠ WHAT THIS ROW IS AND IS NOT.**  Exactly the two degeneracies `end_to_end_flat` discloses, and
they are theorems elsewhere, not opinions: at the witness datum `Q = I`
(`TerminalAssembly.assemblyDatum_Q_bijective`), so the composed floor is the brick; and at `U = 1`
the source vanishes (`TerminalAssembly.trivialU_in_class`), so the source term contributes nothing.
It establishes SATISFIABILITY of the recomposed hypothesis set and nothing more. -/

/-- The identity gauge puts the flat background in the per-cube class at radius `0`, hence at every
nonnegative radius. -/
theorem flat_percube_class {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (α : ℝ) (hα : 0 ≤ α)
    (Y : CSite L ell → Finset (CSite L ell)) :
    ∀ i ∈ (Finset.univ : Finset (CSite L ell)),
      ∀ b ∈ bondsOn (tilde hdvd (tilde hdvd (Y i))),
        frobNorm (((periodicGaugeTransform (fun _ => 1)
          (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L)) b :
            Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α := by
  intro i _ b _
  have h1 : ((periodicGaugeTransform (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L)) b :
        Matrix.specialUnitaryGroup (Fin 2) ℂ) = 1 := by
    show (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) * _ * _ = 1
    show (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) * (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      * (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)⁻¹ = 1
    simp
  rw [h1]
  have h2 : ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := rfl
  rw [h2, sub_self, AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
  exact hα

/-- **EVERY BINDER OF THE RECOMPOSED CHAIN, DISCHARGED SIMULTANEOUSLY.**  At `ℓ ≥ 2` on a tiled
torus, at the flat background, at `TerminalAssembly`'s witness datum, on the single-block family
with the identity gauge, with the printed `D̃⁽²⁾` shape: the recomposed `C*Δ_kC` is positive
definite on `ℓ²(Λ̃)`.  Read the warning above before quoting it. -/
theorem sum_end_to_end_flat {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (bc : BaseConstant) (ha : 0 < usedAt bc 0)
    (v : BondFnL2 L) (hv : v ≠ 0) (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < cdcFormTrue
        (AdalyFormal.Balaban.TerminalAssembly.assemblyDatum
          (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L) ha)
        bc (AdalyFormal.Balaban.DeltaKWiring.bondQext v)
        (AdalyFormal.Balaban.SourceWiredJ.JsuTwo
          (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L))
        (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L) ell
        (dinvC (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L) ell) w := by
  classical
  have hell : 0 < ell := by omega
  set U0 := AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L with hU0
  obtain ⟨_, hlink⟩ := AdalyFormal.Balaban.TerminalAssembly.trivialU_in_class (L := L) (ell := ell)
    hell
  have hJ0 : ‖AdalyFormal.Balaban.SourceWiredJ.JsuTwo U0‖ ≤ 0 := by
    have := AdalyFormal.Balaban.SourceWiredJ.norm_JsuTwo_le U0 hlink
    simpa using this
  have hγ : 0 < gammaSum ell := gammaSum_pos hell
  have hrad : (0 : ℝ) ≤ sumRadius ell := by
    unfold sumRadius
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  have hsharp : sharpFloorConst (gammaSum ell) 0 1 = gammaSum ell := by
    unfold sharpFloorConst
    rw [sub_zero]
    have : Real.sqrt (gammaSum ell) ^ 2 = gammaSum ell := Real.sq_sqrt (le_of_lt hγ)
    simpa using this
  refine terminal_sum_posDef_on_range hell2 hstrict hdvd U0 (sumRadius ell) hrad le_rfl
    (Finset.univ : Finset (CSite L ell)) (fun z => ({z} : Finset (CSite L ell)))
    (fun _ => (fun _ => 1)) singleton_family_ok.1 singleton_family_ok.2
    (flat_percube_class hdvd (sumRadius ell) hrad (fun z => ({z} : Finset (CSite L ell))))
    (AdalyFormal.Balaban.TerminalAssembly.assemblyDatum U0 ha) bc
    (AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2 U0)
    (0 : BondFnL2 L →L[ℝ] BondFnL2 L) 1 0 one_pos le_rfl (by rw [hsharp] at *; positivity)
    (fun B => AdalyFormal.Balaban.TerminalAssembly.assemblyDatum_isPrintedG1Form U0 ha _)
    (fun B => AdalyFormal.Balaban.TerminalAssembly.assemblyDatum_hraw U0 ha _)
    (AdalyFormal.Balaban.DeltaKWiring.bondQext v)
    (AdalyFormal.Balaban.SourceWiredJ.JsuTwo U0) _
    (AdalyFormal.Balaban.TerminalAssembly.assemblyDatum_isSourceOperator U0 ha v _)
    ‖v‖ (norm_nonneg v) (AdalyFormal.Balaban.TerminalAssembly.assemblyDatum_hD2 v)
    0 hJ0 ?_ w hw
  rw [hsharp]
  simpa using hγ

/-! ## §8 — THE FLOOR HALF AT A GENUINELY CURVED BACKGROUND, ON THE RECOMPOSED CHAIN

`sum_end_to_end_flat` is at `U = 1`.  This section runs the whole FLOOR half — everything except
the source term — at the tree's curved witness `CovLemma24Witness.witU witT`, on the SUMMATION
chain, with a strictly positive left-hand side at a NAMED nonzero element of the printed carrier.

**The recomposed radius is four times tighter than the old class, and the tree's curved witness
still clears it**: `α₁(witU witT) = √(8t²/(1+t²))` at `t = 10⁻⁵` is `2.83…·10⁻⁵`, and
`sumRadius 3 = 1/20088 = 4.97…·10⁻⁵`.  So the swap does NOT cost the curved witness — a fact worth
having, since `SCOPE.md` §2's factor `4` might otherwise be assumed to have eaten it. -/

/-- **THE CURVED WITNESS CLEARS THE RECOMPOSED RADIUS.**  Not the old one being reused: this is
`sumRadius 3 = 1/(744·27)`, four times tighter than `1/(186·27)`. -/
theorem witU_alpha_le_sumRadius :
    AdalyFormal.Balaban.RegularUPerturbation.frobSupBond
      (AdalyFormal.Balaban.CovLemma24Witness.witU AdalyFormal.Balaban.CovLemma24Witness.witT)
      ≤ sumRadius 3 := by
  rw [AdalyFormal.Balaban.CovLemma24Witness.frobSupBond_witU]
  unfold sumRadius
  have hle : 8 * AdalyFormal.Balaban.CovLemma24Witness.witT ^ 2
      / (1 + AdalyFormal.Balaban.CovLemma24Witness.witT ^ 2)
      ≤ (1 / (744 * ((3 : ℕ) : ℝ) ^ 3)) ^ 2 := by
    rw [AdalyFormal.Balaban.CovLemma24Witness.witT]
    norm_num
  refine (Real.sqrt_le_sqrt hle).trans (le_of_eq ?_)
  exact Real.sqrt_sq (by norm_num)

/-- **THE COMPOSED SCHUR FLOOR AT A CURVED BACKGROUND, ON THE SUMMATION CHAIN, NON-VACUOUSLY.**

At `ℓ = 3` on the `9³` torus, at `CovLemma24Witness.witU witT` (plaquette holonomy `≠ 1` and
`α₁ > 0`, `TerminalCompose.witness_background_curved_and_in_class`, CITED), at the `TerminalAssembly`
§9 witness datum, on `construct_cdc`'s own named nonzero element of `ℓ²(Λ̃)`:

    0  <  gammaSum 3 · ‖C₀B̃‖²  ≤  ⟨C₀B̃, (Q G₁ Q*)⁻¹ C₀B̃⟩ − a‖C₀B̃‖² .

Both conjuncts matter: the second is the floor, the first rules out the degenerate reading
`0 ≤ something`.  The covariance hypothesis is the PER-CUBE one, discharged here by
`hclass_of_frobSupBond` from the witness's own ungauged bound — which is legitimate precisely
because that theorem proves the ungauged class implies the per-cube one at the same radius. -/
theorem sum_schur_floor_curved_nonvacuous {a : ℝ} (ha : 0 < a) :
    0 < sharpFloorConst (gammaSum 3) 0 1
        * ‖cZero (AdalyFormal.Balaban.CovLemma24Witness.witU
            AdalyFormal.Balaban.CovLemma24Witness.witT) 3
            (dinvC (AdalyFormal.Balaban.CovLemma24Witness.witU
              AdalyFormal.Balaban.CovLemma24Witness.witT) 3)
            (AdalyFormal.Balaban.ConstructCDC.tildeSpike
              (L := AdalyFormal.Balaban.Lemma24GeneralEll.witL3)
              (by norm_num : (2 : ℕ) ≤ 3)
              (AdalyFormal.Balaban.TerminalCompose.witL3_hyps).2)‖ ^ 2
    ∧ sharpFloorConst (gammaSum 3) 0 1
        * ‖cZero (AdalyFormal.Balaban.CovLemma24Witness.witU
            AdalyFormal.Balaban.CovLemma24Witness.witT) 3
            (dinvC (AdalyFormal.Balaban.CovLemma24Witness.witU
              AdalyFormal.Balaban.CovLemma24Witness.witT) 3)
            (AdalyFormal.Balaban.ConstructCDC.tildeSpike
              (by norm_num : (2 : ℕ) ≤ 3)
              (AdalyFormal.Balaban.TerminalCompose.witL3_hyps).2)‖ ^ 2
      ≤ AdalyFormal.Balaban.Gamma1Positive.deltaKQuadForm
          (AdalyFormal.Balaban.TerminalAssembly.assemblyDatum
            (AdalyFormal.Balaban.CovLemma24Witness.witU
              AdalyFormal.Balaban.CovLemma24Witness.witT) ha) a
          (cZero (AdalyFormal.Balaban.CovLemma24Witness.witU
              AdalyFormal.Balaban.CovLemma24Witness.witT) 3
            (dinvC (AdalyFormal.Balaban.CovLemma24Witness.witU
              AdalyFormal.Balaban.CovLemma24Witness.witT) 3)
            (AdalyFormal.Balaban.ConstructCDC.tildeSpike
              (by norm_num : (2 : ℕ) ≤ 3)
              (AdalyFormal.Balaban.TerminalCompose.witL3_hyps).2)) := by
  classical
  set U0 := AdalyFormal.Balaban.CovLemma24Witness.witU
    AdalyFormal.Balaban.CovLemma24Witness.witT with hU0
  have hγ : 0 < gammaSum 3 := gammaSum_pos (by norm_num)
  have hsharp : sharpFloorConst (gammaSum 3) 0 1 = gammaSum 3 := by
    unfold sharpFloorConst
    rw [sub_zero]
    have : Real.sqrt (gammaSum 3) ^ 2 = gammaSum 3 := Real.sq_sqrt (le_of_lt hγ)
    simpa using this
  have hne : cZero U0 3 (dinvC U0 3)
      (AdalyFormal.Balaban.ConstructCDC.tildeSpike
        (L := AdalyFormal.Balaban.Lemma24GeneralEll.witL3)
        (by norm_num : (2 : ℕ) ≤ 3)
        (AdalyFormal.Balaban.TerminalCompose.witL3_hyps).2) ≠ 0 :=
    AdalyFormal.Balaban.TerminalAssembly.cZero_ne_zero_of_ne_zero _ _ _
      AdalyFormal.Balaban.TerminalCompose.tildeSpike_witL3_ne_zero
  have hn : 0 < ‖cZero U0 3 (dinvC U0 3)
      (AdalyFormal.Balaban.ConstructCDC.tildeSpike
        (L := AdalyFormal.Balaban.Lemma24GeneralEll.witL3)
        (by norm_num : (2 : ℕ) ≤ 3)
        (AdalyFormal.Balaban.TerminalCompose.witL3_hyps).2)‖ := norm_pos_iff.mpr hne
  have hrad : (0 : ℝ) ≤ sumRadius 3 := by
    unfold sumRadius; norm_num
  refine ⟨by rw [hsharp]; positivity, ?_⟩
  exact schur_floor_sum_on_range (by norm_num : (2 : ℕ) ≤ 3)
    (AdalyFormal.Balaban.TerminalCompose.witL3_hyps).1
    (AdalyFormal.Balaban.TerminalCompose.witL3_hyps).2 U0 (sumRadius 3) hrad le_rfl
    (Finset.univ : Finset (CSite AdalyFormal.Balaban.Lemma24GeneralEll.witL3 3))
    (fun z => ({z} : Finset (CSite AdalyFormal.Balaban.Lemma24GeneralEll.witL3 3)))
    (fun _ => (fun _ => 1)) singleton_family_ok.1 singleton_family_ok.2
    (hclass_of_frobSupBond (AdalyFormal.Balaban.TerminalCompose.witL3_hyps).2 U0 (sumRadius 3)
      witU_alpha_le_sumRadius _ _)
    (AdalyFormal.Balaban.TerminalAssembly.assemblyDatum U0 ha) a
    (AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2 U0)
    (0 : BondFnL2 AdalyFormal.Balaban.Lemma24GeneralEll.witL3 →L[ℝ]
      BondFnL2 AdalyFormal.Balaban.Lemma24GeneralEll.witL3)
    1 0 one_pos le_rfl (by positivity)
    (fun B => AdalyFormal.Balaban.TerminalAssembly.assemblyDatum_isPrintedG1Form U0 ha _)
    (fun B => AdalyFormal.Balaban.TerminalAssembly.assemblyDatum_hraw U0 ha _) _

#print axioms witU_alpha_le_sumRadius
#print axioms sum_schur_floor_curved_nonvacuous
#print axioms CubesRefine
#print axioms cubesRefine_of_boxes
#print axioms flat_percube_class
#print axioms sum_end_to_end_flat
#print axioms exists_gauges_of_refine
#print axioms sqrt2_mul_le_sumRadius
#print axioms sqrt2_mul_le_sumRadius_rational
#print axioms perCubeRegular_at_sumRadius_of_printed
#print axioms tilde2_singleton_subset_displacements
#print axioms tilde2_singleton_card_le
#print axioms actO_val_bounds
#print axioms tilde2_singleton_in_box
#print axioms terminal_sum_posDef_from_printed
#print axioms cubesRefine_inhabited_and_not_automatic
#print axioms hclass_of_frobSupBond
#print axioms printed_class_gap_recalled

end AdalyFormal.Balaban.RecomposeSum
