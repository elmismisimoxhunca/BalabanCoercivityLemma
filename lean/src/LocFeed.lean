/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import LocPath
import LocSum

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
# FEEDING THE SUMMATION: a GLOBAL covariant floor from PER-CUBE gauges alone.

This is the composition. `LocPath.local_covariant_lemma24_local` supplies the per-cube covariant
floor at a SINGLE LOCAL smallness parameter; `LocSum.floor_sums_gauged_multiplicity` sums per-cube
floors with one unrelated gauge per cube; this module converts the coarse-site multiplicities of
`LocSum` §2 into the bond / plaquette multiplicities the summation asks for, and composes.

## THE RESULT

`global_floor_from_percube_gauges` — for a family of PAIRWISE DISJOINT cubes COVERING the coarse
lattice, each carrying its OWN gauge `γ i` with nothing relating them, and with the holonomy
deviations of the LOCALLY GAUGED background bounded by `α` on each cube's doubly-enlarged bond set:

>  `((1/360)·ell⁻⁵ − 1536·α²)·∑_b ‖A b‖² ≤ ell·∑_c ‖(Q(U)A)(c)‖² + 4·∑_p ‖(D_U A)(p)‖²`

at the ORIGINAL `U` — **no global gauge, no gauge-orbit hypothesis, no global smallness.**

`1536 = 96 · 16` is the per-cube coefficient times the doubly-enlarged multiplicity, and `4` is the
enlarged-cube multiplicity. Both factors are `LocSum`'s counted ones; `96` is
`CovLemma24.covariant_lemma24`'s own. **`16` is not claimed least** (see
`LocSum.tilde2_mult_le_sixteen`).

## WHAT REMAINS OUTSIDE THIS MODULE

The hypothesis `hclass` is the per-cube smallness class. Landing CMP99b (3.35) INTO `hclass` at the
campaign's threshold is `GaugeInvPrinted`'s `perCubeRegular_at_threshold_of_printed`, which is
stated at `GaugeRegular`'s Frobenius norm per cube; matching its cube family to this module's
`bondsOn (tilde (tilde (Y i)))` is a geometry question about the source's cube side `12ML^jη`
versus the block side `ell`, and is NOT performed here.
-/

namespace AdalyFormal.Balaban.LocalizedEstimates

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CoarseCurl
open GeomScratch
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.CovariantLemma24
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA)
open AdalyFormal.Balaban.GaugeInvClass (suAdmissible_gauge)

variable {L : PeriodicLatticeExtent} {ell : ℕ}

/-! ## §1 — OWNERSHIP: every fine site has exactly one block -/

/-- Membership in `bondsOn` is decided by the bond's OWNING block. -/
theorem mem_bondsOn_iff_owner (Z : Finset (CSite L ell)) (b : Bond L) {z0 : CSite L ell}
    (hz0 : b.1 ∈ blockOf z0.1 ell) : b ∈ bondsOn Z ↔ z0 ∈ Z := by
  constructor
  · intro h
    obtain ⟨z, hzZ, hbz⟩ := Finset.mem_biUnion.mp h
    have hb : b.1 ∈ blockOf z.1 ell := by
      simpa only [bondsBasedIn, Finset.mem_filter, Finset.mem_univ, true_and] using hbz
    have : z = z0 := Subtype.ext (coarseLattice_unique ell z.2 z0.2 hb hz0)
    exact this ▸ hzZ
  · intro h
    exact Finset.mem_biUnion.mpr ⟨z0, h, by
      simp only [bondsBasedIn, Finset.mem_filter, Finset.mem_univ, true_and]; exact hz0⟩

/-- Membership in `plaqsOn` is decided by the plaquette's OWNING block. -/
theorem mem_plaqsOn_iff_owner (Z : Finset (CSite L ell)) (p : PeriodicLatticePlaquette L)
    {z0 : CSite L ell} (hz0 : p.1 ∈ blockOf z0.1 ell) : p ∈ plaqsOn Z ↔ z0 ∈ Z := by
  constructor
  · intro h
    obtain ⟨z, hzZ, hpz⟩ := Finset.mem_biUnion.mp h
    have hp : p.1 ∈ blockOf z.1 ell := mem_plaqsBasedIn.mp hpz
    have : z = z0 := Subtype.ext (coarseLattice_unique ell z.2 z0.2 hp hz0)
    exact this ▸ hzZ
  · intro h
    exact Finset.mem_biUnion.mpr ⟨z0, h, by rw [mem_plaqsBasedIn]; exact hz0⟩

/-- The owning block of a fine site, as a coarse site. -/
theorem exists_owner (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (x : PeriodicLatticeSite L) : ∃ z : CSite L ell, x ∈ blockOf z.1 ell := by
  obtain ⟨y, hy, hxy⟩ := coarseLattice_exists ell hell hdvd x
  exact ⟨⟨y, hy⟩, hxy⟩

/-! ## §2 — THE THREE MULTIPLICITIES, IN THE FORM THE SUMMATION CONSUMES -/

theorem bondsOn_cover {ι : Type*} [DecidableEq ι] (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell))
    (hcov : ∀ z : CSite L ell, ∃ i ∈ 𝒞, z ∈ Y i) (b : Bond L) :
    1 ≤ (𝒞.filter (fun i => b ∈ bondsOn (Y i))).card := by
  obtain ⟨z0, hz0⟩ := exists_owner hell hdvd b.1
  obtain ⟨i, hi𝒞, hiY⟩ := hcov z0
  refine Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi𝒞, ?_⟩⟩
  exact (mem_bondsOn_iff_owner (Y i) b hz0).mpr hiY

theorem coarseOn_mult_le_one {ι : Type*} [DecidableEq ι] (𝒞 : Finset ι)
    (Y : ι → Finset (CSite L ell))
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j)) (c : CoarseBond L ell) :
    (𝒞.filter (fun i => c ∈ coarseOn (Y i))).card ≤ 1 := by
  refine Finset.card_le_one.mpr (fun i hi j hj => ?_)
  by_contra hne
  have hi' := Finset.mem_filter.mp hi
  have hj' := Finset.mem_filter.mp hj
  exact (Finset.disjoint_left.mp (hdisj i hi'.1 j hj'.1 hne)
    (mem_coarseOn.mp hi'.2)) (mem_coarseOn.mp hj'.2)

theorem plaqsOn_tilde_mult_le_four {ι : Type*} [DecidableEq ι] (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell))
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (p : PeriodicLatticePlaquette L) :
    (𝒞.filter (fun i => p ∈ plaqsOn (tilde hdvd (Y i)))).card ≤ 4 := by
  obtain ⟨z0, hz0⟩ := exists_owner hell hdvd p.1
  have hcongr : 𝒞.filter (fun i => p ∈ plaqsOn (tilde hdvd (Y i)))
      = 𝒞.filter (fun i => z0 ∈ tilde hdvd (Y i)) := by
    refine Finset.filter_congr (fun i _ => ?_)
    exact ⟨fun h => (mem_plaqsOn_iff_owner _ p hz0).mp h,
      fun h => (mem_plaqsOn_iff_owner _ p hz0).mpr h⟩
  rw [hcongr]
  exact tilde_mult_le_four hdvd 𝒞 Y hdisj z0

theorem bondsOn_tilde2_mult_le_sixteen {ι : Type*} [DecidableEq ι] (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell))
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j)) (b : Bond L) :
    (𝒞.filter (fun i => b ∈ bondsOn (tilde hdvd (tilde hdvd (Y i))))).card ≤ 16 := by
  obtain ⟨z0, hz0⟩ := exists_owner hell hdvd b.1
  have hcongr : 𝒞.filter (fun i => b ∈ bondsOn (tilde hdvd (tilde hdvd (Y i))))
      = 𝒞.filter (fun i => z0 ∈ tilde hdvd (tilde hdvd (Y i))) := by
    refine Finset.filter_congr (fun i _ => ?_)
    exact ⟨fun h => (mem_bondsOn_iff_owner _ b hz0).mp h,
      fun h => (mem_bondsOn_iff_owner _ b hz0).mpr h⟩
  rw [hcongr]
  exact tilde2_mult_le_sixteen hdvd 𝒞 Y hdisj z0

/-! ## §3 — THE COMPOSITION -/

/-- **A GLOBAL COVARIANT FLOOR FROM PER-CUBE GAUGES ALONE.**

Pairwise-disjoint cubes covering the coarse lattice, one unrelated gauge per cube, and a smallness
bound holding only cube-by-cube for the LOCALLY GAUGED background. The conclusion is at the
ORIGINAL `U`: no global gauge is formed and no gauge-orbit hypothesis is used. -/
theorem global_floor_from_percube_gauges {ι : Type*} [DecidableEq ι]
    (hell2 : 2 ≤ ell) (hstrict : ∀ ν : Fin 3, ell < L ν + 1)
    (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) (α : ℝ) (hα0 : 0 ≤ α)
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell)) (γ : ι → GaugeFn L)
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (hcov : ∀ z : CSite L ell, ∃ i ∈ 𝒞, z ∈ Y i)
    (hclass : ∀ i ∈ 𝒞, ∀ b ∈ bondsOn (tilde hdvd (tilde hdvd (Y i))),
      RMapLipschitz.frobNorm
        (((periodicGaugeTransform (γ i) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    ((1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * α ^ 2 * (16 : ℕ))
        * bondEnergy A
      ≤ ((1 : ℕ) : ℝ) * ((ell : ℝ) * coarseQEnergyCov U ell A)
        + ((4 : ℕ) : ℝ) * curlEnergyCov U A := by
  have hell : 0 < ell := by omega
  have hcoef : (0 : ℝ) ≤ (1 / 360) * (1 / (ell : ℝ) ^ 5) := by positivity
  have hd : (0 : ℝ) ≤ 96 * α ^ 2 := by positivity
  refine floor_sums_gauged_multiplicity ((1 / 360) * (1 / (ell : ℝ) ^ 5)) (96 * α ^ 2)
    hcoef hd 1 4 16 U A 𝒞 (fun i => bondsOn (Y i))
    (fun i => bondsOn (tilde hdvd (tilde hdvd (Y i)))) (fun i => coarseOn (Y i))
    (fun i => plaqsOn (tilde hdvd (Y i))) γ
    (bondsOn_cover hell hdvd 𝒞 Y hcov)
    (coarseOn_mult_le_one 𝒞 Y hdisj)
    (plaqsOn_tilde_mult_le_four hell hdvd 𝒞 Y hdisj)
    (bondsOn_tilde2_mult_le_sixteen hell hdvd 𝒞 Y hdisj)
    (fun i hi => ?_)
  have hloc := local_covariant_lemma24_local hell2 hstrict hdvd
    (periodicGaugeTransform (γ i) U) (gaugeActA (γ i) A)
    (suAdmissible_gauge (γ i) ell A hadm) α hα0 (Y i) (hclass i hi)
  linarith [hloc]

/-! ## §4 — CONTROLS -/

/-- **The composed coefficient is positive on a nonempty range of `α`**, so the conclusion is not
vacuous: at `α² < ell⁻⁵/552960` the floor coefficient is strictly positive. `552960 = 360·1536`. -/
theorem composed_threshold (t : ℝ) (ht : 0 < t) (α : ℝ)
    (hα : α ^ 2 < 1 / (552960 * t ^ 5)) :
    0 < (1 / 360) * (1 / t ^ 5) - 96 * α ^ 2 * (16 : ℕ) := by
  have h5 : (0 : ℝ) < t ^ 5 := by positivity
  have hd : (0 : ℝ) < 552960 * t ^ 5 := by positivity
  have h1 : 96 * α ^ 2 * (16 : ℕ) < 1536 * (1 / (552960 * t ^ 5)) := by
    push_cast
    nlinarith [hα, h5]
  have h2 : (1536 : ℝ) * (1 / (552960 * t ^ 5)) = (1 / 360) * (1 / t ^ 5) := by
    field_simp; ring
  linarith [h1, h2.le, h2.ge]

/-- **The single-block cube family satisfies the two geometric hypotheses**, so
`global_floor_from_percube_gauges` is not conditioned on an unsatisfiable covering: taking one cube
per coarse site gives a pairwise-disjoint family that covers. -/
theorem singleton_family_ok :
    (∀ i ∈ (Finset.univ : Finset (CSite L ell)), ∀ j ∈ (Finset.univ : Finset (CSite L ell)),
      i ≠ j → Disjoint ({i} : Finset (CSite L ell)) ({j} : Finset (CSite L ell)))
    ∧ (∀ z : CSite L ell, ∃ i ∈ (Finset.univ : Finset (CSite L ell)),
        z ∈ ({i} : Finset (CSite L ell))) := by
  constructor
  · intro i _ j _ hij
    simpa using hij
  · intro z
    exact ⟨z, Finset.mem_univ _, Finset.mem_singleton_self z⟩

#print axioms mem_bondsOn_iff_owner
#print axioms mem_plaqsOn_iff_owner
#print axioms exists_owner
#print axioms bondsOn_cover
#print axioms coarseOn_mult_le_one
#print axioms plaqsOn_tilde_mult_le_four
#print axioms bondsOn_tilde2_mult_le_sixteen
#print axioms global_floor_from_percube_gauges
#print axioms composed_threshold
#print axioms singleton_family_ok

end AdalyFormal.Balaban.LocalizedEstimates
