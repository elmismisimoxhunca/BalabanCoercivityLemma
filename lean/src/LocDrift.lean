/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import LocGeom
import AdalyFormal.Balaban.RegularUQChain

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
# THE TWO DRIFT BOUNDS, LOCALIZED TO A CUBE.

`RegularUPerturbation.plaqEnergy_curlDrift_le` and `RegularUQChain.coarseDriftEnergy_le` are the two
inputs by which `CovLemma24.covariant_lemma24` converts the FLAT Lemma 2.4 into the COVARIANT one.
Both are stated globally: their index sums run over the whole torus, and their smallness parameter
`α` is a bound on `frobNorm(U b − 1)` over EVERY bond.

This module localizes both, by the method the dispatch asked to be tested first — **is restriction
free?** The answer proved here is: **yes, and by a MODIFICATION rather than a re-derivation.**

## The method: cut the data, then apply the GLOBAL theorem

Both estimates are sums of per-plaquette / per-coarse-bond terms, and each term reads `U` and `A`
only on an explicitly bounded stencil. So instead of re-proving either estimate with restricted
index sets — which would duplicate their Cauchy–Schwarz and incidence counting — we

1. replace `U` by `linkCut S U` (equal to `U` on `S`, `1` off it) and `A` by `bondCut S' A`
   (equal to `A` on `S'`, `0` off it);
2. prove the drift is UNCHANGED on the cube's index set (`curlDrift_cut`, `rZeroA_cut`) — this is
   the LOCALITY statement, and it is where the stencil geometry is discharged;
3. apply the global theorem to the cut data, whose global `α` is now the cube's LOCAL `α`
   (`frobSupBond_linkCut_le`) and whose global bond energy is now the cube's LOCAL bond energy
   (`bondEnergy_bondCut`).

Nothing is re-derived and no constant moves: the `32` and the `64/ell` are the cited ones.

## THE STENCIL, PROVED

`pathSite_mem_block_or_next` — for `x` in the block `B(y)` and `i < ell`, the site `x + i·e_μ` lies
in `B(y)` **or in `B(y + ell·e_μ)`, and nowhere else.** One block layer forward, the SAME `□̃` the
flat lemma needed (`LocGeom.tilde`). At `i = 1` this is the radius-one statement for the curl
stencil; at general `i < ell` it is the statement for the coarse-graining segment.

## WHAT IS AND IS NOT LOCALIZED — stated at the narrowest true reading

| bound | index sets | smallness parameter `α` |
|---|---|---|
| curl drift (`local_curlDrift_le`) | LOCAL (`plaqsOn Y`, `bondsOn (tilde Y)`) | **LOCAL**: `∀ b ∈ bondsOn Y` |
| coarse drift (`local_coarseDrift_le`) | LOCAL (`coarseOn Y`, `bondsOn (tilde Y)`) | **GLOBAL**: `frobSupBond U` |

The curl drift reads `U` only at the two bonds BASED AT the plaquette's own corner
(`RegularUPerturbation.curlDrift_apply`), so its `α` localizes with the same cut.
The coarse drift reads `U` along `Q1Real.transportPath = GammaPath ++ straightSegment`, i.e. through
a HOLONOMY, and this module does not localize that read set: `local_coarseDrift_le` keeps the global
`frobSupBond U`. The exact missing statement is named in `LocCov.lean` §4 and is a statement about
`Q1Real.periodicPathHolonomy`, not about the drift estimate.
-/

namespace AdalyFormal.Balaban.LocalizedEstimates

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CoarseCurl
open GeomScratch
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.RegularUQChain

variable {L : PeriodicLatticeExtent} {ell : ℕ}

/-! ## §1 — THE STENCIL: one block layer forward, and no further. -/

/-- `pathSite` and `coarseShift` are the SAME iterate; stated so the coordinate lemmas of
`CoarseCurl` (`coarseShift_val_eq`, `coarseShift_apply_ne`) apply verbatim to path sites. -/
theorem pathSite_eq_coarseShift (x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    pathSite x μ i = coarseShift x i μ := rfl

/-- A block centre's coordinate plus `ell` is either the extent itself or leaves room for a WHOLE
further block: there is no partial block, because `ell` divides the extent and the centre. -/
theorem block_step_room (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (μ : Fin 3)
    (hlt : (y μ).val + ell < L μ + 1) : (y μ).val + 2 * ell ≤ L μ + 1 := by
  obtain ⟨k, hk⟩ := hdvd μ
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hy) μ)
  have hlt' : ell * (m + 1) < ell * k := by
    rw [Nat.mul_succ, ← hm, ← hk]; exact hlt
  have hmk : m + 1 < k := lt_of_mul_lt_mul_left hlt' (Nat.zero_le ell)
  have h2 : ell * (m + 2) ≤ ell * k := Nat.mul_le_mul_left ell (by omega)
  have h3 : ell * m + 2 * ell ≤ ell * k := by
    have hr : ell * m + 2 * ell = ell * (m + 2) := by ring
    rw [hr]; exact h2
  omega

/-- **THE STENCIL, PROVED.** For `x` in the block `B(y)` and any offset `i < ell`, the site
`x + i·e_μ` lies in `B(y)` or in the ONE forward-neighbouring block `B(y + ell·e_μ)`. It cannot
reach any further block, and it cannot reach a BACKWARD one. This is the geometric content of the
enlarged cube `□̃`, and it is the same statement at `i = 1` (curl stencil, radius one) and at
general `i < ell` (coarse-graining segment). -/
theorem pathSite_mem_block_or_next (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y x : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (hx : x ∈ blockOf y ell)
    (μ : Fin 3) {i : ℕ} (hi : i < ell) :
    pathSite x μ i ∈ blockOf y ell ∨ pathSite x μ i ∈ blockOf (coarseShift y ell μ) ell := by
  have hxb := mem_blockOf.mp hx
  have hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1 := fun ν => coarseLattice_mem_fits hdvd hy ν
  have hmu : ((pathSite x μ i) μ).val = ((x μ).val + i) % (L μ + 1) := by
    rw [pathSite_eq_coarseShift]; exact coarseShift_val_eq x i μ
  have hne : ∀ ρ : Fin 3, ρ ≠ μ → (pathSite x μ i) ρ = x ρ := by
    intro ρ hρ; rw [pathSite_eq_coarseShift]; exact coarseShift_apply_ne x i μ ρ hρ
  have hxμ := hxb μ
  have hfitμ := hfit μ
  by_cases hcase : (x μ).val + i < (y μ).val + ell
  · left
    rw [mem_blockOf]
    intro ρ
    by_cases hρ : ρ = μ
    · subst hρ
      rw [hmu, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [hne ρ hρ]; exact hxb ρ
  · right
    rw [mem_blockOf]
    intro ρ
    by_cases hρ : ρ = μ
    · subst hρ
      have hcsv : ((coarseShift y ell ρ) ρ).val = ((y ρ).val + ell) % (L ρ + 1) :=
        coarseShift_val_eq y ell ρ
      rw [hmu, hcsv]
      by_cases hw : (x ρ).val + i < L ρ + 1
      · have h1 : (y ρ).val + ell < L ρ + 1 := by omega
        rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt h1]
        omega
      · push_neg at hw
        have h2 : (y ρ).val + ell = L ρ + 1 := by
          by_contra hcon
          have hlt : (y ρ).val + ell < L ρ + 1 := by omega
          have := block_step_room hdvd hy ρ hlt
          omega
        rw [h2, Nat.mod_self, Nat.mod_eq_sub_mod hw,
          Nat.mod_eq_of_lt (show (x ρ).val + i - (L ρ + 1) < L ρ + 1 by omega)]
        omega
    · rw [hne ρ hρ, coarseShift_apply_ne y ell μ ρ hρ]; exact hxb ρ

/-- **The stencil, in the cube vocabulary.** For a cube `Y`, a block site of `Y` shifted `i < ell`
steps forward carries every bond based on it into `bondsOn (tilde Y)`. -/
theorem pathSite_bond_mem_tilde (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {Y : Finset (CSite L ell)} {y : CSite L ell} (hyY : y ∈ Y)
    {x : PeriodicLatticeSite L} (hx : x ∈ blockOf y.1 ell) (μ : Fin 3) {i : ℕ} (hi : i < ell)
    (ρ : Fin 3) : (pathSite x μ i, ρ) ∈ bondsOn (tilde hdvd Y) := by
  rcases pathSite_mem_block_or_next hdvd y.2 hx μ hi with h | h
  · exact Finset.mem_biUnion.mpr ⟨y, subset_tilde hdvd Y hyY, by
      simp only [bondsBasedIn, Finset.mem_filter, Finset.mem_univ, true_and]; exact h⟩
  · exact Finset.mem_biUnion.mpr ⟨shiftC hdvd y μ, shiftC_mem_tilde hdvd hyY μ, by
      simp only [bondsBasedIn, Finset.mem_filter, Finset.mem_univ, true_and]; exact h⟩

/-- Every bond based in a block of `Y` is a bond of `Y`. -/
theorem bond_mem_bondsOn {Y : Finset (CSite L ell)} {y : CSite L ell} (hyY : y ∈ Y)
    {x : PeriodicLatticeSite L} (hx : x ∈ blockOf y.1 ell) (ρ : Fin 3) :
    (x, ρ) ∈ bondsOn Y :=
  Finset.mem_biUnion.mpr ⟨y, hyY, by
    simp only [bondsBasedIn, Finset.mem_filter, Finset.mem_univ, true_and]; exact hx⟩

/-! ## §2 — CUTTING THE DATA -/

/-- `A` restricted to `S`, extended by `0`. -/
noncomputable def bondCut (S : Finset (Bond L)) (A : Bond L → SuTwo) : Bond L → SuTwo :=
  fun b => if b ∈ S then A b else 0

/-- `U` restricted to `S`, extended by the identity link. -/
noncomputable def linkCut (S : Finset (Bond L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L :=
  fun b => if b ∈ S then U b else 1

theorem bondCut_mem {S : Finset (Bond L)} {A : Bond L → SuTwo} {b : Bond L} (h : b ∈ S) :
    bondCut S A b = A b := by simp [bondCut, h]

theorem linkCut_mem {S : Finset (Bond L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} {b : Bond L}
    (h : b ∈ S) : linkCut S U b = U b := by simp [linkCut, h]

/-- `∑_b ‖(bondCut S A) b‖² = ∑_{b ∈ S} ‖A b‖²` — the cut turns the GLOBAL bond energy into the
cube's LOCAL one. -/
theorem bondEnergy_bondCut (S : Finset (Bond L)) (A : Bond L → SuTwo) :
    bondEnergy (bondCut S A) = ∑ b ∈ S, ‖A b‖ ^ 2 := by
  unfold bondEnergy
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Bond L)) (fun b => b ∈ S)]
  have h1 : (Finset.univ : Finset (Bond L)).filter (fun b => b ∈ S) = S := by
    ext b; simp
  have h2 : ∑ b ∈ (Finset.univ : Finset (Bond L)).filter (fun b => ¬ b ∈ S),
      ‖bondCut S A b‖ ^ 2 = 0 := by
    refine Finset.sum_eq_zero (fun b hb => ?_)
    have hnb : b ∉ S := (Finset.mem_filter.mp hb).2
    simp [bondCut, hnb]
  rw [h1, h2, add_zero]
  exact Finset.sum_congr rfl (fun b hb => by rw [bondCut_mem hb])

/-- `frobSupBond (linkCut S U) ≤ α` whenever `α` bounds the deviations ON `S`. **This is the step
that converts a per-cube smallness hypothesis into the GLOBAL hypothesis the cited theorems ask
for**, at no cost: off `S` the cut link is `1` and its deviation is exactly `0`. -/
theorem frobSupBond_linkCut_le (S : Finset (Bond L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {α : ℝ}
    (hα0 : 0 ≤ α) (hα : ∀ b ∈ S, RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    ∀ b : Bond L,
      RMapLipschitz.frobNorm ((linkCut S U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α := by
  intro b
  by_cases hb : b ∈ S
  · rw [linkCut_mem hb]; exact hα b hb
  · have h1 : linkCut S U b = 1 := by simp [linkCut, hb]
    rw [h1]
    have : ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1 = 0 := by
      simp
    rw [this, RMapLipschitz.frobNorm_zero]
    exact hα0

/-! ## §3 — THE CURL DRIFT, LOCALIZED IN BOTH THE INDEX SET AND `α` -/

/-- **Locality of the curl drift.** At a plaquette `p`, `curlDrift` reads `U` at the two bonds
BASED AT `p.1` and `A` at the two bonds one forward step away. Cutting `U` and `A` to any sets
containing those four bonds changes nothing. Read straight off
`RegularUPerturbation.curlDrift_apply`. -/
theorem curlDrift_cut (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (SU SA : Finset (Bond L)) (p : PeriodicLatticePlaquette L)
    (hU1 : (p.1, p.2.1.1) ∈ SU) (hU2 : (p.1, p.2.1.2) ∈ SU)
    (hA1 : (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∈ SA)
    (hA2 : (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∈ SA) :
    curlDrift U A p = curlDrift (linkCut SU U) (bondCut SA A) p := by
  rw [curlDrift_apply, curlDrift_apply, linkCut_mem hU1, linkCut_mem hU2,
    bondCut_mem hA1, bondCut_mem hA2]

/-- **THE LOCALIZED CURL DRIFT.** For every cube `Y` and every `α` bounding the holonomy deviations
ON THE CUBE'S OWN BONDS,

`∑_{p ∈ plaqsOn Y} ‖(D_U − D_1)A(p)‖² ≤ 32·α²·∑_{b ∈ bondsOn (tilde Y)} ‖A b‖²`.

The constant `32` is `RegularUPerturbation.plaqEnergy_curlDrift_le`'s, cited, not re-derived. -/
theorem local_curlDrift_le (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (α : ℝ) (hα0 : 0 ≤ α) (Y : Finset (CSite L ell))
    (hα : ∀ b ∈ bondsOn Y, RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    ∑ p ∈ plaqsOn Y, ‖curlDrift U A p‖ ^ 2
      ≤ 32 * α ^ 2 * ∑ b ∈ bondsOn (tilde hdvd Y), ‖A b‖ ^ 2 := by
  have hell1 : 1 < ell := by omega
  set U' := linkCut (bondsOn Y) U with hU'
  set A' := bondCut (bondsOn (tilde hdvd Y)) A with hA'
  -- (a) the drift is unchanged on the cube
  have hcut : ∀ p ∈ plaqsOn Y, curlDrift U A p = curlDrift U' A' p := by
    intro p hp
    obtain ⟨y, hyY, hpy⟩ := Finset.mem_biUnion.mp hp
    have hp1 : p.1 ∈ blockOf y.1 ell := mem_plaqsBasedIn.mp hpy
    refine curlDrift_cut U A _ _ p (bond_mem_bondsOn hyY hp1 _) (bond_mem_bondsOn hyY hp1 _) ?_ ?_
    · have := pathSite_bond_mem_tilde hdvd hyY hp1 p.2.1.1 hell1 p.2.1.2
      rwa [show pathSite p.1 p.2.1.1 1 = periodicLatticeShift p.1 p.2.1.1 from rfl] at this
    · have := pathSite_bond_mem_tilde hdvd hyY hp1 p.2.1.2 hell1 p.2.1.1
      rwa [show pathSite p.1 p.2.1.2 1 = periodicLatticeShift p.1 p.2.1.2 from rfl] at this
  rw [Finset.sum_congr rfl (fun p hp => by rw [hcut p hp])]
  -- (b) enlarge the index set, then apply the GLOBAL theorem to the cut data
  have hsub : ∑ p ∈ plaqsOn Y, ‖curlDrift U' A' p‖ ^ 2 ≤ plaqEnergy (curlDrift U' A') :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  refine hsub.trans ?_
  have hglob := plaqEnergy_curlDrift_le U' A' α hα0
    (frobSupBond_linkCut_le (bondsOn Y) U hα0 hα)
  rw [hA'] at hglob
  rwa [bondEnergy_bondCut] at hglob

/-! ## §4 — THE COARSE DRIFT, LOCALIZED IN THE INDEX SETS -/

/-- **Locality of the coarse drift IN `A`.** `lineCoarseRestrictCov U ell A c` reads `A` only at the
bonds `(pathSite x c.2 i, c.2)` with `x ∈ B(c₋)` and `i < ell` (`Q1Real.rZeroA`), all of which lie in
`bondsOn (tilde Y)` when `c` is a coarse bond of `Y`. -/
theorem lineCoarseRestrictCov_cutA (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) {Y : Finset (CSite L ell)} {c : CoarseBond L ell} (hc : c ∈ coarseOn Y) :
    lineCoarseRestrictCov U ell A c
      = lineCoarseRestrictCov U ell (bondCut (bondsOn (tilde hdvd Y)) A) c := by
  have hcY : c.1 ∈ Y := mem_coarseOn.mp hc
  unfold lineCoarseRestrictCov
  congr 1
  refine Finset.sum_congr rfl (fun x hx => ?_)
  unfold AdalyFormal.Balaban.Q1Real.rZeroA
  refine Finset.sum_congr rfl (fun i hi => ?_)
  congr 1
  exact (bondCut_mem
    (pathSite_bond_mem_tilde hdvd hcY hx c.2 (Finset.mem_range.mp hi) c.2)).symm

/-- **THE LOCALIZED COARSE DRIFT.** For every cube `Y`,

`∑_{c ∈ coarseOn Y} ‖(Q(1) − Q(U))A(c)‖² ≤ (64/ell)·α₁²·∑_{b ∈ bondsOn (tilde Y)} ‖A b‖²`,

`α₁ = frobSupBond U`. The constant `64/ell` is `RegularUQChain.coarseDriftEnergy_le`'s, cited.

**`α₁` IS STILL THE GLOBAL SUP** — see the module header. The index sets are localized; the
smallness parameter is not. -/
theorem local_coarseDrift_le (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (Y : Finset (CSite L ell)) :
    ∑ c ∈ coarseOn Y,
        ‖lineCoarseRestrictCov (trivialU L) ell A c - lineCoarseRestrictCov U ell A c‖ ^ 2
      ≤ (64 / (ell : ℝ)) * frobSupBond U ^ 2 * ∑ b ∈ bondsOn (tilde hdvd Y), ‖A b‖ ^ 2 := by
  set A' := bondCut (bondsOn (tilde hdvd Y)) A with hA'
  have hcut : ∀ c ∈ coarseOn Y,
      ‖lineCoarseRestrictCov (trivialU L) ell A c - lineCoarseRestrictCov U ell A c‖ ^ 2
        = ‖lineCoarseRestrictCov (trivialU L) ell A' c - lineCoarseRestrictCov U ell A' c‖ ^ 2 := by
    intro c hc
    rw [← lineCoarseRestrictCov_cutA hdvd (trivialU L) A hc,
      ← lineCoarseRestrictCov_cutA hdvd U A hc]
  rw [Finset.sum_congr rfl hcut]
  have hsub : ∑ c ∈ coarseOn Y,
        ‖lineCoarseRestrictCov (trivialU L) ell A' c - lineCoarseRestrictCov U ell A' c‖ ^ 2
      ≤ ∑ c : CoarseBond L ell,
        ‖lineCoarseRestrictCov (trivialU L) ell A' c - lineCoarseRestrictCov U ell A' c‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  refine hsub.trans ?_
  have hglob := coarseDriftEnergy_le U hell hdvd A'
  rw [hA'] at hglob
  rwa [bondEnergy_bondCut] at hglob

/-! ## §5 — NON-VACUITY: the cut is not the zero map, and the stencil is not the whole torus. -/

/-- The cut operators are IDENTITIES on the full index set — so nothing in §2 can be vacuously
true by the cut collapsing its argument. -/
theorem cut_univ_id (A : Bond L → SuTwo)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    bondCut (Finset.univ : Finset (Bond L)) A = A
    ∧ linkCut (Finset.univ : Finset (Bond L)) U = U := by
  constructor
  · funext b; simp [bondCut]
  · funext b; simp [linkCut]

#print axioms pathSite_eq_coarseShift
#print axioms block_step_room
#print axioms pathSite_mem_block_or_next
#print axioms pathSite_bond_mem_tilde
#print axioms bond_mem_bondsOn
#print axioms bondCut
#print axioms bondCut_mem
#print axioms linkCut_mem
#print axioms linkCut
#print axioms bondEnergy_bondCut
#print axioms frobSupBond_linkCut_le
#print axioms curlDrift_cut
#print axioms local_curlDrift_le
#print axioms lineCoarseRestrictCov_cutA
#print axioms local_coarseDrift_le
#print axioms cut_univ_id

end AdalyFormal.Balaban.LocalizedEstimates
