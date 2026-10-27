/-
Owned file (compute/m1_si1_l18/l1/). Compiles the REMAINING two clauses of
`expand/CHANNEL_EXPANSION.md` §7 lemma L1 ("Forward path carrier dictionary"), plus the
GammaPath/coarseGammaPath direction-list equality that clause also names. The far-endpoint clause
(1) `cPlusS 1 m c = ModifiedAverageDeriv.cPlus m c` is ALREADY PAID as
`cPlusS_one_eq_modifiedAverageDeriv_cPlus` in `compute/m1_si1_astra_match/lemma/L1CPlusBridge.lean`
(exit 0, axioms `[propext, Quot.sound]`, see `compute/m1_si1_astra_match/lemma/RESULT.md`); it is
imported here READ-ONLY (byte-identical `.lean`/`.olean` copies in `l1/deps/`, hash-verified
against the originals before this file was written) and is NOT re-derived, re-proved, or claimed
as this file's own work. L1 as a whole is NOT complete from clause (1) alone.

## What this file adds

* `GammaPath_eq_coarseGammaPath_one_map` — `Q1Real.GammaPath y x` (the fine `List (Fin 3 × Bool)`
  staircase) equals `(TowerLawCov.coarseGammaPath 1 y x).map (fun μ => (μ, true))` (the unit-scale
  `List (Fin 3)` staircase, forward-tagged). Unconditional in `y x`.
* `cPlus_oneStep124_eq_cPlusS` — clause (2), the `CoarseBond L (1*m)` subtype/cast for `cPlus`:
  `OneStep124.cPlus` applied to the coarse-cast of a fine edge `c` equals `UbarTowerCov.cPlusS 1 m
  c`. This genuinely needs `c.1 ∈ CoarseLattice L m` as a LOCAL hypothesis — `OneStep124.cPlus`'s
  domain `CoarseBond L (1*m)` forces its base point onto the `m`-coarse sublattice, unlike clause
  (1)'s unconstrained `PeriodicLatticeEdge L`. This is a minimal typing hypothesis for the cast
  itself, not the full geometric-fitting package (`m ∣ L_μ+1`, partner bijection) that belongs to
  L6/the coefficient match.
* `unitSitesOf_one_image_eq_blockOf` — clause (3): `unitSitesOf 1 (1*m) y`, imaged under
  `Subtype.val`, equals `blockOf y m`. Unconditional: `unitSitesOf`'s FIRST index is `1`, so its
  subtype constraint is `CoarseLattice L 1`, which is trivial for every site
  (`StridedAveraging.mem_coarseLattice_one`) — no fitting hypothesis is needed for this clause.

None of these three theorems assumes, restates, or depends on L2-L8. No boxed SI1 claim, no
coefficient-match claim, no channel extraction is made here.
-/
import AdalyFormal.Balaban.Q1Real
import AdalyFormal.Balaban.TowerLawCovariant
import AdalyFormal.Balaban.AdmissibleSubspace
import AdalyFormal.Balaban.ThirdLevelArrows
import AdalyFormal.Balaban.StridedAveraging
import AdalyFormal.Balaban.LatticeOperators
import AdalyFormal.Balaban.UbarTowerCovariance
import AdalyFormal.Balaban.QOne
import T1MainSegment
import L1CPlusBridge

set_option autoImplicit false

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLatticeEdge)

variable {L : PeriodicLatticeExtent}

/-- **L1, remaining clause: `GammaPath` / `coarseGammaPath` direction-list equality.** At stride
`1`, the fine forward staircase `GammaPath` is exactly the unit staircase `coarseGammaPath 1`,
each of its `Fin 3` direction entries forward-tagged. Unconditional in `y x`; no coarse-block
fitting or cardinality hypothesis is used. -/
theorem GammaPath_eq_coarseGammaPath_one_map (y x : PeriodicLatticeSite L) :
    AdalyFormal.Balaban.Q1Real.GammaPath y x
      = (AdalyFormal.Balaban.TowerLawCov.coarseGammaPath 1 y x).map (fun μ => (μ, true)) := by
  unfold AdalyFormal.Balaban.Q1Real.GammaPath AdalyFormal.Balaban.Q1Real.straightSegment
    AdalyFormal.Balaban.Q1Real.coordSteps
    AdalyFormal.Balaban.TowerLawCov.coarseGammaPath
    AdalyFormal.Balaban.TowerLawCov.coarseStraightSegment
    AdalyFormal.Balaban.TowerLawCov.coarseCoordSteps
  simp [List.map_append, List.map_replicate, Nat.div_one, List.append_assoc]

/-- **L1, remaining clause: `CoarseBond L (1*m)` subtype/cast for `cPlus`.** Under the local
hypothesis that the fine edge's base point `c.1` is already `m`-coarse (the minimal typing
hypothesis `OneStep124.cPlus`'s domain forces, not the full L6 fitting package), the q-side
`OneStep124.cPlus` of the coarse-cast bond agrees with `cPlusS 1 m c`. Chained with the already
paid `cPlusS_one_eq_modifiedAverageDeriv_cPlus`, this also identifies it with
`ModifiedAverageDeriv.cPlus m c` — but that chaining is recorded as a corollary below, not
claimed as this theorem's own new content. -/
theorem cPlus_oneStep124_eq_cPlusS (m : ℕ) (c : PeriodicLatticeEdge L)
    (hc : c.1 ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L m) :
    OneStep124.cPlus
        (⟨⟨c.1, by rw [one_mul]; exact hc⟩, c.2⟩ :
          AdalyFormal.Balaban.LatticeOperators.CoarseBond L (1 * m))
      = AdalyFormal.Balaban.UbarTowerCov.cPlusS 1 m c := by
  have hval : OneStep124.cPlus
        (⟨⟨c.1, by rw [one_mul]; exact hc⟩, c.2⟩ :
          AdalyFormal.Balaban.LatticeOperators.CoarseBond L (1 * m))
      = AdalyFormal.Balaban.QOne.pathSite c.1 c.2 (m * 1) := by
    unfold OneStep124.cPlus
    rfl
  rw [hval, mul_one, AdalyFormal.Balaban.UbarTowerCov.cPlusS_eq, one_mul]
  rfl

/-- Corollary: the coarse-cast `OneStep124.cPlus` also agrees with `ModifiedAverageDeriv.cPlus`,
BY CHAINING the two clauses above with the separately paid far-endpoint lemma
`cPlusS_one_eq_modifiedAverageDeriv_cPlus`. Not itself a new equality; recorded so L1's three
clauses are visibly composed, not merely three isolated facts. -/
theorem cPlus_oneStep124_eq_modifiedAverageDeriv_cPlus (m : ℕ) (c : PeriodicLatticeEdge L)
    (hc : c.1 ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L m) :
    OneStep124.cPlus
        (⟨⟨c.1, by rw [one_mul]; exact hc⟩, c.2⟩ :
          AdalyFormal.Balaban.LatticeOperators.CoarseBond L (1 * m))
      = AdalySI1.ModifiedAverageDeriv.cPlus m c := by
  rw [cPlus_oneStep124_eq_cPlusS m c hc, cPlusS_one_eq_modifiedAverageDeriv_cPlus]

/-- **L1, remaining clause: `unitSitesOf`/`blockOf` image identification.** At `ell₀ = 1`,
`unitSitesOf 1 (1*m) y`'s underlying `Finset (PeriodicLatticeSite L)` (its `Subtype.val` image) is
exactly `blockOf y m`. Unconditional: the `1`-coarse-lattice constraint on `unitSitesOf`'s carrier
is trivial for every site, so no fitting hypothesis on `y` or `m` is needed. -/
theorem unitSitesOf_one_image_eq_blockOf (y : PeriodicLatticeSite L) (m : ℕ) :
    (AdalyFormal.Balaban.ThirdLevelArrows.unitSitesOf 1 (1 * m) y).image Subtype.val
      = AdalyFormal.Balaban.AdmissibleSubspace.blockOf y m := by
  unfold AdalyFormal.Balaban.ThirdLevelArrows.unitSitesOf
  ext z
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, one_mul]
  constructor
  · rintro ⟨⟨u, hu⟩, hmem, rfl⟩
    exact hmem
  · intro hz
    exact ⟨⟨z, AdalyFormal.Balaban.StridedAveraging.mem_coarseLattice_one z⟩, hz, rfl⟩

#print axioms GammaPath_eq_coarseGammaPath_one_map
#print axioms cPlus_oneStep124_eq_cPlusS
#print axioms cPlus_oneStep124_eq_modifiedAverageDeriv_cPlus
#print axioms unitSitesOf_one_image_eq_blockOf
