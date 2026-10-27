/-
# `Erratum126Slim.lean` -- verbatim excerpt of `compute/erratum_126/stage/Erratum126.lean`

Carries `Erratum126Slim.norm_delta124_le_Lfree`, the slim copy of
`Erratum126.norm_delta124_le_Lfree` (CLAIMS row `erratum126`), together with the lemmas of the
original sections 2-3 that its proof uses.  Source line ranges of `Erratum126.lean`: 76-91, 132-348.
Textual changes: `namespace Erratum126` is `namespace Erratum126Slim`, `open OneStep124` is
`open OneStep124Slim`.  Imports `OneStep124Slim` (an excerpt of `OneStep124`) and nothing with `sorry`.
-/
import OneStep124Slim

set_option maxHeartbeats 2000000
set_option autoImplicit false

namespace Erratum126Slim

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_one)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice blockOf mem_blockOf)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.ReparamCDisjoint (pathSite_eq pathSite_apply_ne)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarseStraightSegment coarseCoordSteps
  coarsePathHolonomy coarsePathHolonomy_trivialU)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open OneStep124Slim

variable {L : PeriodicLatticeExtent}


/-! ##############################################################################################
## §2 — THE CONTOUR GEOMETRY THE PREFACTOR COUNT NEEDS  (all DERIVED)

`compute/onestep_124`'s own contour-length bound is `pathBudget L ell = L 0/ell + L 1/ell + L 2/ell`
— the length of a staircase that may cross the WHOLE lattice.  Every staircase occurring in (124)
runs from a block base to a point of ITS OWN BLOCK, so the correct bound is the BLOCK diameter
`3m`, not the lattice diameter.  Recovering that is what turns the estimate `L`-uniform, and it is
the whole mathematical content of the erratum.
############################################################################################## -/

/-- **The staircase length, in closed form.**  The middle legs' bases are `Function.update`s of `y`
at coordinates the leg does not read, so the length depends only on the raw endpoint coordinate
differences.  DERIVED. -/
theorem coarseGammaPath_length_eq (ell : ℕ) (y x : PeriodicLatticeSite L) :
    (coarseGammaPath ell y x).length
      = (x 2 - y 2).val / ell + ((x 1 - y 1).val / ell + (x 0 - y 0).val / ell) := by
  have h12 : ((1 : Fin 3)) ≠ ((2 : Fin 3)) := by decide
  have h01 : ((0 : Fin 3)) ≠ ((1 : Fin 3)) := by decide
  have h02 : ((0 : Fin 3)) ≠ ((2 : Fin 3)) := by decide
  rw [coarseGammaPath, List.length_append, List.length_append]
  simp only [coarseStraightSegment, List.length_replicate, coarseCoordSteps,
    Function.update_of_ne h12, Function.update_of_ne h01, Function.update_of_ne h02]

/-- **Inside a block, each axial leg is shorter than `m` scale-`ell` steps.**  DERIVED from
`inBlock`'s own two-sided coordinate bound; no divisibility, no torus hypothesis, and the `Fin`
subtraction does not wrap because `inBlock` gives `y μ ≤ u μ`. -/
theorem coordSteps_lt_of_mem_block {ell m : ℕ} {y u : PeriodicLatticeSite L}
    (hu : u ∈ blockOf y (ell * m)) (μ : Fin 3) :
    (u μ - y μ).val / ell < m := by
  have hin := (mem_blockOf.mp hu) μ
  have hle : y μ ≤ u μ := by rw [Fin.le_def]; exact hin.1
  have hval : (u μ - y μ).val = (u μ).val - (y μ).val := Fin.sub_val_of_le hle
  rw [hval]
  exact Nat.div_lt_of_lt_mul (by omega)

/-- **THE BLOCK STAIRCASE IS SHORT: `|Γ_{y,u}| ≤ 3m`.**  DERIVED.  This is the estimate
`compute/onestep_124` does not have — there the same contour is bounded by the LATTICE extent
`pathBudget L ell`, which is not `m`-controlled.  `3` is the number of coordinate directions,
i.e. `d`; the bound is `d·m`. -/
theorem coarseGammaPath_length_le_block {ell m : ℕ} {y u : PeriodicLatticeSite L}
    (hu : u ∈ blockOf y (ell * m)) :
    (coarseGammaPath ell y u).length ≤ 3 * m := by
  rw [coarseGammaPath_length_eq]
  have h2 := coordSteps_lt_of_mem_block hu 2
  have h1 := coordSteps_lt_of_mem_block hu 1
  have h0 := coordSteps_lt_of_mem_block hu 0
  omega

/-- **The `c₊`-side staircase has the SAME endpoint differences as the `c₋`-side one.**  Both
`cPlus c` and `partner c u` are the same translate `pathSite · c.2 (m·ell)`, and a translate is a
`Fin`-group shift, so it cancels in the difference — transverse coordinates by
`pathSite_apply_ne`, the moved one by `pathSite_eq` and `abel`.  DERIVED. -/
theorem partner_sub_cPlus {ell m : ℕ} (c : CoarseBond L (ell * m)) (u : PeriodicLatticeSite L)
    (ν : Fin 3) : partner c u ν - cPlus c ν = u ν - c.1.1 ν := by
  by_cases h : ν = c.2
  · subst h
    rw [partner, cPlus, pathSite_eq, pathSite_eq, Function.update_self, Function.update_self]
    abel
  · rw [partner, cPlus, pathSite_apply_ne _ _ _ _ h, pathSite_apply_ne _ _ _ _ h]

/-- **Hence the two staircases have EQUAL length.**  DERIVED.  This is what lets the `c₊` term be
bounded by the block diameter without a separate block-membership statement for `partner c u`. -/
theorem coarseGammaPath_length_partner {ell m : ℕ} (c : CoarseBond L (ell * m))
    (u : PeriodicLatticeSite L) :
    (coarseGammaPath ell (cPlus c) (partner c u)).length
      = (coarseGammaPath ell c.1.1 u).length := by
  rw [coarseGammaPath_length_eq, coarseGammaPath_length_eq,
    partner_sub_cPlus, partner_sub_cPlus, partner_sub_cPlus]

/-! ##############################################################################################
## §3 — THE FOUR CONTOUR INTEGRALS, BOUNDED BY THE BLOCK DIAMETER
############################################################################################## -/

/-- Every staircase in (124) is bounded by `3m·a`.  DERIVED from
`OneStep124.norm_lineIntegral_le` (PINNED) and §2. -/
theorem norm_lineIntegral_gamma_le {ell m : ℕ}
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : CoarseBond L ell → SuTwo) (a : ℝ) (ha : 0 ≤ a) (hA : ∀ b, ‖A b‖ ≤ a)
    {y u : PeriodicLatticeSite L} (hu : u ∈ blockOf y (ell * m)) :
    ‖lineIntegral ell V A y (coarseGammaPath ell y u)‖ ≤ 3 * (m : ℝ) * a := by
  refine le_trans (norm_lineIntegral_le ell V A a ha hA y (coarseGammaPath ell y u)) ?_
  have hlen : (((coarseGammaPath ell y u).length : ℕ) : ℝ) ≤ 3 * (m : ℝ) := by
    have := coarseGammaPath_length_le_block (L := L) (ell := ell) (m := m) hu
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right hlen ha

/-- The `m`-step segment `[x,x']` (and the coarse bond `c` itself) is bounded by `m·a`.  DERIVED. -/
theorem norm_lineIntegral_replicate_le {ell m : ℕ}
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : CoarseBond L ell → SuTwo) (a : ℝ) (ha : 0 ≤ a) (hA : ∀ b, ‖A b‖ ≤ a)
    (y : PeriodicLatticeSite L) (μ : Fin 3) :
    ‖lineIntegral ell V A y (List.replicate m μ)‖ ≤ (m : ℝ) * a := by
  refine le_trans (norm_lineIntegral_le ell V A a ha hA y (List.replicate m μ)) ?_
  rw [List.length_replicate]

/-- The `c₊`-side staircase, bounded by `3m·a` — via the length EQUALITY of §2, so no separate
block statement about `partner` is needed.  DERIVED. -/
theorem norm_lineIntegral_gamma_plus_le {ell m : ℕ}
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : CoarseBond L ell → SuTwo) (a : ℝ) (ha : 0 ≤ a) (hA : ∀ b, ‖A b‖ ≤ a)
    (c : CoarseBond L (ell * m)) {u : PeriodicLatticeSite L}
    (hu : u ∈ blockOf c.1.1 (ell * m)) :
    ‖lineIntegral ell V A (cPlus c) (coarseGammaPath ell (cPlus c) (partner c u))‖
      ≤ 3 * (m : ℝ) * a := by
  refine le_trans (norm_lineIntegral_le ell V A a ha hA (cPlus c)
    (coarseGammaPath ell (cPlus c) (partner c u))) ?_
  have hlen : (((coarseGammaPath ell (cPlus c) (partner c u)).length : ℕ) : ℝ) ≤ 3 * (m : ℝ) := by
    rw [coarseGammaPath_length_partner]
    have := coarseGammaPath_length_le_block (L := L) (ell := ell) (m := m) hu
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right hlen ha

/-! ##############################################################################################
## §4 — THE ERRATUM, POSITIVE HALF: (126)'s FORM HOLDS WITH AN `L`-FREE CONSTANT
############################################################################################## -/

/-- **THE `L`-FREE CORRECTION BOUND.**  DERIVED from `OneStep124.norm_delta124_le` (PINNED) by
applying the block-diameter contour bounds of §3 and the block cardinality `≤ m³`
(`OneStep124.unitSitesOf_card_le`, PINNED).  The arithmetic is

    (1/m⁴)·m³·(κ·3m·a + κ·m·a + κ·3m·a) + (1/m)·(κ·m·a)
  = (1/m⁴)·m³·(7κ·m·a) + κ·a
  = 7κ·a + κ·a = 8κ·a .

Every factor is counted: `m³` is the block cardinality, `3m` is `d` axial legs of at most `m`
steps, `m` is the segment `[x,x']`, and `m⁻⁴`/`m⁻¹` are the printed prefactors `L^{-(d+1)}` and
`L^{-1}`.  **The result contains no `m` and no lattice extent.**

**BILLING OF THE CONSTANT `8`** (added 2026-08-08 on the consolidated three-family repair list;
S75 — the superseded sentence is RETAINED STRUCK, not deleted):
~~"With `κ` the source's own `O(L²α₀)` this is exactly (126)'s printed right-hand side, with
`O(1) = 8 = 2d+2`."~~  That sentence claims more than this theorem proves.  What IS proved:

* `8` is the **combinatorial multiplier of the COMMON bracket ceiling `kap`** — the hypotheses
  bound all three brackets `E₁, E₂, E₃` by the SAME number `kap`, and the conclusion is `8` times
  that one number (times `a`).
* If instead the three printed brackets carry their own constants `B₁` (on `E₁`), `B₂` (on `E₂`),
  `B₃` (on `E₃`), the same count is weighted: `E₁` occurs on four legs (three staircase steps of
  the `c₋`-side contour plus the one `[x,x']` segment), `E₂` on three, `E₃` once, so the bound is
  `(4B₁ + 3B₂ + B₃)·a ≤ 8·max(B₁,B₂,B₃)·a`.  Setting `kap = max Bᵢ` recovers the `8`.
* Therefore this theorem proves **the multiplier `8 = 2d+2` at `d = 3`, relative to `kap`**.  It
  does **not** prove that the page's own unnamed `O(1)` in (126) is literally the number `8`:
  that would additionally require the absolute values of `B₁, B₂, B₃`, which p.36 leaves unnamed
  behind `O(L²α₀)`. -/
theorem norm_delta124_le_Lfree {ell m : ℕ} (hell : 0 < ell) (hm : 0 < m)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo)
    (c : CoarseBond L (ell * m)) (kap a : ℝ) (hkap : 0 ≤ kap) (ha : 0 ≤ a)
    (hE1 : ∀ u ∈ unitSitesOf ell (ell * m) c.1.1, ‖K.E1 c u.1‖ ≤ kap)
    (hE2 : ∀ u ∈ unitSitesOf ell (ell * m) c.1.1, ‖K.E2 c u.1‖ ≤ kap)
    (hE3 : ‖K.E3 c‖ ≤ kap) (hA : ∀ b, ‖A b‖ ≤ a) :
    ‖delta124 ell m V K A c‖ ≤ 8 * kap * a := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hB7 : (0 : ℝ) ≤ 7 * kap * ((m : ℝ) * a) := by positivity
  -- (a) every summand of the block sum is at most `7·κ·m·a`
  have hterm : ∀ u ∈ unitSitesOf ell (ell * m) c.1.1,
      (‖K.E1 c u.1‖ * ‖lineIntegral ell V A c.1.1 (coarseGammaPath ell c.1.1 u.1)‖
        + ‖K.E1 c u.1‖ * ‖lineIntegral ell V A u.1 (List.replicate m c.2)‖
        + ‖K.E2 c u.1‖
            * ‖lineIntegral ell V A (cPlus c)
                (coarseGammaPath ell (cPlus c) (partner c u.1))‖)
        ≤ 7 * kap * ((m : ℝ) * a) := by
    intro u hu
    have hblk : u.1 ∈ blockOf c.1.1 (ell * m) := by
      simpa [unitSitesOf] using hu
    have h1 : ‖K.E1 c u.1‖ * ‖lineIntegral ell V A c.1.1 (coarseGammaPath ell c.1.1 u.1)‖
        ≤ kap * (3 * (m : ℝ) * a) :=
      mul_le_mul (hE1 u hu) (norm_lineIntegral_gamma_le V A a ha hA hblk) (norm_nonneg _) hkap
    have h2 : ‖K.E1 c u.1‖ * ‖lineIntegral ell V A u.1 (List.replicate m c.2)‖
        ≤ kap * ((m : ℝ) * a) :=
      mul_le_mul (hE1 u hu) (norm_lineIntegral_replicate_le V A a ha hA u.1 c.2)
        (norm_nonneg _) hkap
    have h3 : ‖K.E2 c u.1‖
          * ‖lineIntegral ell V A (cPlus c) (coarseGammaPath ell (cPlus c) (partner c u.1))‖
        ≤ kap * (3 * (m : ℝ) * a) :=
      mul_le_mul (hE2 u hu) (norm_lineIntegral_gamma_plus_le V A a ha hA c hblk)
        (norm_nonneg _) hkap
    nlinarith [h1, h2, h3]
  -- (b) the block sum, with the cardinality bound
  have hcard : (((unitSitesOf ell (ell * m) c.1.1).card : ℕ) : ℝ) ≤ (m : ℝ) ^ 3 := by
    have := unitSitesOf_card_le (L := L) (m := m) hell c.1.1 (coarseLattice_mono c.1.2)
    exact_mod_cast this
  have hsum :
      (∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
        (‖K.E1 c u.1‖ * ‖lineIntegral ell V A c.1.1 (coarseGammaPath ell c.1.1 u.1)‖
          + ‖K.E1 c u.1‖ * ‖lineIntegral ell V A u.1 (List.replicate m c.2)‖
          + ‖K.E2 c u.1‖
              * ‖lineIntegral ell V A (cPlus c)
                  (coarseGammaPath ell (cPlus c) (partner c u.1))‖))
        ≤ (m : ℝ) ^ 3 * (7 * kap * ((m : ℝ) * a)) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ (7 * kap * ((m : ℝ) * a)) hterm) ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard hB7
  -- (c) the `c`-term
  have hc5 : ‖K.E3 c‖ * ‖lineIntegral ell V A c.1.1 (List.replicate m c.2)‖
      ≤ kap * ((m : ℝ) * a) :=
    mul_le_mul hE3 (norm_lineIntegral_replicate_le V A a ha hA c.1.1 c.2)
      (norm_nonneg _) hkap
  -- (d) assemble
  refine le_trans (norm_delta124_le ell m hm V K A c) ?_
  have hstep :
      (1 / (m : ℝ) ^ 4)
          * (∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
              (‖K.E1 c u.1‖ * ‖lineIntegral ell V A c.1.1 (coarseGammaPath ell c.1.1 u.1)‖
                + ‖K.E1 c u.1‖ * ‖lineIntegral ell V A u.1 (List.replicate m c.2)‖
                + ‖K.E2 c u.1‖
                    * ‖lineIntegral ell V A (cPlus c)
                        (coarseGammaPath ell (cPlus c) (partner c u.1))‖))
        + (1 / (m : ℝ)) * (‖K.E3 c‖ * ‖lineIntegral ell V A c.1.1 (List.replicate m c.2)‖)
      ≤ (1 / (m : ℝ) ^ 4) * ((m : ℝ) ^ 3 * (7 * kap * ((m : ℝ) * a)))
        + (1 / (m : ℝ)) * (kap * ((m : ℝ) * a)) := by
    refine add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity))
      (mul_le_mul_of_nonneg_left hc5 (by positivity))
  refine le_trans hstep (le_of_eq ?_)
  field_simp
  ring

end Erratum126Slim
