/-
# `OneStep124Slim.lean` -- verbatim excerpt of `compute/onestep_124/stage/OneStep124.lean`

An EXCERPT, not a new development.  Every declaration below is copied character for character from
`OneStep124.lean` (source line ranges: 74-91 namespace/opens, 103-124, 276-282, 411-421, 429-480,
762-836, 1581-1677) with two changes: `namespace OneStep124` is `namespace OneStep124Slim` (so that a check file can
import both modules), and `import AdalyFormal.Balaban.AlphaAnalyticity` is explicit (in the original
it arrives through the `GUAlpha1Package` chain).  It exists because `OneStep124` imports
`GUAlpha1Package`, whose cone reaches the `sorry`-bearing module `AdalyFormal.Balaban.SpineCovariant`,
although none of the theorems below uses anything from that chain.  Only `Mathlib`,
`AdalyFormal.Balaban.QjComposite` and `AdalyFormal.Balaban.AlphaAnalyticity` are imported.  Omitted: `IsFlat` and everything else not used by the theorem.
-/
import Mathlib
import AdalyFormal.Balaban.QjComposite
import AdalyFormal.Balaban.AlphaAnalyticity

set_option maxHeartbeats 4000000
set_option autoImplicit false

noncomputable section

namespace OneStep124Slim

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo RMap RMap_one RMap_mul_apply)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice blockOf mem_blockOf)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.ReparamCDisjoint (pathSite_apply_ne pathSite_apply_self_val)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf pathSite_mul_coarse)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarsePathEndpoint coarsePathHolonomy coarseGammaPath
  coarseStraightSegment coarseCoordSteps
  coarseStraightSegment coarseCoordSteps coarseTransportPath unitToCoarseCov unitToCoarseCovLM)
open AdalyFormal.Balaban.QjComposite (coarsePathHolonomy_append coarsePathEndpoint_append)

variable {L : PeriodicLatticeExtent}


/-- **`(R_{0,y}A)(Γ)`** — the `A`-line-integral along the scale-`ell` forward contour `Γ` starting
at `y`, transported back to `y`.  The `dite` supplies the `CoarseLattice` membership exactly as
`unitToCoarseCov` does; on the compatible torus it always fires (`pathSite_mul_coarse`). -/
def lineIntegral (ell : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : CoarseBond L ell → SuTwo) : PeriodicLatticeSite L → List (Fin 3) → SuTwo
  | _, [] => 0
  | y, μ :: rest =>
      (if h : y ∈ CoarseLattice L ell then A (⟨y, h⟩, μ) else 0)
        + RMap (V (y, μ)) (lineIntegral ell V A (coarseShift y ell μ) rest)

@[simp] theorem lineIntegral_nil (ell : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : CoarseBond L ell → SuTwo) (y : PeriodicLatticeSite L) :
    lineIntegral ell V A y [] = 0 := rfl

theorem lineIntegral_cons (ell : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : CoarseBond L ell → SuTwo) (y : PeriodicLatticeSite L) (μ : Fin 3) (rest : List (Fin 3)) :
    lineIntegral ell V A y (μ :: rest)
      = (if h : y ∈ CoarseLattice L ell then A (⟨y, h⟩, μ) else 0)
        + RMap (V (y, μ)) (lineIntegral ell V A (coarseShift y ell μ) rest) := rfl


/-- **The (124) coefficient package.**  `E1 c u`, `E2 c u`, `E3 c` are the three bracket operators;
`gbar c` is the `SU(2)` element whose adjoint action is `R̄_{0,c}` (the transport by the BLOCKED
background along the coarse bond `c`, p.35's `R̄_{0,c}`).  Carrying `gbar` as a GROUP element rather
than as a free linear map is deliberate: `RMap g` is an isometry, so no choice of `gbar` can inflate
the correction terms. -/
structure Coeff124 (L : PeriodicLatticeExtent) (ell m : ℕ) where
  E1 : CoarseBond L (ell * m) → PeriodicLatticeSite L → (SuTwo →L[ℝ] SuTwo)
  E2 : CoarseBond L (ell * m) → PeriodicLatticeSite L → (SuTwo →L[ℝ] SuTwo)
  E3 : CoarseBond L (ell * m) → (SuTwo →L[ℝ] SuTwo)
  gbar : CoarseBond L (ell * m) → Matrix.specialUnitaryGroup (Fin 2) ℂ


/-- The `c₊` site of a coarse bond: `m` scale-`ell` steps from `c₋` in direction `c.2`. -/
def cPlus {ell m : ℕ} (c : CoarseBond L (ell * m)) : PeriodicLatticeSite L :=
  pathSite c.1.1 c.2 (m * ell)

/-- The partner site `x' ∈ B(c₊)` of `x ∈ B(c₋)` — translation by the coarse bond
(`SOURCE.md` §3(d)); a bijection `B(c₋) → B(c₊)`. -/
def partner {ell m : ℕ} (c : CoarseBond L (ell * m)) (u : PeriodicLatticeSite L) :
    PeriodicLatticeSite L :=
  pathSite u c.2 (m * ell)

/-- **(124) T2** — `Σ_x L^{-(d+1)} E₁(x)(R_{0,c₋}A)(Γ_{c₋,x})`.  ASSEMBLED. -/
def term2 (ell m : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) : SuTwo :=
  (1 / (m : ℝ) ^ 4) • ∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
    K.E1 c u.1 (lineIntegral ell V A c.1.1 (coarseGammaPath ell c.1.1 u.1))

/-- **(124) T3** — `Σ_x L^{-(d+1)} E₁(x)(R_{0,c₋}A)([x,x'])`.  ASSEMBLED.  Note the argument is
the SAME segment integral that T1 uses, transported to `c₋` by the staircase holonomy — the source
writes `(R_{0,c₋}A)([x,x'])` in both T1 and T3. -/
def term3 (ell m : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) : SuTwo :=
  (1 / (m : ℝ) ^ 4) • ∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
    K.E1 c u.1
      (RMap (coarsePathHolonomy ell V c.1.1 (coarseGammaPath ell c.1.1 u.1))
        (lineIntegral ell V A u.1 (List.replicate m c.2)))

/-- **(124) T4** — `− Σ_x L^{-(d+1)} E₂(x) R̄_{0,c}(R_{0,c₊}A)(Γ_{c₊,x'})`.  ASSEMBLED. -/
def term4 (ell m : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) : SuTwo :=
  -((1 / (m : ℝ) ^ 4) • ∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
    K.E2 c u.1
      (RMap (K.gbar c)
        (lineIntegral ell V A (cPlus c) (coarseGammaPath ell (cPlus c) (partner c u.1)))))

/-- **(124) T5** — `E₃ · L^{-1}(R_{0,c₋}A)(c)`.  ASSEMBLED.  `(R_{0,c₋}A)(c)` is the line integral
along the coarse bond `c` itself, i.e. the `m`-step segment based at `c₋`. -/
def term5 (ell m : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) : SuTwo :=
  (1 / (m : ℝ)) • K.E3 c (lineIntegral ell V A c.1.1 (List.replicate m c.2))

/-- **CMP98 (124), THE FULL ONE-STEP AVERAGING LINEAR FORM.**  ASSEMBLED from the five TRANSCRIBED
terms; T1 is the tree's own `unitToCoarseCov`, so the split `(124) = (125) + Δ` is exact by
construction and the four correction terms are visible as `term2 + term3 + term4 + term5`. -/
def q124 (ell m : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) : SuTwo :=
  unitToCoarseCov ell m V A c
    + term2 ell m V K A c + term3 ell m V K A c + term4 ell m V K A c + term5 ell m V K A c

/-- The four correction terms, as one object. -/
def delta124 (ell m : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) : SuTwo :=
  term2 ell m V K A c + term3 ell m V K A c + term4 ell m V K A c + term5 ell m V K A c

/-- **The pointwise size of `Δ`.**  DERIVED: every factor is counted, none is absorbed into an
`O(1)`.  The source's own version is the sentence below (124) (*"the terms can be estimated by
`O(1)L²α₀L|A|`"*) and (126); this is that estimate with the constants exhibited.

`RMap` is an isometry (`AlphaAnalyticity.norm_RMap`), so the two transports contribute exactly `1`
and the whole correction is controlled by the three bracket norms against the three contour
integrals. -/
theorem norm_delta124_le (ell m : ℕ) (hm : 0 < m)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) :
    ‖delta124 ell m V K A c‖
      ≤ (1 / (m : ℝ) ^ 4) *
          (∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
            (‖K.E1 c u.1‖ * ‖lineIntegral ell V A c.1.1 (coarseGammaPath ell c.1.1 u.1)‖
             + ‖K.E1 c u.1‖ * ‖lineIntegral ell V A u.1 (List.replicate m c.2)‖
             + ‖K.E2 c u.1‖ *
                 ‖lineIntegral ell V A (cPlus c) (coarseGammaPath ell (cPlus c) (partner c u.1))‖))
        + (1 / (m : ℝ)) * (‖K.E3 c‖ * ‖lineIntegral ell V A c.1.1 (List.replicate m c.2)‖) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hpos4 : (0 : ℝ) ≤ 1 / (m : ℝ) ^ 4 := by positivity
  have hpos1 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  -- bound the three block-sum terms together, then the `c`-term
  have hsum :
      ‖term2 ell m V K A c + term3 ell m V K A c + term4 ell m V K A c‖
        ≤ (1 / (m : ℝ) ^ 4) *
          (∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
            (‖K.E1 c u.1‖ * ‖lineIntegral ell V A c.1.1 (coarseGammaPath ell c.1.1 u.1)‖
             + ‖K.E1 c u.1‖ * ‖lineIntegral ell V A u.1 (List.replicate m c.2)‖
             + ‖K.E2 c u.1‖ *
                 ‖lineIntegral ell V A (cPlus c) (coarseGammaPath ell (cPlus c) (partner c u.1))‖)) := by
    have hcollapse :
        term2 ell m V K A c + term3 ell m V K A c + term4 ell m V K A c
          = (1 / (m : ℝ) ^ 4) • ∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
              (K.E1 c u.1 (lineIntegral ell V A c.1.1 (coarseGammaPath ell c.1.1 u.1))
               + K.E1 c u.1
                   (RMap (coarsePathHolonomy ell V c.1.1 (coarseGammaPath ell c.1.1 u.1))
                     (lineIntegral ell V A u.1 (List.replicate m c.2)))
               - K.E2 c u.1
                   (RMap (K.gbar c)
                     (lineIntegral ell V A (cPlus c)
                       (coarseGammaPath ell (cPlus c) (partner c u.1))))) := by
      simp only [term2, term3, term4]
      rw [← smul_add, ← smul_neg, ← smul_add, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib]
      refine congrArg _ (Finset.sum_congr rfl fun u _ => ?_)
      abel
    rw [hcollapse, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos4]
    refine mul_le_mul_of_nonneg_left (le_trans (norm_sum_le _ _) ?_) hpos4
    refine Finset.sum_le_sum fun u _ => ?_
    refine le_trans (norm_sub_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add ?_ ?_)) ?_
    · exact (K.E1 c u.1).le_opNorm _
    · calc ‖K.E1 c u.1 (RMap (coarsePathHolonomy ell V c.1.1 (coarseGammaPath ell c.1.1 u.1))
              (lineIntegral ell V A u.1 (List.replicate m c.2)))‖
          ≤ ‖K.E1 c u.1‖ * ‖RMap (coarsePathHolonomy ell V c.1.1 (coarseGammaPath ell c.1.1 u.1))
              (lineIntegral ell V A u.1 (List.replicate m c.2))‖ := (K.E1 c u.1).le_opNorm _
        _ = ‖K.E1 c u.1‖ * ‖lineIntegral ell V A u.1 (List.replicate m c.2)‖ := by
              rw [AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]
    · calc ‖K.E2 c u.1 (RMap (K.gbar c) (lineIntegral ell V A (cPlus c)
              (coarseGammaPath ell (cPlus c) (partner c u.1))))‖
          ≤ ‖K.E2 c u.1‖ * ‖RMap (K.gbar c) (lineIntegral ell V A (cPlus c)
              (coarseGammaPath ell (cPlus c) (partner c u.1)))‖ := (K.E2 c u.1).le_opNorm _
        _ = ‖K.E2 c u.1‖ * ‖lineIntegral ell V A (cPlus c)
              (coarseGammaPath ell (cPlus c) (partner c u.1))‖ := by
              rw [AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]
  have hterm5 : ‖term5 ell m V K A c‖
      ≤ (1 / (m : ℝ)) * (‖K.E3 c‖ * ‖lineIntegral ell V A c.1.1 (List.replicate m c.2)‖) := by
    rw [term5, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos1]
    exact mul_le_mul_of_nonneg_left ((K.E3 c).le_opNorm _) hpos1
  have hdelta : delta124 ell m V K A c
      = (term2 ell m V K A c + term3 ell m V K A c + term4 ell m V K A c)
        + term5 ell m V K A c := by
    simp only [delta124]
  rw [hdelta]
  exact le_trans (norm_add_le _ _) (add_le_add hsum hterm5)


/-- A site of the `ell·k` coarse lattice is a site of the `ell` coarse lattice.  DERIVED. -/
theorem coarseLattice_mono {ell k : ℕ} {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L (ell * k)) : y ∈ CoarseLattice L ell := by
  refine mem_CoarseLattice.mpr fun μ => ?_
  obtain ⟨j, hj⟩ :=
    dvd_trans (⟨k, rfl⟩ : ell ∣ ell * k) (Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy μ))
  rw [hj, Nat.mul_mod_right]

/-- **The contour-length budget** — a staircase contour at scale `ell` takes at most this many
steps, on this lattice.  DERIVED from the coordinate ranges alone. -/
def pathBudget (L : PeriodicLatticeExtent) (ell : ℕ) : ℕ :=
  L 0 / ell + L 1 / ell + L 2 / ell

/-- A straight scale-`ell` segment takes at most `L μ / ell` steps, because a coordinate
difference lives in `Fin (L μ + 1)`.  DERIVED. -/
theorem coarseStraightSegment_length_le (ell : ℕ) (a b : PeriodicLatticeSite L) (μ : Fin 3) :
    (coarseStraightSegment ell a b μ).length ≤ L μ / ell := by
  rw [coarseStraightSegment, List.length_replicate, coarseCoordSteps]
  exact Nat.div_le_div_right (Nat.lt_succ_iff.mp (b μ - a μ).isLt)

/-- **THE STAIRCASE CONTOUR IS SHORT** — its length is bounded by the lattice's own extents,
uniformly in the endpoints.  DERIVED. -/
theorem coarseGammaPath_length_le (ell : ℕ) (y x : PeriodicLatticeSite L) :
    (coarseGammaPath ell y x).length ≤ pathBudget L ell := by
  rw [coarseGammaPath, List.length_append, List.length_append, pathBudget]
  have h2 := coarseStraightSegment_length_le ell y x 2
  have h1 := coarseStraightSegment_length_le (L := L) ell (Function.update y 2 (x 2)) x 1
  have h0 := coarseStraightSegment_length_le (L := L) ell
    (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0
  omega

/-- **THE BLOCK HAS AT MOST `m³` SCALE-`ell` SITES.**  DERIVED by an explicit injection of the block
into `Fin 3 → Fin m`: a scale-`ell` site `u` of the `(ell·m)`-block of `y` is determined by the
triple of cell indices `((u μ) − (y μ))/ell`, because both `u` and `y` sit on the scale-`ell`
lattice, so the coordinate difference is a MULTIPLE of `ell`. -/
theorem unitSitesOf_card_le {ell m : ℕ} (hell : 0 < ell) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L ell) :
    (unitSitesOf ell (ell * m) y).card ≤ m ^ 3 := by
  classical
  have hidx : ∀ u ∈ unitSitesOf ell (ell * m) y, ∀ μ : Fin 3,
      ((u.1 μ).val - (y μ).val) / ell < m := by
    intro u hu μ
    have hb : u.1 ∈ blockOf y (ell * m) := by
      simpa [unitSitesOf] using hu
    have hin := (mem_blockOf.mp hb) μ
    have hlt : (u.1 μ).val - (y μ).val < ell * m := by omega
    exact Nat.div_lt_of_lt_mul (by omega)
  refine le_trans (Finset.card_le_card_of_injOn
    (t := Fintype.piFinset (fun _ : Fin 3 => Finset.range m))
    (fun u => (fun μ : Fin 3 => (((u.1 μ).val - (y μ).val) / ell)))
    (fun u hu => Fintype.mem_piFinset.mpr
      (fun μ => Finset.mem_range.mpr (hidx u hu μ))) ?_) ?_
  · intro u hu v hv heq
    apply Subtype.ext
    funext μ
    apply Fin.ext
    have hbu : u.1 ∈ blockOf y (ell * m) := by simpa [unitSitesOf] using hu
    have hbv : v.1 ∈ blockOf y (ell * m) := by simpa [unitSitesOf] using hv
    have hinu := (mem_blockOf.mp hbu) μ
    have hinv := (mem_blockOf.mp hbv) μ
    have hmu : (u.1 μ).val % ell = 0 := (mem_CoarseLattice.mp u.2) μ
    have hmv : (v.1 μ).val % ell = 0 := (mem_CoarseLattice.mp v.2) μ
    have hmy : (y μ).val % ell = 0 := (mem_CoarseLattice.mp hy) μ
    have hdu : ((u.1 μ).val - (y μ).val) % ell = 0 := Nat.sub_mod_eq_zero_of_mod_eq (by omega)
    have hdv : ((v.1 μ).val - (y μ).val) % ell = 0 := Nat.sub_mod_eq_zero_of_mod_eq (by omega)
    have hq : ((u.1 μ).val - (y μ).val) / ell = ((v.1 μ).val - (y μ).val) / ell :=
      congrFun heq μ
    have hu' : (u.1 μ).val - (y μ).val = ((u.1 μ).val - (y μ).val) / ell * ell :=
      (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdu)).symm
    have hv' : (v.1 μ).val - (y μ).val = ((v.1 μ).val - (y μ).val) / ell * ell :=
      (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdv)).symm
    have hsub : (u.1 μ).val - (y μ).val = (v.1 μ).val - (y μ).val := by
      rw [hu', hv', hq]
    omega
  · rw [Fintype.card_piFinset]
    simp [Finset.card_range, Finset.prod_const, pow_succ]

/-! ### §9a — the pointwise size of the correction, in terms of `κ` and `‖A‖` -/

/-- **`‖∮A‖ ≤ (contour length)·sup‖A‖`.**  DERIVED by induction on the contour; the transports are
isometries (`norm_RMap`), so they contribute exactly `1`. -/
theorem norm_lineIntegral_le (ell : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : CoarseBond L ell → SuTwo) (Ma : ℝ) (hMa : 0 ≤ Ma) (hA : ∀ b, ‖A b‖ ≤ Ma)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    ‖lineIntegral ell V A y p‖ ≤ (p.length : ℝ) * Ma := by
  induction p generalizing y with
  | nil => simpa using hMa
  | cons μ rest ih =>
    rw [lineIntegral_cons]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖(if h : y ∈ CoarseLattice L ell then A (⟨y, h⟩, μ) else 0)‖ ≤ Ma := by
      by_cases h : y ∈ CoarseLattice L ell
      · rw [dif_pos h]; exact hA _
      · rw [dif_neg h]; simpa using hMa
    have h2 : ‖RMap (V (y, μ)) (lineIntegral ell V A (coarseShift y ell μ) rest)‖
        = ‖lineIntegral ell V A (coarseShift y ell μ) rest‖ :=
      AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap _ _
    have h3 := ih (coarseShift y ell μ)
    rw [h2]
    have hlen : ((μ :: rest).length : ℝ) = (rest.length : ℝ) + 1 := by
      simp [List.length_cons]
    rw [hlen]
    nlinarith [h1, h3]


end OneStep124Slim
