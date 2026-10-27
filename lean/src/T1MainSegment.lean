/-
T1 stage — identify CMP98 (124)'s main-segment channel T1 with `q124Principal`'s own T1 channel
(`unitToCoarseCov`, CMP98 (125)), for ARBITRARY `A`, and settle the `L^{-4}` vs `ell^{-3}`
cardinality question named by the charge.

PROVENANCE.  Every declaration up to and including `Coeff124.ofPrincipalBackground`/`q124Principal`
below is copied VERBATIM (statement AND proof, byte-for-byte where the surrounding trimmed import
list allows) from the READ-ONLY originals:
  * `compute/deltak_ladder/OneStep124.lean` (namespace `OneStep124`)      -- §1, §3, §4, §8a-§8d
  * `compute/deltak_r66/PrincipalCoeff.lean` (namespace `AdalyFormal.DeltaKR66`)
  * `compute/deltak_r85/FaithfulEncoding.lean` (namespace `AdalyFormal.DeltaKR85`)
No source text of any copied declaration was altered; only UNUSED imports were dropped (`Mathlib`,
`GUAlpha1Package`, `HitSetCard`, `PerturbSurj`, `PreimageNorm`, `CovariantBlockWall`,
`FeasibilityAssembly`) after confirming by direct inspection that none of the declarations needed
for `q124Principal` itself (as opposed to the surjectivity/`L²`-operator-norm/tower sections of
those files, which are NOT reused here) reference anything from them. The three originals are not
reachable as prebuilt `.olean`s anywhere on this workflow's fixed `LEAN_PATH` (only
`compute/forall_u_rung/deps`'s `AdalyFormal.Balaban.*` snapshot, an unrelated Yang-Mills legacy
cache, and its Mathlib/aesop/etc. packages are); this file recompiles the needed slice directly
against that snapshot instead of the source files' own historical lane-local dependency chains.

NEW content, not present in any original: `unitSitesOf_card_eq` (the exact `m³` cardinality,
adapting the equality argument from `compute/erratum_126/work/probeFull.lean`'s
`unitSitesOf_card_eq`/`base_add_block_le`, itself built from this file's own `unitSitesOf_card_le`)
and the two theorems in the closing `AdalyFormal.DeltaKR85` section identifying `q124Principal`'s
T1 channel and discharging the `L^{-4}` vs `ell^{-3}` question.
-/
import AdalyFormal.Balaban.CovariantOperators
import AdalyFormal.Balaban.LatticeOperators
import AdalyFormal.Balaban.AdmissibleSubspace
import AdalyFormal.Balaban.QOne
import AdalyFormal.Balaban.ReparamCDisjoint
import AdalyFormal.Balaban.ThirdLevelArrows
import AdalyFormal.Balaban.CoarseCurl
import AdalyFormal.Balaban.TowerLawCovariant
import AdalyFormal.Balaban.QjComposite
import AdalyFormal.Balaban.BlockedBackground
import AdalyFormal.Balaban.UbarTowerCovariance
import AdalyFormal.Balaban.SuTwoLogExpCore
import AdalyFormal.Balaban.SuTwoLogExpTorus

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

noncomputable section

/-! ############################################################################################
## Part 1 — `OneStep124` (verbatim slice of `compute/deltak_ladder/OneStep124.lean`)
############################################################################################ -/

namespace OneStep124

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
  coarseStraightSegment coarseCoordSteps coarseTransportPath unitToCoarseCov unitToCoarseCovLM)
open AdalyFormal.Balaban.QjComposite (coarsePathHolonomy_append coarsePathEndpoint_append)

variable {L : PeriodicLatticeExtent}

/-! ### §1 — `(R_{0,y}A)(Γ)`, the Lie-algebra line integral along a scale-`ell` forward contour -/

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

theorem lineIntegral_append (ell : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : CoarseBond L ell → SuTwo) (y : PeriodicLatticeSite L) (p q : List (Fin 3)) :
    lineIntegral ell V A y (p ++ q)
      = lineIntegral ell V A y p
        + RMap (coarsePathHolonomy ell V y p) (lineIntegral ell V A (coarsePathEndpoint ell y p) q) := by
  induction p generalizing y with
  | nil =>
    show lineIntegral ell V A y q
        = 0 + RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) (lineIntegral ell V A y q)
    rw [RMap_one]
    simp
  | cons μ rest ih =>
    show (if h : y ∈ CoarseLattice L ell then A (⟨y, h⟩, μ) else 0)
        + RMap (V (y, μ)) (lineIntegral ell V A (coarseShift y ell μ) (rest ++ q))
      = ((if h : y ∈ CoarseLattice L ell then A (⟨y, h⟩, μ) else 0)
        + RMap (V (y, μ)) (lineIntegral ell V A (coarseShift y ell μ) rest))
        + RMap (V (y, μ) * coarsePathHolonomy ell V (coarseShift y ell μ) rest) _
    rw [ih, map_add, RMap_mul_apply]
    show _ = _
    abel

theorem lineIntegral_add (ell : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A₁ A₂ : CoarseBond L ell → SuTwo) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    lineIntegral ell V (A₁ + A₂) y p = lineIntegral ell V A₁ y p + lineIntegral ell V A₂ y p := by
  induction p generalizing y with
  | nil => simp
  | cons μ rest ih =>
    rw [lineIntegral_cons, lineIntegral_cons, lineIntegral_cons, ih, map_add]
    by_cases h : y ∈ CoarseLattice L ell
    · rw [dif_pos h, dif_pos h, dif_pos h]
      show A₁ _ + A₂ _ + _ = _
      abel
    · rw [dif_neg h, dif_neg h, dif_neg h]
      abel

theorem lineIntegral_smul (ell : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (r : ℝ) (A : CoarseBond L ell → SuTwo) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    lineIntegral ell V (r • A) y p = r • lineIntegral ell V A y p := by
  induction p generalizing y with
  | nil => simp
  | cons μ rest ih =>
    rw [lineIntegral_cons, lineIntegral_cons, ih, map_smul, smul_add]
    by_cases h : y ∈ CoarseLattice L ell
    · rw [dif_pos h, dif_pos h]; rfl
    · rw [dif_neg h, dif_neg h, smul_zero]

@[simp] theorem lineIntegral_zero (ell : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    lineIntegral ell V (0 : CoarseBond L ell → SuTwo) y p = 0 := by
  induction p generalizing y with
  | nil => rfl
  | cons μ rest ih => rw [lineIntegral_cons, ih]; simp

/-! ### `coarseLattice_mono` (§2a original), needed by the cardinality equality below -/

theorem coarseLattice_mono {ell k : ℕ} {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L (ell * k)) : y ∈ CoarseLattice L ell := by
  refine mem_CoarseLattice.mpr fun μ => ?_
  obtain ⟨j, hj⟩ :=
    dvd_trans (⟨k, rfl⟩ : ell ∣ ell * k) (Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy μ))
  rw [hj, Nat.mul_mod_right]

/-! ### §3 — the coefficient package and the FULL (124) operator -/

structure Coeff124 (L : PeriodicLatticeExtent) (ell m : ℕ) where
  E1 : CoarseBond L (ell * m) → PeriodicLatticeSite L → (SuTwo →L[ℝ] SuTwo)
  E2 : CoarseBond L (ell * m) → PeriodicLatticeSite L → (SuTwo →L[ℝ] SuTwo)
  E3 : CoarseBond L (ell * m) → (SuTwo →L[ℝ] SuTwo)
  gbar : CoarseBond L (ell * m) → Matrix.specialUnitaryGroup (Fin 2) ℂ

def IsFlat {ell m : ℕ} (K : Coeff124 L ell m) : Prop :=
  (∀ c u, K.E1 c u = 0) ∧ (∀ c u, K.E2 c u = 0) ∧ (∀ c, K.E3 c = 0)

def cPlus {ell m : ℕ} (c : CoarseBond L (ell * m)) : PeriodicLatticeSite L :=
  pathSite c.1.1 c.2 (m * ell)

def partner {ell m : ℕ} (c : CoarseBond L (ell * m)) (u : PeriodicLatticeSite L) :
    PeriodicLatticeSite L :=
  pathSite u c.2 (m * ell)

def term2 (ell m : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) : SuTwo :=
  (1 / (m : ℝ) ^ 4) • ∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
    K.E1 c u.1 (lineIntegral ell V A c.1.1 (coarseGammaPath ell c.1.1 u.1))

def term3 (ell m : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) : SuTwo :=
  (1 / (m : ℝ) ^ 4) • ∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
    K.E1 c u.1
      (RMap (coarsePathHolonomy ell V c.1.1 (coarseGammaPath ell c.1.1 u.1))
        (lineIntegral ell V A u.1 (List.replicate m c.2)))

def term4 (ell m : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) : SuTwo :=
  -((1 / (m : ℝ) ^ 4) • ∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
    K.E2 c u.1
      (RMap (K.gbar c)
        (lineIntegral ell V A (cPlus c) (coarseGammaPath ell (cPlus c) (partner c u.1)))))

def term5 (ell m : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) : SuTwo :=
  (1 / (m : ℝ)) • K.E3 c (lineIntegral ell V A c.1.1 (List.replicate m c.2))

/-- **CMP98 (124), THE FULL ONE-STEP AVERAGING LINEAR FORM.** `unitToCoarseCov` IS T1 = (125),
literally the first summand, by construction. -/
def q124 (ell m : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) : SuTwo :=
  unitToCoarseCov ell m V A c
    + term2 ell m V K A c + term3 ell m V K A c + term4 ell m V K A c + term5 ell m V K A c

def delta124 (ell m : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) : SuTwo :=
  term2 ell m V K A c + term3 ell m V K A c + term4 ell m V K A c + term5 ell m V K A c

/-! ### §4 — the relation theorems: (124) = T1(=125) + Δ, exactly, for ARBITRARY `A` -/

theorem q124_eq_main_add_delta (ell m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) :
    q124 ell m V K A c = unitToCoarseCov ell m V A c + delta124 ell m V K A c := by
  simp only [q124, delta124]
  abel

theorem delta124_eq_sub (ell m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) :
    delta124 ell m V K A c = q124 ell m V K A c - unitToCoarseCov ell m V A c := by
  rw [q124_eq_main_add_delta]
  abel

/-! ### Linearity of the full (124) -/

theorem term2_add (ell m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A₁ A₂ : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) :
    term2 ell m V K (A₁ + A₂) c = term2 ell m V K A₁ c + term2 ell m V K A₂ c := by
  simp only [term2, lineIntegral_add, map_add]
  rw [Finset.sum_add_distrib, smul_add]

theorem term3_add (ell m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A₁ A₂ : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) :
    term3 ell m V K (A₁ + A₂) c = term3 ell m V K A₁ c + term3 ell m V K A₂ c := by
  simp only [term3, lineIntegral_add, map_add]
  rw [Finset.sum_add_distrib, smul_add]

theorem term4_add (ell m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A₁ A₂ : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) :
    term4 ell m V K (A₁ + A₂) c = term4 ell m V K A₁ c + term4 ell m V K A₂ c := by
  simp only [term4, lineIntegral_add, map_add]
  rw [Finset.sum_add_distrib, smul_add, neg_add]

theorem term5_add (ell m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A₁ A₂ : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) :
    term5 ell m V K (A₁ + A₂) c = term5 ell m V K A₁ c + term5 ell m V K A₂ c := by
  simp only [term5, lineIntegral_add, map_add, smul_add]

theorem term2_smul (ell m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (r : ℝ) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) :
    term2 ell m V K (r • A) c = r • term2 ell m V K A c := by
  simp only [term2, lineIntegral_smul, map_smul]
  rw [← Finset.smul_sum, smul_comm]

theorem term3_smul (ell m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (r : ℝ) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) :
    term3 ell m V K (r • A) c = r • term3 ell m V K A c := by
  simp only [term3, lineIntegral_smul, map_smul]
  rw [← Finset.smul_sum, smul_comm]

theorem term4_smul (ell m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (r : ℝ) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) :
    term4 ell m V K (r • A) c = r • term4 ell m V K A c := by
  simp only [term4, lineIntegral_smul, map_smul]
  rw [← Finset.smul_sum, smul_comm, smul_neg]

theorem term5_smul (ell m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (r : ℝ) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) :
    term5 ell m V K (r • A) c = r • term5 ell m V K A c := by
  simp only [term5, lineIntegral_smul, map_smul]
  rw [smul_comm]

def q124LM (ell m : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) :
    (CoarseBond L ell → SuTwo) →ₗ[ℝ] (CoarseBond L (ell * m) → SuTwo) where
  toFun A := q124 ell m V K A
  map_add' A₁ A₂ := by
    funext c
    simp only [q124, Pi.add_apply, AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov_add,
      term2_add, term3_add, term4_add, term5_add]
    abel
  map_smul' r A := by
    funext c
    simp only [q124, Pi.smul_apply, RingHom.id_apply,
      AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov_smul,
      term2_smul, term3_smul, term4_smul, term5_smul, smul_add]

theorem q124LM_apply (ell m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) :
    q124LM ell m V K A = q124 ell m V K A := rfl

/-! ### The block has EXACTLY `m³` scale-`ell` sites, on the compatible torus.

`unitSitesOf_card_le` is the original's own upper bound (verbatim).  `unitSitesOf_card_eq`
(NEW: adapted from `compute/erratum_126/work/probeFull.lean`'s theorem of the same name, itself
built on `unitSitesOf_card_le`) supplies the matching lower bound, so the cardinality driving
`unitToCoarseCov`'s `1/m⁴` normalization is EXACTLY `m³`, not merely bounded by it. -/

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

theorem base_add_block_le {ell m : ℕ} {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L (ell * m)) (hdvd : ∀ μ : Fin 3, (ell * m) ∣ (L μ + 1))
    (μ : Fin 3) : (y μ).val + ell * m ≤ L μ + 1 := by
  have h1 : (y μ).val % (ell * m) = 0 := (mem_CoarseLattice.mp hy) μ
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h1
  obtain ⟨j, hj⟩ := hdvd μ
  have hlt : (y μ).val < L μ + 1 := (y μ).isLt
  have hkj : k < j := by
    rw [hk, hj] at hlt
    exact lt_of_mul_lt_mul_left hlt (Nat.zero_le _)
  rw [hk, hj]
  calc ell * m * k + ell * m = ell * m * (k + 1) := by ring
    _ ≤ ell * m * j := Nat.mul_le_mul_left _ hkj

/-- **THE EXACT `m³` CARDINALITY.** `L^{-(d+1)} = L^{-4}` at `d = 3` (CMP98's own printed
exponent) is EXACTLY `unitToCoarseCov`'s `1/m⁴`: `m³` block sites (this theorem) times `m`
line-integration steps `= m⁴`, under the file's own header dictionary `L ↦ m` (this file's `ell`
is the FINE stride, never CMP98's block factor). -/
theorem unitSitesOf_card_eq {ell m : ℕ} (hell : 0 < ell) {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L (ell * m)) (hdvd : ∀ μ : Fin 3, (ell * m) ∣ (L μ + 1)) :
    (unitSitesOf ell (ell * m) y).card = m ^ 3 := by
  classical
  refine le_antisymm (unitSitesOf_card_le hell y (coarseLattice_mono hy)) ?_
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · simp [hm0]
  have hroom := base_add_block_le (L := L) (ell := ell) (m := m) hy hdvd
  have hdvdy : ∀ μ : Fin 3, ell ∣ (y μ).val := by
    intro μ
    have h1 : (y μ).val % (ell * m) = 0 := (mem_CoarseLattice.mp hy) μ
    exact dvd_trans (Dvd.intro m rfl) (Nat.dvd_of_mod_eq_zero h1)
  have hlt : ∀ (f : Fin 3 → ℕ) (μ : Fin 3), (y μ).val + (f μ % m) * ell < L μ + 1 := by
    intro f μ
    have h1 : f μ % m < m := Nat.mod_lt _ hm
    have h2 : (f μ % m) * ell < ell * m := by
      calc (f μ % m) * ell < m * ell := (Nat.mul_lt_mul_right hell).mpr h1
        _ = ell * m := Nat.mul_comm _ _
    have h3 := hroom μ
    omega
  have hFmem : ∀ f : Fin 3 → ℕ,
      (fun μ => (⟨(y μ).val + (f μ % m) * ell, hlt f μ⟩ : Fin (L μ + 1)))
        ∈ CoarseLattice L ell := by
    intro f
    rw [mem_CoarseLattice]
    intro μ
    obtain ⟨k, hk⟩ := hdvdy μ
    show ((y μ).val + (f μ % m) * ell) % ell = 0
    rw [hk, Nat.add_mul_mod_self_right]
    exact Nat.mul_mod_right ell k
  have hcard : (Fintype.piFinset (fun _ : Fin 3 => Finset.range m)).card = m ^ 3 := by
    rw [Fintype.card_piFinset]
    simp [Finset.card_range, Finset.prod_const, pow_succ]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun f => (⟨fun μ => ⟨(y μ).val + (f μ % m) * ell, hlt f μ⟩, hFmem f⟩ :
      {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell})) ?_ ?_
  · intro f hf
    have hblk : (fun μ => (⟨(y μ).val + (f μ % m) * ell, hlt f μ⟩ : Fin (L μ + 1)))
        ∈ blockOf y (ell * m) := by
      rw [mem_blockOf]
      intro μ
      have h1 : f μ < m := Finset.mem_range.mp (Fintype.mem_piFinset.mp hf μ)
      have h2 : f μ % m = f μ := Nat.mod_eq_of_lt h1
      have h3 : f μ * ell < ell * m := by
        calc f μ * ell < m * ell := (Nat.mul_lt_mul_right hell).mpr h1
          _ = ell * m := Nat.mul_comm _ _
      show (y μ).val ≤ (y μ).val + (f μ % m) * ell ∧
        (y μ).val + (f μ % m) * ell < (y μ).val + ell * m
      rw [h2]
      omega
    simpa [unitSitesOf] using hblk
  · intro f hf g hg heq
    funext μ
    have h1 : f μ < m := Finset.mem_range.mp (Fintype.mem_piFinset.mp hf μ)
    have h2 : g μ < m := Finset.mem_range.mp (Fintype.mem_piFinset.mp hg μ)
    have hval : (y μ).val + (f μ % m) * ell = (y μ).val + (g μ % m) * ell := by
      have := congrFun (congrArg Subtype.val heq) μ
      exact congrArg Fin.val this
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval
    have : f μ * ell = g μ * ell := by omega
    exact Nat.eq_of_mul_eq_mul_right hell this

/-! ### §8a — `ad`, the adjoint action of `𝔰𝔲(2)` on itself (verbatim, definitions only: the
surrounding non-degeneracy/scalar-tie THEOREMS of the original are not needed to build
`Coeff124.ofBackground` and are dropped). -/

def adVal (Y X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Y * X - X * Y

theorem adVal_mem (Y X : Matrix (Fin 2) (Fin 2) ℂ) (hY : Y ∈ suTwo) (hX : X ∈ suTwo) :
    adVal Y X ∈ suTwo := by
  obtain ⟨hY1, hY2⟩ := hY
  obtain ⟨hX1, hX2⟩ := hX
  refine ⟨?_, ?_⟩
  · rw [adVal, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hX1, hY1]
    noncomm_ring
  · rw [adVal, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

def adLM (Y : SuTwo) : SuTwo →ₗ[ℝ] SuTwo where
  toFun X := ⟨adVal (Y : Matrix (Fin 2) (Fin 2) ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ),
    adVal_mem _ _ Y.2 X.2⟩
  map_add' X₁ X₂ := by
    apply Subtype.ext
    simp only [adVal, Submodule.coe_add]
    noncomm_ring
  map_smul' r X := by
    apply Subtype.ext
    simp only [adVal, SetLike.val_smul, RingHom.id_apply]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

def adOp (Y : SuTwo) : SuTwo →L[ℝ] SuTwo := LinearMap.toContinuousLinearMap (adLM Y)

/-! ### §8b — `g`, `g^{-1}` and `exp` as operator functions (definitions only) -/

def gCoeff (n : ℕ) : ℝ := (-1) ^ n / (Nat.factorial (n + 1))

def gOp (T : SuTwo →L[ℝ] SuTwo) : SuTwo →L[ℝ] SuTwo := ∑' n : ℕ, gCoeff n • T ^ n

def gInvOp (T : SuTwo →L[ℝ] SuTwo) : SuTwo →L[ℝ] SuTwo := Ring.inverse (gOp T)

def expCoeff (n : ℕ) : ℝ := ((Nat.factorial n : ℝ))⁻¹

def expOp (T : SuTwo →L[ℝ] SuTwo) : SuTwo →L[ℝ] SuTwo := ∑' n : ℕ, expCoeff n • T ^ n

/-! ### §8d — the background's logarithm data and the constructor -/

structure LogData (L : PeriodicLatticeExtent) (ell m : ℕ) where
  Zx : CoarseBond L (ell * m) → PeriodicLatticeSite L → SuTwo

def LogData.Z {L : PeriodicLatticeExtent} {ell m : ℕ} (D : LogData L ell m)
    (c : CoarseBond L (ell * m)) : SuTwo :=
  ∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
    (1 / ((unitSitesOf ell (ell * m) c.1.1).card : ℝ)) • D.Zx c u.1

def Coeff124.ofBackground {L : PeriodicLatticeExtent} (ell m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (D : LogData L ell m) : Coeff124 L ell m where
  E1 := fun c x => gOp (-(adOp (D.Z c))) * gInvOp (-(adOp (D.Zx c x))) - 1
  E2 := fun c x =>
    gOp (-(adOp (D.Z c))) * gInvOp (adOp (D.Zx c x)) * expOp (-(adOp (D.Z c))) - 1
  E3 := fun c =>
    expOp (adOp (D.Z c))
      - gOp (-(adOp (D.Z c))) *
          (∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
            (1 / ((unitSitesOf ell (ell * m) c.1.1).card : ℝ)) • gInvOp (adOp (D.Zx c u.1)))
  gbar := fun c => coarsePathHolonomy ell V c.1.1 (List.replicate m c.2)

end OneStep124

/-! ############################################################################################
## Part 2 — `AdalyFormal.DeltaKR66` (verbatim slice of `compute/deltak_r66/PrincipalCoeff.lean`)
############################################################################################ -/

namespace AdalyFormal.DeltaKR66

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open OneStep124

variable {L : PeriodicLatticeExtent}

def principalSuTwoLog (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    AdalyFormal.Balaban.CovariantOperators.SuTwo :=
  ⟨AdalyFormal.Balaban.SuTwoLogExp.su2Log g,
    AdalyFormal.Balaban.SuTwoLogExp.su2Log_antiHermitian g,
    AdalyFormal.Balaban.SuTwoLogExp.su2Log_traceless g⟩

def sourcePrincipalLogData (ell m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : LogData L ell m where
  Zx := fun c x => principalSuTwoLog (loopVar ell m V (c.1.1, c.2) x)

end AdalyFormal.DeltaKR66

/-! ############################################################################################
## Part 3 — `AdalyFormal.DeltaKR85` (verbatim slice of `compute/deltak_r85/FaithfulEncoding.lean`,
## plus the NEW T1-identification and cardinality theorems this stage owes)
############################################################################################ -/

namespace AdalyFormal.DeltaKR85

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.DeltaKR66 (principalSuTwoLog sourcePrincipalLogData)
open OneStep124

abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

/-- The corrected genuine coefficient constructor — VERBATIM copy of
`compute/deltak_r85/FaithfulEncoding.lean`'s `Coeff124.ofPrincipalBackground`. -/
def Coeff124.ofPrincipalBackground (ell m : ℕ)
    (V : PeriodicLinkConfiguration SU2 L) : Coeff124 L ell m where
  E1 := (Coeff124.ofBackground ell m V (sourcePrincipalLogData ell m V)).E1
  E2 := (Coeff124.ofBackground ell m V (sourcePrincipalLogData ell m V)).E2
  E3 := (Coeff124.ofBackground ell m V (sourcePrincipalLogData ell m V)).E3
  gbar := fun c => ubarSU2 ell m V (c.1.1, c.2)

/-- **THE ACTUAL `q124Principal`** — VERBATIM copy of
`compute/deltak_r85/FaithfulEncoding.lean`'s `q124Principal`, the packet's own fixed comparison
object `AdalyFormal.DeltaKR85.q124Principal s L V`. -/
def q124Principal (ell m : ℕ) (V : PeriodicLinkConfiguration SU2 L) :
    (CoarseBond L ell → SuTwo) →ₗ[ℝ] (CoarseBond L (ell * m) → SuTwo) :=
  q124LM ell m V (Coeff124.ofPrincipalBackground ell m V)

/-! ### NEW: the T1 identification, for ARBITRARY `A`, and the `L^{-4}` vs `ell^{-3}` cardinality
question. -/

/-- **T1 IDENTIFICATION.** For `q124Principal` — the ACTUAL, source-faithful CMP98 (124)
five-channel operator, not a gradient-only restriction or a newly chosen linear map — the
main-segment channel T1 is literally `unitToCoarseCov` (CMP98 (125)), for EVERY `A` (arbitrary,
not merely gradients or a flat background) and every coarse bond `c`. This is `q124Principal`'s
own T1 channel (its unfolding through `q124LM_apply`/`q124_eq_main_add_delta` at
`K := Coeff124.ofPrincipalBackground ell m V`), so `q124Principal.term1` and `unitToCoarseCov`
coincide as a matter of construction, exactly as `OneStep124.q124`'s own header states
(`T1 = unitToCoarseCov`, "the split `(124) = (125) + Δ` is exact by construction"). -/
theorem q124Principal_eq_unitToCoarseCov_add_delta (ell m : ℕ)
    (V : PeriodicLinkConfiguration SU2 L)
    (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) :
    q124Principal ell m V A c
      = AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov ell m V A c
        + delta124 ell m V (Coeff124.ofPrincipalBackground ell m V) A c := by
  show q124 ell m V (Coeff124.ofPrincipalBackground ell m V) A c = _
  exact q124_eq_main_add_delta ell m V (Coeff124.ofPrincipalBackground ell m V) A c

/-- Corollary in `q124Principal`'s own name for its main channel: T1 = `unitToCoarseCov`
literally, i.e. `q124Principal`'s first (main-segment) summand needs no correction to equal the
tree's `unitToCoarseCov`, for arbitrary `A`. -/
theorem q124Principal_T1_eq_unitToCoarseCov (ell m : ℕ)
    (V : PeriodicLinkConfiguration SU2 L)
    (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) :
    q124Principal ell m V A c - delta124 ell m V (Coeff124.ofPrincipalBackground ell m V) A c
      = AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov ell m V A c := by
  rw [q124Principal_eq_unitToCoarseCov_add_delta]
  abel

/-- **THE `L^{-4}` vs `ell^{-3}` CARDINALITY QUESTION, DISCHARGED.** `q124Principal`'s T1 channel
`unitToCoarseCov ell m V` carries the normalization `1/m⁴`, where `m` is CMP98's own block factor
`L` under `OneStep124`'s dictionary (`d = 3`, `L ↦ m`, field at scale `ell`) — `ell` here is the
FINE stride, never the block factor. On the compatible torus (`ell*m ∣ L μ + 1` for every `μ`),
`unitSitesOf_card_eq` proves the block `B(c₋)` this normalization sums over has EXACTLY `m³` sites;
combined with the `m`-step line integration each summand carries, the total count is `m³·m = m⁴`,
matching CMP98's printed `L^{-(d+1)} = L^{-4}` exactly. This is emphatically NOT `ell³`/`ell⁻³`:
that exponent belongs to a DIFFERENT object entirely — `endpointAvg`/`modifiedAverage`'s own
`ℓ⁻³`-weighted CMP98 (63) block-spatial average (`compute/m1_si1_deriv/sonnet/
ModifiedAverageDeriv.lean`), where the tree's own `ell` parameter plays the role of CMP98's block
factor `L` (matching THIS file's `m`, not THIS file's `ell`) and there is no extra
line-integration factor, so THAT average is `ℓ⁻³` rather than `ℓ⁻⁴`. The two normalizations are
for two different CMP98 displays ((63) vs (125)) and are not interchangeable; nothing in the T1
identification above conflates them. -/
theorem unitToCoarseCov_card_eq_m_cubed_mul_m_eq_m_pow_four
    {ell m : ℕ} (hell : 0 < ell) {y : PeriodicLatticeSite L}
    (hy : y ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L (ell * m))
    (hdvd : ∀ μ : Fin 3, (ell * m) ∣ (L μ + 1)) :
    (AdalyFormal.Balaban.ThirdLevelArrows.unitSitesOf ell (ell * m) y).card * m = m ^ 4 := by
  rw [unitSitesOf_card_eq hell hy hdvd]
  ring

#print axioms q124Principal_eq_unitToCoarseCov_add_delta
#print axioms q124Principal_T1_eq_unitToCoarseCov
#print axioms unitToCoarseCov_card_eq_m_cubed_mul_m_eq_m_pow_four
#print axioms OneStep124.unitSitesOf_card_eq
#print axioms OneStep124.q124_eq_main_add_delta
#print axioms OneStep124.q124LM_apply

end AdalyFormal.DeltaKR85
