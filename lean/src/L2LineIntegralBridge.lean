/-
Owned file (compute/m1_si1_l18/l2/). Compiles the three equalities named by
`expand/CHANNEL_EXPANSION.md` §7 lemma L2 ("Right-trivialized line integral"), all at the stride
`ell = 1` this campaign fixes (`q124Principal 1 ell`, never `ell ell`):

1. `holonomyDirDeriv_mul_holonomy_conjTranspose_eq_lineIntegral` — for every forward list `p`,
   `holonomyDirDeriv V0 A 1 y p * (coarsePathHolonomy 1 V0 y p)ᴴ = ↑(lineIntegral 1 V0 A' y p)`,
   where `A'` is `A` (an arbitrary traceless anti-Hermitian direction field) packaged into
   `CoarseBond L 1 → SuTwo` — a genuine, at-`ell=1` fact (`coarseHolDeriv`-style adjoint bridges do
   NOT hold at general `ell`, since `lineIntegral`'s masking `dite` can be false there; at `ell=1`
   `StridedAveraging.mem_coarseLattice_one` makes it unconditionally true).
2. `dirDeriv_map_true_eq_lineIntegral` — `IngredientDeriv.dirDeriv` on the `(μ,true)`-tagged
   (i.e. `GammaPath`-shaped) forward list, at an arbitrary starting transport, computes the SAME
   `RMap`-conjugated integral — proved directly by induction generalizing the transport, not by
   restating clause 1's identity.
3. `unitToCoarseCov_one_eq_sum_blockOf` — `unitToCoarseCov 1 m` expands, by unwinding its own
   `coarseTransportPath` prefix sum, to `m⁻⁴ Σ_{x ∈ blockOf c.1.1 m} σ_x`, `σ_x` being exactly
   term3's own `RMap(treeHolonomy)(lineIntegral … x (replicate m μ))` pattern
   (`expand/CHANNEL_EXPANSION.md` §2's own naming), imported nowhere — this is what genuinely
   IDENTIFIES `unitToCoarseCov`'s definition with the paper's σ-sum, not merely restated. Uses the
   already-paid L1 clause `unitSitesOf_one_image_eq_blockOf` (imported read-only from `l1/`,
   hash-verified byte-identical in `l2/deps/`) for the block/subtype reindexing, and otherwise only
   already-paid library facts (`coarsePathHolonomy_append`, `coarsePathEndpoint_replicate`,
   `coarsePathEndpoint_coarseGammaPath`, `RMap_mul_apply`, `mem_blockOf`) — no §6 geometric-fitting
   package (`m ∣ L_μ+1`, partner bijection, mean substitutions) is invoked anywhere in this file.

Clauses 1 and 2 each also have two small corollaries (`..._conjTranspose`, `trace_..._eq_zero`)
discharging the dispatch's explicit "show its skewness and trace zero" — both inherited directly
from `lineIntegral`'s `SuTwo` (skew-Hermitian, traceless) codomain via the main equality, not fresh
computations.

None of the theorems here assumes, restates, or depends on L3–L8. No boxed SI1 claim, no
coefficient-match claim, no channel extraction, no `HasDerivAt`/differentiability claim is made
here — this file is pure algebra on already-defined recursions.
-/
import AdalyFormal.Balaban.Q1Real
import AdalyFormal.Balaban.TowerLawCovariant
import AdalyFormal.Balaban.AdmissibleSubspace
import AdalyFormal.Balaban.StridedAveraging
import AdalyFormal.Balaban.ThirdLevelArrows
import AdalyFormal.Balaban.CoarseCurl
import AdalyFormal.Balaban.QjComposite
import AdalyFormal.Balaban.LatticeOperators
import AdalyFormal.Balaban.CovariantOperators
import AdalyFormal.Balaban.SuTwoLogExpCore
import T1MainSegment
import IngredientDeriv
import RawAverageDeriv
import L1ForwardCarrier

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Matrix
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_one RMap_mul_apply RMap_coe_apply)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice blockOf mem_blockOf)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero)
open AdalyFormal.Balaban.QjComposite (coarsePathHolonomy_append coarsePathEndpoint_append
  coarsePathEndpoint_replicate coarsePathEndpoint_coarseGammaPath)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath
  coarseTransportPath unitToCoarseCov)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

/-! ## Clause 1 — `holonomyDirDeriv * (holonomy)ᴴ = lineIntegral`, at stride `1` -/

/-- Package an arbitrary traceless anti-Hermitian fine direction field into a `CoarseBond L 1 →
SuTwo` field — every site is trivially `1`-coarse (`mem_coarseLattice_one`), so no masking loss
occurs; this is CHANNEL_EXPANSION's `a ↦ a'`. -/
noncomputable def fineDirToUnitBond (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0) :
    CoarseBond L 1 → SuTwo :=
  fun b => ⟨A (b.1.1, b.2), hah (b.1.1, b.2), htr (b.1.1, b.2)⟩

theorem coe_fineDirToUnitBond (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (y : PeriodicLatticeSite L) (μ : Fin 3) :
    ((fineDirToUnitBond A hah htr (⟨y, mem_coarseLattice_one y⟩, μ) : SuTwo) : M2) = A (y, μ) := rfl

/-- **L2, clause 1.** For every forward list `p`, the right-trivialized (Maurer–Cartan) derivative
`holonomyDirDeriv V0 A 1 y p * (coarsePathHolonomy 1 V0 y p)ᴴ` is exactly the coerced line integral
`lineIntegral 1 V0 (fineDirToUnitBond A hah htr) y p`. Genuinely needs `ell = 1`: at general `ell`
`lineIntegral`'s masking `dite` can be `0` where `holonomyDirDeriv`'s matching summand is not. -/
theorem holonomyDirDeriv_mul_holonomy_conjTranspose_eq_lineIntegral
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    AdalySI1.RawAverageDeriv.holonomyDirDeriv V0 A 1 y p
        * ((coarsePathHolonomy 1 V0 y p : SU2) : M2)ᴴ
      = (OneStep124.lineIntegral 1 V0 (fineDirToUnitBond A hah htr) y p : M2) := by
  induction p generalizing y with
  | nil =>
      simp [AdalySI1.RawAverageDeriv.holonomyDirDeriv, OneStep124.lineIntegral_nil]
  | cons μ rest ih =>
      have hstep : AdalySI1.RawAverageDeriv.holonomyDirDeriv V0 A 1 y (μ :: rest)
          = A (y, μ) * (V0 (y, μ) : M2)
              * ((coarsePathHolonomy 1 V0 (coarseShift y 1 μ) rest : SU2) : M2)
            + (V0 (y, μ) : M2)
                * AdalySI1.RawAverageDeriv.holonomyDirDeriv V0 A 1 (coarseShift y 1 μ) rest := rfl
      have hhol : ((coarsePathHolonomy 1 V0 y (μ :: rest) : SU2) : M2)
          = (V0 (y, μ) : M2) * ((coarsePathHolonomy 1 V0 (coarseShift y 1 μ) rest : SU2) : M2) := by
        show ((V0 (y, μ) * coarsePathHolonomy 1 V0 (coarseShift y 1 μ) rest : SU2) : M2) = _
        rw [coe_mul]
      have hWW : ((coarsePathHolonomy 1 V0 (coarseShift y 1 μ) rest : SU2) : M2)
          * ((coarsePathHolonomy 1 V0 (coarseShift y 1 μ) rest : SU2) : M2)ᴴ = 1 :=
        AdalyFormal.Balaban.SuTwoLogExp.mul_star_self _
      have hgg : (V0 (y, μ) : M2) * (V0 (y, μ) : M2)ᴴ = 1 :=
        AdalyFormal.Balaban.SuTwoLogExp.mul_star_self _
      have hIH := ih (coarseShift y 1 μ)
      have hterm1 : A (y, μ) * (V0 (y, μ) : M2)
            * (((coarsePathHolonomy 1 V0 (coarseShift y 1 μ) rest : SU2) : M2)
                * ((coarsePathHolonomy 1 V0 (coarseShift y 1 μ) rest : SU2) : M2)ᴴ)
            * (V0 (y, μ) : M2)ᴴ
          = A (y, μ) := by
        rw [hWW, mul_one, mul_assoc, hgg, mul_one]
      have hterm2 : (V0 (y, μ) : M2)
            * (AdalySI1.RawAverageDeriv.holonomyDirDeriv V0 A 1 (coarseShift y 1 μ) rest
                * ((coarsePathHolonomy 1 V0 (coarseShift y 1 μ) rest : SU2) : M2)ᴴ)
            * (V0 (y, μ) : M2)ᴴ
          = (V0 (y, μ) : M2)
              * (OneStep124.lineIntegral 1 V0 (fineDirToUnitBond A hah htr)
                  (coarseShift y 1 μ) rest : M2)
              * (V0 (y, μ) : M2)ᴴ := by
        rw [hIH]
      have hexpand :
          (A (y, μ) * (V0 (y, μ) : M2)
                * ((coarsePathHolonomy 1 V0 (coarseShift y 1 μ) rest : SU2) : M2)
              + (V0 (y, μ) : M2)
                  * AdalySI1.RawAverageDeriv.holonomyDirDeriv V0 A 1 (coarseShift y 1 μ) rest)
            * (((coarsePathHolonomy 1 V0 (coarseShift y 1 μ) rest : SU2) : M2)ᴴ
                * (V0 (y, μ) : M2)ᴴ)
          = A (y, μ) * (V0 (y, μ) : M2)
              * (((coarsePathHolonomy 1 V0 (coarseShift y 1 μ) rest : SU2) : M2)
                  * ((coarsePathHolonomy 1 V0 (coarseShift y 1 μ) rest : SU2) : M2)ᴴ)
              * (V0 (y, μ) : M2)ᴴ
            + (V0 (y, μ) : M2)
                * (AdalySI1.RawAverageDeriv.holonomyDirDeriv V0 A 1 (coarseShift y 1 μ) rest
                    * ((coarsePathHolonomy 1 V0 (coarseShift y 1 μ) rest : SU2) : M2)ᴴ)
                * (V0 (y, μ) : M2)ᴴ := by noncomm_ring
      rw [hstep, hhol, Matrix.conjTranspose_mul, hexpand, hterm1, hterm2]
      rw [OneStep124.lineIntegral_cons, dif_pos (mem_coarseLattice_one y),
        Submodule.coe_add, coe_fineDirToUnitBond, RMap_coe_apply]

#print axioms holonomyDirDeriv_mul_holonomy_conjTranspose_eq_lineIntegral

/-- **Skewness**, named explicitly per the dispatch ("show its skewness and trace zero"): the raw
right-trivialized derivative is anti-Hermitian, inherited from `lineIntegral`'s `SuTwo` codomain
via clause 1 — not a fresh computation. -/
theorem holonomyDirDeriv_mul_holonomy_conjTranspose_conjTranspose
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    (AdalySI1.RawAverageDeriv.holonomyDirDeriv V0 A 1 y p
        * ((coarsePathHolonomy 1 V0 y p : SU2) : M2)ᴴ)ᴴ
      = -(AdalySI1.RawAverageDeriv.holonomyDirDeriv V0 A 1 y p
        * ((coarsePathHolonomy 1 V0 y p : SU2) : M2)ᴴ) := by
  rw [holonomyDirDeriv_mul_holonomy_conjTranspose_eq_lineIntegral]
  exact (OneStep124.lineIntegral 1 V0 (fineDirToUnitBond A hah htr) y p).2.1

/-- **Trace zero**, the other half of the dispatch's request, likewise inherited from
`lineIntegral`'s `SuTwo` codomain via clause 1. -/
theorem trace_holonomyDirDeriv_mul_holonomy_conjTranspose_eq_zero
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    Matrix.trace (AdalySI1.RawAverageDeriv.holonomyDirDeriv V0 A 1 y p
        * ((coarsePathHolonomy 1 V0 y p : SU2) : M2)ᴴ) = 0 := by
  rw [holonomyDirDeriv_mul_holonomy_conjTranspose_eq_lineIntegral]
  exact (OneStep124.lineIntegral 1 V0 (fineDirToUnitBond A hah htr) y p).2.2

#print axioms holonomyDirDeriv_mul_holonomy_conjTranspose_conjTranspose
#print axioms trace_holonomyDirDeriv_mul_holonomy_conjTranspose_eq_zero

/-! ## Clause 2 — `dirDeriv` on the `(μ,true)`-mapped forward list -/

theorem periodicLatticeStep_true_eq_coarseShift_one (y : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicLatticeStep y (μ, true) = coarseShift y 1 μ := by
  show Function.update y μ (if True then y μ + 1 else y μ - 1) = (fun z => periodicLatticeShift z μ)^[1] y
  rw [if_pos trivial, Function.iterate_one]
  rfl

/-- **L2, clause 2.** `IngredientDeriv.dirDeriv` on the `GammaPath`-shaped `(μ,true)`-tagged
mapped forward list computes the SAME `RMap`-conjugated integral as clause 1, for an ARBITRARY
starting transport (generalized so the induction closes; setting `transport := 1` is the case
the dispatch names). -/
theorem dirDeriv_map_true_eq_lineIntegral
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) (transport : SU2) :
    AdalySI1.IngredientDeriv.dirDeriv V0 A y (p.map (fun μ => (μ, true))) transport
      = (RMap transport (OneStep124.lineIntegral 1 V0 (fineDirToUnitBond A hah htr) y p) : M2) := by
  induction p generalizing y transport with
  | nil => simp [AdalySI1.IngredientDeriv.dirDeriv, OneStep124.lineIntegral_nil]
  | cons μ rest ih =>
      rw [List.map_cons]
      have hstep : AdalySI1.IngredientDeriv.dirDeriv V0 A y ((μ, true) :: rest.map (fun μ => (μ, true))) transport
          = AdalyFormal.Balaban.SuTwoLogExp.adMap transport (A (y, μ))
            + AdalySI1.IngredientDeriv.dirDeriv V0 A (periodicLatticeStep y (μ, true))
                (rest.map (fun μ => (μ, true))) (transport * V0 (y, μ)) := rfl
      rw [hstep, periodicLatticeStep_true_eq_coarseShift_one,
        ih (coarseShift y 1 μ) (transport * V0 (y, μ)), ← RMap_mul_apply]
      rw [OneStep124.lineIntegral_cons, dif_pos (mem_coarseLattice_one y), map_add,
        Submodule.coe_add]
      simp only [RMap_coe_apply]
      rw [coe_fineDirToUnitBond, AdalyFormal.Balaban.SuTwoLogExp.adMap_apply]

#print axioms dirDeriv_map_true_eq_lineIntegral

/-- Corollary: the dispatch's own phrasing, `transport := 1`. -/
theorem dirDeriv_map_true_one_eq_lineIntegral
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    AdalySI1.IngredientDeriv.dirDeriv V0 A y (p.map (fun μ => (μ, true))) 1
      = (OneStep124.lineIntegral 1 V0 (fineDirToUnitBond A hah htr) y p : M2) := by
  rw [dirDeriv_map_true_eq_lineIntegral V0 A hah htr y p 1, RMap_one]
  rfl

#print axioms dirDeriv_map_true_one_eq_lineIntegral

/-- **Skewness**, `dirDeriv` side (dispatch's other named object), at `transport := 1`. -/
theorem dirDeriv_map_true_one_conjTranspose
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    (AdalySI1.IngredientDeriv.dirDeriv V0 A y (p.map (fun μ => (μ, true))) 1)ᴴ
      = -(AdalySI1.IngredientDeriv.dirDeriv V0 A y (p.map (fun μ => (μ, true))) 1) := by
  rw [dirDeriv_map_true_one_eq_lineIntegral]
  exact (OneStep124.lineIntegral 1 V0 (fineDirToUnitBond A hah htr) y p).2.1

/-- **Trace zero**, `dirDeriv` side, at `transport := 1`. -/
theorem trace_dirDeriv_map_true_one_eq_zero
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    Matrix.trace (AdalySI1.IngredientDeriv.dirDeriv V0 A y (p.map (fun μ => (μ, true))) 1) = 0 := by
  rw [dirDeriv_map_true_one_eq_lineIntegral]
  exact (OneStep124.lineIntegral 1 V0 (fineDirToUnitBond A hah htr) y p).2.2

#print axioms dirDeriv_map_true_one_conjTranspose
#print axioms trace_dirDeriv_map_true_one_eq_zero

/-! ## Clause 3 — `unitToCoarseCov 1 m = m⁻⁴ Σ σ_x`, expanding its own prefix sum -/

/-- The inner double sum's `i`-prefix, at a FIXED base, IS `lineIntegral` on the replicated
direction list — the genuine "expand the prefix sum" content, proved by growing `replicate` from
the FAR end (matching `lineIntegral_append`'s own recursion, so no site re-indexing is needed). -/
theorem lineIntegral_replicate_eq_sum_range (ell : ℕ)
    (V : PeriodicLinkConfiguration SU2 L) (B : CoarseBond L ell → SuTwo)
    (y : PeriodicLatticeSite L) (μ : Fin 3) (m : ℕ) :
    OneStep124.lineIntegral ell V B y (List.replicate m μ)
      = ∑ i ∈ Finset.range m,
          if h : pathSite y μ (i * ell) ∈ CoarseLattice L ell then
            RMap (coarsePathHolonomy ell V y (List.replicate i μ))
              (B (⟨pathSite y μ (i * ell), h⟩, μ))
          else 0 := by
  induction m with
  | zero => simp [OneStep124.lineIntegral_nil]
  | succ n ih =>
      rw [List.replicate_succ', OneStep124.lineIntegral_append, ih, Finset.sum_range_succ,
        coarsePathEndpoint_replicate]
      congr 1
      rw [OneStep124.lineIntegral_cons, OneStep124.lineIntegral_nil, map_zero, add_zero,
        Nat.mul_comm ell n]
      split_ifs with h
      · rfl
      · exact map_zero _

#print axioms lineIntegral_replicate_eq_sum_range

/-- **L2, clause 3.** `unitToCoarseCov 1 m` expands to `m⁻⁴ Σ_{x ∈ blockOf c.1.1 m} σ_x`, `σ_x`
being exactly term3's own `RMap(treeHolonomy)(lineIntegral 1 V B x (replicate m c.2))` pattern —
IDENTIFYING the code definition with the paper's σ-sum, no §6 fitting hypothesis used. -/
theorem unitToCoarseCov_one_eq_sum_blockOf (m : ℕ)
    (V : PeriodicLinkConfiguration SU2 L) (B : CoarseBond L 1 → SuTwo)
    (c : CoarseBond L (1 * m)) :
    unitToCoarseCov 1 m V B c
      = (1 / (m : ℝ) ^ 4) • ∑ x ∈ blockOf c.1.1 m,
          RMap (coarsePathHolonomy 1 V c.1.1 (coarseGammaPath 1 c.1.1 x))
            (OneStep124.lineIntegral 1 V B x (List.replicate m c.2)) := by
  unfold unitToCoarseCov
  have hpointwise : ∀ u ∈ unitSitesOf 1 (1 * m) c.1.1,
      (∑ i ∈ Finset.range m,
        if h : pathSite u.1 c.2 (i * 1) ∈ CoarseLattice L 1 then
          RMap (coarsePathHolonomy 1 V c.1.1 (coarseTransportPath 1 c.1.1 u.1 c.2 i))
            (B (⟨pathSite u.1 c.2 (i * 1), h⟩, c.2))
        else 0)
      = RMap (coarsePathHolonomy 1 V c.1.1 (coarseGammaPath 1 c.1.1 u.1))
          (OneStep124.lineIntegral 1 V B u.1 (List.replicate m c.2)) := by
    intro u hu
    have h1 : u.1 ∈ blockOf c.1.1 (1 * m) := (Finset.mem_filter.mp hu).2
    have hord : ∀ ν : Fin 3, (c.1.1 ν).val ≤ (u.1 ν).val ∧ (1 : ℕ) ∣ ((u.1 ν).val - (c.1.1 ν).val) :=
      fun ν => ⟨(mem_blockOf.mp h1 ν).1, one_dvd _⟩
    have hend : coarsePathEndpoint 1 c.1.1 (coarseGammaPath 1 c.1.1 u.1) = u.1 :=
      coarsePathEndpoint_coarseGammaPath hord
    have hstep : ∀ i : ℕ,
        coarsePathHolonomy 1 V c.1.1 (coarseTransportPath 1 c.1.1 u.1 c.2 i)
          = coarsePathHolonomy 1 V c.1.1 (coarseGammaPath 1 c.1.1 u.1)
              * coarsePathHolonomy 1 V u.1 (List.replicate i c.2) := by
      intro i
      show coarsePathHolonomy 1 V c.1.1 (coarseGammaPath 1 c.1.1 u.1 ++ List.replicate i c.2) = _
      rw [coarsePathHolonomy_append, hend]
    have hcond : ∀ i : ℕ, pathSite u.1 c.2 (i * 1) ∈ CoarseLattice L 1 :=
      fun i => mem_coarseLattice_one _
    simp only [dif_pos (hcond _)]
    rw [show (∑ i ∈ Finset.range m, RMap (coarsePathHolonomy 1 V c.1.1
            (coarseTransportPath 1 c.1.1 u.1 c.2 i)) (B (⟨pathSite u.1 c.2 (i * 1), hcond i⟩, c.2)))
        = ∑ i ∈ Finset.range m, RMap (coarsePathHolonomy 1 V c.1.1 (coarseGammaPath 1 c.1.1 u.1))
            (RMap (coarsePathHolonomy 1 V u.1 (List.replicate i c.2))
              (B (⟨pathSite u.1 c.2 (i * 1), hcond i⟩, c.2))) from
      Finset.sum_congr rfl (fun i _ => by rw [hstep i, RMap_mul_apply]),
      ← map_sum]
    congr 1
    rw [lineIntegral_replicate_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => by rw [dif_pos (hcond i)])
  rw [Finset.sum_congr rfl hpointwise, ← unitSitesOf_one_image_eq_blockOf c.1.1 m,
    Finset.sum_image (fun a _ b _ h => Subtype.ext h)]

#print axioms unitToCoarseCov_one_eq_sum_blockOf
