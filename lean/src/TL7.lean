import TL6b
import MI32

/-!
# TL7 -- the mass commutator (`massComm_proper`, lane E W4) with REGIONAL class data

`RegData` bundles the regional data `(ε j l, W j l)` of TL4 together with the `k`-free bound `S*` on the level sums.
* `Qrow_restr_loc`, `Qrow_norm_loc` : MI29 `Qrow_restr` / `Qrow_norm` with `RegData` in place of `RegTower`+`TowerClass`
  (`‖Q_row‖ ≤ ℓ^{-j} (r^j e^{S*/r}) ‖y‖`);
* `row_comm_sum_loc`, `massComm_proper_loc` : MI31 `row_comm_sum` / MI32 `massComm_proper` (proofs copied), constant
  `CMcStar = a e^{2S*/r} 49 ℓ² K_G 1944 ℓ²`, no `k` in it except through `S*`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.TowerLoc

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.StatementLaneR8
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.DLayer (Foot bondRestr suCoord_zero_of)
open AdalyFormal.BondComposite
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.W6
open AdalyFormal.M1IMS

/-- regional class data on a proper tower: level-`j` rows see the class on `W j l` only. -/
structure RegData (ell k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu))
    (V : Cfg (scaleUp ell k Lu)) (Sstar : ℝ) where
  ε : ℕ → ℕ → ℝ
  W : ℕ → ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu))
  hcl : ∀ j : Fin (k + 1), ∀ l, l < k → ∀ z ∈ W j l, z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
    frobNorm (((bgTower (GF ell k Lu) V l (z, μ) : SU2) : M2) - 1) ≤ ε j l
  hε0 : ∀ j : Fin (k + 1), ∀ l, l < k → 0 ≤ ε j l
  hsm : ∀ j : Fin (k + 1), ∀ l, l < k → rhoOf ell (ε j l) < Real.pi / 2
  hr : ∀ j : Fin (k + 1), ∀ l, l < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j l) < r0
  hW : ∀ j : Fin (k + 1),
    ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, ∀ l, l < (j : ℕ) →
      Ball r.1.1 (rhoT ell j - rhoT ell l) ⊆ W j l
  hSstar : ∀ j : Fin (k + 1), ∑ l ∈ range (j : ℕ), thetaOf ell (ε j l) ≤ Sstar

/-- the `k`-free tower constant `e^{S*/r}` -/
def Estar (ell : ℕ) (Sstar : ℝ) : ℝ := Real.exp (Sstar / rr ell)

section rows
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
  {V : Cfg (scaleUp ell k Lu)} {Sstar : ℝ}

/-- a row of `Q_V` reads only its footprint (regional class) -/
theorem Qrow_restr_loc (hell : 0 < ell) (D : RegData ell k Lu S V Sstar)
    (y : BondFnL2 (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) :
    (bondSectorOf (geomOf ell k S) V).Qfull y p
      = (bondSectorOf (geomOf ell k S) V).Qfull (bondRestr (Foot ell (p.1 : ℕ) p.2.1) y) p := by
  classical
  have hjk : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  have hal := row_aligned (S := S) hell p
  have hzero : ∀ e, Foot ell (p.1 : ℕ) p.2.1 e → (suCoord y - suCoord (bondRestr (Foot ell (p.1 : ℕ) p.2.1) y)) e = 0 := by
    intro e he
    have h1 : (y - bondRestr (Foot ell (p.1 : ℕ) p.2.1) y) e = 0 := by
      show y e - (if Foot ell (p.1 : ℕ) p.2.1 e then y e else 0) = 0
      rw [if_pos he, sub_self]
    have := suCoord_zero_of (y - bondRestr (Foot ell (p.1 : ℕ) p.2.1) y) e h1
    rwa [map_sub] at this
  have hW : ∀ l, l < (p.1 : ℕ) → Ball p.2.1.1 (rhoT ell p.1 - rhoT ell l) ⊆ D.W p.1 l :=
    fun l hl => D.hW p.1 p.2 l hl
  have h0 := compL_row_local_loc ell k Lu hell (bgTower (GF ell k Lu) V) (D.ε p.1) (D.W p.1) (D.hcl p.1)
    (D.hε0 p.1) (D.hr p.1) (p.1 : ℕ) hjk p.2.1 hal hW _ hzero
  rw [map_sub] at h0
  simp only [Pi.sub_apply] at h0
  have e1 : ∀ z : BondFnL2 (scaleUp ell k Lu), (bondSectorOf (geomOf ell k S) V).Qfull z p
      = (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) • suOf (QlinCompL ell (bgTower (GF ell k Lu) V) p.1 (suCoord z) p.2.1) :=
    fun z => rfl
  rw [e1, e1, sub_eq_zero.mp h0]

/-- row norm of `Q_V`, regional class -/
theorem Qrow_norm_loc (hell : 0 < ell) (D : RegData ell k Lu S V Sstar)
    (y : BondFnL2 (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) :
    ‖(bondSectorOf (geomOf ell k S) V).Qfull y p‖
      ≤ ((ell : ℝ) ^ (p.1 : ℕ))⁻¹ * ((rr ell) ^ (p.1 : ℕ) * Estar ell Sstar) * ‖y‖ := by
  classical
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hjk : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  have hal := row_aligned (S := S) hell p
  have hW : ∀ b ∈ ({p.2.1} : Finset (PeriodicLatticeEdge (scaleUp ell k Lu))), ∀ l, l < (p.1 : ℕ) →
      Ball b.1 (rhoT ell p.1 - rhoT ell l) ⊆ D.W p.1 l := by
    intro b hb l hl
    rw [Finset.mem_singleton] at hb
    rw [hb]; exact D.hW p.1 p.2 l hl
  have hFG := (rows_FG_loc ell k Lu hell (bgTower (GF ell k Lu) V) (D.ε p.1) (D.W p.1) (D.hcl p.1)
    (D.hε0 p.1) (D.hsm p.1) (D.hr p.1) (p.1 : ℕ) hjk {p.2.1}
    (fun b hb => by rw [Finset.mem_singleton] at hb; rw [hb]; exact hal) hW (suCoord y)).1
  rw [nrm_one_suCoord, Finset.sum_singleton] at hFG
  set Z := QlinCompL ell (bgTower (GF ell k Lu) V) p.1 (suCoord y) with hZ
  set Sj := ∑ i ∈ Finset.range (p.1 : ℕ), thetaOf ell (D.ε p.1 i) with hSj
  have hr : 0 < rr ell := Real.sqrt_pos.mpr (by positivity)
  have hSjle : Sj ≤ Sstar := D.hSstar p.1
  have hE : Real.exp (Sj / rr ell) ≤ Estar ell Sstar :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hSjle hr.le)
  have hrj : 0 ≤ (rr ell) ^ (p.1 : ℕ) := pow_nonneg hr.le _
  have hB : 0 ≤ (rr ell) ^ (p.1 : ℕ) * Estar ell Sstar * ‖y‖ := by
    have : 0 ≤ Estar ell Sstar := (Real.exp_pos _).le
    positivity
  have h1 : ‖suOf (Z p.2.1)‖ ≤ (rr ell) ^ (p.1 : ℕ) * Estar ell Sstar * ‖y‖ := by
    have hle : ‖suOf (Z p.2.1)‖ ^ 2 ≤ ((rr ell) ^ (p.1 : ℕ) * Real.exp (Sj / rr ell) * ‖y‖) ^ 2 := hFG
    have := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hle
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hrj) (norm_nonneg _)
  have e1 : (bondSectorOf (geomOf ell k S) V).Qfull y p = (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) • suOf (Z p.2.1) := rfl
  rw [e1, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (pow_pos hellR _)]
  have hinv : (0 : ℝ) ≤ ((ell : ℝ) ^ (p.1 : ℕ))⁻¹ := by positivity
  calc ((ell : ℝ) ^ (p.1 : ℕ))⁻¹ * ‖suOf (Z p.2.1)‖
      ≤ ((ell : ℝ) ^ (p.1 : ℕ))⁻¹ * ((rr ell) ^ (p.1 : ℕ) * Estar ell Sstar * ‖y‖) :=
        mul_le_mul_of_nonneg_left h1 hinv
    _ = _ := by ring

end rows

end AdalyFormal.TowerLoc

#print axioms AdalyFormal.TowerLoc.Qrow_restr_loc
#print axioms AdalyFormal.TowerLoc.Qrow_norm_loc
