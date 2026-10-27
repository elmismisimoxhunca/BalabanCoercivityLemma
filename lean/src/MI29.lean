import MI18
import DLR31

/-!
# MI29 -- the genuine bond `Q = QfullOf` on a PROPER tower: row locality, row norm, row alignment (M1 lane E, 2026-10-13)

`G = geomOf ell k S` on `scaleUp ell k Lu`; rows `p = (j, c)` at every level `j ≤ k` (not only `k`, as in the full-tower
DLR30).  Under the M0-chain tower hypotheses on the blocked background (`RegTower`, `TowerClass ε`, `ρ(ε_i) < π/2`,
`ε_i ≥ 0` — the same objects DLR30/BC5 use; `bgTower G U` depends on `G` only through `G.ell`):
* `Qrow_local` / `Qrow_restr` : row `p` of `Q` reads only `Foot ℓ j c` (DL28 `QlinCompX_row_local`, any `j ≤ k`);
* `row_aligned` : the base site of a level-`j` row is on the `ℓ^j`-lattice;
* **`Qrow_norm`** : `‖(Q y)(p)‖ ≤ ℓ^{-j} · r^j e^{S/r} · ‖y‖` (`r = ℓ^{-1/2}`, `S = Σ_{i<k} θ(ε_i)`; BC5 `tower_FG` at level `j`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.DLayer (Foot QlinCompX_row_local bondRestr suOf_zero suCoord_zero_of Reach Rfoot Foot_reach Rfoot_le
  card_reach_coarse_le Reach_trans Reach_coarseShift Reach_refl)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.NonflatJet (suOf rhoOf)
open AdalyFormal.BondComposite (Qfull_apply_level nrm nrm_sq nrm_nonneg rr nrm_one_suCoord tower_FG TowerClass thetaOf
  thetaOf_nonneg hdvd_scaleUp)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)

section rows
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- row locality of `Q` on `geomOf` (any level). -/
theorem Qrow_local (U : Cfg (scaleUp ell k Lu)) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (x : BondFnL2 (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S))
    (hx : ∀ b, Foot ell (p.1 : ℕ) p.2.1 b → x b = 0) :
    (bondSectorOf (geomOf ell k S) U).Qfull x p = 0 := by
  have hreg' : RegTower (geomOf ell k S).ell (bgTower (geomOf ell k S) U) (geomOf ell k S).k := hreg
  rw [Qfull_apply_level ell k Lu (geomOf ell k S) U hreg' x p]
  have hj : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  have h0 := QlinCompX_row_local ell (bgTower (geomOf ell k S) U) k hreg' (p.1 : ℕ) hj p.2.1 (suCoord x)
    (fun e he => suCoord_zero_of x e (hx e he))
  show (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) • suOf (QlinCompX ell (bgTower (geomOf ell k S) U) p.1 (suCoord x) p.2.1) = 0
  rw [h0, suOf_zero, smul_zero]

open Classical in
theorem Qrow_restr (U : Cfg (scaleUp ell k Lu)) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (y : BondFnL2 (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) :
    (bondSectorOf (geomOf ell k S) U).Qfull y p
      = (bondSectorOf (geomOf ell k S) U).Qfull (bondRestr (Foot ell (p.1 : ℕ) p.2.1) y) p := by
  have h0 := Qrow_local U hreg (y - bondRestr (Foot ell (p.1 : ℕ) p.2.1) y) p (fun b hb => by
    show y b - (if Foot ell (p.1 : ℕ) p.2.1 b then y b else 0) = 0
    rw [if_pos hb, sub_self])
  rw [map_sub, PiLp.sub_apply, sub_eq_zero] at h0
  exact h0

/-- the base site of a level-`j` row is aligned. -/
theorem row_aligned (hell : 0 < ell) (p : BIdx (geomOf ell k S)) :
    p.2.1.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (p.1 : ℕ)) := by
  have hj : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  have hb : p.2.1.1 ∈ (geomOf ell k S).Lam (p.1 : ℕ) ∨
      coarseShift p.2.1.1 ((geomOf ell k S).ell ^ (p.1 : ℕ)) p.2.1.2 ∈ (geomOf ell k S).Lam (p.1 : ℕ) := p.2.2.1
  rw [mem_CoarseLattice]
  intro ν
  rcases hb with h | h
  · exact Nat.mod_eq_zero_of_dvd (h.1 ν)
  · have hz := h.1 ν
    by_cases hν : ν = p.2.1.2
    · rw [hν] at hz ⊢
      rw [show (geomOf ell k S).ell = ell from rfl, coarseShift_val_eq] at hz
      have hN : ell ^ (p.1 : ℕ) ∣ scaleUp ell k Lu p.2.1.2 + 1 := hdvd_scaleUp ell k Lu hell _ hj _
      have h1 := (Nat.dvd_mod_iff hN).mp hz
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add_self_right.mp h1)
    · rw [show (geomOf ell k S).ell = ell from rfl, coarseShift_apply_ne _ _ _ ν hν] at hz
      exact Nat.mod_eq_zero_of_dvd hz

/-- the tower constant `e^{S/r}`. -/
noncomputable def EQ (ell k : ℕ) (ε : ℕ → ℝ) : ℝ := Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell)

theorem EQ_pos (ell k : ℕ) (ε : ℕ → ℝ) : 0 < EQ ell k ε := Real.exp_pos _

/-- **row norm of `Q` on a proper tower**. -/
theorem Qrow_norm (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (y : BondFnL2 (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) :
    ‖(bondSectorOf (geomOf ell k S) U).Qfull y p‖
      ≤ ((ell : ℝ) ^ (p.1 : ℕ))⁻¹ * ((rr ell) ^ (p.1 : ℕ) * EQ ell k ε) * ‖y‖ := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hreg' : RegTower (geomOf ell k S).ell (bgTower (geomOf ell k S) U) (geomOf ell k S).k := hreg
  have hj : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  rw [Qfull_apply_level ell k Lu (geomOf ell k S) U hreg' y p]
  set Z := QlinCompX ell (bgTower (GF ell k Lu) U) (p.1 : ℕ) (suCoord y) with hZ
  show ‖(((ell : ℝ) ^ (p.1 : ℕ))⁻¹) • suOf (Z p.2.1)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (pow_pos hellR _)]
  -- one row against the level-`j` sum
  have hc : p.2.1.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (p.1 : ℕ)) := row_aligned hell p
  have h1 : ‖suOf (Z p.2.1)‖ ≤ nrm (ell ^ (p.1 : ℕ)) Z := by
    have hsq : ‖suOf (Z p.2.1)‖ ^ 2 ≤ nrm (ell ^ (p.1 : ℕ)) Z ^ 2 := by
      rw [nrm_sq]
      have := Finset.single_le_sum (f := fun c : CoarseBond (scaleUp ell k Lu) (ell ^ (p.1 : ℕ)) =>
        ‖suOf (Z (c.1.1, c.2))‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ (⟨p.2.1.1, hc⟩, p.2.1.2))
      exact this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (nrm_nonneg _ _) two_ne_zero).mp hsq
  have hFG := (tower_FG ell k Lu hell U ε hreg hcl hε0 hsm (suCoord y) (p.1 : ℕ) hj).1
  rw [nrm_one_suCoord] at hFG
  have hS : (∑ i ∈ Finset.range (p.1 : ℕ), thetaOf ell (ε i)) ≤ ∑ i ∈ Finset.range k, thetaOf ell (ε i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
      (fun i hi _ => thetaOf_nonneg ell (ε i) (hε0 i (Finset.mem_range.mp hi)))
  have hr : 0 < rr ell := Real.sqrt_pos.mpr (by positivity)
  have hE : Real.exp ((∑ i ∈ Finset.range (p.1 : ℕ), thetaOf ell (ε i)) / rr ell) ≤ EQ ell k ε :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hS hr.le)
  have hrj : 0 ≤ (rr ell) ^ (p.1 : ℕ) := pow_nonneg hr.le _
  have h2 : nrm (ell ^ (p.1 : ℕ)) Z ≤ (rr ell) ^ (p.1 : ℕ) * EQ ell k ε * ‖y‖ :=
    hFG.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hrj) (norm_nonneg _))
  have hinv : (0 : ℝ) ≤ ((ell : ℝ) ^ (p.1 : ℕ))⁻¹ := by positivity
  calc ((ell : ℝ) ^ (p.1 : ℕ))⁻¹ * ‖suOf (Z p.2.1)‖
      ≤ ((ell : ℝ) ^ (p.1 : ℕ))⁻¹ * ((rr ell) ^ (p.1 : ℕ) * EQ ell k ε * ‖y‖) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hinv
    _ = _ := by ring

end rows

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.Qrow_local
#print axioms AdalyFormal.M1IMS.Qrow_restr
#print axioms AdalyFormal.M1IMS.row_aligned
#print axioms AdalyFormal.M1IMS.EQ
#print axioms AdalyFormal.M1IMS.Qrow_norm
#print axioms AdalyFormal.M1IMS.EQ_pos
