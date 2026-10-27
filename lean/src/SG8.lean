import SG7
import TL9

/-!
# SG8 -- row-local mass commutator: `RowQ`, and `MassComm` from per-row data (lane m2_fields123_20261015)

`RowQ U p S*` : the two properties of the row `p` of `Q_U` that `TL8.row_comm_sum_loc` consumes from `RegData` (via `Qrow_restr_loc`, `Qrow_norm_loc`):
the row reads only its footprint, and its norm bound with the `k`-free constant `ℓ^{-j} (rr^j E*)`.
* `row_comm_sum_row` / `massComm_of_rowQ` : the proofs of `row_comm_sum_loc` / `massComm_proper_loc` with `RegData` replaced by `∀ p, RowQ U p S*` (text-copied, the
  only two uses of `D` replaced by the two `RowQ` fields).
* `RowQ_of_RegData` ; `RowQ_gauge` (`RowQ (U^γ) p ⇒ RowQ U p`: `QfullOf_gauge`) ; `Qfull_row_congr` (row value depends on `U` only through `AgreeAt` on a ball: `compL_cut`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.M2F123

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.DLayer (Foot Reach Rfoot Foot_reach Rfoot_le card_reach_coarse_le bondRestr bondWt bondWt_apply)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (Tower Admissible scaleUp bigSide pdist)
open AdalyFormal.NonflatJet (rhoOf)
open AdalyFormal.BondComposite (rr TowerClass hdvd_scaleUp sum_le_of_injective)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.W6
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc

/-- the two row-`p` properties of `Q_U` that the mass commutator bound uses -/
def RowQ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (U : Cfg (scaleUp ell k Lu)) (Sstar : ℝ)
    (p : BIdx (geomOf ell k S)) : Prop :=
  (∀ y : BondFnL2 (scaleUp ell k Lu), (bondSectorOf (geomOf ell k S) U).Qfull y p
      = (bondSectorOf (geomOf ell k S) U).Qfull (bondRestr (Foot ell (p.1 : ℕ) p.2.1) y) p) ∧
  (∀ y : BondFnL2 (scaleUp ell k Lu), ‖(bondSectorOf (geomOf ell k S) U).Qfull y p‖
      ≤ ((ell : ℝ) ^ (p.1 : ℕ))⁻¹ * ((rr ell) ^ (p.1 : ℕ) * Estar ell Sstar) * ‖y‖)

theorem RowQ_of_RegData {ell k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {U : Cfg (scaleUp ell k Lu)}
    {Sstar : ℝ} (hell : 0 < ell) (D : RegData ell k Lu S U Sstar) (p : BIdx (geomOf ell k S)) : RowQ ell k Lu S U Sstar p :=
  ⟨fun y => Qrow_restr_loc hell D y p, fun y => Qrow_norm_loc hell D y p⟩

section mass
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c)

include hS hκ hM hell hR1 hR hc in
open Classical in
/-- **the per-row commutator sum**. -/
theorem row_comm_sum_row (U : Cfg (scaleUp ell k Lu)) (Sstar : ℝ) (a : ℝ) (ha : 0 ≤ a)
    (A : BondFnL2 (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) (hQ : RowQ ell k Lu S U Sstar p) :
    ∑ i, ‖(rowMul (geomOf ell k S) (hrow ell M k κ c S i) (Ymass (geomOf ell k S) U a A)
      - Ymass (geomOf ell k S) U a (bondMul (hbond ell M k κ c S i) A)) p‖ ^ 2
      ≤ a * Estar ell Sstar ^ 2 * (49 * (ell : ℝ) ^ 2 * KG ell M κ c)
        * ((((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 * ∑ e, (if Foot ell (p.1 : ℕ) p.2.1 e then ‖A e‖ ^ 2 else 0)) := by
  have hell0 : 0 < ell := by omega
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell0
  set j : ℕ := (p.1 : ℕ) with hj
  have hmw : massW (geomOf ell k S) a p = a * (ell : ℝ) ^ j := rfl
  have hmw0 : 0 ≤ massW (geomOf ell k S) a p := by rw [hmw]; positivity
  set C := ((ell : ℝ) ^ j)⁻¹ * ((rr ell) ^ j * Estar ell Sstar) with hC
  have hC0 : 0 ≤ C := by have : 0 ≤ Estar ell Sstar := (Real.exp_pos _).le; have : 0 ≤ rr ell := Real.sqrt_nonneg _; positivity
  -- per `i`
  have hi : ∀ i, ‖(rowMul (geomOf ell k S) (hrow ell M k κ c S i) (Ymass (geomOf ell k S) U a A)
      - Ymass (geomOf ell k S) U a (bondMul (hbond ell M k κ c S i) A)) p‖ ^ 2
      ≤ massW (geomOf ell k S) a p * C ^ 2
        * ∑ e, (if Foot ell j p.2.1 e then (hbond ell M k κ c S i e - hrow ell M k κ c S i p) ^ 2 * ‖A e‖ ^ 2 else 0) := by
    intro i
    rw [row_comm_eq U a A i p, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hmw0, hQ.1]
    have h1 := hQ.2
      (bondRestr (Foot ell j p.2.1) (bondMul (fun e => hbond ell M k κ c S i e - hrow ell M k κ c S i p) A))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, norm_restr_bondMul_sq] at h2
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 hmw0
  refine (Finset.sum_le_sum (fun i _ => hi i)).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  -- swap and oscillation
  have hosc : ∑ e, ∑ i, (if Foot ell j p.2.1 e then (hbond ell M k κ c S i e - hrow ell M k κ c S i p) ^ 2 * ‖A e‖ ^ 2 else 0)
      ≤ ∑ e, (if Foot ell j p.2.1 e then (49 * (ell : ℝ) ^ 2 * KG ell M κ c) * ‖A e‖ ^ 2 else 0) := by
    refine Finset.sum_le_sum (fun e _ => ?_)
    split_ifs with he
    · rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (osc_foot hS hκ hM hell hR1 hR hc p e he) (sq_nonneg _)
    · simp
  have hpull : ∑ e, (if Foot ell j p.2.1 e then (49 * (ell : ℝ) ^ 2 * KG ell M κ c) * ‖A e‖ ^ 2 else 0)
      = (49 * (ell : ℝ) ^ 2 * KG ell M κ c) * ∑ e, (if Foot ell j p.2.1 e then ‖A e‖ ^ 2 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    split_ifs <;> ring
  have hCsq : massW (geomOf ell k S) a p * C ^ 2 = a * Estar ell Sstar ^ 2 * (((ell : ℝ) ^ j)⁻¹) ^ 2 := by
    have hr2 : (rr ell) ^ 2 = (ell : ℝ)⁻¹ := by
      unfold rr; rw [Real.sq_sqrt (by positivity), one_div]
    have hrj : ((rr ell) ^ j) ^ 2 = ((ell : ℝ) ^ j)⁻¹ := by
      rw [← pow_mul, mul_comm, pow_mul, hr2, inv_pow]
    have hpos : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
    rw [hmw, hC, mul_pow, mul_pow, hrj]
    field_simp
  calc massW (geomOf ell k S) a p * C ^ 2
        * ∑ e, ∑ i, (if Foot ell j p.2.1 e then (hbond ell M k κ c S i e - hrow ell M k κ c S i p) ^ 2 * ‖A e‖ ^ 2 else 0)
      ≤ massW (geomOf ell k S) a p * C ^ 2
        * ((49 * (ell : ℝ) ^ 2 * KG ell M κ c) * ∑ e, (if Foot ell j p.2.1 e then ‖A e‖ ^ 2 else 0)) :=
        mul_le_mul_of_nonneg_left (hosc.trans (le_of_eq hpull)) (by positivity)
    _ = _ := by rw [hCsq]; ring

include hS hκ hM hell hR1 hR hc

open Classical in
/-- **the mass commutator on a proper tower**. -/
theorem massComm_of_rowQ (U : Cfg (scaleUp ell k Lu)) (Sstar : ℝ) (hQ : ∀ p : BIdx (geomOf ell k S), RowQ ell k Lu S U Sstar p) (a : ℝ) (ha : 0 ≤ a) :
    MassComm ell M k κ c S U a (CMcStar ell M κ c a Sstar) := by
  intro A
  have hell0 : 0 < ell := by omega
  have hK0 := KG_nonneg ell M κ c
  set K1 := a * Estar ell Sstar ^ 2 * (49 * (ell : ℝ) ^ 2 * KG ell M κ c) with hK1
  have hK10 : 0 ≤ K1 := by positivity
  simp only [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  have hrow := fun p => row_comm_sum_row hS hκ hM hell hR1 hR hc U Sstar a ha A p (hQ p)
  refine (Finset.sum_le_sum (fun p _ => hrow p)).trans ?_
  rw [← Finset.mul_sum]
  -- swap rows and bonds
  have hswap : ∑ p : BIdx (geomOf ell k S), (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2
        * ∑ e, (if Foot ell (p.1 : ℕ) p.2.1 e then ‖A e‖ ^ 2 else 0)
      = ∑ e, ‖A e‖ ^ 2 * ∑ p : BIdx (geomOf ell k S),
          (if Foot ell (p.1 : ℕ) p.2.1 e then (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 else 0) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun p _ => ?_))
    split_ifs <;> ring
  rw [hswap]
  have hcnt : ∀ e, ‖A e‖ ^ 2 * ∑ p : BIdx (geomOf ell k S),
        (if Foot ell (p.1 : ℕ) p.2.1 e then (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 else 0)
      ≤ (1944 * (ell : ℝ) ^ 2) * ‖bondWt (-sigG (geomOf ell k S)) A e‖ ^ 2 := by
    intro e
    have h := foot_count hS hκ hM hell hR1 hR hc e
    have hw : ‖bondWt (-sigG (geomOf ell k S)) A e‖ ^ 2
        = (((ell : ℝ) ^ AdalyFormal.M1.strat S k e.1)⁻¹) ^ 2 * ‖A e‖ ^ 2 := by
      rw [bondWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
      show Real.exp (-(sigG (geomOf ell k S) e.1)) ^ 2 * _ = _
      rw [Real.exp_neg, exp_sig (geomOf ell k S) hell0, ← strat_eq_stratG hell0 hS]
      try rfl
    rw [hw]
    have := mul_le_mul_of_nonneg_left h (sq_nonneg ‖A e‖)
    calc ‖A e‖ ^ 2 * ∑ p : BIdx (geomOf ell k S),
          (if Foot ell (p.1 : ℕ) p.2.1 e then (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 else 0)
        ≤ ‖A e‖ ^ 2 * (1944 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ AdalyFormal.M1.strat S k e.1)⁻¹) ^ 2) := this
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hcnt e)
  rw [← Finset.mul_sum] at hsum
  calc K1 * ∑ e, ‖A e‖ ^ 2 * ∑ p : BIdx (geomOf ell k S),
          (if Foot ell (p.1 : ℕ) p.2.1 e then (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 else 0)
      ≤ K1 * ((1944 * (ell : ℝ) ^ 2) * ∑ e, ‖bondWt (-sigG (geomOf ell k S)) A e‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hK10
    _ = CMcStar ell M κ c a Sstar * ∑ e, ‖bondWt (-sigG (geomOf ell k S)) A e‖ ^ 2 := by
        rw [hK1]; unfold CMcStar; ring


end mass

end AdalyFormal.M2F123

#print axioms AdalyFormal.M2F123.RowQ_of_RegData
#print axioms AdalyFormal.M2F123.row_comm_sum_row
#print axioms AdalyFormal.M2F123.massComm_of_rowQ
