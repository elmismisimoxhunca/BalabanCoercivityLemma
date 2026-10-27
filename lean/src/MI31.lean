import MI30

/-!
# MI31 -- the row-wise mass commutator on a proper tower (M1 lane E, 2026-10-13)

* `row_comm_eq` : the row-`p` commutator is `−√w_p · Q(g A)(p)`, `g = hbond_i − hrow_i(p)`;
* `norm_restr_bondMul_sq` : `‖1_P · (g A)‖² = Σ_{e ∈ P} g(e)² ‖A e‖²`;
* `row_comm_sum` : `Σ_i ‖…(p)‖² ≤ a e^{2S/r} 49ℓ²K_G · ℓ^{−2j} Σ_{e ∈ Foot(p)} ‖A e‖²` (MI29 row norm + locality,
  MI30 oscillation);
* `row_window` : a row whose footprint meets `e` has `strat(e) − 1 ≤ j ≤ strat(e) + 1` (lane B's G1 `strat_close` + the
  collar `admissible_ball`).
(The multiplicity count `foot_count` and `massComm_proper` are in MI32.)
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
open AdalyFormal.DLayer (Foot Reach Rfoot Foot_reach Rfoot_le card_reach_coarse_le bondRestr)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (Tower Admissible scaleUp bigSide pdist)
open AdalyFormal.StatementLaneR8 (pdist_triangle pdist_comm pdist_shift_le pdist_coarseShift_le admissible_ball)
open AdalyFormal.NonflatJet (rhoOf)
open AdalyFormal.BondComposite (rr TowerClass hdvd_scaleUp)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

section mass
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c)

/-- the row-`p` commutator. -/
theorem row_comm_eq (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (A : BondFnL2 (scaleUp ell k Lu))
    (i : Fin (k + 1) × PeriodicLatticeSite (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) :
    (rowMul (geomOf ell k S) (hrow ell M k κ c S i) (Ymass (geomOf ell k S) U a A)
      - Ymass (geomOf ell k S) U a (bondMul (hbond ell M k κ c S i) A)) p
      = -(Real.sqrt (massW (geomOf ell k S) a p)
          • (bondSectorOf (geomOf ell k S) U).Qfull
              (bondMul (fun e => hbond ell M k κ c S i e - hrow ell M k κ c S i p) A) p) := by
  have e1 : bondMul (fun e => hbond ell M k κ c S i e - hrow ell M k κ c S i p) A
      = bondMul (hbond ell M k κ c S i) A - hrow ell M k κ c S i p • A := by
    refine PiLp.ext (fun b => ?_)
    rw [bondMul_apply, PiLp.sub_apply, bondMul_apply, PiLp.smul_apply, sub_smul]
  have hL : (rowMul (geomOf ell k S) (hrow ell M k κ c S i) (Ymass (geomOf ell k S) U a A)
      - Ymass (geomOf ell k S) U a (bondMul (hbond ell M k κ c S i) A)) p
      = hrow ell M k κ c S i p • (Real.sqrt (massW (geomOf ell k S) a p) • (bondSectorOf (geomOf ell k S) U).Qfull A p)
        - Real.sqrt (massW (geomOf ell k S) a p)
          • (bondSectorOf (geomOf ell k S) U).Qfull (bondMul (hbond ell M k κ c S i) A) p := rfl
  have hR : (bondSectorOf (geomOf ell k S) U).Qfull
        (bondMul (fun e => hbond ell M k κ c S i e - hrow ell M k κ c S i p) A) p
      = (bondSectorOf (geomOf ell k S) U).Qfull (bondMul (hbond ell M k κ c S i) A) p
        - hrow ell M k κ c S i p • (bondSectorOf (geomOf ell k S) U).Qfull A p := by
    rw [e1, map_sub, map_smul]; rfl
  rw [hL, hR, smul_sub, smul_comm (hrow ell M k κ c S i p) (Real.sqrt (massW (geomOf ell k S) a p))]
  abel

open Classical in
theorem norm_restr_bondMul_sq (P : Bond (scaleUp ell k Lu) → Prop) (g : Bond (scaleUp ell k Lu) → ℝ)
    (A : BondFnL2 (scaleUp ell k Lu)) :
    ‖bondRestr P (bondMul g A)‖ ^ 2 = ∑ e, (if P e then g e ^ 2 * ‖A e‖ ^ 2 else 0) := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  show ‖(if P e then (bondMul g A) e else 0)‖ ^ 2 = _
  split_ifs
  · rw [bondMul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  · simp

include hS hκ hM hell hR1 hR hc in
open Classical in
/-- **the per-row commutator sum**. -/
theorem row_comm_sum (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 ≤ a) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (A : BondFnL2 (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) :
    ∑ i, ‖(rowMul (geomOf ell k S) (hrow ell M k κ c S i) (Ymass (geomOf ell k S) U a A)
      - Ymass (geomOf ell k S) U a (bondMul (hbond ell M k κ c S i) A)) p‖ ^ 2
      ≤ a * EQ ell k ε ^ 2 * (49 * (ell : ℝ) ^ 2 * KG ell M κ c)
        * ((((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 * ∑ e, (if Foot ell (p.1 : ℕ) p.2.1 e then ‖A e‖ ^ 2 else 0)) := by
  have hell0 : 0 < ell := by omega
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell0
  set j : ℕ := (p.1 : ℕ) with hj
  have hmw : massW (geomOf ell k S) a p = a * (ell : ℝ) ^ j := rfl
  have hmw0 : 0 ≤ massW (geomOf ell k S) a p := by rw [hmw]; positivity
  set C := ((ell : ℝ) ^ j)⁻¹ * ((rr ell) ^ j * EQ ell k ε) with hC
  have hC0 : 0 ≤ C := by have := EQ_pos ell k ε; have : 0 ≤ rr ell := Real.sqrt_nonneg _; positivity
  -- per `i`
  have hi : ∀ i, ‖(rowMul (geomOf ell k S) (hrow ell M k κ c S i) (Ymass (geomOf ell k S) U a A)
      - Ymass (geomOf ell k S) U a (bondMul (hbond ell M k κ c S i) A)) p‖ ^ 2
      ≤ massW (geomOf ell k S) a p * C ^ 2
        * ∑ e, (if Foot ell j p.2.1 e then (hbond ell M k κ c S i e - hrow ell M k κ c S i p) ^ 2 * ‖A e‖ ^ 2 else 0) := by
    intro i
    rw [row_comm_eq U a A i p, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hmw0, Qrow_restr U hreg]
    have h1 := Qrow_norm hell0 U ε hreg hcl hε0 hsm
      (bondRestr (Foot ell j p.2.1) (bondMul (fun e => hbond ell M k κ c S i e - hrow ell M k κ c S i p) A)) p
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
  have hCsq : massW (geomOf ell k S) a p * C ^ 2 = a * EQ ell k ε ^ 2 * (((ell : ℝ) ^ j)⁻¹) ^ 2 := by
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

include hS hM hell hR1 hR hc hκ in
/-- **the level window of a row meeting `e`**. -/
theorem row_window (p : BIdx (geomOf ell k S)) (e : Bond (scaleUp ell k Lu)) (he : Foot ell (p.1 : ℕ) p.2.1 e) :
    AdalyFormal.M1.strat S k e.1 ≤ (p.1 : ℕ) + 1 ∧ (p.1 : ℕ) ≤ AdalyFormal.M1.strat S k e.1 + 1 := by
  classical
  have hell0 : 0 < ell := by omega
  set j : ℕ := (p.1 : ℕ) with hjdef
  have hj : j ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  have hRl : 8 * ell ≤ R := by
    have h1 : 8 ≤ (c + 3) * κ := le_trans (by omega : 8 ≤ c + 3) (Nat.le_mul_of_pos_right _ hκ)
    exact le_trans (Nat.mul_le_mul_right ell h1) hR
  -- anchor
  have hanc : ∃ a, a ∈ S.Om j ∧ a ∉ S.Om (j + 1) ∧ pdist a p.2.1.1 ≤ ell ^ j := by
    have hb : p.2.1.1 ∈ (geomOf ell k S).Lam (p.1 : ℕ) ∨
        coarseShift p.2.1.1 ((geomOf ell k S).ell ^ (p.1 : ℕ)) p.2.1.2 ∈ (geomOf ell k S).Lam (p.1 : ℕ) := p.2.2.1
    rcases hb with h | h
    · exact ⟨p.2.1.1, h.2.1, h.2.2, by rw [AdalyFormal.StatementLaneR8.pdist_self]; exact Nat.zero_le _⟩
    · refine ⟨coarseShift p.2.1.1 (ell ^ j) p.2.1.2, h.2.1, h.2.2, ?_⟩
      rw [pdist_comm]; exact pdist_coarseShift_le p.2.1.1 (ell ^ j) p.2.1.2
  obtain ⟨a, haO, haN, had⟩ := hanc
  have hreach := Foot_reach ell hell0 j p.2.1 e he
  have hpe : pdist p.2.1.1 e.1 ≤ 5 * ell ^ j := (pdist_of_reach hreach).trans (Rfoot_le ell hell j)
  have hae : pdist a e.1 ≤ 6 * ell ^ j := by
    have := pdist_triangle a p.2.1.1 e.1; omega
  -- strat a = j
  have hsa : AdalyFormal.M1.strat S k a = j := by
    refine le_antisymm ?_ (AdalyFormal.M1.le_strat_of_mem hj haO)
    by_contra hlt
    push Not at hlt
    have hk1 : j + 1 ≤ k := le_trans hlt (AdalyFormal.M1.strat_le S k a)
    exact haN ((AdalyFormal.M1.le_strat_iff hS (by omega) hk1 a).mp hlt)
  constructor
  · have hcl := AdalyFormal.M1.strat_close hS (x := a) (y := e.1) (by
      rw [hsa]; unfold bigSide
      have h1 : 6 * ell ^ j ≤ R * (M * ell ^ (j + 1)) := by
        have hp : ell ^ (j + 1) = ell * ell ^ j := by rw [pow_succ']
        rw [hp]
        have : 6 * ell ^ j ≤ (8 * ell) * ell ^ j := Nat.mul_le_mul_right _ (by omega)
        calc 6 * ell ^ j ≤ (8 * ell) * ell ^ j := this
          _ ≤ R * ell ^ j := Nat.mul_le_mul_right _ hRl
          _ ≤ R * (M * (ell * ell ^ j)) := Nat.mul_le_mul_left _ (by
              have : ell ^ j ≤ ell * ell ^ j := Nat.le_mul_of_pos_left _ hell0
              exact le_trans this (Nat.le_mul_of_pos_left _ hM))
      omega)
    rw [hsa] at hcl; exact hcl
  · by_cases hj0 : j = 0
    · omega
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    have hsub := admissible_ball hS (j := j - 1) (by omega) (y := a) (by rw [Nat.sub_add_cancel hj1]; exact haO)
    have hin : e.1 ∈ S.Om (j - 1) := by
      apply hsub
      show pdist a e.1 ≤ R * bigSide M ell (j - 1)
      unfold bigSide
      have hpow : ell ^ j = ell * ell ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
      have h1 : 6 * ell ^ j ≤ R * (M * ell ^ (j - 1)) := by
        calc 6 * ell ^ j ≤ 8 * ell ^ j := by omega
          _ = (8 * ell) * ell ^ (j - 1) := by rw [hpow]; ring
          _ ≤ R * ell ^ (j - 1) := Nat.mul_le_mul_right _ hRl
          _ ≤ R * (M * ell ^ (j - 1)) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hM)
      omega
    have := AdalyFormal.M1.le_strat_of_mem (by omega : j - 1 ≤ k) hin
    omega

end mass

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.row_comm_eq
#print axioms AdalyFormal.M1IMS.norm_restr_bondMul_sq
#print axioms AdalyFormal.M1IMS.row_comm_sum
#print axioms AdalyFormal.M1IMS.row_window
