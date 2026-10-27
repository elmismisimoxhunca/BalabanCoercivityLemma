import TL8
import MI32
import DL1

/-!
# DM1 -- the Combes–Thomas difference of the mass square `√w Q` on a proper tower, regional tower class
(M1 D-layer lane, 2026-10-14)

Weight `ξ` on sites; bonds weighted at the tail `e.1`, constraint rows at their base site `rowBase p` (MI18).
Hypothesis on `ξ` (stratified Lipschitz, the form DW1 `phiC_step` gives): `|ξ(x+e_μ) − ξ(x)| ≤ θ'/ℓ^{strat x}`.
* `reach_xi` : telescoping of `ξ` along a `Reach` path inside a set where every step is `≤ s0`;
* `osc_foot_xi` : for a row `p` and a bond `e` of its footprint, `|ξ(rowBase p) − ξ(e.1)| ≤ 6ℓθ'`
  (MI30 `osc_foot` with a scalar weight; collar `R ≥ 8ℓ`);
* `mass_row_eq` : the row `p` of `e^{ξ} Ymass e^{−ξ} A − Ymass A` is `√w_p · Q(f·A)(p)`, `f(e) = e^{ξ(rowBase p) − ξ(e.1)} − 1`;
* **`mass_cj_diff`** : `‖e^{ξ} Ymass(e^{−ξ} A) − Ymass A‖² ≤ a E*² (e^{6ℓθ'} − 1)² · 1944ℓ² · ‖e^{−σ} A‖²`
  with the REGIONAL tower data `RegData … Sstar` (towerloc TL7), i.e. `k`-free under `M1Regular` (TL9 `regData_M1`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.DLayer (Foot Reach Rfoot Foot_reach Rfoot_le Reach_trans Reach_coarseShift Reach_refl Reach_mono
  bondRestr bondWt bondWt_apply)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.StatementLane (Tower Admissible scaleUp bigSide pdist)
open AdalyFormal.StatementLaneR8 (pdist_triangle pdist_comm pdist_shift_le pdist_coarseShift_le admissible_ball Ball)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.M1IMS
open AdalyFormal.M1Site
open AdalyFormal.TowerLoc
open AdalyFormal.BondComposite (rr)

variable {L : PeriodicLatticeExtent}

/-- telescoping of a scalar along a `Reach` path whose steps stay where they are bounded -/
theorem reach_xi (ξ : PeriodicLatticeSite L → ℝ) (s0 : ℝ) (hs0 : 0 ≤ s0) :
    ∀ (l : List (Fin 3)) (x : PeriodicLatticeSite L) (m : ℕ), l.length ≤ m →
      (∀ w, pdist x w < m → ∀ μ, |ξ w - ξ (periodicLatticeShift w μ)| ≤ s0) →
      |ξ x - ξ (l.foldl (fun w μ => periodicLatticeShift w μ) x)| ≤ m * s0 := by
  intro l
  induction l with
  | nil =>
    intro x m _ _
    simp only [List.foldl_nil, sub_self, abs_zero]
    positivity
  | cons μ rest ih =>
    intro x m hl hstep
    rw [List.foldl_cons]
    rw [List.length_cons] at hl
    have hm : 1 ≤ m := by omega
    have h1 : |ξ x - ξ (periodicLatticeShift x μ)| ≤ s0 :=
      hstep x (by rw [AdalyFormal.StatementLaneR8.pdist_self]; omega) μ
    have h2 := ih (periodicLatticeShift x μ) (m - 1) (by omega) (fun w hw ν => hstep w (by
      have := pdist_triangle x (periodicLatticeShift x μ) w
      have := pdist_shift_le x μ
      omega) ν)
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm]; simp
    rw [hcast] at h2
    have h3 := abs_sub_le (ξ x) (ξ (periodicLatticeShift x μ))
      (ξ (rest.foldl (fun w μ => periodicLatticeShift w μ) (periodicLatticeShift x μ)))
    nlinarith

theorem reach_xi' (ξ : PeriodicLatticeSite L → ℝ) (s0 : ℝ) (hs0 : 0 ≤ s0) {m : ℕ} {x z : PeriodicLatticeSite L}
    (hr : Reach m x z) (hstep : ∀ w, pdist x w < m → ∀ μ, |ξ w - ξ (periodicLatticeShift w μ)| ≤ s0) :
    |ξ x - ξ z| ≤ m * s0 := by
  obtain ⟨l, hl, rfl⟩ := hr
  exact reach_xi ξ s0 hs0 l x m hl hstep

section osc
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hM : 0 < M) (hell : 2 ≤ ell) (hR : 8 * ell ≤ R)
include hS hM hell hR

/-- **oscillation of the weight across a row footprint** -/
theorem osc_foot_xi (ξ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ' : ℝ) (hθ' : 0 ≤ θ')
    (hL : ∀ (x : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3),
      |ξ (periodicLatticeShift x μ) - ξ x| ≤ θ' / (ell : ℝ) ^ AdalyFormal.M1.strat S k x)
    (p : BIdx (geomOf ell k S)) (e : Bond (scaleUp ell k Lu)) (he : Foot ell (p.1 : ℕ) p.2.1 e) :
    |ξ (rowBase (geomOf ell k S) p) - ξ e.1| ≤ 6 * (ell : ℝ) * θ' := by
  classical
  have hell0 : 0 < ell := by omega
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  set j : ℕ := (p.1 : ℕ) with hjdef
  have hj : j ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  set x0 := p.2.1.1 with hx0
  have hstepAll : ∀ w μ, |ξ w - ξ (periodicLatticeShift w μ)| ≤ θ' := by
    intro w μ
    rw [abs_sub_comm]
    refine (hL w μ).trans ?_
    rw [div_le_iff₀ (by positivity)]
    have := one_le_pow₀ (n := AdalyFormal.M1.strat S k w) hellR
    nlinarith
  by_cases hj0 : j = 0
  · have hfe : e = p.2.1 := by
      have : Foot ell 0 p.2.1 e := by rw [← hj0]; exact he
      exact this
    have h10 : (p.1 : ℕ) = 0 := hj0
    have hr : Reach 1 e.1 (rowBase (geomOf ell k S) p) := by
      rw [hfe]
      unfold rowBase
      simp only [show (geomOf ell k S).ell = ell from rfl, h10, pow_zero]
      split_ifs
      · exact Reach_mono (Nat.zero_le 1) (Reach_refl _)
      · exact Reach_coarseShift 1 _ _
    have h := reach_xi' ξ θ' hθ' hr (fun w _ μ => hstepAll w μ)
    rw [abs_sub_comm] at h
    have : (1 : ℝ) * θ' ≤ 6 * ell * θ' := by nlinarith
    push_cast at h; linarith
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
  have hanc : ∃ a, a ∈ S.Om j ∧ pdist a x0 ≤ ell ^ j := by
    have hb : p.2.1.1 ∈ (geomOf ell k S).Lam (p.1 : ℕ) ∨
        coarseShift p.2.1.1 ((geomOf ell k S).ell ^ (p.1 : ℕ)) p.2.1.2 ∈ (geomOf ell k S).Lam (p.1 : ℕ) := p.2.2.1
    rcases hb with h | h
    · exact ⟨x0, h.2.1, by rw [AdalyFormal.StatementLaneR8.pdist_self]; exact Nat.zero_le _⟩
    · refine ⟨coarseShift x0 (ell ^ j) p.2.1.2, h.2.1, ?_⟩
      rw [pdist_comm]; exact pdist_coarseShift_le x0 (ell ^ j) p.2.1.2
  obtain ⟨a, haO, had⟩ := hanc
  have hball : ∀ w, pdist x0 w ≤ 6 * ell ^ j → w ∈ S.Om (j - 1) := by
    intro w hw
    have hsub := admissible_ball hS (j := j - 1) (by omega) (y := a) (by rw [Nat.sub_add_cancel hj1]; exact haO)
    apply hsub
    show pdist a w ≤ R * bigSide M ell (j - 1)
    have htri := pdist_triangle a x0 w
    have hpow : ell ^ j = ell * ell ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h1 : 7 * ell ^ j ≤ R * (M * ell ^ (j - 1)) := by
      have hM1 : 1 ≤ M := hM
      calc 7 * ell ^ j ≤ 8 * ell ^ j := by omega
        _ = (8 * ell) * ell ^ (j - 1) := by rw [hpow]; ring
        _ ≤ R * ell ^ (j - 1) := Nat.mul_le_mul_right _ hR
        _ ≤ R * (M * ell ^ (j - 1)) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hM)
    unfold bigSide
    omega
  have hlr : (0 : ℝ) < (ell : ℝ) ^ (j - 1) := by positivity
  set s0 := θ' / (ell : ℝ) ^ (j - 1) with hs0def
  have hs0 : 0 ≤ s0 := by positivity
  have hstep : ∀ w, pdist x0 w < 6 * ell ^ j → ∀ μ, |ξ w - ξ (periodicLatticeShift w μ)| ≤ s0 := by
    intro w hw μ
    have hwO := hball w (by omega)
    have hstr : j - 1 ≤ AdalyFormal.M1.strat S k w := AdalyFormal.M1.le_strat_of_mem (by omega) hwO
    rw [abs_sub_comm]
    refine (hL w μ).trans ?_
    rw [hs0def]
    apply div_le_div_of_nonneg_left hθ' hlr
    exact pow_le_pow_right₀ hellR hstr
  have hRf := Rfoot_le ell hell j
  have hre : Reach (Rfoot ell j) x0 e.1 := Foot_reach ell hell0 j p.2.1 e he
  have hrb : Reach (ell ^ j) x0 (rowBase (geomOf ell k S) p) := by
    unfold rowBase
    split_ifs
    · exact Reach_mono (Nat.zero_le _) (Reach_refl _)
    · exact Reach_coarseShift (ell ^ j) x0 p.2.1.2
  have hd1 := reach_xi' ξ s0 hs0 hre (fun w hw μ => hstep w (by
    have : 1 ≤ ell ^ j := Nat.one_le_pow _ _ hell0
    omega) μ)
  have hd2 := reach_xi' ξ s0 hs0 hrb (fun w hw μ => hstep w (by
    have : 1 ≤ ell ^ j := Nat.one_le_pow _ _ hell0
    omega) μ)
  have hcast1 : ((Rfoot ell j : ℕ) : ℝ) ≤ 5 * (ell : ℝ) ^ j := by exact_mod_cast hRf
  have hcast2 : ((ell ^ j : ℕ) : ℝ) = (ell : ℝ) ^ j := by push_cast; rfl
  rw [hcast2] at hd2
  have htri := abs_sub_le (ξ (rowBase (geomOf ell k S) p)) (ξ x0) (ξ e.1)
  rw [abs_sub_comm] at hd2
  have hval : 6 * (ell : ℝ) ^ j * s0 = 6 * (ell : ℝ) * θ' := by
    rw [hs0def]
    have hpow : (ell : ℝ) ^ j = (ell : ℝ) * (ell : ℝ) ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpow]; field_simp
  have e1 := mul_le_mul_of_nonneg_right hcast1 hs0
  nlinarith

end osc

section mass
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c)

/-- the row weight `e^{ξ(rowBase p)}` -/
noncomputable def rowWt (G : TowerGeom L) (ξ : PeriodicLatticeSite L → ℝ) : FSp G →L[ℝ] FSp G :=
  diagW G (fun p => Real.exp (ξ (rowBase G p)))

/-- the row identity -/
theorem mass_row_eq (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ξ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ)
    (A : BondFnL2 (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) :
    (rowWt (geomOf ell k S) ξ (Ymass (geomOf ell k S) U a (bondWt (-ξ) A)) - Ymass (geomOf ell k S) U a A) p
      = Real.sqrt (massW (geomOf ell k S) a p)
          • (bondSectorOf (geomOf ell k S) U).Qfull
              (bondMul (fun e => Real.exp (ξ (rowBase (geomOf ell k S) p) - ξ e.1) - 1) A) p := by
  have e1 : bondMul (fun e => Real.exp (ξ (rowBase (geomOf ell k S) p) - ξ e.1) - 1) A
      = Real.exp (ξ (rowBase (geomOf ell k S) p)) • bondWt (-ξ) A - A := by
    refine PiLp.ext (fun b => ?_)
    rw [bondMul_apply, PiLp.sub_apply, PiLp.smul_apply, bondWt_apply, smul_smul, sub_smul, one_smul]
    congr 2
    rw [← Real.exp_add]; congr 1
  have hL : (rowWt (geomOf ell k S) ξ (Ymass (geomOf ell k S) U a (bondWt (-ξ) A)) - Ymass (geomOf ell k S) U a A) p
      = Real.exp (ξ (rowBase (geomOf ell k S) p))
          • (Real.sqrt (massW (geomOf ell k S) a p) • (bondSectorOf (geomOf ell k S) U).Qfull (bondWt (-ξ) A) p)
        - Real.sqrt (massW (geomOf ell k S) a p) • (bondSectorOf (geomOf ell k S) U).Qfull A p := rfl
  rw [hL, e1, map_sub, map_smul]
  show _ = Real.sqrt (massW (geomOf ell k S) a p) • (Real.exp (ξ (rowBase (geomOf ell k S) p))
      • (bondSectorOf (geomOf ell k S) U).Qfull (bondWt (-ξ) A) p - (bondSectorOf (geomOf ell k S) U).Qfull A p)
  rw [smul_sub, smul_comm (Real.exp (ξ (rowBase (geomOf ell k S) p))) (Real.sqrt (massW (geomOf ell k S) a p))]

include hS hκ hM hell hR1 hR hc

open Classical in
/-- **the mass Combes–Thomas difference** (regional tower class) -/
theorem mass_cj_diff (U : Cfg (scaleUp ell k Lu)) (Sstar : ℝ) (D : RegData ell k Lu S U Sstar) (a : ℝ) (ha : 0 ≤ a)
    (ξ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ' : ℝ) (hθ' : 0 ≤ θ')
    (hL : ∀ (x : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3),
      |ξ (periodicLatticeShift x μ) - ξ x| ≤ θ' / (ell : ℝ) ^ AdalyFormal.M1.strat S k x)
    (A : BondFnL2 (scaleUp ell k Lu)) :
    ‖rowWt (geomOf ell k S) ξ (Ymass (geomOf ell k S) U a (bondWt (-ξ) A)) - Ymass (geomOf ell k S) U a A‖ ^ 2
      ≤ a * Estar ell Sstar ^ 2 * (Real.exp (6 * (ell : ℝ) * θ') - 1) ^ 2 * (1944 * (ell : ℝ) ^ 2)
        * ‖bondWt (-sigG (geomOf ell k S)) A‖ ^ 2 := by
  have hell0 : 0 < ell := by omega
  have hRl : 8 * ell ≤ R := by
    have h1 : 8 ≤ (c + 3) * κ := le_trans (by omega : 8 ≤ c + 3) (Nat.le_mul_of_pos_right _ hκ)
    exact le_trans (Nat.mul_le_mul_right ell h1) hR
  set E := Real.exp (6 * (ell : ℝ) * θ') - 1 with hE
  have hE0 : 0 ≤ E := by
    have h1 := Real.add_one_le_exp (6 * (ell : ℝ) * θ')
    have h2 : 0 ≤ 6 * (ell : ℝ) * θ' := by positivity
    linarith
  -- per row
  have hrow : ∀ p : BIdx (geomOf ell k S),
      ‖(rowWt (geomOf ell k S) ξ (Ymass (geomOf ell k S) U a (bondWt (-ξ) A)) - Ymass (geomOf ell k S) U a A) p‖ ^ 2
        ≤ a * Estar ell Sstar ^ 2 * E ^ 2
          * ((((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 * ∑ e, (if Foot ell (p.1 : ℕ) p.2.1 e then ‖A e‖ ^ 2 else 0)) := by
    intro p
    set j : ℕ := (p.1 : ℕ) with hj
    set f : Bond (scaleUp ell k Lu) → ℝ := fun e => Real.exp (ξ (rowBase (geomOf ell k S) p) - ξ e.1) - 1 with hf
    have hmw : massW (geomOf ell k S) a p = a * (ell : ℝ) ^ j := rfl
    have hmw0 : 0 ≤ massW (geomOf ell k S) a p := by rw [hmw]; positivity
    rw [mass_row_eq U a ξ A p, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hmw0, Qrow_restr_loc hell0 D]
    have h1 := Qrow_norm_loc hell0 D (bondRestr (Foot ell j p.2.1) (bondMul f A)) p
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, norm_restr_bondMul_sq] at h2
    have hfe : ∑ e, (if Foot ell j p.2.1 e then f e ^ 2 * ‖A e‖ ^ 2 else 0)
        ≤ E ^ 2 * ∑ e, (if Foot ell j p.2.1 e then ‖A e‖ ^ 2 else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun e _ => ?_)
      split_ifs with he
      · have hosc := osc_foot_xi hS hM hell hRl ξ θ' hθ' hL p e he
        have hb : |f e| ≤ E := by
          rw [hf]; dsimp only
          refine (AdalyFormal.M1DStrat.abs_exp_sub_one_le_abs _).trans ?_
          rw [hE]; linarith [Real.exp_le_exp.mpr hosc]
        have : f e ^ 2 ≤ E ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      · simp
    have hCsq : massW (geomOf ell k S) a p * (((ell : ℝ) ^ j)⁻¹ * ((rr ell) ^ j * Estar ell Sstar)) ^ 2
        = a * Estar ell Sstar ^ 2 * (((ell : ℝ) ^ j)⁻¹) ^ 2 := by
      have hr2 : (rr ell) ^ 2 = (ell : ℝ)⁻¹ := by
        unfold rr; rw [Real.sq_sqrt (by positivity), one_div]
      have hrj : ((rr ell) ^ j) ^ 2 = ((ell : ℝ) ^ j)⁻¹ := by
        rw [← pow_mul, mul_comm, pow_mul, hr2, inv_pow]
      have hpos : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
      rw [hmw, mul_pow, mul_pow, hrj]
      field_simp
    calc massW (geomOf ell k S) a p
          * ‖(bondSectorOf (geomOf ell k S) U).Qfull (bondRestr (Foot ell j p.2.1) (bondMul f A)) p‖ ^ 2
        ≤ massW (geomOf ell k S) a p * ((((ell : ℝ) ^ j)⁻¹ * ((rr ell) ^ j * Estar ell Sstar)) ^ 2
            * ∑ e, (if Foot ell j p.2.1 e then f e ^ 2 * ‖A e‖ ^ 2 else 0)) :=
          mul_le_mul_of_nonneg_left h2 hmw0
      _ = (massW (geomOf ell k S) a p * (((ell : ℝ) ^ j)⁻¹ * ((rr ell) ^ j * Estar ell Sstar)) ^ 2)
            * ∑ e, (if Foot ell j p.2.1 e then f e ^ 2 * ‖A e‖ ^ 2 else 0) := by ring
      _ ≤ (a * Estar ell Sstar ^ 2 * (((ell : ℝ) ^ j)⁻¹) ^ 2) * (E ^ 2 * ∑ e, (if Foot ell j p.2.1 e then ‖A e‖ ^ 2 else 0)) := by
          rw [hCsq]
          exact mul_le_mul_of_nonneg_left hfe (by positivity)
      _ = _ := by ring
  set K1 := a * Estar ell Sstar ^ 2 * E ^ 2 with hK1
  have hK10 : 0 ≤ K1 := by positivity
  rw [PiLp.norm_sq_eq_of_L2]
  refine (Finset.sum_le_sum (fun p _ => hrow p)).trans ?_
  rw [← Finset.mul_sum]
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
  rw [PiLp.norm_sq_eq_of_L2]
  calc K1 * ∑ e, ‖A e‖ ^ 2 * ∑ p : BIdx (geomOf ell k S),
          (if Foot ell (p.1 : ℕ) p.2.1 e then (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 else 0)
      ≤ K1 * ((1944 * (ell : ℝ) ^ 2) * ∑ e, ‖bondWt (-sigG (geomOf ell k S)) A e‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hK10
    _ = _ := by rw [hK1]; ring

end mass

#print axioms reach_xi
#print axioms reach_xi'
#print axioms osc_foot_xi
#print axioms rowWt
#print axioms mass_row_eq
#print axioms mass_cj_diff

end AdalyFormal.M1DStrat
