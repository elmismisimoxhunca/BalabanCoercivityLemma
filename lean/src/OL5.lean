import OL4

/-!
# OL5 -- the Combes–Thomas Schur instance of the genuine `H` with the row-local `RowQ` in place of `RegData`
(lane m2_oplayer_20261015)

`RegData` (a GAUGE-dependent regional class) enters the M1 Combes–Thomas chain ONLY through the mass difference
DG2b `M_diffE` (via DM1 `mass_cj_diff`, via TL7 `Qrow_restr_loc` / `Qrow_norm_loc`).  fields123 SG8 `RowQ` packages
exactly those two row properties gauge-invariantly.  Text copies (renamed `…R`):
* `mass_cj_diffR` (DM1), `M_diffER`, `gsplitR`, `hHB_genuineR` (DG2b), `wschurR`, `wschur_HR` (DH1),
  with `Dr : ∀ p, RowQ … p` in place of `Dr : RegData …`.  Every other field is the original lemma.
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


section massR
variable {L : PeriodicLatticeExtent}
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c)
include hS hκ hM hell hR1 hR hc

open Classical in
/-- **the mass Combes–Thomas difference** (row-local `RowQ` in place of `RegData`) -/
theorem mass_cj_diffR (U : Cfg (scaleUp ell k Lu)) (Sstar : ℝ) (D : ∀ p : BIdx (geomOf ell k S), AdalyFormal.M2F123.RowQ ell k Lu S U Sstar p) (a : ℝ) (ha : 0 ≤ a)
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
      Real.sq_sqrt hmw0, (D p).1]
    have h1 := (D p).2 (bondRestr (Foot ell j p.2.1) (bondMul f A))
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

end massR

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (Estar)
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply plaqMask_symm deltaPrimeBilL2NormLoc)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

section gs
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {W : ℕ}
  (D : CTData ell M R k S W) (hell0 : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu))
  (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k D.U ρ)
  (hεγ : D.epsG * D.γ ≤ 1) (hcG : 0 < D.cG)
variable (cw : ℝ) (hcw : 0 < cw)
  (hW4 : ∀ A : ↥(bondSupp (geomOf ell k S)),
    cw * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv A⟫)
  (θ' : ℝ) (hθ' : 0 ≤ θ')
  (hL : ∀ (x : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3),
    |D.χ (periodicLatticeShift x μ) - D.χ x| ≤ θ' / (ell : ℝ) ^ AdalyFormal.M1.strat S k x)
  (hR8 : 8 * ell ≤ R) (Sstar : ℝ) (Dr : ∀ p : BIdx (geomOf ell k S), AdalyFormal.M2F123.RowQ ell k Lu S D.U Sstar p)

include hR8 hθ' hL in
theorem M_diffER (Sstar : ℝ) (Dr : ∀ p : BIdx (geomOf ell k S), AdalyFormal.M2F123.RowQ ell k Lu S D.U Sstar p)
    (ξ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (hξ : ξ = D.χ ∨ ξ = -D.χ)
    (x : ↥(bondSupp (geomOf ell k S))) :
    ‖rowWt (geomOf ell k S) ξ (Ymass (geomOf ell k S) D.U D.a (iE (geomOf ell k S) (eW (geomOf ell k S) (-ξ) x)))
        - Ymass (geomOf ell k S) D.U D.a (iE (geomOf ell k S) x)‖ ≤ d3c ell D.a Sstar θ' * NnE (geomOf ell k S) x := by
  rw [iE_eW]
  have h := mass_cj_diffR D.hS (show 0 < 1 by norm_num) (show 0 < M by have := D.hM; omega) D.hell D.hR
    (show (5 + 3) * 1 * ell ≤ R by omega) (le_refl 5) D.U Sstar Dr D.a D.hp.ha.le ξ θ' hθ'
    (D.hL_s θ' hθ' hL ξ hξ) (iE (geomOf ell k S) x)
  have hR : 0 ≤ d3c ell D.a Sstar θ' * NnE (geomOf ell k S) x := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).mp (h.trans (le_of_eq ?_))
  unfold d3c NnE
  rw [mul_pow, Real.sq_sqrt (by have := D.hp.ha; positivity)]

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 in
/-- **the genuine `Ginv` as a `GSplit`** -/
noncomputable def gsplitR : GSplit ↥(bondSupp (geomOf ell k S)) (PlaqFnL2 (scaleUp ell k Lu))
    (SiteL2 (scaleUp ell k Lu)) (FSp (geomOf ell k S)) where
  Ginv := (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv
  Nw := eW (geomOf ell k S) (-sigG (geomOf ell k S))
  ωE := EWP (geomOf ell k S) D.χ
  Y1 := Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0))
  Y2 := Y2 (geomOf ell k S) D.U
  Y3 := Y3 (geomOf ell k S) D.U D.a
  ω1 := plaqWP D.χ
  ω2 := siteWP D.χ
  ω3 := rowWP (geomOf ell k S) D.χ
  Δ := Δg (geomOf ell k S) D.U D.a (plaqIn (S.Om 0))
  cw := cw
  cΔ := cDc ell ρ cw D.kZc D.kWc
  cΔ' := cDc' ell ρ cw D.kZc D.kWc θ' (d1c ell θ')
  d1 := d1c ell θ'
  d2 := D.dTc D.θχ
  d3 := d3c ell D.a Sstar θ'
  hcw := hcw
  hcΔ := by
    unfold cDc cYc; have := kapK_nonneg ell ρ hρ; have := D.kZc_nonneg hcG; have := nuD_nonneg ell ρ hρ; positivity
  hcΔ' := by
    unfold cDc' cYc; have := kapK_nonneg ell ρ hρ; have := D.kZc_nonneg hcG; have := nuD_nonneg ell ρ hρ
    have := D.d1c_nonneg θ' hθ'; positivity
  hd1 := D.d1c_nonneg θ' hθ'
  hd2 := D.dTc_nonneg hcG
  hd3 := Real.sqrt_nonneg _
  hdec := fun x y => ginv_bil hell0 S D.U D.a D.hp.ha.le Lam D.hp.hu x y
  hcoer := fun f => by rw [D.Nn_eq]; exact D.NE hell0 Lam cw hcw hW4 f
  hΔ0 := fun x y => D.Dg0 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL x y
  hΔ1 := fun x y => D.Dg1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL x y
  hp1 := fun x => by
    rw [D.Nn_eq, ContinuousLinearMap.sub_apply, cjp_apply]
    exact D.Y1_diff θ' hθ' hL D.χ (Or.inl rfl) x
  hm1 := fun x => by
    rw [D.Nn_eq, ContinuousLinearMap.sub_apply]
    have h := D.Y1_diff θ' hθ' hL (-D.χ) (Or.inr rfl) x
    rw [neg_neg] at h
    exact h
  hp2 := fun x => by
    rw [D.Nn_eq, ContinuousLinearMap.sub_apply, cjp_apply]
    exact D.T_diffE hεγ hcG D.χ (Or.inl rfl) x
  hm2 := fun x => by
    rw [D.Nn_eq, ContinuousLinearMap.sub_apply]
    have h := D.T_diffE hεγ hcG (-D.χ) (Or.inr rfl) x
    rw [neg_neg] at h
    exact h
  hp3 := fun x => by
    rw [D.Nn_eq, ContinuousLinearMap.sub_apply, cjp_apply]
    exact M_diffER D θ' hθ' hL hR8 Sstar Dr D.χ (Or.inl rfl) x
  hm3 := fun x => by
    rw [D.Nn_eq, ContinuousLinearMap.sub_apply]
    have h := M_diffER D θ' hθ' hL hR8 Sstar Dr (-D.χ) (Or.inr rfl) x
    rw [neg_neg] at h
    exact h

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 in
/-- **the form-relative Combes–Thomas bound of the genuine `Ginv`** (`hHB` of DC2) -/
theorem hHB_genuineR (x y : ↥(bondSupp (geomOf ell k S))) :
    |⟪x, cjp (EWP (geomOf ell k S) D.χ) (EWP (geomOf ell k S) D.χ)
          (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv y⟫
        - ⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv y⟫|
      ≤ (gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap
        * (Real.sqrt ⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv x⟫
          * Real.sqrt ⟪y, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv y⟫) :=
  (gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).hHB_of_split x y

end gs

section ws
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {W : ℕ}
  (D : CTData ell M R k S W) (hell0 : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu))
  (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k D.U ρ)
  (hεγ : D.epsG * D.γ ≤ 1) (hcG : 0 < D.cG)
  (cw : ℝ) (hcw : 0 < cw)
  (hW4 : ∀ A : ↥(bondSupp (geomOf ell k S)),
    cw * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv A⟫)
  (θ' : ℝ) (hθ' : 0 ≤ θ')
  (hL : ∀ (x : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3),
    |D.χ (periodicLatticeShift x μ) - D.χ x| ≤ θ' / (ell : ℝ) ^ AdalyFormal.M1.strat S k x)
  (hR8 : 8 * ell ≤ R) (Sstar : ℝ) (Dr : ∀ p : BIdx (geomOf ell k S), AdalyFormal.M2F123.RowQ ell k Lu S D.U Sstar p)
  (bN : ℝ) (hbN : 0 < bN)
  (hext : ∀ v : FSp (geomOf ell k S), ∃ g : ↥(bondSupp (geomOf ell k S)),
    (gparams ell k Lu hell0 S D.U D.a Lam).data.Q g = v ∧
      ⟪g, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv g⟫
        ≤ bN * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) D.a p)) v‖ ^ 2)
  (hQs : Function.Injective (gparams ell k Lu hell0 S D.U D.a Lam).data.Qs)
include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 hbN hext hQs in
/-- **the `WSchur` instance of the genuine `H`** -/
noncomputable def wschurR
    (hκ1 : (gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap < 1) :
    WSchur ↥(bondSupp (geomOf ell k S)) (FSp (geomOf ell k S)) where
  Ginv := (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv
  Gi := (gparams ell k Lu hell0 S D.U D.a Lam).data.G
  Q := (gparams ell k Lu hell0 S D.U D.a Lam).data.Q
  Ninv := Ring.inverse (((gparams ell k Lu hell0 S D.U D.a Lam).data.Q.comp
    (gparams ell k Lu hell0 S D.U D.a Lam).data.G).comp (gparams ell k Lu hell0 S D.U D.a Lam).data.Qs)
  ωE := EWP (geomOf ell k S) D.χ
  ωF := rowWP (geomOf ell k S) D.χ
  Nw := eW (geomOf ell k S) (-sigG (geomOf ell k S))
  Mw := massWP (geomOf ell k S) D.a D.hp.ha hell0
  cw := cw
  κ := (gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap
  CQ := (gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).ss
  dB := d3c ell D.a Sstar θ'
  bN := bN
  hcw := hcw
  hκ0 := (gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap_nonneg
  hκ1 := hκ1
  hCQ := (gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).ss_nonneg
  hdB := Real.sqrt_nonneg _
  hbN := hbN
  hsym := (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv_symm (gparams ell k Lu hell0 S D.U D.a Lam).data_laws
  hGi1 := D.Ginv_G hell0 Lam cw hcw hW4
  hGi2 := D.G_Ginv hell0 Lam cw hcw hW4
  hcoer := (gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).hcoer
  hHB := hHB_genuineR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr
  hQ := fun h => by
    set J := gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr
    have h1 := J.sq_sum_le h
    have h0 : ‖J.Y3 h‖ ^ 2 ≤ (1 + J.cΔ) * J.En h := by
      have := sq_nonneg ‖J.Y1 h‖; have := sq_nonneg ‖J.Y2 h‖; linarith
    have hq : 0 ≤ 1 + J.cΔ := by have := J.hcΔ; linarith
    show ‖J.Y3 h‖ ≤ J.ss * Real.sqrt (J.En h)
    unfold GSplit.ss
    rw [← Real.sqrt_mul hq, ← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt h0
  hQp := fun h => by
    set J := gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr
    have h1 := J.hp3 h
    rw [ContinuousLinearMap.sub_apply, cjp_apply] at h1 ⊢
    show ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) D.a p))
      (rowWt (geomOf ell k S) D.χ ((gparams ell k Lu hell0 S D.U D.a Lam).data.Q (eW (geomOf ell k S) (-D.χ) h))
        - (gparams ell k Lu hell0 S D.U D.a Lam).data.Q h)‖ ≤ _
    rw [map_sub, D.diagW_rowWt]
    exact h1
  hQm := fun h => by
    set J := gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr
    have h1 := J.hm3 h
    rw [ContinuousLinearMap.sub_apply] at h1 ⊢
    show ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) D.a p))
      (rowWt (geomOf ell k S) (-D.χ) ((gparams ell k Lu hell0 S D.U D.a Lam).data.Q (eW (geomOf ell k S) D.χ h))
        - (gparams ell k Lu hell0 S D.U D.a Lam).data.Q h)‖ ≤ _
    rw [map_sub, D.diagW_rowWt]
    exact h1
  hext := hext
  hN1 := fun u => by
    have h := Ring.mul_inverse_cancel _ (D.N_unit hell0 Lam cw hcw hW4 hQs)
    exact ContinuousLinearMap.ext_iff.mp h u
  hN2 := fun u => by
    have h := Ring.inverse_mul_cancel _ (D.N_unit hell0 Lam cw hcw hW4 hQs)
    exact ContinuousLinearMap.ext_iff.mp h u

theorem wschur_HR (hκ1 : (gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap < 1) :
    (wschurR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs hκ1).H
      = (gparams ell k Lu hell0 S D.U D.a Lam).data.H := by
  ext1 x; rfl


end ws

end AdalyFormal.M1DStrat

#print axioms AdalyFormal.M1DStrat.mass_cj_diffR
#print axioms AdalyFormal.M1DStrat.M_diffER
#print axioms AdalyFormal.M1DStrat.gsplitR
#print axioms AdalyFormal.M1DStrat.hHB_genuineR
#print axioms AdalyFormal.M1DStrat.wschurR
#print axioms AdalyFormal.M1DStrat.wschur_HR
