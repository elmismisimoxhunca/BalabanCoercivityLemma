import DR1
import DH1

/-!
# DU1 -- an UPPER bound of the genuine `Ginv` form by gradients, the stratum-weighted norm and the mass term, and the
energy right inverse `hext` of DC2/DH1 in the M1 regime (M1 D-layer lane, 2026-10-14)

Link hypothesis at the configuration `V`: `frobNorm(V_b − 1) ≤ ρL / ℓ^{bstrat b}` on every bond.
* `curl_upper` : `‖χ_P C_V B‖² ≤ 24 Σ_ν gradW B ν + 96 ℓ² ρL² wnormSq B`;
* `div_upper`  : `‖D_V* B‖² ≤ 6 Σ_ν gradW B ν + 24 ρL² wnormSq B`;  hence `‖T B‖²` (the projection `R` is a contraction);
* **`ginv_upper`** : `⟪A, Ginv A⟫ ≤ (1+η)(30 Σ_ν gradW + (96ℓ² + 24) ρL² wnormSq + ‖√w Q A‖²) + 2ν wnormSq`
  (lane E's MI19 `sandwich`, upper side);
* **`hext_of_rightinv`** : any right inverse with `wnormSq x ≤ cW nD u`, `gradW x ≤ cG nD u` is an energy right inverse
  `⟪x, Ginv x⟫ ≤ bN ‖√w u‖²` with an explicit `bN` (`nD u = ‖√w u‖²/a`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2 periodicLatticeShiftBack periodicLatticeShift_shiftBack
  periodicLatticeShiftBack_shift gradCovariantAdjointValue)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.M1 (strat bstrat wnormSq strat_adj)
open AdalyFormal.W6 (gradW nD wD)

section up
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf}
  (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hR1 : 1 ≤ R) (hM1 : 1 ≤ M)
include hS hell hR1 hM1

omit hS hell hR1 hM1 in
/-- `‖R(g)v − v‖ ≤ 2 frob(g − 1) ‖v‖` and the inverse version -/
theorem RMap_sub_le (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : SuTwo) :
    ‖RMap g v - v‖ ≤ 2 * frobNorm ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) * ‖v‖ := by
  have h := RMap_diff_le g 1 v
  rw [inv_one, mul_one, AdalyFormal.Balaban.CovariantOperators.RMap_one] at h
  exact h

omit hS hell hR1 hM1 in
theorem RMap_inv_sub_le (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : SuTwo) :
    ‖RMap g⁻¹ v - v‖ ≤ 2 * frobNorm ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) * ‖v‖ := by
  have e1 : RMap g (RMap g⁻¹ v) = v := by
    have h := LinearMap.congr_fun (AdalyFormal.Balaban.CovariantOperators.RMap_mul g g⁻¹) v
    rw [mul_inv_cancel, AdalyFormal.Balaban.CovariantOperators.RMap_one] at h
    simpa using h.symm
  have e : RMap g (RMap g⁻¹ v - v) = v - RMap g v := by
    rw [map_sub, e1]
  have h1 : ‖RMap g (RMap g⁻¹ v - v)‖ = ‖RMap g⁻¹ v - v‖ := AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap _ _
  rw [← h1, e, norm_sub_rev]
  exact RMap_sub_le g v

/-- the stratum of a bond controls the next one -/
theorem bstrat_next (x : PeriodicLatticeSite Lf) (μ ν : Fin 3) :
    bstrat S k (periodicLatticeShift x μ, ν) ≤ bstrat S k (x, μ) + 1 := by
  have h := (strat_adj hS hR1 hM1 (by omega) x μ).1
  unfold bstrat
  dsimp only
  have h2 : min (strat S k (periodicLatticeShift x μ)) (strat S k (periodicLatticeShift (periodicLatticeShift x μ) ν))
      ≤ strat S k (periodicLatticeShift x μ) := min_le_left _ _
  have h3 := (strat_adj hS hR1 hM1 (by omega) x μ).2
  omega

omit hS hell hR1 hM1 in
/-- gradient sub-sum -/
theorem grad_sub (B : BondFnL2 Lf) (μ ν : Fin 3) :
    ∑ x : PeriodicLatticeSite Lf, ‖B (periodicLatticeShift x μ, ν) - B (x, ν)‖ ^ 2 ≤ gradW B μ := by
  unfold gradW
  rw [show (Finset.univ : Finset (Bond Lf)) = Finset.univ ×ˢ Finset.univ from rfl, Finset.sum_product_right]
  exact Finset.single_le_sum (f := fun ν' => ∑ x : PeriodicLatticeSite Lf,
    ‖B (periodicLatticeShift x μ, ν') - B (x, ν')‖ ^ 2) (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.mem_univ ν)

omit hS hell hR1 hM1 in
theorem gradW_le_sum (B : BondFnL2 Lf) (μ : Fin 3) : gradW B μ ≤ ∑ ν : Fin 3, gradW B ν :=
  Finset.single_le_sum (f := fun ν => gradW B ν)
    (fun ν _ => by unfold gradW; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ μ)

omit hS hell hR1 hM1 in
/-- one direction of the weighted norm -/
theorem wdir_le (B : BondFnL2 Lf) (ν : Fin 3) :
    ∑ x : PeriodicLatticeSite Lf, (((ell : ℝ) ^ bstrat S k (x, ν))⁻¹) ^ 2 * ‖B (x, ν)‖ ^ 2 ≤ wnormSq S ell k B := by
  unfold wnormSq
  rw [show (Finset.univ : Finset (Bond Lf)) = Finset.univ ×ˢ Finset.univ from rfl, Finset.sum_product_right]
  exact Finset.single_le_sum (f := fun ν' => ∑ x : PeriodicLatticeSite Lf,
    (((ell : ℝ) ^ bstrat S k (x, ν'))⁻¹) ^ 2 * ‖B (x, ν')‖ ^ 2) (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
    (Finset.mem_univ ν)

/-- the link perturbation, one transported bond -/
theorem link_term (V : Cfg Lf) (ρL : ℝ) (hρL : 0 ≤ ρL)
    (hlink : ∀ b : Bond Lf, frobNorm (((V b : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      ≤ ρL / (ell : ℝ) ^ bstrat S k b)
    (B : BondFnL2 Lf) (x : PeriodicLatticeSite Lf) (μ ν : Fin 3) :
    ‖RMap (V (x, μ)) (B (periodicLatticeShift x μ, ν)) - B (periodicLatticeShift x μ, ν)‖ ^ 2
      ≤ 4 * ρL ^ 2 * (ell : ℝ) ^ 2
        * ((((ell : ℝ) ^ bstrat S k (periodicLatticeShift x μ, ν))⁻¹) ^ 2 * ‖B (periodicLatticeShift x μ, ν)‖ ^ 2) := by
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have h1 := RMap_sub_le (V (x, μ)) (B (periodicLatticeShift x μ, ν))
  have h2 := hlink (x, μ)
  have hn := bstrat_next hS hell hR1 hM1 x μ ν
  set t := bstrat S k (x, μ)
  set t' := bstrat S k (periodicLatticeShift x μ, ν)
  have hp : (0 : ℝ) < (ell : ℝ) ^ t := by have := one_le_pow₀ (n := t) hellr; positivity
  have hp' : (0 : ℝ) < (ell : ℝ) ^ t' := by have := one_le_pow₀ (n := t') hellr; positivity
  have hpow : ((ell : ℝ) ^ t)⁻¹ ≤ (ell : ℝ) * ((ell : ℝ) ^ t')⁻¹ := by
    rw [inv_le_comm₀ hp (by positivity), mul_inv, inv_inv]
    have : (ell : ℝ) ^ t' ≤ (ell : ℝ) ^ (t + 1) := pow_le_pow_right₀ hellr hn
    rw [pow_succ] at this
    have hl0 : (0 : ℝ) < ell := by linarith
    calc (ell : ℝ)⁻¹ * (ell : ℝ) ^ t' ≤ (ell : ℝ)⁻¹ * ((ell : ℝ) ^ t * ell) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = (ell : ℝ) ^ t := by field_simp
  have h3 : ‖RMap (V (x, μ)) (B (periodicLatticeShift x μ, ν)) - B (periodicLatticeShift x μ, ν)‖
      ≤ 2 * ρL * (ell : ℝ) * ((ell : ℝ) ^ t')⁻¹ * ‖B (periodicLatticeShift x μ, ν)‖ := by
    refine h1.trans ?_
    have hf : frobNorm (((V (x, μ) : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ ρL * ((ell : ℝ) * ((ell : ℝ) ^ t')⁻¹) := by
      refine h2.trans ?_
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hpow hρL
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf (show (0:ℝ) ≤ 2 by norm_num))
      (norm_nonneg (B (periodicLatticeShift x μ, ν)))
    calc _ ≤ 2 * (ρL * ((ell : ℝ) * ((ell : ℝ) ^ t')⁻¹)) * ‖B (periodicLatticeShift x μ, ν)‖ := this
      _ = _ := by ring
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  calc _ ≤ (2 * ρL * (ell : ℝ) * ((ell : ℝ) ^ t')⁻¹ * ‖B (periodicLatticeShift x μ, ν)‖) ^ 2 := h4
    _ = _ := by ring

/-- **the covariant curl by gradients** -/
theorem curl_upper (V : Cfg Lf) (ρL : ℝ) (hρL : 0 ≤ ρL)
    (hlink : ∀ b : Bond Lf, frobNorm (((V b : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      ≤ ρL / (ell : ℝ) ^ bstrat S k b)
    (B : BondFnL2 Lf) :
    ‖plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 V B)‖ ^ 2
      ≤ 24 * ∑ ν : Fin 3, gradW B ν + 96 * (ell : ℝ) ^ 2 * ρL ^ 2 * wnormSq S ell k B := by
  classical
  have hmask : ‖plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 V B)‖ ^ 2 ≤ ‖curlCovariantLM_L2 V B‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum (fun p _ => ?_)
    rw [plaqMask_apply]; split_ifs
    · exact le_rfl
    · rw [norm_zero, zero_pow two_ne_zero]; exact sq_nonneg _
  refine hmask.trans ?_
  set Gs := ∑ ν : Fin 3, gradW B ν
  have hpt : ∀ p : PeriodicLatticePlaquette Lf, ‖(curlCovariantLM_L2 V B) p‖ ^ 2
      ≤ 4 * (‖B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) - B (p.1, p.2.1.2)‖ ^ 2
        + ‖B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - B (p.1, p.2.1.1)‖ ^ 2
        + ‖RMap (V (p.1, p.2.1.1)) (B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)) - B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
        + ‖RMap (V (p.1, p.2.1.2)) (B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) := by
    intro p
    rw [curlLM_apply]
    unfold curlValueCovariant
    have e : (WithLp.ofLp B) (p.1, p.2.1.1) + RMap (V (p.1, p.2.1.1)) ((WithLp.ofLp B) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
          - RMap (V (p.1, p.2.1.2)) ((WithLp.ofLp B) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - (WithLp.ofLp B) (p.1, p.2.1.2)
        = (B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) - B (p.1, p.2.1.2))
          - (B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - B (p.1, p.2.1.1))
          + (RMap (V (p.1, p.2.1.1)) (B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)) - B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
          - (RMap (V (p.1, p.2.1.2)) (B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) := by
      show B (p.1, p.2.1.1) + RMap (V (p.1, p.2.1.1)) (B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
          - RMap (V (p.1, p.2.1.2)) (B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - B (p.1, p.2.1.2) = _
      abel
    rw [e]
    set u1 := B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) - B (p.1, p.2.1.2)
    set u2 := B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - B (p.1, p.2.1.1)
    set u3 := RMap (V (p.1, p.2.1.1)) (B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)) - B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
    set u4 := RMap (V (p.1, p.2.1.2)) (B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)
    have t : ‖u1 - u2 + u3 - u4‖ ≤ ‖u1‖ + ‖u2‖ + ‖u3‖ + ‖u4‖ := by
      have := norm_sub_le (u1 - u2 + u3) u4
      have := norm_add_le (u1 - u2) u3
      have := norm_sub_le u1 u2
      linarith
    have h2 := pow_le_pow_left₀ (norm_nonneg _) t 2
    nlinarith [sq_nonneg (‖u1‖ - ‖u2‖), sq_nonneg (‖u1‖ - ‖u3‖), sq_nonneg (‖u1‖ - ‖u4‖), sq_nonneg (‖u2‖ - ‖u3‖),
      sq_nonneg (‖u2‖ - ‖u4‖), sq_nonneg (‖u3‖ - ‖u4‖)]
  rw [PiLp.norm_sq_eq_of_L2]
  refine (Finset.sum_le_sum (fun p _ => hpt p)).trans ?_
  rw [Fintype.sum_prod_type_right]
  have hd : ∀ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite Lf,
      4 * (‖B (periodicLatticeShift x d.1.1, d.1.2) - B (x, d.1.2)‖ ^ 2
        + ‖B (periodicLatticeShift x d.1.2, d.1.1) - B (x, d.1.1)‖ ^ 2
        + ‖RMap (V (x, d.1.1)) (B (periodicLatticeShift x d.1.1, d.1.2)) - B (periodicLatticeShift x d.1.1, d.1.2)‖ ^ 2
        + ‖RMap (V (x, d.1.2)) (B (periodicLatticeShift x d.1.2, d.1.1)) - B (periodicLatticeShift x d.1.2, d.1.1)‖ ^ 2)
      ≤ 8 * Gs + 32 * (ell : ℝ) ^ 2 * ρL ^ 2 * wnormSq S ell k B := by
    intro d
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have a1 := (grad_sub B d.1.1 d.1.2).trans (gradW_le_sum B d.1.1)
    have a2 := (grad_sub B d.1.2 d.1.1).trans (gradW_le_sum B d.1.2)
    have r1 : ∑ x : PeriodicLatticeSite Lf,
        ‖RMap (V (x, d.1.1)) (B (periodicLatticeShift x d.1.1, d.1.2)) - B (periodicLatticeShift x d.1.1, d.1.2)‖ ^ 2
        ≤ 4 * ρL ^ 2 * (ell : ℝ) ^ 2 * wnormSq S ell k B := by
      refine (Finset.sum_le_sum (fun x _ => link_term hS hell hR1 hM1 V ρL hρL hlink B x d.1.1 d.1.2)).trans ?_
      rw [← Finset.mul_sum, sum_shift_site d.1.1 (fun y => (((ell : ℝ) ^ bstrat S k (y, d.1.2))⁻¹) ^ 2 * ‖B (y, d.1.2)‖ ^ 2)]
      exact mul_le_mul_of_nonneg_left (wdir_le B d.1.2) (by positivity)
    have r2 : ∑ x : PeriodicLatticeSite Lf,
        ‖RMap (V (x, d.1.2)) (B (periodicLatticeShift x d.1.2, d.1.1)) - B (periodicLatticeShift x d.1.2, d.1.1)‖ ^ 2
        ≤ 4 * ρL ^ 2 * (ell : ℝ) ^ 2 * wnormSq S ell k B := by
      refine (Finset.sum_le_sum (fun x _ => link_term hS hell hR1 hM1 V ρL hρL hlink B x d.1.2 d.1.1)).trans ?_
      rw [← Finset.mul_sum, sum_shift_site d.1.2 (fun y => (((ell : ℝ) ^ bstrat S k (y, d.1.1))⁻¹) ^ 2 * ‖B (y, d.1.1)‖ ^ 2)]
      exact mul_le_mul_of_nonneg_left (wdir_le B d.1.1) (by positivity)
    nlinarith
  calc ∑ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite Lf, _ ≤
        ∑ _d : PeriodicPlaquetteDirections, (8 * Gs + 32 * (ell : ℝ) ^ 2 * ρL ^ 2 * wnormSq S ell k B) :=
        Finset.sum_le_sum (fun d _ => hd d)
    _ = 24 * Gs + 96 * (ell : ℝ) ^ 2 * ρL ^ 2 * wnormSq S ell k B := by
        rw [Finset.sum_const, Finset.card_univ, card_dirs]; simp; ring

/-- **the covariant divergence by gradients** -/
theorem div_upper (V : Cfg Lf) (ρL : ℝ) (hρL : 0 ≤ ρL)
    (hlink : ∀ b : Bond Lf, frobNorm (((V b : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      ≤ ρL / (ell : ℝ) ^ bstrat S k b)
    (B : BondFnL2 Lf) :
    ‖gradAdj V B‖ ^ 2 ≤ 6 * ∑ ν : Fin 3, gradW B ν + 24 * ρL ^ 2 * wnormSq S ell k B := by
  classical
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  set c : Fin 3 → PeriodicLatticeSite Lf → ℝ := fun μ y => ‖B (periodicLatticeShiftBack y μ, μ) - B (y, μ)‖
  set s : Fin 3 → PeriodicLatticeSite Lf → ℝ := fun μ y =>
    ‖RMap (V (periodicLatticeShiftBack y μ, μ))⁻¹ (B (periodicLatticeShiftBack y μ, μ)) - B (periodicLatticeShiftBack y μ, μ)‖
  have hpt : ∀ y, ‖(gradAdj V B) y‖ ^ 2 ≤ 6 * ∑ μ : Fin 3, (c μ y ^ 2 + s μ y ^ 2) := by
    intro y
    show ‖(WithLp.ofLp (gradAdj V B)) y‖ ^ 2 ≤ _
    rw [gradAdj_apply]
    unfold gradCovariantAdjointValue
    have e : ∀ μ : Fin 3, RMap (V (periodicLatticeShiftBack y μ, μ))⁻¹ ((WithLp.ofLp B) (periodicLatticeShiftBack y μ, μ))
        - (WithLp.ofLp B) (y, μ)
        = (B (periodicLatticeShiftBack y μ, μ) - B (y, μ))
          + (RMap (V (periodicLatticeShiftBack y μ, μ))⁻¹ (B (periodicLatticeShiftBack y μ, μ))
            - B (periodicLatticeShiftBack y μ, μ)) := fun μ => by
      show RMap (V (periodicLatticeShiftBack y μ, μ))⁻¹ (B (periodicLatticeShiftBack y μ, μ)) - B (y, μ) = _
      abel
    simp only [e]
    have t : ‖∑ μ : Fin 3, ((B (periodicLatticeShiftBack y μ, μ) - B (y, μ))
          + (RMap (V (periodicLatticeShiftBack y μ, μ))⁻¹ (B (periodicLatticeShiftBack y μ, μ))
            - B (periodicLatticeShiftBack y μ, μ)))‖
        ≤ ∑ μ : Fin 3, (c μ y + s μ y) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun μ _ => norm_add_le _ _))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) t 2
    refine h2.trans ?_
    simp only [Fin.sum_univ_three]
    have := sq_nonneg (c 0 y); have := sq_nonneg (s 0 y)
    nlinarith [sq_nonneg (c 0 y - c 1 y), sq_nonneg (c 0 y - c 2 y), sq_nonneg (c 1 y - c 2 y),
      sq_nonneg (s 0 y - s 1 y), sq_nonneg (s 0 y - s 2 y), sq_nonneg (s 1 y - s 2 y),
      sq_nonneg (c 0 y - s 0 y), sq_nonneg (c 0 y - s 1 y), sq_nonneg (c 0 y - s 2 y),
      sq_nonneg (c 1 y - s 0 y), sq_nonneg (c 1 y - s 1 y), sq_nonneg (c 1 y - s 2 y),
      sq_nonneg (c 2 y - s 0 y), sq_nonneg (c 2 y - s 1 y), sq_nonneg (c 2 y - s 2 y)]
  -- reindexing `y = x + e_μ`
  have hre : ∀ (μ : Fin 3) (g : Bond Lf → PeriodicLatticeSite Lf → ℝ),
      ∑ y : PeriodicLatticeSite Lf, g (periodicLatticeShiftBack y μ, μ) y
        = ∑ x : PeriodicLatticeSite Lf, g (x, μ) (periodicLatticeShift x μ) := by
    intro μ g
    rw [← sum_shift_site μ (fun y => g (periodicLatticeShiftBack y μ, μ) y)]
    simp only [periodicLatticeShiftBack_shift]
  have hc : ∀ μ, ∑ y, c μ y ^ 2 ≤ gradW B μ := by
    intro μ
    have := hre μ (fun b y => ‖B b - B (y, b.2)‖ ^ 2)
    simp only at this
    show ∑ y, ‖B (periodicLatticeShiftBack y μ, μ) - B (y, μ)‖ ^ 2 ≤ _
    rw [this]
    have h := grad_sub B μ μ
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [norm_sub_rev]
  have hwsum : ∑ μ : Fin 3, ∑ x : PeriodicLatticeSite Lf, (((ell : ℝ) ^ bstrat S k (x, μ))⁻¹) ^ 2 * ‖B (x, μ)‖ ^ 2
      = wnormSq S ell k B := by
    unfold wnormSq
    rw [show (Finset.univ : Finset (Bond Lf)) = Finset.univ ×ˢ Finset.univ from rfl, Finset.sum_product_right]
  have hs : ∀ μ, ∑ y, s μ y ^ 2 ≤ 4 * ρL ^ 2 *
      ∑ x : PeriodicLatticeSite Lf, (((ell : ℝ) ^ bstrat S k (x, μ))⁻¹) ^ 2 * ‖B (x, μ)‖ ^ 2 := by
    intro μ
    show ∑ y, ‖RMap (V (periodicLatticeShiftBack y μ, μ))⁻¹ (B (periodicLatticeShiftBack y μ, μ))
      - B (periodicLatticeShiftBack y μ, μ)‖ ^ 2 ≤ _
    have := hre μ (fun b _ => ‖RMap (V b)⁻¹ (B b) - B b‖ ^ 2)
    simp only at this
    rw [this]
    have hb : ∀ x : PeriodicLatticeSite Lf, ‖RMap (V (x, μ))⁻¹ (B (x, μ)) - B (x, μ)‖ ^ 2
        ≤ 4 * ρL ^ 2 * ((((ell : ℝ) ^ bstrat S k (x, μ))⁻¹) ^ 2 * ‖B (x, μ)‖ ^ 2) := by
      intro x
      have h1 := RMap_inv_sub_le (V (x, μ)) (B (x, μ))
      have h2 := hlink (x, μ)
      have hp : (0 : ℝ) < (ell : ℝ) ^ bstrat S k (x, μ) := by have := one_le_pow₀ (n := bstrat S k (x, μ)) hellr; positivity
      have h3 : ‖RMap (V (x, μ))⁻¹ (B (x, μ)) - B (x, μ)‖ ≤ 2 * ρL * ((ell : ℝ) ^ bstrat S k (x, μ))⁻¹ * ‖B (x, μ)‖ := by
        refine h1.trans ?_
        rw [div_eq_mul_inv] at h2
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (show (0:ℝ) ≤ 2 by norm_num)) (norm_nonneg (B (x, μ)))
        linarith
      have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      calc _ ≤ (2 * ρL * ((ell : ℝ) ^ bstrat S k (x, μ))⁻¹ * ‖B (x, μ)‖) ^ 2 := h4
        _ = _ := by ring
    exact (Finset.sum_le_sum (fun x _ => hb x)).trans (le_of_eq (Finset.mul_sum _ _ _).symm)
  rw [PiLp.norm_sq_eq_of_L2]
  refine (Finset.sum_le_sum (fun y _ => hpt y)).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [Finset.sum_add_distrib]
  have hc' := Finset.sum_le_sum (fun μ (_ : μ ∈ Finset.univ) => hc μ)
  have hs' : ∑ μ : Fin 3, ∑ y, s μ y ^ 2 ≤ 4 * ρL ^ 2 * wnormSq S ell k B := by
    rw [← hwsum, Finset.mul_sum]; exact Finset.sum_le_sum (fun μ _ => hs μ)
  linarith


end up


/-! ## the `Ginv` upper bound and the energy right inverse -/

section ginvup
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {W : ℕ}
  (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hR1 : 1 ≤ R) (hM1 : 1 ≤ M) (hW : 1 ≤ W)
  (hWR : W ≤ R * M * ell)
include hS hell hR1 hM1 hW hWR

/-- the sandwich constant `η` (lane E MI19) -/
noncomputable def etaS (ell W : ℕ) (cs ρ ε1 : ℝ) : ℝ :=
  ε1 + (1 + 1 / ε1) * (12 * ρ ^ 2 * (ell : ℝ) ^ 8 * (4 * ell / cs) ^ 2)
    + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) *
      ((ell : ℝ) * (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))) ^ 2

omit hS hell hR1 hM1 hW hWR in
theorem etaS_nonneg (ell W : ℕ) (cs ρ ε1 : ℝ) (hcs : 0 < cs) (hρ : 0 ≤ ρ) (hε1 : 0 < ε1)
    (hd : 0 ≤ Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) : 0 ≤ etaS ell W cs ρ ε1 := by
  unfold etaS; positivity

/-- **`Ginv` from above by gradients, the weighted norm and the mass** -/
theorem ginv_upper (hell0 : 0 < ell) (V : Cfg (scaleUp ell k Lu)) (a cs : ℝ)
    (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) V a cs)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k V ρ) (ε1 : ℝ) (hε1 : 0 < ε1)
    (ρL : ℝ) (hρL : 0 ≤ ρL)
    (hlink : ∀ b : Bond (scaleUp ell k Lu),
      frobNorm (((V b : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρL / (ell : ℝ) ^ bstrat S k b)
    (Lam : Set (PeriodicLatticeSite Lu)) (A : ↥(bondSupp (geomOf ell k S))) :
    ⟪A, (gparams ell k Lu hell0 S V a Lam).data.Ginv A⟫
      ≤ (1 + etaS ell W cs ρ ε1) * (30 * ∑ ν : Fin 3, gradW (A : BondFnL2 (scaleUp ell k Lu)) ν
          + (96 * (ell : ℝ) ^ 2 + 24) * ρL ^ 2 * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
          + ‖Ymass (geomOf ell k S) V a (A : BondFnL2 (scaleUp ell k Lu))‖ ^ 2)
        + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) := by
  have hF := ginv_form hell0 S V a Lam hp.ha.le hp.hu A
  have hsw := (sandwich hS hell hR1 hM1 hW hWR V a cs hp ρ hρ hreg ε1 hε1 (A : BondFnL2 (scaleUp ell k Lu))).2
  have e : ⟪A, (gparams ell k Lu hell0 S V a Lam).data.Ginv A⟫ = Fform S ell k V a (A : BondFnL2 (scaleUp ell k Lu)) := by
    rw [hF]; rfl
  rw [e]
  refine hsw.trans ?_
  have hc := curl_upper hS hell hR1 hM1 V ρL hρL hlink (A : BondFnL2 (scaleUp ell k Lu))
  have hd := div_upper hS hell hR1 hM1 V ρL hρL hlink (A : BondFnL2 (scaleUp ell k Lu))
  have hT : ‖Tfull (geomOf ell k S) V (A : BondFnL2 (scaleUp ell k Lu))‖ ^ 2
      ≤ ‖gradAdj V (A : BondFnL2 (scaleUp ell k Lu))‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (Rproj_norm_le (geomOf ell k S) V _) 2
  have hN := N_le_wnorm hS hell0 (A : BondFnL2 (scaleUp ell k Lu))
  have hη : 0 ≤ 1 + (ε1 + (1 + 1 / ε1) * (12 * ρ ^ 2 * (ell : ℝ) ^ 8 * (4 * ell / cs) ^ 2)
        + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) *
          ((ell : ℝ) * (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))) ^ 2) := by
    have hlg : 0 ≤ Real.log ell := Real.log_nonneg (by exact_mod_cast (show 1 ≤ ell by omega))
    have hq : 0 ≤ 2 * (ell : ℝ) ^ 2 * Real.log ell / W := by positivity
    have h := etaS_nonneg ell W cs ρ ε1 hp.hcs hρ hε1 (by linarith [Real.add_one_le_exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W)])
    unfold etaS at h; linarith
  have hν : 0 ≤ 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) := by positivity
  unfold G0form etaS
  have hG : ‖plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 V (A : BondFnL2 (scaleUp ell k Lu)))‖ ^ 2
        + ‖Tfull (geomOf ell k S) V (A : BondFnL2 (scaleUp ell k Lu))‖ ^ 2
        + ‖Ymass (geomOf ell k S) V a (A : BondFnL2 (scaleUp ell k Lu))‖ ^ 2
      ≤ 30 * ∑ ν : Fin 3, gradW (A : BondFnL2 (scaleUp ell k Lu)) ν
          + (96 * (ell : ℝ) ^ 2 + 24) * ρL ^ 2 * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
          + ‖Ymass (geomOf ell k S) V a (A : BondFnL2 (scaleUp ell k Lu))‖ ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hG hη
  have := mul_le_mul_of_nonneg_left hN hν
  linarith

/-- **the energy right inverse from a gradient-controlled right inverse** -/
theorem hext_of_rightinv (hell0 : 0 < ell) (V : Cfg (scaleUp ell k Lu)) (a cs : ℝ)
    (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) V a cs)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k V ρ) (ε1 : ℝ) (hε1 : 0 < ε1)
    (ρL : ℝ) (hρL : 0 ≤ ρL)
    (hlink : ∀ b : Bond (scaleUp ell k Lu),
      frobNorm (((V b : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρL / (ell : ℝ) ^ bstrat S k b)
    (Lam : Set (PeriodicLatticeSite Lu)) (cW cG : ℝ) (hcW : 0 ≤ cW) (hcG : 0 ≤ cG)
    (hR : ∀ u : FSp (geomOf ell k S), ∃ x : ↥(bondSupp (geomOf ell k S)),
      (gparams ell k Lu hell0 S V a Lam).data.Q x = u ∧
      wnormSq S ell k (x : BondFnL2 (scaleUp ell k Lu)) ≤ cW * nD u ∧
      ∀ ν0 : Fin 3, gradW (x : BondFnL2 (scaleUp ell k Lu)) ν0 ≤ cG * nD u)
    (v : FSp (geomOf ell k S)) :
    ∃ g : ↥(bondSupp (geomOf ell k S)), (gparams ell k Lu hell0 S V a Lam).data.Q g = v ∧
      ⟪g, (gparams ell k Lu hell0 S V a Lam).data.Ginv g⟫
        ≤ ((1 + etaS ell W cs ρ ε1) * (90 * cG + (96 * (ell : ℝ) ^ 2 + 24) * ρL ^ 2 * cW) / a
            + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) * cW / a + (1 + etaS ell W cs ρ ε1))
          * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v‖ ^ 2 := by
  obtain ⟨x, hx, hw, hg⟩ := hR v
  refine ⟨x, hx, ?_⟩
  have ha := hp.ha
  have hup := ginv_upper hS hell hR1 hM1 hW hWR hell0 V a cs hp ρ hρ hreg ε1 hε1 ρL hρL hlink Lam x
  -- the mass term is `‖√w v‖²`
  have hY : Ymass (geomOf ell k S) V a (x : BondFnL2 (scaleUp ell k Lu))
      = diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v := by
    rw [← hx]; rfl
  rw [hY] at hup
  -- `nD v = ‖√w v‖² / a`
  have hnD : nD v * a = ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    unfold nD
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [diagW_apply', norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (by unfold massW; positivity)]
    unfold wD massW; rw [show (((geomOf ell k S).ell : ℕ) : ℝ) = (ell : ℝ) from rfl]; ring
  set Nv := ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v‖ ^ 2 with hNv
  have hnD' : nD v = Nv / a := by rw [eq_div_iff ha.ne']; exact hnD
  have hgs : ∑ ν : Fin 3, gradW (x : BondFnL2 (scaleUp ell k Lu)) ν ≤ 3 * (cG * nD v) := by
    rw [Fin.sum_univ_three]; have := hg 0; have := hg 1; have := hg 2; linarith
  rw [hnD'] at hgs hw
  have hη := etaS_nonneg ell W cs ρ ε1 hp.hcs hρ hε1 (by
    have : 0 ≤ 2 * (ell : ℝ) ^ 2 * Real.log ell / W := by
      have : 0 ≤ Real.log ell := Real.log_nonneg (by exact_mod_cast (show 1 ≤ ell by omega)); positivity
    linarith [Real.add_one_le_exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W)])
  have hν : 0 ≤ 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) := by positivity
  have hNv0 : 0 ≤ Nv := sq_nonneg _
  have h1 : 30 * ∑ ν : Fin 3, gradW (x : BondFnL2 (scaleUp ell k Lu)) ν
        + (96 * (ell : ℝ) ^ 2 + 24) * ρL ^ 2 * wnormSq S ell k (x : BondFnL2 (scaleUp ell k Lu)) + Nv
      ≤ (90 * cG + (96 * (ell : ℝ) ^ 2 + 24) * ρL ^ 2 * cW) / a * Nv + Nv := by
    have h2 := mul_le_mul_of_nonneg_left hw (show 0 ≤ (96 * (ell : ℝ) ^ 2 + 24) * ρL ^ 2 by positivity)
    have e : (90 * cG + (96 * (ell : ℝ) ^ 2 + 24) * ρL ^ 2 * cW) / a * Nv
        = 30 * (3 * (cG * (Nv / a))) + (96 * (ell : ℝ) ^ 2 + 24) * ρL ^ 2 * (cW * (Nv / a)) := by
      field_simp; ring
    rw [e]; linarith
  have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 + etaS ell W cs ρ ε1 by linarith)
  have h4 := mul_le_mul_of_nonneg_left hw hν
  have e2 : ((1 + etaS ell W cs ρ ε1) * (90 * cG + (96 * (ell : ℝ) ^ 2 + 24) * ρL ^ 2 * cW) / a
        + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) * cW / a + (1 + etaS ell W cs ρ ε1)) * Nv
      = (1 + etaS ell W cs ρ ε1) * ((90 * cG + (96 * (ell : ℝ) ^ 2 + 24) * ρL ^ 2 * cW) / a * Nv + Nv)
        + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) * (cW * (Nv / a)) := by
    field_simp; ring
  rw [e2]
  unfold etaS at hup h3 ⊢
  linarith

end ginvup

#print axioms RMap_sub_le
#print axioms RMap_inv_sub_le
#print axioms bstrat_next
#print axioms grad_sub
#print axioms gradW_le_sum
#print axioms wdir_le
#print axioms link_term
#print axioms curl_upper
#print axioms div_upper
#print axioms etaS
#print axioms etaS_nonneg
#print axioms ginv_upper
#print axioms hext_of_rightinv

end AdalyFormal.M1DStrat
