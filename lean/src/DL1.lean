import MI14
import DLR26

/-!
# DL1 -- the LOCAL pieces of the Combes–Thomas form for `Ginv`: curl, curvature, `Δ'` (M1 D-layer lane, 2026-10-14)

Weights: a site function `ξ`; bonds weighted at the tail, plaquettes at the base point `q.1`.
* `exp_sub_one_le_mul` : `e^{at} − 1 ≤ t (e^a − 1)` (`0 ≤ t ≤ 1`, `0 ≤ a`).
* **`curl_cj_diff`** : if `|ξ(x) − ξ(x+e_μ)| ≤ θ'/ℓ^{strat x}` on every bond, then
  `‖e^{ξ} χ_P C (e^{−ξ} A) − χ_P C A‖ ≤ √12 ℓ (e^{θ'} − 1) ‖e^{−σ} A‖`  (stratified analogue of DL25 `curl_cjp_norm`);
* **`curv_cj`** : if `|ξ(x) − ξ(x+e_μ)| ≤ L` on every bond and `HolRegime ρ`, then
  `‖e^{ξ} χ_P C(Dm(e^{−ξ} λ))‖ ≤ e^{2L} √12 ρ ℓ⁴ ‖e^{−2σ} λ‖`  (MI14 `curv_strat` with the weights);
* **`dp_cj`** : under the same hypotheses, `|Δ'_P(e^{ξ} x, e^{−ξ} y)| ≤ e^{2L} (17/√2)·12 ρ ℓ⁴ ‖e^{−σ} x‖ ‖e^{−σ} y‖`
  (the weights cancel inside each plaquette up to `e^{2L}`; MI13 `deltaPrime_strat` is the case `ξ = 0`, `x = y`).
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
open AdalyFormal.StatementLane (Tower Admissible bigSide pdist)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply deltaPrimeBilL2NormLoc deltaPrimeBilNormLoc deltaPrimeBilRawLoc_apply)
open AdalyFormal.Balaban.DeltaPrimeOperator (bilPlaq)
open AdalyFormal.Balaban.LemmaAssembly (plaqBondSq plaqBondSq_nonneg)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

theorem exp_sub_one_le_mul (a t : ℝ) (ha : 0 ≤ a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (a * t) - 1 ≤ t * (Real.exp a - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ a) (show 0 ≤ 1 - t by linarith) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have e : t * a = a * t := mul_comm _ _
  rw [e] at h
  linarith

/-- `|e^{u} − 1| ≤ e^{|u|} − 1` -/
theorem abs_exp_sub_one_le_abs (u : ℝ) : |Real.exp u - 1| ≤ Real.exp |u| - 1 := by
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by linarith [Real.add_one_le_exp u])]
  · rw [abs_of_neg h]
    have h1 : Real.exp u < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr h
    rw [abs_of_neg (by linarith)]
    have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
    have h3 : 0 < Real.exp u := Real.exp_pos u
    have h4 : 1 - Real.exp u ≤ Real.exp (-u) - 1 := by nlinarith [Real.add_one_le_exp u, Real.add_one_le_exp (-u)]
    linarith

section loc
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf}
  (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hR1 : 1 ≤ R) (hM1 : 1 ≤ M)
include hS hell hR1 hM1

/-- the stratified factor `e^{|u|} − 1 ≤ (e^{θ'} − 1)/ℓ^{s}` when `|u| ≤ θ'/ℓ^s` -/
theorem strat_exp_le (θ' : ℝ) (hθ' : 0 ≤ θ') (s : ℕ) (u : ℝ) (hu : |u| ≤ θ' / (ell : ℝ) ^ s) :
    |Real.exp u - 1| ≤ (Real.exp θ' - 1) / (ell : ℝ) ^ s := by
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hp : (0 : ℝ) < (ell : ℝ) ^ s := by have := one_le_pow₀ (n := s) hellr; positivity
  have ht0 : 0 ≤ 1 / (ell : ℝ) ^ s := by positivity
  have ht1 : 1 / (ell : ℝ) ^ s ≤ 1 := by rw [div_le_one hp]; exact one_le_pow₀ hellr
  refine (abs_exp_sub_one_le_abs u).trans ?_
  have h1 : Real.exp |u| ≤ Real.exp (θ' * (1 / (ell : ℝ) ^ s)) := by
    apply Real.exp_le_exp.mpr; rw [mul_one_div]; exact hu
  have h2 := exp_sub_one_le_mul θ' (1 / (ell : ℝ) ^ s) hθ' ht0 ht1
  have e : 1 / (ell : ℝ) ^ s * (Real.exp θ' - 1) = (Real.exp θ' - 1) / (ell : ℝ) ^ s := by ring
  linarith

/-- **the curl Combes–Thomas difference** -/
theorem curl_cj_diff (U : Cfg Lf) (ξ : PeriodicLatticeSite Lf → ℝ) (θ' : ℝ) (hθ' : 0 ≤ θ')
    (hL : ∀ (x : PeriodicLatticeSite Lf) (μ : Fin 3),
      |ξ x - ξ (periodicLatticeShift x μ)| ≤ θ' / (ell : ℝ) ^ stratG (geomOf ell k S) x)
    (A : BondFnL2 Lf) :
    ‖plaqMul (fun q => Real.exp (ξ q.1)) (plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (bondWt (-ξ) A)))
        - plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U A)‖
      ≤ Real.sqrt 12 * (ell : ℝ) * (Real.exp θ' - 1) * ‖bondWt (-sigG (geomOf ell k S)) A‖ := by
  classical
  set A' := bondWt (-sigG (geomOf ell k S)) A
  have hell0 : 0 < ell := by omega
  have hellr : (0 : ℝ) < ell := by exact_mod_cast hell0
  have hE : 0 ≤ Real.exp θ' - 1 := by linarith [Real.add_one_le_exp θ']
  set E := Real.exp θ' - 1 with hEdef
  -- pointwise
  have hpt : ∀ q : PeriodicLatticePlaquette Lf,
      ‖(plaqMul (fun q => Real.exp (ξ q.1)) (plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (bondWt (-ξ) A)))
        - plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U A)) q‖ ^ 2
      ≤ 2 * (ell : ℝ) ^ 2 * E ^ 2 * (‖A' (periodicLatticeShift q.1 q.2.1.1, q.2.1.2)‖ ^ 2
          + ‖A' (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)‖ ^ 2) := by
    intro q
    by_cases hq : q ∈ plaqIn (S.Om 0)
    · have hval : (plaqMul (fun q => Real.exp (ξ q.1)) (plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (bondWt (-ξ) A)))
          - plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U A)) q
          = (Real.exp (ξ q.1 - ξ (periodicLatticeShift q.1 q.2.1.1)) - 1) • RMap (U (q.1, q.2.1.1)) (A (periodicLatticeShift q.1 q.2.1.1, q.2.1.2))
            - (Real.exp (ξ q.1 - ξ (periodicLatticeShift q.1 q.2.1.2)) - 1) • RMap (U (q.1, q.2.1.2)) (A (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)) := by
        rw [PiLp.sub_apply, plaqMul_apply, plaqMask_apply, plaqMask_apply, if_pos hq, if_pos hq, curlLM_apply, curlLM_apply]
        unfold curlValueCovariant
        have e1 : ∀ b : Bond Lf, (WithLp.ofLp (bondWt (-ξ) A)) b = Real.exp (-ξ b.1) • A b := fun b => by
          show (bondWt (-ξ) A) b = _
          rw [bondWt_apply]; rfl
        have e2 : ∀ b : Bond Lf, (WithLp.ofLp A) b = A b := fun b => rfl
        simp only [e1, e2, map_smul, smul_add, smul_sub, sub_smul, smul_smul]
        have k1 : Real.exp (ξ q.1) * Real.exp (-ξ q.1) = 1 := by rw [← Real.exp_add]; simp
        have k2 : Real.exp (ξ q.1) * Real.exp (-ξ (periodicLatticeShift q.1 q.2.1.1)) = Real.exp (ξ q.1 - ξ (periodicLatticeShift q.1 q.2.1.1)) := by
          rw [← Real.exp_add]; ring_nf
        have k3 : Real.exp (ξ q.1) * Real.exp (-ξ (periodicLatticeShift q.1 q.2.1.2)) = Real.exp (ξ q.1 - ξ (periodicLatticeShift q.1 q.2.1.2)) := by
          rw [← Real.exp_add]; ring_nf
        rw [k1, k2, k3]
        simp only [one_smul]
        abel
      set Dmu := Real.exp (ξ q.1 - ξ (periodicLatticeShift q.1 q.2.1.1)) - 1
      set Dnu := Real.exp (ξ q.1 - ξ (periodicLatticeShift q.1 q.2.1.2)) - 1
      have hdμ : |Dmu| ≤ E / (ell : ℝ) ^ stratG (geomOf ell k S) q.1 :=
        strat_exp_le hS hell hR1 hM1 θ' hθ' _ _ (hL q.1 q.2.1.1)
      have hdν : |Dnu| ≤ E / (ell : ℝ) ^ stratG (geomOf ell k S) q.1 :=
        strat_exp_le hS hell hR1 hM1 θ' hθ' _ _ (hL q.1 q.2.1.2)
      -- convert to tail weights
      have hconv : ∀ (τ : Fin 3) (b : Bond Lf), b.1 = periodicLatticeShift q.1 τ →
          ‖A b‖ ^ 2 ≤ (ell : ℝ) ^ 2 * ((ell : ℝ) ^ stratG (geomOf ell k S) q.1) ^ 2 * ‖A' b‖ ^ 2 := by
        intro τ b hbt
        have hpd : pdist q.1 b.1 ≤ 2 := by rw [hbt]; exact pdist_corner1 hS hell hR1 hM1 q.1 τ
        have hadj := strat_near hS hell hR1 hM1 hpd
        rw [strat_eq_stratG hell0 hS, strat_eq_stratG hell0 hS] at hadj
        have e : ‖A' b‖ ^ 2 = ‖A b‖ ^ 2 / ((ell : ℝ) ^ stratG (geomOf ell k S) b.1) ^ 2 := by
          show ‖(bondWt (-sigG (geomOf ell k S)) A) b‖ ^ 2 = _
          rw [bondWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
          have : Real.exp ((-sigG (geomOf ell k S)) b.1) ^ 2 = 1 / ((ell : ℝ) ^ stratG (geomOf ell k S) b.1) ^ 2 := by
            show Real.exp (-(sigG (geomOf ell k S) b.1)) ^ 2 = _
            rw [Real.exp_neg, exp_sig (geomOf ell k S) hell0, inv_pow, one_div]; rfl
          rw [this]; ring
        rw [e]
        have hp1 : (0 : ℝ) < ((ell : ℝ) ^ stratG (geomOf ell k S) b.1) ^ 2 := by positivity
        rw [mul_div_assoc', le_div_iff₀ hp1]
        have hpow : ((ell : ℝ) ^ stratG (geomOf ell k S) b.1) ^ 2 ≤ (ell : ℝ) ^ 2 * ((ell : ℝ) ^ stratG (geomOf ell k S) q.1) ^ 2 := by
          rw [← pow_mul, ← pow_mul, ← pow_add]
          exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ ell by omega)) (by omega)
        nlinarith [sq_nonneg ‖A b‖]
      have hA1 := hconv q.2.1.1 (periodicLatticeShift q.1 q.2.1.1, q.2.1.2) rfl
      have hA2 := hconv q.2.1.2 (periodicLatticeShift q.1 q.2.1.2, q.2.1.1) rfl
      rw [hval]
      have h1 := norm_sub_le (Dmu • RMap (U (q.1, q.2.1.1)) (A (periodicLatticeShift q.1 q.2.1.1, q.2.1.2)))
        (Dnu • RMap (U (q.1, q.2.1.2)) (A (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)))
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap,
        AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap] at h1
      set P := (ell : ℝ) ^ stratG (geomOf ell k S) q.1
      have hP : 0 < P := by positivity
      set a1 := ‖A (periodicLatticeShift q.1 q.2.1.1, q.2.1.2)‖
      set a2 := ‖A (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)‖
      have ha1 : 0 ≤ a1 := norm_nonneg _
      have ha2 : 0 ≤ a2 := norm_nonneg _
      -- |Δ| a ≤ (E/P) a, and (E/P)² a² ≤ E² ℓ² ‖A'‖²
      have hb1 : |Dmu| * a1 ≤ E / P * a1 := mul_le_mul_of_nonneg_right hdμ ha1
      have hb2 : |Dnu| * a2 ≤ E / P * a2 := mul_le_mul_of_nonneg_right hdν ha2
      have hc1 : (E / P * a1) ^ 2 ≤ (ell : ℝ) ^ 2 * E ^ 2 * ‖A' (periodicLatticeShift q.1 q.2.1.1, q.2.1.2)‖ ^ 2 := by
        rw [div_mul_eq_mul_div, div_pow, div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left hA1 (sq_nonneg E)
        nlinarith
      have hc2 : (E / P * a2) ^ 2 ≤ (ell : ℝ) ^ 2 * E ^ 2 * ‖A' (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)‖ ^ 2 := by
        rw [div_mul_eq_mul_div, div_pow, div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left hA2 (sq_nonneg E)
        nlinarith
      have hx1 : 0 ≤ E / P * a1 := by positivity
      have hx2 : 0 ≤ E / P * a2 := by positivity
      have hsum : ‖Dmu • RMap (U (q.1, q.2.1.1)) (A (periodicLatticeShift q.1 q.2.1.1, q.2.1.2))
          - Dnu • RMap (U (q.1, q.2.1.2)) (A (periodicLatticeShift q.1 q.2.1.2, q.2.1.1))‖ ≤ E / P * a1 + E / P * a2 := by
        linarith
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hsum 2
      nlinarith [sq_nonneg (E / P * a1 - E / P * a2)]
    · have hz : (plaqMul (fun q => Real.exp (ξ q.1)) (plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (bondWt (-ξ) A)))
          - plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U A)) q = 0 := by
        rw [PiLp.sub_apply, plaqMul_apply, plaqMask_apply, plaqMask_apply, if_neg hq, if_neg hq, smul_zero, sub_zero]
      rw [hz, norm_zero, zero_pow two_ne_zero]
      have := sq_nonneg ‖A' (periodicLatticeShift q.1 q.2.1.1, q.2.1.2)‖
      have := sq_nonneg ‖A' (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)‖
      positivity
  have hsq : ‖plaqMul (fun q => Real.exp (ξ q.1)) (plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (bondWt (-ξ) A)))
        - plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U A)‖ ^ 2
      ≤ (Real.sqrt 12 * (ell : ℝ) * E * ‖A'‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ q, ‖(plaqMul (fun q => Real.exp (ξ q.1)) (plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (bondWt (-ξ) A)))
          - plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U A)) q‖ ^ 2
        ≤ ∑ q : PeriodicLatticePlaquette Lf, 2 * (ell : ℝ) ^ 2 * E ^ 2 * (‖A' (periodicLatticeShift q.1 q.2.1.1, q.2.1.2)‖ ^ 2
            + ‖A' (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)‖ ^ 2) := Finset.sum_le_sum (fun q _ => hpt q)
      _ = 2 * (ell : ℝ) ^ 2 * E ^ 2 * ∑ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite Lf,
            (‖A' (periodicLatticeShift x d.1.1, d.1.2)‖ ^ 2 + ‖A' (periodicLatticeShift x d.1.2, d.1.1)‖ ^ 2) := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type_right]
      _ ≤ 2 * (ell : ℝ) ^ 2 * E ^ 2 * ∑ _d : PeriodicPlaquetteDirections, 2 * ‖A'‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d _ => ?_)) (by positivity)
          rw [Finset.sum_add_distrib, sum_shift_site d.1.1 (fun y => ‖A' (y, d.1.2)‖ ^ 2),
            sum_shift_site d.1.2 (fun y => ‖A' (y, d.1.1)‖ ^ 2)]
          linarith [sum_dir_le A' d.1.2, sum_dir_le A' d.1.1]
      _ = (Real.sqrt 12 * (ell : ℝ) * E * ‖A'‖) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, card_dirs, mul_pow, mul_pow, mul_pow,
            Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
          simp; ring
  have hR : 0 ≤ Real.sqrt 12 * (ell : ℝ) * E * ‖A'‖ := by positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).mp hsq

/-- two steps of a bond-Lipschitz weight -/
theorem two_step (ξ : PeriodicLatticeSite Lf → ℝ) (L : ℝ)
    (hL : ∀ (x : PeriodicLatticeSite Lf) (μ : Fin 3), |ξ x - ξ (periodicLatticeShift x μ)| ≤ L)
    (x : PeriodicLatticeSite Lf) (μ ν : Fin 3) :
    ξ x - ξ (periodicLatticeShift (periodicLatticeShift x μ) ν) ≤ 2 * L := by
  have h1 := (abs_le.mp (hL x μ)).2
  have h2 := (abs_le.mp (hL (periodicLatticeShift x μ) ν)).2
  linarith

/-- **the conjugated curvature** (crude, `e^{2L}`) -/
theorem curv_cj (U : Cfg Lf) (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k U ρ)
    (ξ : PeriodicLatticeSite Lf → ℝ) (L : ℝ)
    (hL : ∀ (x : PeriodicLatticeSite Lf) (μ : Fin 3), |ξ x - ξ (periodicLatticeShift x μ)| ≤ L)
    (lam : SiteL2 Lf) :
    ‖plaqMul (fun q => Real.exp (ξ q.1)) (plaqMask (plaqIn (S.Om 0))
        (curlCovariantLM_L2 U (Dm (geomOf ell k S) U (siteWt (-ξ) lam))))‖
      ≤ Real.exp (2 * L) * (Real.sqrt 12 * ρ * (ell : ℝ) ^ 4)
        * ‖siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S))) lam‖ := by
  classical
  set G := geomOf ell k S
  set Λ := siteWt (-(sigG G + sigG G)) lam
  have hell0 : 0 < ell := by omega
  have hellr : (0 : ℝ) < ell := by exact_mod_cast hell0
  have hpt : ∀ p : PeriodicLatticePlaquette Lf,
      ‖(plaqMul (fun q => Real.exp (ξ q.1)) (plaqMask (plaqIn (S.Om 0))
          (curlCovariantLM_L2 U (Dm G U (siteWt (-ξ) lam))))) p‖ ^ 2
        ≤ Real.exp (2 * L) ^ 2 * (4 * ρ ^ 2 * (ell : ℝ) ^ 8)
          * ‖Λ (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)‖ ^ 2 := by
    intro p
    rw [plaqMul_apply, plaqMask_apply]
    split_ifs with hp
    · set z := periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2
      have hc := curv_pt U (siteMask G.Om0 (siteWt (-ξ) lam)) p
      have e : (curlCovariantLM_L2 U (Dm G U (siteWt (-ξ) lam))) p
          = (curlC U (gradL2 U (siteMask G.Om0 (siteWt (-ξ) lam)))) p := rfl
      rw [e]
      have hd := hol_strat hS hell hR1 hM1 U ρ hρ hreg p hp
      have hz : pdist p.1 z ≤ 2 := pdist_corner2 hS hell hR1 hM1 p.1 _ _
      have hinv := inv_strat_le hS hell hR1 hM1 hz
      have hgz : ‖siteMask G.Om0 (siteWt (-ξ) lam) z‖ ≤ Real.exp (-ξ z) * ‖lam z‖ := by
        by_cases hz0 : z ∈ G.Om0
        · rw [siteMask_on _ _ _ hz0, siteWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          rfl
        · rw [siteMask_off _ _ _ hz0, norm_zero]; positivity
      have hΛ : ‖Λ z‖ = ‖lam z‖ * (1 / ((ell : ℝ) ^ AdalyFormal.M1.strat S k z) ^ 2) := by
        show ‖siteWt (-(sigG G + sigG G)) lam z‖ = _
        rw [siteWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
        congr 1
        rw [Pi.neg_apply, Pi.add_apply, neg_add, Real.exp_add, ← sq, exp_neg_sig_sq hS hell hR1 hM1 z]
      set s := AdalyFormal.M1.strat S k p.1
      set sz := AdalyFormal.M1.strat S k z
      have hdn : 0 ≤ AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p) :=
        AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _
      have hstep : Real.exp (ξ p.1) * Real.exp (-ξ z) ≤ Real.exp (2 * L) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
        have := two_step hS hell hR1 hM1 ξ L hL p.1 p.2.1.1 p.2.1.2
        linarith
      have h1 : ‖Real.exp (ξ p.1) • (curlC U (gradL2 U (siteMask G.Om0 (siteWt (-ξ) lam)))) p‖
          ≤ Real.exp (2 * L) * (2 * (ρ * (ell : ℝ) ^ 2 / ((ell : ℝ) ^ s) ^ 2) * ‖lam z‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have h0 : ‖(curlC U (gradL2 U (siteMask G.Om0 (siteWt (-ξ) lam)))) p‖
            ≤ 2 * (ρ * (ell : ℝ) ^ 2 / ((ell : ℝ) ^ s) ^ 2) * (Real.exp (-ξ z) * ‖lam z‖) :=
          hc.trans (mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num)) hgz (norm_nonneg _) (by positivity))
        calc Real.exp (ξ p.1) * ‖(curlC U (gradL2 U (siteMask G.Om0 (siteWt (-ξ) lam)))) p‖
            ≤ Real.exp (ξ p.1) * (2 * (ρ * (ell : ℝ) ^ 2 / ((ell : ℝ) ^ s) ^ 2) * (Real.exp (-ξ z) * ‖lam z‖)) :=
              mul_le_mul_of_nonneg_left h0 (Real.exp_pos _).le
          _ = (Real.exp (ξ p.1) * Real.exp (-ξ z)) * (2 * (ρ * (ell : ℝ) ^ 2 / ((ell : ℝ) ^ s) ^ 2) * ‖lam z‖) := by ring
          _ ≤ Real.exp (2 * L) * (2 * (ρ * (ell : ℝ) ^ 2 / ((ell : ℝ) ^ s) ^ 2) * ‖lam z‖) :=
              mul_le_mul_of_nonneg_right hstep (by positivity)
      have h2 : 2 * (ρ * (ell : ℝ) ^ 2 / ((ell : ℝ) ^ s) ^ 2) * ‖lam z‖ ≤ 2 * ρ * (ell : ℝ) ^ 4 * ‖Λ z‖ := by
        rw [hΛ]
        have := mul_le_mul_of_nonneg_left hinv (show (0:ℝ) ≤ 2 * ρ * (ell : ℝ) ^ 2 * ‖lam z‖ by positivity)
        calc 2 * (ρ * (ell : ℝ) ^ 2 / ((ell : ℝ) ^ s) ^ 2) * ‖lam z‖
            = 2 * ρ * (ell : ℝ) ^ 2 * ‖lam z‖ * (1 / ((ell : ℝ) ^ s) ^ 2) := by ring
          _ ≤ 2 * ρ * (ell : ℝ) ^ 2 * ‖lam z‖ * ((ell : ℝ) ^ 2 / ((ell : ℝ) ^ sz) ^ 2) := this
          _ = 2 * ρ * (ell : ℝ) ^ 4 * (‖lam z‖ * (1 / ((ell : ℝ) ^ sz) ^ 2)) := by ring
      have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
      calc ‖Real.exp (ξ p.1) • (curlC U (gradL2 U (siteMask G.Om0 (siteWt (-ξ) lam)))) p‖ ^ 2
          ≤ (Real.exp (2 * L) * (2 * ρ * (ell : ℝ) ^ 4 * ‖Λ z‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
        _ = Real.exp (2 * L) ^ 2 * (4 * ρ ^ 2 * (ell : ℝ) ^ 8) * ‖Λ z‖ ^ 2 := by ring
    · rw [smul_zero, norm_zero, zero_pow two_ne_zero]; positivity
  have hsq : ‖plaqMul (fun q => Real.exp (ξ q.1)) (plaqMask (plaqIn (S.Om 0))
        (curlCovariantLM_L2 U (Dm G U (siteWt (-ξ) lam))))‖ ^ 2
      ≤ (Real.exp (2 * L) * (Real.sqrt 12 * ρ * (ell : ℝ) ^ 4) * ‖Λ‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ p, ‖(plaqMul (fun q => Real.exp (ξ q.1)) (plaqMask (plaqIn (S.Om 0))
            (curlCovariantLM_L2 U (Dm G U (siteWt (-ξ) lam))))) p‖ ^ 2
        ≤ ∑ p : PeriodicLatticePlaquette Lf, Real.exp (2 * L) ^ 2 * (4 * ρ ^ 2 * (ell : ℝ) ^ 8) *
            ‖Λ (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)‖ ^ 2 :=
          Finset.sum_le_sum (fun p _ => hpt p)
      _ = Real.exp (2 * L) ^ 2 * (4 * ρ ^ 2 * (ell : ℝ) ^ 8) * ∑ d : PeriodicPlaquetteDirections,
            ∑ x : PeriodicLatticeSite Lf, ‖Λ (periodicLatticeShift (periodicLatticeShift x d.1.1) d.1.2)‖ ^ 2 := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type_right]
      _ = Real.exp (2 * L) ^ 2 * (4 * ρ ^ 2 * (ell : ℝ) ^ 8) * ∑ _d : PeriodicPlaquetteDirections, ‖Λ‖ ^ 2 := by
          congr 1
          exact Finset.sum_congr rfl (fun d _ => sum_site_le Λ d.1.1 d.1.2)
      _ = (Real.exp (2 * L) * (Real.sqrt 12 * ρ * (ell : ℝ) ^ 4) * ‖Λ‖) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, card_dirs, mul_pow, mul_pow, mul_pow, mul_pow,
            Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
          simp; ring
  have hR : 0 ≤ Real.exp (2 * L) * (Real.sqrt 12 * ρ * (ell : ℝ) ^ 4) * ‖Λ‖ := by positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).mp hsq

/-- the local symmetrised plaquette form, bilinear bound with the LOCAL curvature -/
theorem Sp_loc (U : Cfg Lf) (A B : Bond Lf → SuTwo) (p : PeriodicLatticePlaquette Lf) :
    |Sp U p A B| ≤ (17 / Real.sqrt 2) * AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p)
      * Real.sqrt (plaqBondSq A p) * Real.sqrt (plaqBondSq B p) := by
  set d := AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p)
  have hd0 : 0 ≤ d := AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hβ : 0 ≤ (17 / Real.sqrt 2) * d := by positivity
  refine amgm_to_prod _ _ _ _ hβ (plaqBondSq_nonneg A p) (plaqBondSq_nonneg B p) (fun s hs => ?_)
  have key : 4 * s * Sp U p A B = Sp U p (s • A + B) (s • A + B) - Sp U p (s • A - B) (s • A - B) := by
    simp only [Sp_add_left, Sp_add_right, Sp_sub_left, Sp_sub_right, Sp_smul_left, Sp_smul_right, Sp_symm U p B A]
    ring
  have hq : ∀ X : Bond Lf → SuTwo, |Sp U p X X| ≤ (17 / Real.sqrt 2) * d * plaqBondSq X p := by
    intro X
    have h := bilPlaq_dv U X p
    unfold Sp
    rw [show (1 / 4 : ℝ) * (bilPlaq U p X X + bilPlaq U p X X) = (1 / 2) * bilPlaq U p X X by ring, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have e : (34 / Real.sqrt 2) * d * plaqBondSq X p = 2 * ((17 / Real.sqrt 2) * d * plaqBondSq X p) := by ring
    linarith
  have h1 := hq (s • A + B)
  have h2 := hq (s • A - B)
  have hpar := pbs_par A B p s
  have h3 : |4 * s * Sp U p A B| ≤ (17 / Real.sqrt 2) * d * (2 * s ^ 2 * plaqBondSq A p + 2 * plaqBondSq B p) := by
    rw [key, ← hpar, mul_add]
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * s)] at h3
  rw [show ((17 / Real.sqrt 2) * d / 2) * (s * plaqBondSq A p + plaqBondSq B p / s)
      = ((17 / Real.sqrt 2) * d * (2 * s ^ 2 * plaqBondSq A p + 2 * plaqBondSq B p)) / (4 * s) by field_simp; ring]
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- `Δ'_P` as a plaquette sum of `Sp` -/
theorem dp_eq_sum (U : Cfg Lf) (P : Set (PeriodicLatticePlaquette Lf)) (x y : BondFnL2 Lf) :
    deltaPrimeBilL2NormLoc U P x y
      = ∑ p : PeriodicLatticePlaquette Lf, (open Classical in if p ∈ P then Sp U p (WithLp.ofLp x) (WithLp.ofLp y) else 0) := by
  classical
  show deltaPrimeBilNormLoc U P (WithLp.ofLp x) (WithLp.ofLp y) = _
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul, deltaPrimeBilRawLoc_apply]
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs
  · unfold Sp; ring
  · ring

/-- the per-plaquette weighted squares -/
theorem pbs_wt (ξ : PeriodicLatticeSite Lf → ℝ) (L : ℝ)
    (hL : ∀ (x : PeriodicLatticeSite Lf) (μ : Fin 3), |ξ x - ξ (periodicLatticeShift x μ)| ≤ L)
    (c : ℝ) (hc : c = 1 ∨ c = -1) (x : BondFnL2 Lf) (p : PeriodicLatticePlaquette Lf) :
    plaqBondSq (WithLp.ofLp (bondWt (c • ξ) x)) p
      ≤ Real.exp (2 * (c * ξ p.1)) * Real.exp (2 * L) * plaqBondSq (WithLp.ofLp x) p := by
  have hb : ∀ b : Bond Lf, (b.1 = p.1 ∨ b.1 = periodicLatticeShift p.1 p.2.1.1 ∨ b.1 = periodicLatticeShift p.1 p.2.1.2) →
      ‖(WithLp.ofLp (bondWt (c • ξ) x)) b‖ ^ 2 ≤ Real.exp (2 * (c * ξ p.1)) * Real.exp (2 * L) * ‖(WithLp.ofLp x) b‖ ^ 2 := by
    intro b hb
    show ‖(bondWt (c • ξ) x) b‖ ^ 2 ≤ _
    rw [bondWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hL p.1 p.2.1.1)
    have hdiff : |ξ b.1 - ξ p.1| ≤ L := by
      rcases hb with h | h | h
      · rw [h, sub_self, abs_zero]; exact hL0
      · rw [h, abs_sub_comm]; exact hL _ _
      · rw [h, abs_sub_comm]; exact hL _ _
    have hcb : |c * ξ b.1 - c * ξ p.1| ≤ L := by
      rcases hc with h | h <;> rw [h]
      · simpa using hdiff
      · rw [show -1 * ξ b.1 - -1 * ξ p.1 = -(ξ b.1 - ξ p.1) by ring, abs_neg]; exact hdiff
    have := (abs_le.mp hcb).2
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast; linarith
  unfold plaqBondSq
  have h1 := hb (p.1, p.2.1.1) (Or.inl rfl)
  have h2 := hb (p.1, p.2.1.2) (Or.inl rfl)
  have h3 := hb (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) (Or.inr (Or.inl rfl))
  have h4 := hb (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) (Or.inr (Or.inr rfl))
  nlinarith

/-- **the conjugated `Δ'`** (crude, `e^{2L}`) -/
theorem dp_cj (U : Cfg Lf) (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k U ρ)
    (ξ : PeriodicLatticeSite Lf → ℝ) (L : ℝ)
    (hL : ∀ (x : PeriodicLatticeSite Lf) (μ : Fin 3), |ξ x - ξ (periodicLatticeShift x μ)| ≤ L)
    (x y : BondFnL2 Lf) :
    |deltaPrimeBilL2NormLoc U (plaqIn (S.Om 0)) (bondWt ξ x) (bondWt (-ξ) y)|
      ≤ Real.exp (2 * L) * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4))
        * (‖bondWt (-sigG (geomOf ell k S)) x‖ * ‖bondWt (-sigG (geomOf ell k S)) y‖) := by
  classical
  rw [dp_eq_sum hS hell hR1 hM1]
  set x' := bondWt (-sigG (geomOf ell k S)) x
  set y' := bondWt (-sigG (geomOf ell k S)) y
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hell0 : 0 < ell := by omega
  have hellr : (0 : ℝ) < ell := by exact_mod_cast hell0
  -- the conversion `ℓ^{-2s_p} sq_p(x) ≤ ℓ² sq_p(x')`
  have hconvX : ∀ (z : BondFnL2 Lf) (p : PeriodicLatticePlaquette Lf),
      plaqBondSq (WithLp.ofLp z) p / ((ell : ℝ) ^ AdalyFormal.M1.strat S k p.1) ^ 2
        ≤ (ell : ℝ) ^ 2 * plaqBondSq (WithLp.ofLp (bondWt (-sigG (geomOf ell k S)) z)) p := by
    intro z p
    set s := AdalyFormal.M1.strat S k p.1
    have hy : ∀ b : Bond Lf, pdist p.1 b.1 ≤ 2 →
        ‖(WithLp.ofLp z) b‖ ^ 2 / ((ell : ℝ) ^ s) ^ 2
          ≤ (ell : ℝ) ^ 2 * ‖(WithLp.ofLp (bondWt (-sigG (geomOf ell k S)) z)) b‖ ^ 2 := by
      intro b hb
      have h1 := inv_strat_le hS hell hR1 hM1 hb
      have e : ‖(WithLp.ofLp (bondWt (-sigG (geomOf ell k S)) z)) b‖ ^ 2
          = ‖(WithLp.ofLp z) b‖ ^ 2 * (1 / ((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1) ^ 2) := by
        show ‖(bondWt (-sigG (geomOf ell k S)) z) b‖ ^ 2 = _
        rw [bondWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, mul_comm]
        congr 1
        exact exp_neg_sig_sq hS hell hR1 hM1 b.1
      rw [e, div_eq_mul_one_div]
      have := mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖(WithLp.ofLp z) b‖)
      rw [div_eq_mul_one_div ((ell : ℝ) ^ 2)] at this
      nlinarith [sq_nonneg ‖(WithLp.ofLp z) b‖]
    have hb1 : pdist p.1 (p.1, p.2.1.1).1 ≤ 2 := by simp [AdalyFormal.StatementLaneR8.pdist_self]
    have hb2 : pdist p.1 (p.1, p.2.1.2).1 ≤ 2 := by simp [AdalyFormal.StatementLaneR8.pdist_self]
    have hb3 : pdist p.1 (periodicLatticeShift p.1 p.2.1.1, p.2.1.2).1 ≤ 2 := pdist_corner1 hS hell hR1 hM1 p.1 _
    have hb4 : pdist p.1 (periodicLatticeShift p.1 p.2.1.2, p.2.1.1).1 ≤ 2 := pdist_corner1 hS hell hR1 hM1 p.1 _
    unfold plaqBondSq
    have := hy _ hb1; have := hy _ hb2; have := hy _ hb3; have := hy _ hb4
    rw [add_div, add_div, add_div]
    nlinarith
  set K := Real.exp (2 * L) * (17 / Real.sqrt 2) * (ρ * (ell : ℝ) ^ 4) with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ p : PeriodicLatticePlaquette Lf,
      |(if p ∈ plaqIn (S.Om 0) then Sp U p (WithLp.ofLp (bondWt ξ x)) (WithLp.ofLp (bondWt (-ξ) y)) else 0)|
        ≤ K * (Real.sqrt (plaqBondSq (WithLp.ofLp x') p) * Real.sqrt (plaqBondSq (WithLp.ofLp y') p)) := by
    intro p
    split_ifs with hp
    · refine (Sp_loc hS hell hR1 hM1 U _ _ p).trans ?_
      have hd := hol_strat hS hell hR1 hM1 U ρ hρ hreg p hp
      set d := AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p)
      have hd0 : 0 ≤ d := AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _
      set s := AdalyFormal.M1.strat S k p.1
      have hP : (0 : ℝ) < ((ell : ℝ) ^ s) ^ 2 := by positivity
      -- weights
      have wx := pbs_wt hS hell hR1 hM1 ξ L hL 1 (Or.inl rfl) x p
      have wy := pbs_wt hS hell hR1 hM1 ξ L hL (-1) (Or.inr rfl) y p
      rw [one_smul] at wx
      rw [show ((-1 : ℝ) • ξ) = -ξ by funext z; simp] at wy
      have cx := hconvX x p
      have cy := hconvX y p
      set a := plaqBondSq (WithLp.ofLp x) p
      set b := plaqBondSq (WithLp.ofLp y) p
      set a' := plaqBondSq (WithLp.ofLp x') p
      set b' := plaqBondSq (WithLp.ofLp y') p
      have ha := plaqBondSq_nonneg (WithLp.ofLp x) p
      have hb := plaqBondSq_nonneg (WithLp.ofLp y) p
      have ha' := plaqBondSq_nonneg (WithLp.ofLp x') p
      have hb' := plaqBondSq_nonneg (WithLp.ofLp y') p
      -- √(sq e^{ξ}x) √(sq e^{-ξ}y) ≤ e^{2L} √a √b
      have hprod : Real.sqrt (plaqBondSq (WithLp.ofLp (bondWt ξ x)) p) * Real.sqrt (plaqBondSq (WithLp.ofLp (bondWt (-ξ) y)) p)
          ≤ Real.exp (2 * L) * (Real.sqrt a * Real.sqrt b) := by
        rw [← Real.sqrt_mul (plaqBondSq_nonneg _ p), ← Real.sqrt_mul ha]
        have hm : plaqBondSq (WithLp.ofLp (bondWt ξ x)) p * plaqBondSq (WithLp.ofLp (bondWt (-ξ) y)) p
            ≤ (Real.exp (2 * L)) ^ 2 * (a * b) := by
          have e1 : Real.exp (2 * (1 * ξ p.1)) * Real.exp (2 * (-1 * ξ p.1)) = 1 := by
            rw [← Real.exp_add]; simp
          have := mul_le_mul wx wy (plaqBondSq_nonneg _ p) (by positivity)
          calc _ ≤ Real.exp (2 * (1 * ξ p.1)) * Real.exp (2 * L) * a * (Real.exp (2 * (-1 * ξ p.1)) * Real.exp (2 * L) * b) := this
            _ = (Real.exp (2 * (1 * ξ p.1)) * Real.exp (2 * (-1 * ξ p.1))) * (Real.exp (2 * L)) ^ 2 * (a * b) := by ring
            _ = _ := by rw [e1, one_mul]
        refine (Real.sqrt_le_sqrt hm).trans (le_of_eq ?_)
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]
      -- d √a √b ≤ ρ ℓ⁴ √a' √b'
      have hab : d * (Real.sqrt a * Real.sqrt b) ≤ ρ * (ell : ℝ) ^ 4 * (Real.sqrt a' * Real.sqrt b') := by
        have h1 : Real.sqrt a ≤ (ell : ℝ) ^ s * ((ell : ℝ) * Real.sqrt a') := by
          have : a ≤ ((ell : ℝ) ^ s) ^ 2 * ((ell : ℝ) ^ 2 * a') := by rw [div_le_iff₀ hP] at cx; linarith
          calc Real.sqrt a ≤ Real.sqrt (((ell : ℝ) ^ s) ^ 2 * ((ell : ℝ) ^ 2 * a')) := Real.sqrt_le_sqrt this
            _ = (ell : ℝ) ^ s * ((ell : ℝ) * Real.sqrt a') := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_mul (by positivity),
                Real.sqrt_sq hellr.le]
        have h2 : Real.sqrt b ≤ (ell : ℝ) ^ s * ((ell : ℝ) * Real.sqrt b') := by
          have : b ≤ ((ell : ℝ) ^ s) ^ 2 * ((ell : ℝ) ^ 2 * b') := by rw [div_le_iff₀ hP] at cy; linarith
          calc Real.sqrt b ≤ Real.sqrt (((ell : ℝ) ^ s) ^ 2 * ((ell : ℝ) ^ 2 * b')) := Real.sqrt_le_sqrt this
            _ = (ell : ℝ) ^ s * ((ell : ℝ) * Real.sqrt b') := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_mul (by positivity),
                Real.sqrt_sq hellr.le]
        have h12 := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
        have hdd : d * ((ell : ℝ) ^ s) ^ 2 ≤ ρ * (ell : ℝ) ^ 2 := by
          rw [le_div_iff₀ hP] at hd; linarith
        calc d * (Real.sqrt a * Real.sqrt b)
            ≤ d * ((ell : ℝ) ^ s * ((ell : ℝ) * Real.sqrt a') * ((ell : ℝ) ^ s * ((ell : ℝ) * Real.sqrt b'))) :=
              mul_le_mul_of_nonneg_left h12 hd0
          _ = (d * ((ell : ℝ) ^ s) ^ 2) * ((ell : ℝ) ^ 2 * (Real.sqrt a' * Real.sqrt b')) := by ring
          _ ≤ (ρ * (ell : ℝ) ^ 2) * ((ell : ℝ) ^ 2 * (Real.sqrt a' * Real.sqrt b')) :=
              mul_le_mul_of_nonneg_right hdd (by positivity)
          _ = _ := by ring
      calc (17 / Real.sqrt 2) * d * Real.sqrt (plaqBondSq (WithLp.ofLp (bondWt ξ x)) p)
            * Real.sqrt (plaqBondSq (WithLp.ofLp (bondWt (-ξ) y)) p)
          = (17 / Real.sqrt 2) * d * (Real.sqrt (plaqBondSq (WithLp.ofLp (bondWt ξ x)) p)
            * Real.sqrt (plaqBondSq (WithLp.ofLp (bondWt (-ξ) y)) p)) := by ring
        _ ≤ (17 / Real.sqrt 2) * d * (Real.exp (2 * L) * (Real.sqrt a * Real.sqrt b)) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = Real.exp (2 * L) * (17 / Real.sqrt 2) * (d * (Real.sqrt a * Real.sqrt b)) := by ring
        _ ≤ Real.exp (2 * L) * (17 / Real.sqrt 2) * (ρ * (ell : ℝ) ^ 4 * (Real.sqrt a' * Real.sqrt b')) :=
            mul_le_mul_of_nonneg_left hab (by positivity)
        _ = K * (Real.sqrt a' * Real.sqrt b') := by rw [hK]; ring
    · rw [abs_zero]; positivity
  -- Cauchy–Schwarz over plaquettes
  have hCS : ∑ p : PeriodicLatticePlaquette Lf,
        Real.sqrt (plaqBondSq (WithLp.ofLp x') p) * Real.sqrt (plaqBondSq (WithLp.ofLp y') p)
      ≤ Real.sqrt (∑ p : PeriodicLatticePlaquette Lf, plaqBondSq (WithLp.ofLp x') p)
        * Real.sqrt (∑ p : PeriodicLatticePlaquette Lf, plaqBondSq (WithLp.ofLp y') p) := by
    have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun p => Real.sqrt (plaqBondSq (WithLp.ofLp x') p)) (fun p => Real.sqrt (plaqBondSq (WithLp.ofLp y') p))
    simp only [Real.sq_sqrt (plaqBondSq_nonneg _ _)] at this
    exact this
  have hx12 := pbs_sum_le x'
  have hy12 := pbs_sum_le y'
  have hsx : Real.sqrt (∑ p : PeriodicLatticePlaquette Lf, plaqBondSq (WithLp.ofLp x') p) ≤ Real.sqrt 12 * ‖x'‖ := by
    calc _ ≤ Real.sqrt (12 * ‖x'‖ ^ 2) := Real.sqrt_le_sqrt hx12
      _ = Real.sqrt 12 * ‖x'‖ := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]
  have hsy : Real.sqrt (∑ p : PeriodicLatticePlaquette Lf, plaqBondSq (WithLp.ofLp y') p) ≤ Real.sqrt 12 * ‖y'‖ := by
    calc _ ≤ Real.sqrt (12 * ‖y'‖ ^ 2) := Real.sqrt_le_sqrt hy12
      _ = Real.sqrt 12 * ‖y'‖ := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]
  have h12 : Real.sqrt 12 * Real.sqrt 12 = 12 := Real.mul_self_sqrt (by norm_num)
  calc |∑ p : PeriodicLatticePlaquette Lf, (if p ∈ plaqIn (S.Om 0) then Sp U p (WithLp.ofLp (bondWt ξ x))
          (WithLp.ofLp (bondWt (-ξ) y)) else 0)|
      ≤ ∑ p : PeriodicLatticePlaquette Lf, K * (Real.sqrt (plaqBondSq (WithLp.ofLp x') p)
          * Real.sqrt (plaqBondSq (WithLp.ofLp y') p)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p _ => hpt p))
    _ = K * ∑ p : PeriodicLatticePlaquette Lf, Real.sqrt (plaqBondSq (WithLp.ofLp x') p)
          * Real.sqrt (plaqBondSq (WithLp.ofLp y') p) := by rw [Finset.mul_sum]
    _ ≤ K * ((Real.sqrt 12 * ‖x'‖) * (Real.sqrt 12 * ‖y'‖)) :=
        mul_le_mul_of_nonneg_left (hCS.trans (mul_le_mul hsx hsy (Real.sqrt_nonneg _) (by positivity))) hK0
    _ = Real.exp (2 * L) * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) * (‖x'‖ * ‖y'‖) := by
        rw [hK]
        have : K * ((Real.sqrt 12 * ‖x'‖) * (Real.sqrt 12 * ‖y'‖)) = K * (Real.sqrt 12 * Real.sqrt 12) * (‖x'‖ * ‖y'‖) := by ring
        rw [hK] at this; rw [this, h12]; ring

end loc

#print axioms exp_sub_one_le_mul
#print axioms abs_exp_sub_one_le_abs
#print axioms strat_exp_le
#print axioms curl_cj_diff
#print axioms two_step
#print axioms curv_cj
#print axioms Sp_loc
#print axioms dp_eq_sum
#print axioms pbs_wt
#print axioms dp_cj

end AdalyFormal.M1DStrat
