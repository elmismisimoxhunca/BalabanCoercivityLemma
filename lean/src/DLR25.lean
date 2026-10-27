import DLR24

/-!
# DL25 -- the curl `C = D_U^1`, the curvature operator `K = C ∘ D_U`, and their Combes–Thomas commutators (genuine)

* `plaqWt φ`, `plaqWP φ` : multiplication by `e^{φ(p₀)}` (base point) on `PlaqFnL2`.
* `curl_conj_pt` : `(C⁺A − CA)(p) = (e^{φ(x)−φ(x+μ)}−1)R(U_{xμ})A(x+μ,ν) − (e^{φ(x)−φ(x+ν)}−1)R(U_{xν})A(x+ν,μ)`, norm bound;
  **`curl_cjp_norm`/`curl_cjm_norm`** : `‖C^± − C‖ ≤ 6(e^{θ'}−1)`.
* `curv_pt` (the curvature identity, tree `curlValueCovariant_gradValueCovariant`): `‖(C D λ)(p)‖ ≤ 2 dv(U(∂p)) ‖λ(z_p)‖`;
  **`curv_norm`** : `‖C ∘ D‖ ≤ 6 q0` when every plaquette has `dv(U(∂p)) ≤ q0`;
  **`curv_cjp_norm`/`curv_cjm_norm`** : `‖K^± − K‖ ≤ 6 q0 (e^{2θ'}−1)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant curlValueCovariant
  RMap_mul_apply curlValueCovariant_gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)

variable {L : PeriodicLatticeExtent}

/-- multiplication by `e^{φ(p₀)}` on plaquette fields -/
noncomputable def plaqWt (φ : PeriodicLatticeSite L → ℝ) : PlaqFnL2 L →L[ℝ] PlaqFnL2 L :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun p => Real.exp (φ p.1) • f p)
      map_add' := fun f g => by refine PiLp.ext (fun x => ?_); simp [smul_add]
      map_smul' := fun c f => by
        refine PiLp.ext (fun x => ?_)
        simp only [PiLp.smul_apply, RingHom.id_apply, PiLp.toLp_apply]
        exact smul_comm _ _ _ }

theorem plaqWt_apply (φ : PeriodicLatticeSite L → ℝ) (f : PlaqFnL2 L) (p : PeriodicLatticePlaquette L) :
    (plaqWt φ f) p = Real.exp (φ p.1) • f p := rfl

theorem plaqWt_neg_cancel (φ : PeriodicLatticeSite L → ℝ) (f : PlaqFnL2 L) : plaqWt φ (plaqWt (-φ) f) = f := by
  refine PiLp.ext (fun x => ?_)
  rw [plaqWt_apply, plaqWt_apply, smul_smul, ← Real.exp_add]
  simp

theorem plaqWt_cancel_neg (φ : PeriodicLatticeSite L → ℝ) (f : PlaqFnL2 L) : plaqWt (-φ) (plaqWt φ f) = f := by
  have := plaqWt_neg_cancel (-φ) f
  simpa using this

theorem plaqWt_symm (φ : PeriodicLatticeSite L → ℝ) (f g : PlaqFnL2 L) : ⟪plaqWt φ f, g⟫ = ⟪f, plaqWt φ g⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [plaqWt_apply, plaqWt_apply, real_inner_smul_left, real_inner_smul_right]

noncomputable def plaqWP (φ : PeriodicLatticeSite L → ℝ) : WPair (PlaqFnL2 L) where
  w := plaqWt φ
  wi := plaqWt (-φ)
  w_wi := plaqWt_neg_cancel φ
  wi_w := plaqWt_cancel_neg φ
  w_sym := plaqWt_symm φ
  wi_sym := plaqWt_symm (-φ)

/-- the curl on the `L²` carriers -/
noncomputable abbrev curlC (U : Cfg L) : BondFnL2 L →L[ℝ] PlaqFnL2 L := curlCovariantCLM_L2 U

theorem curlC_apply (U : Cfg L) (A : BondFnL2 L) (p : PeriodicLatticePlaquette L) :
    (curlC U A) p = curlValueCovariant U (WithLp.ofLp A) p := by
  have h := curlCovariantCLM_L2_toLp U (WithLp.ofLp A)
  have hA : WithLp.toLp 2 (WithLp.ofLp A) = A := rfl
  rw [hA] at h
  show (curlCovariantCLM_L2 U A) p = _
  rw [h]

/-! ## shift sums -/

theorem sum_shift_site (μ : Fin 3) (g : PeriodicLatticeSite L → ℝ) :
    ∑ x : PeriodicLatticeSite L, g (periodicLatticeShift x μ) = ∑ x : PeriodicLatticeSite L, g x := by
  have hbij : Function.Bijective (fun x : PeriodicLatticeSite L => periodicLatticeShift x μ) := by
    refine (Function.Injective.bijective_of_finite ?_)
    intro x y hxy
    funext ν
    have h := congrFun hxy ν
    unfold periodicLatticeShift at h
    by_cases hν : ν = μ
    · subst hν
      simp only [Function.update_self] at h
      exact add_right_cancel h
    · simpa [Function.update_of_ne hν] using h
  exact Function.Bijective.sum_comp hbij g

theorem sum_dir_le (A : BondFnL2 L) (ν : Fin 3) : ∑ y : PeriodicLatticeSite L, ‖A (y, ν)‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type_right]
  exact Finset.single_le_sum (f := fun ν' => ∑ y : PeriodicLatticeSite L, ‖A (y, ν')‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ ν)

theorem sum_site_le (f : SiteL2 L) (μ ν : Fin 3) :
    ∑ x : PeriodicLatticeSite L, ‖f (periodicLatticeShift (periodicLatticeShift x μ) ν)‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, sum_shift_site μ (fun y => ‖f (periodicLatticeShift y ν)‖ ^ 2),
    sum_shift_site ν (fun y => ‖f y‖ ^ 2)]

theorem card_dirs_le : (Fintype.card PeriodicPlaquetteDirections : ℝ) ≤ 9 := by
  have h : Fintype.card PeriodicPlaquetteDirections ≤ Fintype.card (Fin 3 × Fin 3) := Fintype.card_subtype_le _
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  exact_mod_cast h

/-! ## the curl commutator -/

theorem curl_conj_pt (U : Cfg L) (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) :
    ‖(plaqWt φ (curlC U (bondWt (-φ) A)) - curlC U A) p‖
      ≤ (Real.exp θ' - 1) * (‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖
          + ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖) := by
  rw [PiLp.sub_apply, plaqWt_apply, curlC_apply, curlC_apply]
  have e1 : ∀ b : Bond L, (WithLp.ofLp (bondWt (-φ) A)) b = Real.exp (-φ b.1) • A b := fun b => rfl
  have e2 : ∀ b : Bond L, (WithLp.ofLp A) b = A b := fun b => rfl
  unfold curlValueCovariant
  simp only [e1, e2, map_smul]
  set x := p.1
  set μ := p.2.1.1
  set ν := p.2.1.2
  have key : Real.exp (φ x) • (Real.exp (-φ (x, μ).1) • A (x, μ)
        + Real.exp (-φ (periodicLatticeShift x μ, ν).1) • RMap (U (x, μ)) (A (periodicLatticeShift x μ, ν))
        - Real.exp (-φ (periodicLatticeShift x ν, μ).1) • RMap (U (x, ν)) (A (periodicLatticeShift x ν, μ))
        - Real.exp (-φ (x, ν).1) • A (x, ν))
      - (A (x, μ) + RMap (U (x, μ)) (A (periodicLatticeShift x μ, ν))
        - RMap (U (x, ν)) (A (periodicLatticeShift x ν, μ)) - A (x, ν))
      = (Real.exp (φ x - φ (periodicLatticeShift x μ)) - 1) • RMap (U (x, μ)) (A (periodicLatticeShift x μ, ν))
        - (Real.exp (φ x - φ (periodicLatticeShift x ν)) - 1) • RMap (U (x, ν)) (A (periodicLatticeShift x ν, μ)) := by
    simp only [smul_add, smul_sub, smul_smul, ← Real.exp_add]
    have h0 : φ x + -φ x = 0 := by ring
    have h1 : φ x + -φ (periodicLatticeShift x μ) = φ x - φ (periodicLatticeShift x μ) := by ring
    have h2 : φ x + -φ (periodicLatticeShift x ν) = φ x - φ (periodicLatticeShift x ν) := by ring
    simp only [h0, h1, h2, Real.exp_zero, one_smul, sub_smul, one_smul]
    abel
  rw [key]
  have b1 : |Real.exp (φ x - φ (periodicLatticeShift x μ)) - 1| ≤ Real.exp θ' - 1 := by
    refine abs_exp_sub_one_le_of _ _ ?_
    rw [abs_sub_comm]; exact hφ x μ
  have b2 : |Real.exp (φ x - φ (periodicLatticeShift x ν)) - 1| ≤ Real.exp θ' - 1 := by
    refine abs_exp_sub_one_le_of _ _ ?_
    rw [abs_sub_comm]; exact hφ x ν
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap,
    AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap, mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right b1 (norm_nonneg _)) (mul_le_mul_of_nonneg_right b2 (norm_nonneg _))

theorem curl_conj_le (U : Cfg L) (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) (A : BondFnL2 L) :
    ‖plaqWt φ (curlC U (bondWt (-φ) A)) - curlC U A‖ ≤ 6 * (Real.exp θ' - 1) * ‖A‖ := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have hδ : 0 ≤ Real.exp θ' - 1 := by linarith [Real.add_one_le_exp θ']
  have hsq : ‖plaqWt φ (curlC U (bondWt (-φ) A)) - curlC U A‖ ^ 2 ≤ (6 * (Real.exp θ' - 1) * ‖A‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    have hpt : ∀ p : PeriodicLatticePlaquette L, ‖(plaqWt φ (curlC U (bondWt (-φ) A)) - curlC U A) p‖ ^ 2
        ≤ 2 * (Real.exp θ' - 1) ^ 2 * (‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
          + ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) := by
      intro p
      have h := curl_conj_pt U φ θ' hφ A p
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      nlinarith [sq_nonneg (‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖
        - ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖)]
    have hs1 : ∀ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite L,
        (‖A (periodicLatticeShift x d.1.1, d.1.2)‖ ^ 2 + ‖A (periodicLatticeShift x d.1.2, d.1.1)‖ ^ 2) ≤ 2 * ‖A‖ ^ 2 := by
      intro d
      rw [Finset.sum_add_distrib, sum_shift_site d.1.1 (fun y => ‖A (y, d.1.2)‖ ^ 2),
        sum_shift_site d.1.2 (fun y => ‖A (y, d.1.1)‖ ^ 2)]
      linarith [sum_dir_le A d.1.2, sum_dir_le A d.1.1]
    calc ∑ p, ‖(plaqWt φ (curlC U (bondWt (-φ) A)) - curlC U A) p‖ ^ 2
        ≤ ∑ p : PeriodicLatticePlaquette L, 2 * (Real.exp θ' - 1) ^ 2 * (‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
          + ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) := Finset.sum_le_sum (fun p _ => hpt p)
      _ = 2 * (Real.exp θ' - 1) ^ 2 * ∑ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite L,
          (‖A (periodicLatticeShift x d.1.1, d.1.2)‖ ^ 2 + ‖A (periodicLatticeShift x d.1.2, d.1.1)‖ ^ 2) := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type_right]
      _ ≤ 2 * (Real.exp θ' - 1) ^ 2 * ∑ _d : PeriodicPlaquetteDirections, 2 * ‖A‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d _ => hs1 d)) (by positivity)
      _ = 2 * (Real.exp θ' - 1) ^ 2 * ((Fintype.card PeriodicPlaquetteDirections : ℝ) * (2 * ‖A‖ ^ 2)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ 2 * (Real.exp θ' - 1) ^ 2 * (9 * (2 * ‖A‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right card_dirs_le (by positivity)) (by positivity)
      _ ≤ (6 * (Real.exp θ' - 1) * ‖A‖) ^ 2 := by nlinarith [sq_nonneg (Real.exp θ' - 1), sq_nonneg ‖A‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem curl_cjp_norm (U : Cfg L) (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) :
    ‖cjp (bondWP φ) (plaqWP φ) (curlC U) - curlC U‖ ≤ 6 * (Real.exp θ' - 1) := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have hδ : 0 ≤ Real.exp θ' - 1 := by linarith [Real.add_one_le_exp θ']
  refine opnorm_le_of _ _ (by positivity) (fun A => ?_)
  rw [ContinuousLinearMap.sub_apply, cjp_apply]
  exact curl_conj_le U φ θ' hφ A

theorem curl_cjm_norm (U : Cfg L) (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) :
    ‖cjm (bondWP φ) (plaqWP φ) (curlC U) - curlC U‖ ≤ 6 * (Real.exp θ' - 1) := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have hδ : 0 ≤ Real.exp θ' - 1 := by linarith [Real.add_one_le_exp θ']
  refine opnorm_le_of _ _ (by positivity) (fun A => ?_)
  rw [ContinuousLinearMap.sub_apply]
  have e : cjm (bondWP φ) (plaqWP φ) (curlC U) A = plaqWt (-φ) (curlC U (bondWt (-(-φ)) A)) := by
    rw [neg_neg]; rfl
  rw [e]
  exact curl_conj_le U (-φ) θ' (WtLip_neg θ' φ hφ) A

/-! ## the curvature operator `K = C ∘ D` -/

theorem curv_value (U : Cfg L) (f : SiteL2 L) (p : PeriodicLatticePlaquette L) :
    (curlC U (gradL2 U f)) p
      = RMap (U (p.1, p.2.1.1) * U (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
          (f (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2))
        - RMap (U (p.1, p.2.1.2) * U (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))
          (f (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)) := by
  rw [curlC_apply]
  have h : WithLp.ofLp (gradL2 U f) = gradValueCovariant U (WithLp.ofLp f) := gradL2_apply U f
  rw [h, curlValueCovariant_gradValueCovariant]


theorem RMap_diff_le (g1 g2 : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : SuTwo) :
    ‖RMap g1 v - RMap g2 v‖
      ≤ 2 * AdalyFormal.Balaban.RMapLipschitz.frobNorm (((g1 * g2⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) - 1) * ‖v‖ := by
  have e : RMap g1 v = RMap (g1 * g2⁻¹) (RMap g2 v) := by
    rw [RMap_mul_apply, inv_mul_cancel_right]
  rw [e]
  have h := AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le (g1 * g2⁻¹) (RMap g2 v)
  rwa [AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap] at h

theorem curv_pt (U : Cfg L) (f : SiteL2 L) (p : PeriodicLatticePlaquette L) :
    ‖(curlC U (gradL2 U f)) p‖
      ≤ 2 * AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p)
          * ‖f (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)‖ := by
  rw [curv_value]
  refine (RMap_diff_le _ _ _).trans (le_of_eq ?_)
  unfold AdalyFormal.CurvBlock.dv periodicPlaquetteHolonomy
  congr 3
  group

theorem curv_le (U : Cfg L) (q0 : ℝ) (hq0 : 0 ≤ q0)
    (hplaq : ∀ p : PeriodicLatticePlaquette L, AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p) ≤ q0)
    (f : SiteL2 L) : ‖curlC U (gradL2 U f)‖ ≤ 6 * q0 * ‖f‖ := by
  have hsq : ‖curlC U (gradL2 U f)‖ ^ 2 ≤ (6 * q0 * ‖f‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    have hpt : ∀ p : PeriodicLatticePlaquette L, ‖(curlC U (gradL2 U f)) p‖ ^ 2
        ≤ 4 * q0 ^ 2 * ‖f (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)‖ ^ 2 := by
      intro p
      have h := (curv_pt U f p).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hplaq p) (by norm_num))
        (norm_nonneg _))
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      nlinarith
    calc ∑ p, ‖(curlC U (gradL2 U f)) p‖ ^ 2
        ≤ ∑ p : PeriodicLatticePlaquette L,
            4 * q0 ^ 2 * ‖f (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)‖ ^ 2 :=
          Finset.sum_le_sum (fun p _ => hpt p)
      _ = 4 * q0 ^ 2 * ∑ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite L,
            ‖f (periodicLatticeShift (periodicLatticeShift x d.1.1) d.1.2)‖ ^ 2 := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type_right]
      _ = 4 * q0 ^ 2 * ((Fintype.card PeriodicPlaquetteDirections : ℝ) * ‖f‖ ^ 2) := by
          simp only [sum_site_le, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ 4 * q0 ^ 2 * (9 * ‖f‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right card_dirs_le (by positivity)) (by positivity)
      _ = (6 * q0 * ‖f‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem curv_norm (U : Cfg L) (q0 : ℝ) (hq0 : 0 ≤ q0)
    (hplaq : ∀ p : PeriodicLatticePlaquette L, AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p) ≤ q0) :
    ‖curlC U ∘L gradL2 U‖ ≤ 6 * q0 :=
  opnorm_le_of _ _ (by positivity) (fun f => curv_le U q0 hq0 hplaq f)

/-- the conjugated curvature operator, pointwise -/
theorem curv_conj_pt (U : Cfg L) (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) (f : SiteL2 L)
    (p : PeriodicLatticePlaquette L) :
    ‖(plaqWt φ (curlC U (gradL2 U (siteWt (-φ) f))) - curlC U (gradL2 U f)) p‖
      ≤ (Real.exp (2 * θ') - 1) * (2 * AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p)
          * ‖f (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)‖) := by
  set z := periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2
  have e : (plaqWt φ (curlC U (gradL2 U (siteWt (-φ) f))) - curlC U (gradL2 U f)) p
      = (Real.exp (φ p.1 - φ z) - 1) • (curlC U (gradL2 U f)) p := by
    rw [PiLp.sub_apply, plaqWt_apply, curv_value, curv_value]
    have hz : (siteWt (-φ) f) z = Real.exp (-φ z) • f z := rfl
    rw [hz, map_smul, map_smul, ← smul_sub, smul_smul, ← Real.exp_add, sub_smul, one_smul]
    congr 2
  rw [e, norm_smul, Real.norm_eq_abs]
  have hb : |φ p.1 - φ z| ≤ 2 * θ' := by
    have h1 := hφ p.1 p.2.1.1
    have h2 := hφ (periodicLatticeShift p.1 p.2.1.1) p.2.1.2
    calc |φ p.1 - φ z| = |(φ (periodicLatticeShift p.1 p.2.1.1) - φ p.1) + (φ z - φ (periodicLatticeShift p.1 p.2.1.1))| := by
          rw [abs_sub_comm]; congr 1; ring
      _ ≤ |φ (periodicLatticeShift p.1 p.2.1.1) - φ p.1| + |φ z - φ (periodicLatticeShift p.1 p.2.1.1)| := abs_add_le _ _
      _ ≤ 2 * θ' := by linarith
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  exact mul_le_mul (abs_exp_sub_one_le_of _ _ hb) (curv_pt U f p) (norm_nonneg _)
    (by linarith [Real.add_one_le_exp (2 * θ')])

theorem curv_conj_le (U : Cfg L) (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) (q0 : ℝ) (hq0 : 0 ≤ q0)
    (hplaq : ∀ p : PeriodicLatticePlaquette L, AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p) ≤ q0)
    (f : SiteL2 L) :
    ‖plaqWt φ (curlC U (gradL2 U (siteWt (-φ) f))) - curlC U (gradL2 U f)‖
      ≤ 6 * q0 * (Real.exp (2 * θ') - 1) * ‖f‖ := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have hδ : 0 ≤ Real.exp (2 * θ') - 1 := by linarith [Real.add_one_le_exp (2 * θ')]
  have hsq : ‖plaqWt φ (curlC U (gradL2 U (siteWt (-φ) f))) - curlC U (gradL2 U f)‖ ^ 2
      ≤ (6 * q0 * (Real.exp (2 * θ') - 1) * ‖f‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    have hpt : ∀ p : PeriodicLatticePlaquette L,
        ‖(plaqWt φ (curlC U (gradL2 U (siteWt (-φ) f))) - curlC U (gradL2 U f)) p‖ ^ 2
        ≤ 4 * (q0 * (Real.exp (2 * θ') - 1)) ^ 2
          * ‖f (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)‖ ^ 2 := by
      intro p
      have h := (curv_conj_pt U φ θ' hφ f p).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hplaq p) (by norm_num)) (norm_nonneg _)) hδ)
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      nlinarith
    calc ∑ p, ‖(plaqWt φ (curlC U (gradL2 U (siteWt (-φ) f))) - curlC U (gradL2 U f)) p‖ ^ 2
        ≤ ∑ p : PeriodicLatticePlaquette L, 4 * (q0 * (Real.exp (2 * θ') - 1)) ^ 2
            * ‖f (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)‖ ^ 2 :=
          Finset.sum_le_sum (fun p _ => hpt p)
      _ = 4 * (q0 * (Real.exp (2 * θ') - 1)) ^ 2 * ∑ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite L,
            ‖f (periodicLatticeShift (periodicLatticeShift x d.1.1) d.1.2)‖ ^ 2 := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type_right]
      _ = 4 * (q0 * (Real.exp (2 * θ') - 1)) ^ 2 * ((Fintype.card PeriodicPlaquetteDirections : ℝ) * ‖f‖ ^ 2) := by
          simp only [sum_site_le, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ 4 * (q0 * (Real.exp (2 * θ') - 1)) ^ 2 * (9 * ‖f‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right card_dirs_le (by positivity)) (by positivity)
      _ = (6 * q0 * (Real.exp (2 * θ') - 1) * ‖f‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem curv_cjp_norm (U : Cfg L) (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) (q0 : ℝ) (hq0 : 0 ≤ q0)
    (hplaq : ∀ p : PeriodicLatticePlaquette L, AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p) ≤ q0) :
    ‖cjp (siteWP φ) (plaqWP φ) (curlC U ∘L gradL2 U) - curlC U ∘L gradL2 U‖ ≤ 6 * q0 * (Real.exp (2 * θ') - 1) := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have hδ : 0 ≤ Real.exp (2 * θ') - 1 := by linarith [Real.add_one_le_exp (2 * θ')]
  refine opnorm_le_of _ _ (by positivity) (fun f => ?_)
  rw [ContinuousLinearMap.sub_apply, cjp_apply]
  exact curv_conj_le U φ θ' hφ q0 hq0 hplaq f

theorem curv_cjm_norm (U : Cfg L) (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) (q0 : ℝ) (hq0 : 0 ≤ q0)
    (hplaq : ∀ p : PeriodicLatticePlaquette L, AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p) ≤ q0) :
    ‖cjm (siteWP φ) (plaqWP φ) (curlC U ∘L gradL2 U) - curlC U ∘L gradL2 U‖ ≤ 6 * q0 * (Real.exp (2 * θ') - 1) := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have hδ : 0 ≤ Real.exp (2 * θ') - 1 := by linarith [Real.add_one_le_exp (2 * θ')]
  refine opnorm_le_of _ _ (by positivity) (fun f => ?_)
  rw [ContinuousLinearMap.sub_apply]
  have e : cjm (siteWP φ) (plaqWP φ) (curlC U ∘L gradL2 U) f
      = plaqWt (-φ) (curlC U (gradL2 U (siteWt (-(-φ)) f))) := by
    rw [neg_neg]; rfl
  rw [e]
  exact curv_conj_le U (-φ) θ' (WtLip_neg θ' φ hφ) q0 hq0 hplaq f

#print axioms plaqWP
#print axioms curlC_apply
#print axioms sum_shift_site
#print axioms sum_dir_le
#print axioms sum_site_le
#print axioms card_dirs_le
#print axioms curl_conj_pt
#print axioms curl_conj_le
#print axioms curl_cjp_norm
#print axioms curl_cjm_norm
#print axioms curv_value
#print axioms RMap_diff_le
#print axioms curv_pt
#print axioms curv_le
#print axioms curv_norm
#print axioms curv_conj_pt
#print axioms curv_conj_le
#print axioms curv_cjp_norm
#print axioms curv_cjm_norm

end AdalyFormal.DLayer
