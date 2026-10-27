import DLR2

/-!
# DL6 -- exponential weights on the genuine carriers and the gradient commutator

* `siteWt φ`, `bondWt φ` : multiplication by `e^{φ(x)}` on site fields, by `e^{φ(b₋)}` on bond fields (self-adjoint, `siteWt (−φ)` inverts).
* `WtLip θ' φ` : `|φ(x + e_μ) − φ(x)| ≤ θ'` (one fine step).
* `grad_conj_sub` : `bondWt φ (D_U (siteWt (−φ) f)) − D_U f` is the field `b ↦ (e^{φ(b₋)−φ(b₊)} − 1)·R(U_b) f(b₊)`;
  `grad_conj_err` : its norm is `≤ √3 (e^{θ'} − 1) ‖f‖` (every site is `b₊` of exactly three bonds).
* `lap_conj_pair` : `⟪f, e^{φ} D*D e^{−φ} f⟫ = ⟪D⁻ f, D⁺ f⟫` with `D^± = bondWt (±φ) ∘ D ∘ siteWt (∓φ)` (the Combes–Thomas form).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

/-- multiplication by `e^{φ}` on site fields -/
noncomputable def siteWt (φ : PeriodicLatticeSite L → ℝ) : SiteL2 L →L[ℝ] SiteL2 L :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun x => Real.exp (φ x) • f x)
      map_add' := fun f g => by refine PiLp.ext (fun x => ?_); simp [smul_add]
      map_smul' := fun c f => by
        refine PiLp.ext (fun x => ?_)
        simp only [PiLp.smul_apply, RingHom.id_apply, PiLp.toLp_apply]
        exact smul_comm _ _ _ }

/-- multiplication by `e^{φ(b₋)}` on bond fields -/
noncomputable def bondWt (φ : PeriodicLatticeSite L → ℝ) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun b => Real.exp (φ b.1) • f b)
      map_add' := fun f g => by refine PiLp.ext (fun x => ?_); simp [smul_add]
      map_smul' := fun c f => by
        refine PiLp.ext (fun x => ?_)
        simp only [PiLp.smul_apply, RingHom.id_apply, PiLp.toLp_apply]
        exact smul_comm _ _ _ }

theorem siteWt_apply (φ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) (x : PeriodicLatticeSite L) :
    (siteWt φ f) x = Real.exp (φ x) • f x := rfl

theorem bondWt_apply (φ : PeriodicLatticeSite L → ℝ) (f : BondFnL2 L) (b : Bond L) :
    (bondWt φ f) b = Real.exp (φ b.1) • f b := rfl

theorem siteWt_neg_cancel (φ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) : siteWt φ (siteWt (-φ) f) = f := by
  refine PiLp.ext (fun x => ?_)
  rw [siteWt_apply, siteWt_apply, smul_smul, ← Real.exp_add]
  simp

theorem siteWt_cancel_neg (φ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) : siteWt (-φ) (siteWt φ f) = f := by
  have := siteWt_neg_cancel (-φ) f
  simpa using this

theorem bondWt_neg_cancel (φ : PeriodicLatticeSite L → ℝ) (f : BondFnL2 L) : bondWt φ (bondWt (-φ) f) = f := by
  refine PiLp.ext (fun x => ?_)
  rw [bondWt_apply, bondWt_apply, smul_smul, ← Real.exp_add]
  simp

theorem bondWt_cancel_neg (φ : PeriodicLatticeSite L → ℝ) (f : BondFnL2 L) : bondWt (-φ) (bondWt φ f) = f := by
  have := bondWt_neg_cancel (-φ) f
  simpa using this

theorem siteWt_symm (φ : PeriodicLatticeSite L → ℝ) (f g : SiteL2 L) : ⟪siteWt φ f, g⟫ = ⟪f, siteWt φ g⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [siteWt_apply, siteWt_apply, real_inner_smul_left, real_inner_smul_right]

theorem bondWt_symm (φ : PeriodicLatticeSite L → ℝ) (f g : BondFnL2 L) : ⟪bondWt φ f, g⟫ = ⟪f, bondWt φ g⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [bondWt_apply, bondWt_apply, real_inner_smul_left, real_inner_smul_right]

/-- one-fine-step Lipschitz weight -/
def WtLip (θ' : ℝ) (φ : PeriodicLatticeSite L → ℝ) : Prop :=
  ∀ (x : PeriodicLatticeSite L) (μ : Fin 3), |φ (periodicLatticeShift x μ) - φ x| ≤ θ'

theorem abs_exp_sub_one_le (t : ℝ) : |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by linarith [Real.add_one_le_exp t])]
  · rw [abs_of_nonpos h]
    have h1 : Real.exp t ≤ 1 := Real.exp_le_one_iff.mpr h
    rw [abs_of_nonpos (by linarith)]
    have h2 : 1 - Real.exp t ≤ -t := by linarith [Real.add_one_le_exp t]
    have h3 : -t ≤ Real.exp (-t) - 1 := by linarith [Real.add_one_le_exp (-t)]
    linarith

theorem abs_exp_sub_one_le_of (t δ : ℝ) (ht : |t| ≤ δ) : |Real.exp t - 1| ≤ Real.exp δ - 1 :=
  (abs_exp_sub_one_le t).trans (by linarith [Real.exp_le_exp.mpr ht])

/-- the conjugated gradient minus the gradient, pointwise -/
theorem grad_conj_sub (U : Cfg L) (φ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) (b : Bond L) :
    (bondWt φ (gradL2 U (siteWt (-φ) f)) - gradL2 U f) b
      = (Real.exp (φ b.1 - φ (periodicLatticeShift b.1 b.2)) - 1) • RMap (U b) (f (periodicLatticeShift b.1 b.2)) := by
  rw [PiLp.sub_apply, bondWt_apply]
  have h1 : (gradL2 U (siteWt (-φ) f)) b = gradValueCovariant U (WithLp.ofLp (siteWt (-φ) f)) b := by
    rw [← gradL2_apply]
  have h2 : (gradL2 U f) b = gradValueCovariant U (WithLp.ofLp f) b := by
    rw [← gradL2_apply]
  rw [h1, h2]
  unfold gradValueCovariant
  have e1 : (WithLp.ofLp (siteWt (-φ) f)) (periodicLatticeShift b.1 b.2)
      = Real.exp (-φ (periodicLatticeShift b.1 b.2)) • f (periodicLatticeShift b.1 b.2) := rfl
  have e2 : (WithLp.ofLp (siteWt (-φ) f)) b.1 = Real.exp (-φ b.1) • f b.1 := rfl
  rw [e1, e2, map_smul, smul_sub, smul_smul, smul_smul, ← Real.exp_add, ← Real.exp_add]
  have e3 : φ b.1 + -φ b.1 = 0 := by ring
  have e4 : φ b.1 + -φ (periodicLatticeShift b.1 b.2) = φ b.1 - φ (periodicLatticeShift b.1 b.2) := by ring
  rw [e3, e4, Real.exp_zero, one_smul, sub_smul, one_smul]
  have ef : (WithLp.ofLp f) (periodicLatticeShift b.1 b.2) = f (periodicLatticeShift b.1 b.2) := rfl
  have ef2 : (WithLp.ofLp f) b.1 = f b.1 := rfl
  rw [ef, ef2]
  abel

/-- each site is the forward end of exactly three bonds -/
theorem sum_shift_sq (f : SiteL2 L) :
    ∑ b : Bond L, ‖f (periodicLatticeShift b.1 b.2)‖ ^ 2 = 3 * ‖f‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type_right]
  have hshift : ∀ μ : Fin 3, ∑ x : PeriodicLatticeSite L, ‖f (periodicLatticeShift x μ)‖ ^ 2
      = ∑ x : PeriodicLatticeSite L, ‖f x‖ ^ 2 := by
    intro μ
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
    exact Function.Bijective.sum_comp hbij (fun x => ‖f x‖ ^ 2)
  simp only [hshift, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **gradient commutator**: `‖bondWt φ (D (siteWt (−φ) f)) − D f‖ ≤ √3 (e^{θ'} − 1) ‖f‖`. -/
theorem grad_conj_err (U : Cfg L) (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) (f : SiteL2 L) :
    ‖bondWt φ (gradL2 U (siteWt (-φ) f)) - gradL2 U f‖ ≤ Real.sqrt 3 * (Real.exp θ' - 1) * ‖f‖ := by
  have hδ : 0 ≤ Real.exp θ' - 1 := by
    have : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
    linarith [Real.add_one_le_exp θ']
  have hpt : ∀ b : Bond L, ‖(bondWt φ (gradL2 U (siteWt (-φ) f)) - gradL2 U f) b‖
      ≤ (Real.exp θ' - 1) * ‖f (periodicLatticeShift b.1 b.2)‖ := by
    intro b
    rw [grad_conj_sub, norm_smul, Real.norm_eq_abs, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine abs_exp_sub_one_le_of _ _ ?_
    rw [abs_sub_comm]; exact hφ b.1 b.2
  have hsq : ‖bondWt φ (gradL2 U (siteWt (-φ) f)) - gradL2 U f‖ ^ 2 ≤ ((Real.exp θ' - 1) ^ 2 * 3) * ‖f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ b, ‖(bondWt φ (gradL2 U (siteWt (-φ) f)) - gradL2 U f) b‖ ^ 2
        ≤ ∑ b : Bond L, ((Real.exp θ' - 1) * ‖f (periodicLatticeShift b.1 b.2)‖) ^ 2 :=
          Finset.sum_le_sum (fun b _ => pow_le_pow_left₀ (norm_nonneg _) (hpt b) 2)
      _ = (Real.exp θ' - 1) ^ 2 * ∑ b : Bond L, ‖f (periodicLatticeShift b.1 b.2)‖ ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun b _ => by ring)
      _ = ((Real.exp θ' - 1) ^ 2 * 3) * ‖f‖ ^ 2 := by rw [sum_shift_sq]; ring
  have h3 : ((Real.exp θ' - 1) ^ 2 * 3) * ‖f‖ ^ 2 = (Real.sqrt 3 * (Real.exp θ' - 1) * ‖f‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
  rw [h3] at hsq
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- the Combes–Thomas form of the conjugated covariant Laplacian -/
theorem lap_conj_pair (U : Cfg L) (φ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) :
    ⟪f, siteWt φ (lapFull U (siteWt (-φ) f))⟫
      = ⟪bondWt (-φ) (gradL2 U (siteWt φ f)), bondWt φ (gradL2 U (siteWt (-φ) f))⟫ := by
  rw [← siteWt_symm, lapFull, ContinuousLinearMap.comp_apply, gradAdj,
    ContinuousLinearMap.adjoint_inner_right]
  rw [bondWt_symm, bondWt_cancel_neg]

#print axioms siteWt
#print axioms bondWt
#print axioms siteWt_neg_cancel
#print axioms siteWt_cancel_neg
#print axioms bondWt_neg_cancel
#print axioms bondWt_cancel_neg
#print axioms siteWt_symm
#print axioms bondWt_symm
#print axioms abs_exp_sub_one_le
#print axioms abs_exp_sub_one_le_of
#print axioms grad_conj_sub
#print axioms sum_shift_sq
#print axioms grad_conj_err
#print axioms lap_conj_pair

end AdalyFormal.DLayer
