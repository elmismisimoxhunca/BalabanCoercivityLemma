import DE3

/-!
# NP1 -- the covariant site operators at a general configuration `U`, pointwise (m1_patch_nonflat, 2026-10-14)

The flat toolkit of DB, re-done at an arbitrary SU(2) configuration `U` (`R_b = RMap (U b)`, an isometry of `su(2)`):
* `grad_cov` : `(D_U f)(x,μ) = R_{(x,μ)} f(x+e_μ) − f x`;
* `lap_cov`  : `(Δ_U f)(x) = Σ_μ (2 f x − R_{(x,μ)} f(x+e_μ) − R_{(x−e_μ,μ)}⁻¹ f(x−e_μ))`;
* `normSq_grad_cov`, `normSq_grad_cov_back` : forward and backward bond sums of `‖D_U f‖²`;
* `grad_norm_le_cov` : `‖D_U f‖² ≤ 12 ‖f‖²`;  `lap_norm_le_cov` : `‖Δ_U f‖ ≤ 12 ‖f‖`;
* **`comm_bound_cov`** : `‖Δ_U(φ f) − φ Δ_U f‖ ≤ Dm ‖f‖ + √12 · c · ‖D_U f‖` for a REAL cutoff `φ` (same constants as flat);
* `lap_zero_far_cov` : `Δ_U F` vanishes one step beyond the support of `F`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1NonFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (pdist)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one RMap_mul)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack
  periodicLatticeShiftBack_shift gradCovariantAdjointValue)
open AdalyFormal.M1Decay (mulR mulR_apply lapR normSq_site normSq_bond sum_shift sum_back sum6_sq pdist_back_le)

variable {L : PeriodicLatticeExtent}

theorem norm_RMap' (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) : ‖RMap g X‖ = ‖X‖ := by
  have h : ‖RMap g X‖ ^ 2 = ‖X‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact AdalyFormal.Balaban.SuTwoInner.inner_RMap g X X
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

theorem RMap_inv_cancel (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) : RMap g⁻¹ (RMap g X) = X := by
  have h := congrArg (fun F => F X) (RMap_mul g⁻¹ g)
  simp only [inv_mul_cancel, RMap_one, LinearMap.id_apply, LinearMap.comp_apply] at h
  exact h.symm

theorem RMap_cancel_inv (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) : RMap g (RMap g⁻¹ X) = X := by
  have h := congrArg (fun F => F X) (RMap_mul g g⁻¹)
  simp only [mul_inv_cancel, RMap_one, LinearMap.id_apply, LinearMap.comp_apply] at h
  exact h.symm

theorem grad_cov (U : Cfg L) (f : SiteL2 L) (b : Bond L) :
    (gradL2 U f) b = RMap (U b) (f (periodicLatticeShift b.1 b.2)) - f b.1 := by
  have h := congrArg (fun g => g b) (gradL2_apply U f)
  simp only at h
  rw [show (gradL2 U f) b = ((gradL2 U) f).ofLp b from rfl, h]
  rfl

theorem lap_cov (U : Cfg L) (f : SiteL2 L) (x : PeriodicLatticeSite L) :
    (lapFull U f) x = ∑ μ : Fin 3, ((2 : ℝ) • f x - RMap (U (x, μ)) (f (periodicLatticeShift x μ))
      - RMap (U (periodicLatticeShiftBack x μ, μ))⁻¹ (f (periodicLatticeShiftBack x μ))) := by
  have h := congrArg (fun g => g x) (gradAdj_apply U (gradL2 U f))
  simp only at h
  rw [show (lapFull U f) x = (gradAdj U (gradL2 U f)).ofLp x from rfl, h]
  unfold gradCovariantAdjointValue
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  have e1 : (WithLp.ofLp (gradL2 U f)) (periodicLatticeShiftBack x μ, μ)
      = RMap (U (periodicLatticeShiftBack x μ, μ)) (f x) - f (periodicLatticeShiftBack x μ) := by
    have := grad_cov U f (periodicLatticeShiftBack x μ, μ)
    simp only [periodicLatticeShift_shiftBack] at this
    exact this
  have e2 : (WithLp.ofLp (gradL2 U f)) (x, μ) = RMap (U (x, μ)) (f (periodicLatticeShift x μ)) - f x :=
    grad_cov U f (x, μ)
  rw [e1, e2, map_sub, RMap_inv_cancel, two_smul]
  abel

theorem normSq_grad_cov (U : Cfg L) (f : SiteL2 L) :
    ‖gradL2 U f‖ ^ 2 = ∑ x, ∑ μ : Fin 3, ‖RMap (U (x, μ)) (f (periodicLatticeShift x μ)) - f x‖ ^ 2 := by
  rw [normSq_bond]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun μ _ => ?_))
  rw [grad_cov]

/-- the backward bond sum is the same sum. -/
theorem normSq_grad_cov_back (U : Cfg L) (f : SiteL2 L) :
    ∑ x, ∑ μ : Fin 3, ‖RMap (U (periodicLatticeShiftBack x μ, μ))⁻¹ (f (periodicLatticeShiftBack x μ)) - f x‖ ^ 2
      = ‖gradL2 U f‖ ^ 2 := by
  rw [normSq_grad_cov, Finset.sum_comm, Finset.sum_comm (f := fun x μ =>
    ‖RMap (U (x, μ)) (f (periodicLatticeShift x μ)) - f x‖ ^ 2)]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  have := sum_back (fun y => ‖RMap (U (y, μ)) (f (periodicLatticeShift y μ)) - f y‖ ^ 2) μ
  rw [← this]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [periodicLatticeShift_shiftBack]
  set g := U (periodicLatticeShiftBack x μ, μ)
  have : RMap g⁻¹ (f (periodicLatticeShiftBack x μ)) - f x
      = RMap g⁻¹ (f (periodicLatticeShiftBack x μ) - RMap g (f x)) := by
    rw [map_sub, RMap_inv_cancel]
  rw [this, norm_RMap', norm_sub_rev]

theorem grad_norm_le_cov (U : Cfg L) (f : SiteL2 L) : ‖gradL2 U f‖ ^ 2 ≤ 12 * ‖f‖ ^ 2 := by
  rw [normSq_grad_cov, normSq_site]
  have hpt : ∀ x (μ : Fin 3), ‖RMap (U (x, μ)) (f (periodicLatticeShift x μ)) - f x‖ ^ 2
      ≤ 2 * ‖f (periodicLatticeShift x μ)‖ ^ 2 + 2 * ‖f x‖ ^ 2 := by
    intro x μ
    have h1 := norm_sub_le (RMap (U (x, μ)) (f (periodicLatticeShift x μ))) (f x)
    rw [norm_RMap'] at h1
    have h0 := norm_nonneg (RMap (U (x, μ)) (f (periodicLatticeShift x μ)) - f x)
    nlinarith [sq_nonneg (‖f (periodicLatticeShift x μ)‖ - ‖f x‖), norm_nonneg (f x),
      norm_nonneg (f (periodicLatticeShift x μ))]
  calc ∑ x, ∑ μ : Fin 3, ‖RMap (U (x, μ)) (f (periodicLatticeShift x μ)) - f x‖ ^ 2
      ≤ ∑ x, ∑ μ : Fin 3, (2 * ‖f (periodicLatticeShift x μ)‖ ^ 2 + 2 * ‖f x‖ ^ 2) :=
        Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun μ _ => hpt x μ))
    _ = 12 * ∑ x, ‖f x‖ ^ 2 := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_shift (fun y => ‖f y‖ ^ 2), Fin.sum_univ_three]
        ring

theorem lap_norm_le_cov (U : Cfg L) (f : SiteL2 L) : ‖lapFull U f‖ ≤ 12 * ‖f‖ := by
  have h1 : ‖lapFull U f‖ ^ 2 = ⟪gradL2 U (lapFull U f), gradL2 U f⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    show ⟪lapFull U f, gradAdj U (gradL2 U f)⟫ = _
    rw [gradAdj, ContinuousLinearMap.adjoint_inner_right]
  have h2 := grad_norm_le_cov U (lapFull U f)
  have h3 := grad_norm_le_cov U f
  have h23 : ‖gradL2 U (lapFull U f)‖ * ‖gradL2 U f‖ ≤ 12 * ‖lapFull U f‖ * ‖f‖ := by
    have hsq : (‖gradL2 U (lapFull U f)‖ * ‖gradL2 U f‖) ^ 2 ≤ (12 * ‖lapFull U f‖ * ‖f‖) ^ 2 := by
      rw [mul_pow, show (12 * ‖lapFull U f‖ * ‖f‖) ^ 2 = (12 * ‖lapFull U f‖ ^ 2) * (12 * ‖f‖ ^ 2) by ring]
      exact mul_le_mul h2 h3 (sq_nonneg _) (by positivity)
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsq
  have h4 : ‖lapFull U f‖ ^ 2 ≤ 12 * ‖lapFull U f‖ * ‖f‖ := by
    rw [h1]; exact (real_inner_le_norm _ _).trans h23
  rcases (norm_nonneg (lapFull U f)).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have : ‖lapFull U f‖ * ‖lapFull U f‖ ≤ ‖lapFull U f‖ * (12 * ‖f‖) := by nlinarith
    exact le_of_mul_le_mul_left this hpos

/-- **the covariant commutator bound** (a REAL cutoff `φ` commutes with every transport). -/
theorem comm_bound_cov (U : Cfg L) (φ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) (Dm c : ℝ) (hDm0 : 0 ≤ Dm)
    (hc0 : 0 ≤ c) (hD : ∀ x, |lapR φ x| ≤ Dm)
    (hS : ∀ x (μ : Fin 3), |φ x - φ (periodicLatticeShift x μ)| ≤ c)
    (hB : ∀ x (μ : Fin 3), |φ x - φ (periodicLatticeShiftBack x μ)| ≤ c) :
    ‖lapFull U (mulR φ f) - mulR φ (lapFull U f)‖ ≤ Dm * ‖f‖ + Real.sqrt 12 * c * ‖gradL2 U f‖ := by
  set Fw : PeriodicLatticeSite L → Fin 3 → SuTwo := fun x μ => RMap (U (x, μ)) (f (periodicLatticeShift x μ)) - f x
    with hFw
  set Bw : PeriodicLatticeSite L → Fin 3 → SuTwo := fun x μ =>
    RMap (U (periodicLatticeShiftBack x μ, μ))⁻¹ (f (periodicLatticeShiftBack x μ)) - f x with hBw
  set a : SiteL2 L := mulR (lapR φ) f with ha
  set b : SiteL2 L := WithLp.toLp 2 (fun x => ∑ μ : Fin 3,
      ((φ x - φ (periodicLatticeShift x μ)) • Fw x μ + (φ x - φ (periodicLatticeShiftBack x μ)) • Bw x μ)) with hb
  have hsplit : lapFull U (mulR φ f) - mulR φ (lapFull U f) = a + b := by
    ext1 x
    show (lapFull U (mulR φ f)) x - φ x • (lapFull U f) x = lapR φ x • f x + ∑ μ : Fin 3,
      ((φ x - φ (periodicLatticeShift x μ)) • Fw x μ + (φ x - φ (periodicLatticeShiftBack x μ)) • Bw x μ)
    rw [lap_cov, lap_cov]
    simp only [mulR_apply, map_smul, hFw, hBw]
    unfold lapR
    rw [Finset.smul_sum, Finset.sum_smul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    module
  rw [hsplit]
  have hna : ‖a‖ ≤ Dm * ‖f‖ :=
    AdalyFormal.M1Decay.norm_mulR_le (lapR φ) f Dm hDm0 hD
  have hnb : ‖b‖ ≤ Real.sqrt 12 * c * ‖gradL2 U f‖ := by
    have hpt : ∀ x, ‖b x‖ ^ 2 ≤ 6 * c ^ 2 * ∑ μ : Fin 3, (‖Fw x μ‖ ^ 2 + ‖Bw x μ‖ ^ 2) := by
      intro x
      have hle : ‖b x‖ ≤ ∑ μ : Fin 3, (c * ‖Fw x μ‖ + c * ‖Bw x μ‖) := by
        show ‖∑ μ : Fin 3, ((φ x - φ (periodicLatticeShift x μ)) • Fw x μ
          + (φ x - φ (periodicLatticeShiftBack x μ)) • Bw x μ)‖ ≤ _
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun μ _ => ?_))
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hS x μ) (norm_nonneg _)
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hB x μ) (norm_nonneg _)
      rw [Fin.sum_univ_three] at hle
      rw [Fin.sum_univ_three]
      have h6 := sum6_sq (c * ‖Fw x 0‖) (c * ‖Bw x 0‖) (c * ‖Fw x 1‖) (c * ‖Bw x 1‖) (c * ‖Fw x 2‖) (c * ‖Bw x 2‖)
      have hb0 := norm_nonneg (b x)
      have hsq := pow_le_pow_left₀ hb0 hle 2
      nlinarith [hsq, h6]
    have hsum : ‖b‖ ^ 2 ≤ 12 * c ^ 2 * ‖gradL2 U f‖ ^ 2 := by
      rw [normSq_site]
      calc ∑ x, ‖b x‖ ^ 2 ≤ ∑ x, 6 * c ^ 2 * ∑ μ : Fin 3, (‖Fw x μ‖ ^ 2 + ‖Bw x μ‖ ^ 2) :=
            Finset.sum_le_sum (fun x _ => hpt x)
        _ = 6 * c ^ 2 * (∑ x, ∑ μ : Fin 3, ‖Fw x μ‖ ^ 2 + ∑ x, ∑ μ : Fin 3, ‖Bw x μ‖ ^ 2) := by
            rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
            congr 1
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [← Finset.sum_add_distrib]
        _ = 12 * c ^ 2 * ‖gradL2 U f‖ ^ 2 := by
            have e1 : ∑ x, ∑ μ : Fin 3, ‖Fw x μ‖ ^ 2 = ‖gradL2 U f‖ ^ 2 := (normSq_grad_cov U f).symm
            have e2 : ∑ x, ∑ μ : Fin 3, ‖Bw x μ‖ ^ 2 = ‖gradL2 U f‖ ^ 2 := normSq_grad_cov_back U f
            rw [e1, e2]; ring
    have hr : (Real.sqrt 12 * c * ‖gradL2 U f‖) ^ 2 = 12 * c ^ 2 * ‖gradL2 U f‖ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    rw [← hr] at hsum
    exact (pow_le_pow_iff_left₀ (norm_nonneg b) (by positivity) (by norm_num)).mp hsum
  exact (norm_add_le a b).trans (add_le_add hna hnb)

/-- `Δ_U F` vanishes far from the support of `F`. -/
theorem lap_zero_far_cov (U : Cfg L) (F : SiteL2 L) (w : PeriodicLatticeSite L) (ρ : ℕ)
    (hF : ∀ z, ρ ≤ pdist w z → F z = 0) (x : PeriodicLatticeSite L) (hx : ρ + 1 ≤ pdist w x) :
    lapFull U F x = 0 := by
  rw [lap_cov]
  refine Finset.sum_eq_zero (fun μ _ => ?_)
  have h1 := pdist_triangle w (periodicLatticeShift x μ) x
  have h2 := pdist_shift_le x μ
  rw [pdist_comm] at h2
  have h3 := pdist_triangle w (periodicLatticeShiftBack x μ) x
  have h4 := pdist_back_le x μ
  rw [pdist_comm] at h4
  rw [hF x (by omega), hF _ (by omega), hF _ (by omega)]
  simp

theorem inner_grad_grad_cov (U : Cfg L) (f g : SiteL2 L) :
    ⟪gradL2 U f, gradL2 U g⟫ = ⟪lapFull U f, g⟫ := by
  show _ = ⟪gradAdj U (gradL2 U f), g⟫
  rw [gradAdj, ContinuousLinearMap.adjoint_inner_left]

end AdalyFormal.M1NonFlat

#print axioms AdalyFormal.M1NonFlat.norm_RMap'
#print axioms AdalyFormal.M1NonFlat.grad_cov
#print axioms AdalyFormal.M1NonFlat.lap_cov
#print axioms AdalyFormal.M1NonFlat.normSq_grad_cov_back
#print axioms AdalyFormal.M1NonFlat.grad_norm_le_cov
#print axioms AdalyFormal.M1NonFlat.lap_norm_le_cov
#print axioms AdalyFormal.M1NonFlat.comm_bound_cov
#print axioms AdalyFormal.M1NonFlat.lap_zero_far_cov
#print axioms AdalyFormal.M1NonFlat.inner_grad_grad_cov
