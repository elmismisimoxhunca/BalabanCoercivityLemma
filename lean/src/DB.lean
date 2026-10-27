import DA

/-!
# DB -- the flat site operators, pointwise (m1_w2_decay, 2026-10-13)

At `U0 = flatCfg` (`U ≡ 1`):
* `grad_flat` : `(D f)(x,μ) = f(x+e_μ) − f x`;  `lap_flat` : `(Δ f)(x) = Σ_μ (2 f x − f(x+e_μ) − f(x−e_μ))`;
* `normSq_site`, `normSq_grad` : `‖f‖² = Σ_x ‖f x‖²`, `‖D f‖² = Σ_x Σ_μ ‖f(x+e_μ) − f x‖²`;
* `grad_norm_le` : `‖D f‖² ≤ 12 ‖f‖²`;  `lap_norm_le` : `‖Δ f‖ ≤ 12 ‖f‖`;
* `mulR φ f` (pointwise product by a real function), `lapR φ`, and the commutator bound
  **`comm_bound`** : `‖Δ(φ f) − φ Δ f‖ ≤ Dm ‖f‖ + √12 · c · ‖D f‖` when `|lapR φ| ≤ Dm` and `φ` moves by at most `c` along every
  unit bond (both directions).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1Decay

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap_one)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack
  periodicLatticeShiftBack_shift periodicLatticeShiftEquiv gradCovariantAdjointValue)

variable {L : PeriodicLatticeExtent}

/-- the flat configuration. -/
abbrev U0 (L : PeriodicLatticeExtent) : Cfg L := (flatCfg : Cfg L)

theorem grad_flat (f : SiteL2 L) (b : Bond L) :
    (gradL2 (U0 L) f) b = f (periodicLatticeShift b.1 b.2) - f b.1 := by
  have h := congrArg (fun g => g b) (gradL2_apply (U0 L) f)
  simp only at h
  rw [show (gradL2 (U0 L) f) b = ((gradL2 (U0 L)) f).ofLp b from rfl, h]
  simp [AdalyFormal.Balaban.CovariantOperators.gradValueCovariant, flatCfg, RMap_one]

theorem lap_flat (f : SiteL2 L) (x : PeriodicLatticeSite L) :
    (lapFull (U0 L) f) x = ∑ μ : Fin 3, ((2 : ℝ) • f x - f (periodicLatticeShift x μ) - f (periodicLatticeShiftBack x μ)) := by
  have h := congrArg (fun g => g x) (gradAdj_apply (U0 L) (gradL2 (U0 L) f))
  simp only at h
  rw [show (lapFull (U0 L) f) x = (gradAdj (U0 L) (gradL2 (U0 L) f)).ofLp x from rfl, h]
  unfold gradCovariantAdjointValue
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  have e1 : (WithLp.ofLp (gradL2 (U0 L) f)) (periodicLatticeShiftBack x μ, μ)
      = f x - f (periodicLatticeShiftBack x μ) := by
    have := grad_flat f (periodicLatticeShiftBack x μ, μ)
    simp only [periodicLatticeShift_shiftBack] at this
    exact this
  have e2 : (WithLp.ofLp (gradL2 (U0 L) f)) (x, μ) = f (periodicLatticeShift x μ) - f x := grad_flat f (x, μ)
  have e3 : ((U0 L) (periodicLatticeShiftBack x μ, μ))⁻¹ = 1 := by simp [U0, flatCfg]
  rw [e3, RMap_one, e1, e2]
  simp only [LinearMap.id_apply]
  rw [two_smul]
  abel

theorem normSq_site (f : SiteL2 L) : ‖f‖ ^ 2 = ∑ x, ‖f x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]

theorem normSq_bond (A : BondFnL2 L) : ‖A‖ ^ 2 = ∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ‖A (x, μ)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Fintype.sum_prod_type _

theorem normSq_grad (f : SiteL2 L) :
    ‖gradL2 (U0 L) f‖ ^ 2 = ∑ x, ∑ μ : Fin 3, ‖f (periodicLatticeShift x μ) - f x‖ ^ 2 := by
  rw [normSq_bond]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun μ _ => ?_))
  rw [grad_flat]

theorem sum_shift (F : PeriodicLatticeSite L → ℝ) (μ : Fin 3) :
    ∑ x, F (periodicLatticeShift x μ) = ∑ x, F x :=
  Equiv.sum_comp (periodicLatticeShiftEquiv μ) F

theorem sum_back (F : PeriodicLatticeSite L → ℝ) (μ : Fin 3) :
    ∑ x, F (periodicLatticeShiftBack x μ) = ∑ x, F x :=
  Equiv.sum_comp (periodicLatticeShiftEquiv μ).symm F

theorem grad_norm_le (f : SiteL2 L) : ‖gradL2 (U0 L) f‖ ^ 2 ≤ 12 * ‖f‖ ^ 2 := by
  rw [normSq_grad, normSq_site]
  have h : ∀ x, ∀ μ : Fin 3, ‖f (periodicLatticeShift x μ) - f x‖ ^ 2
      ≤ 2 * ‖f (periodicLatticeShift x μ)‖ ^ 2 + 2 * ‖f x‖ ^ 2 := by
    intro x μ
    have := norm_sub_le (f (periodicLatticeShift x μ)) (f x)
    nlinarith [norm_nonneg (f (periodicLatticeShift x μ) - f x), norm_nonneg (f (periodicLatticeShift x μ)),
      norm_nonneg (f x), sq_nonneg (‖f (periodicLatticeShift x μ)‖ - ‖f x‖)]
  calc ∑ x, ∑ μ : Fin 3, ‖f (periodicLatticeShift x μ) - f x‖ ^ 2
      ≤ ∑ x, ∑ μ : Fin 3, (2 * ‖f (periodicLatticeShift x μ)‖ ^ 2 + 2 * ‖f x‖ ^ 2) :=
        Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun μ _ => h x μ))
    _ = ∑ μ : Fin 3, 2 * ∑ x, ‖f (periodicLatticeShift x μ)‖ ^ 2 + 6 * ∑ x, ‖f x‖ ^ 2 := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Fin.sum_univ_three]
        ring
    _ = 12 * ∑ x, ‖f x‖ ^ 2 := by
        simp only [sum_shift (fun y => ‖f y‖ ^ 2), Fin.sum_univ_three]
        ring

theorem lap_norm_le (f : SiteL2 L) : ‖lapFull (U0 L) f‖ ≤ 12 * ‖f‖ := by
  set g := lapFull (U0 L) f with hg
  have h1 : ‖g‖ ^ 2 = ⟪gradL2 (U0 L) f, gradL2 (U0 L) g⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    have : ⟪g, g⟫ = ⟪gradAdj (U0 L) (gradL2 (U0 L) f), g⟫ := rfl
    rw [this, gradAdj, ContinuousLinearMap.adjoint_inner_left]
  have h2 := real_inner_le_norm (gradL2 (U0 L) f) (gradL2 (U0 L) g)
  have hgf := grad_norm_le f
  have hgg := grad_norm_le g
  have a1 : ‖gradL2 (U0 L) f‖ ≤ Real.sqrt 12 * ‖f‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (gradL2 (U0 L) f)), ← Real.sqrt_sq (norm_nonneg f), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hgf
  have a2 : ‖gradL2 (U0 L) g‖ ≤ Real.sqrt 12 * ‖g‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (gradL2 (U0 L) g)), ← Real.sqrt_sq (norm_nonneg g), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hgg
  have hs : Real.sqrt 12 * Real.sqrt 12 = 12 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 12 := Real.sqrt_nonneg _
  have key : ‖g‖ ^ 2 ≤ 12 * ‖f‖ * ‖g‖ := by
    calc ‖g‖ ^ 2 ≤ ‖gradL2 (U0 L) f‖ * ‖gradL2 (U0 L) g‖ := h1 ▸ h2
      _ ≤ (Real.sqrt 12 * ‖f‖) * (Real.sqrt 12 * ‖g‖) :=
          mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
      _ = (Real.sqrt 12 * Real.sqrt 12) * ‖f‖ * ‖g‖ := by ring
      _ = 12 * ‖f‖ * ‖g‖ := by rw [hs]
  rcases (norm_nonneg g).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · nlinarith

/-! ## pointwise products by real functions -/

/-- `(φ f)(x) = φ x • f x`. -/
noncomputable def mulR (φ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) : SiteL2 L :=
  WithLp.toLp 2 (fun x => φ x • f x)

theorem mulR_apply (φ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) (x : PeriodicLatticeSite L) :
    mulR φ f x = φ x • f x := rfl

/-- the real flat Laplacian. -/
def lapR (φ : PeriodicLatticeSite L → ℝ) (x : PeriodicLatticeSite L) : ℝ :=
  ∑ μ : Fin 3, (2 * φ x - φ (periodicLatticeShift x μ) - φ (periodicLatticeShiftBack x μ))

theorem lapR_eq (φ : PeriodicLatticeSite L → ℝ) (x : PeriodicLatticeSite L) :
    lapR φ x = -∑ μ : Fin 3, D2 μ φ x := by
  unfold lapR D2
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  ring

theorem lap_mulR_const (φ : PeriodicLatticeSite L → ℝ) (v : SuTwo) (x : PeriodicLatticeSite L) :
    (lapFull (U0 L) (WithLp.toLp 2 (fun z => φ z • v))) x = lapR φ x • v := by
  rw [lap_flat]
  unfold lapR
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  show (2 : ℝ) • (φ x • v) - φ (periodicLatticeShift x μ) • v - φ (periodicLatticeShiftBack x μ) • v = _
  rw [sub_smul, sub_smul, smul_smul, mul_comm]

theorem sum6_sq (a b c d e f : ℝ) :
    (a + b + c + d + e + f) ^ 2 ≤ 6 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (a - f),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (b - f), sq_nonneg (c - d),
    sq_nonneg (c - e), sq_nonneg (c - f), sq_nonneg (d - e), sq_nonneg (d - f), sq_nonneg (e - f)]

/-- **the commutator bound** `‖Δ(φ f) − φ Δ f‖ ≤ Dm ‖f‖ + √12 c ‖D f‖`. -/
theorem comm_bound (φ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) (Dm c : ℝ) (hDm0 : 0 ≤ Dm) (hc0 : 0 ≤ c)
    (hD : ∀ x, |lapR φ x| ≤ Dm)
    (hS : ∀ x (μ : Fin 3), |φ x - φ (periodicLatticeShift x μ)| ≤ c)
    (hB : ∀ x (μ : Fin 3), |φ x - φ (periodicLatticeShiftBack x μ)| ≤ c) :
    ‖lapFull (U0 L) (mulR φ f) - mulR φ (lapFull (U0 L) f)‖ ≤ Dm * ‖f‖ + Real.sqrt 12 * c * ‖gradL2 (U0 L) f‖ := by
  set a : SiteL2 L := mulR (lapR φ) f with ha
  set b : SiteL2 L := WithLp.toLp 2 (fun x => ∑ μ : Fin 3,
      ((φ x - φ (periodicLatticeShift x μ)) • (f (periodicLatticeShift x μ) - f x)
        + (φ x - φ (periodicLatticeShiftBack x μ)) • (f (periodicLatticeShiftBack x μ) - f x))) with hb
  have hsplit : lapFull (U0 L) (mulR φ f) - mulR φ (lapFull (U0 L) f) = a + b := by
    ext1 x
    show (lapFull (U0 L) (mulR φ f)) x - φ x • (lapFull (U0 L) f) x = lapR φ x • f x + ∑ μ : Fin 3,
      ((φ x - φ (periodicLatticeShift x μ)) • (f (periodicLatticeShift x μ) - f x)
        + (φ x - φ (periodicLatticeShiftBack x μ)) • (f (periodicLatticeShiftBack x μ) - f x))
    rw [lap_flat, lap_flat]
    simp only [mulR_apply]
    unfold lapR
    rw [Finset.smul_sum, Finset.sum_smul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    module
  rw [hsplit]
  have hna : ‖a‖ ≤ Dm * ‖f‖ := by
    have h1 : ‖a‖ ^ 2 ≤ (Dm * ‖f‖) ^ 2 := by
      rw [normSq_site, mul_pow, normSq_site, Finset.mul_sum]
      refine Finset.sum_le_sum (fun x _ => ?_)
      show ‖lapR φ x • f x‖ ^ 2 ≤ _
      rw [norm_smul, mul_pow, Real.norm_eq_abs]
      have := hD x
      have h0 := abs_nonneg (lapR φ x)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 this 2) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg a) (by positivity) (by norm_num)).mp h1
  have hnb : ‖b‖ ≤ Real.sqrt 12 * c * ‖gradL2 (U0 L) f‖ := by
    have hpt : ∀ x, ‖b x‖ ^ 2 ≤ 6 * c ^ 2 * ∑ μ : Fin 3,
        (‖f (periodicLatticeShift x μ) - f x‖ ^ 2 + ‖f (periodicLatticeShiftBack x μ) - f x‖ ^ 2) := by
      intro x
      have hle : ‖b x‖ ≤ ∑ μ : Fin 3, (c * ‖f (periodicLatticeShift x μ) - f x‖
          + c * ‖f (periodicLatticeShiftBack x μ) - f x‖) := by
        show ‖∑ μ : Fin 3, ((φ x - φ (periodicLatticeShift x μ)) • (f (periodicLatticeShift x μ) - f x)
          + (φ x - φ (periodicLatticeShiftBack x μ)) • (f (periodicLatticeShiftBack x μ) - f x))‖ ≤ _
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun μ _ => ?_))
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hS x μ) (norm_nonneg _)
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hB x μ) (norm_nonneg _)
      rw [Fin.sum_univ_three] at hle
      rw [Fin.sum_univ_three]
      have h6 := sum6_sq (c * ‖f (periodicLatticeShift x 0) - f x‖) (c * ‖f (periodicLatticeShiftBack x 0) - f x‖)
        (c * ‖f (periodicLatticeShift x 1) - f x‖) (c * ‖f (periodicLatticeShiftBack x 1) - f x‖)
        (c * ‖f (periodicLatticeShift x 2) - f x‖) (c * ‖f (periodicLatticeShiftBack x 2) - f x‖)
      have hb0 := norm_nonneg (b x)
      have hsq := pow_le_pow_left₀ hb0 hle 2
      nlinarith [hsq, h6]
    have hsum : ‖b‖ ^ 2 ≤ 12 * c ^ 2 * ‖gradL2 (U0 L) f‖ ^ 2 := by
      rw [normSq_site, normSq_grad]
      calc ∑ x, ‖b x‖ ^ 2 ≤ ∑ x, 6 * c ^ 2 * ∑ μ : Fin 3,
            (‖f (periodicLatticeShift x μ) - f x‖ ^ 2 + ‖f (periodicLatticeShiftBack x μ) - f x‖ ^ 2) :=
            Finset.sum_le_sum (fun x _ => hpt x)
        _ = 6 * c ^ 2 * (∑ x, ∑ μ : Fin 3, ‖f (periodicLatticeShift x μ) - f x‖ ^ 2
              + ∑ x, ∑ μ : Fin 3, ‖f (periodicLatticeShiftBack x μ) - f x‖ ^ 2) := by
            rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
            congr 1
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [← Finset.sum_add_distrib]
        _ = 12 * c ^ 2 * ∑ x, ∑ μ : Fin 3, ‖f (periodicLatticeShift x μ) - f x‖ ^ 2 := by
            have hq : ∑ x, ∑ μ : Fin 3, ‖f (periodicLatticeShiftBack x μ) - f x‖ ^ 2
                = ∑ x, ∑ μ : Fin 3, ‖f (periodicLatticeShift x μ) - f x‖ ^ 2 := by
              rw [Finset.sum_comm, Finset.sum_comm (f := fun x μ => ‖f (periodicLatticeShift x μ) - f x‖ ^ 2)]
              refine Finset.sum_congr rfl (fun μ _ => ?_)
              have := sum_back (fun y => ‖f (periodicLatticeShift y μ) - f y‖ ^ 2) μ
              simp only [periodicLatticeShift_shiftBack] at this
              rw [← this]
              refine Finset.sum_congr rfl (fun x _ => ?_)
              rw [norm_sub_rev]
            rw [hq]; ring
    have hr : (Real.sqrt 12 * c * ‖gradL2 (U0 L) f‖) ^ 2 = 12 * c ^ 2 * ‖gradL2 (U0 L) f‖ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    rw [← hr] at hsum
    exact (pow_le_pow_iff_left₀ (norm_nonneg b) (by positivity) (by norm_num)).mp hsum
  exact (norm_add_le a b).trans (add_le_add hna hnb)

end AdalyFormal.M1Decay

#print axioms AdalyFormal.M1Decay.grad_flat
#print axioms AdalyFormal.M1Decay.lap_flat
#print axioms AdalyFormal.M1Decay.normSq_grad
#print axioms AdalyFormal.M1Decay.grad_norm_le
#print axioms AdalyFormal.M1Decay.lap_norm_le
#print axioms AdalyFormal.M1Decay.lap_mulR_const
#print axioms AdalyFormal.M1Decay.comm_bound
