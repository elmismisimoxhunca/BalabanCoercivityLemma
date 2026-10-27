import DLR5
import DLR8
import DLR20

/-!
# DL21 -- the genuine site layer as an instance of the abstract `SiteHyp` (full tower, `Ω₀ =` torus)

* `siteWP φ`, `bondWP φ`, `coarseWP φ` : the exponential weights as `WPair`s on `SiteL2`, `BondFnL2`, `coarseC (GF ell k Lu)`.
* `D_cjp_norm`/`D_cjm_norm` : `‖D^± − D‖ ≤ √3(e^{θ'}−1)` for the genuine covariant gradient (DL6).
* `Q_cjp_norm`/`Q_cjm_norm` : `‖Qtop^± − Qtop‖ ≤ (e^{δ}−1)·√((1/ℓ³)^k)` for the genuine top-level `Q'_k(U)` (DL7/DL8 box bounds).
* `Qpa_eq_top` : `Q'*aQ' = m · Qtop*Qtop`, `m = a_k ℓ^k`, on the full tower; `DelpA_eq_L` : `Δ'_a = D*D + m Qtop*Qtop`.
* `Gp_left`/`Gp_right` : `G' = Gp` is a two-sided inverse of `Δ'_a` when `Δ'_a + (1 − Ω₀)` is a unit.
* **`siteHypM0`** : the genuine `(D_U, Qtop, m, G', weights)` as a `SiteHyp`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)

section weights
variable {L : PeriodicLatticeExtent}

noncomputable def siteWP (φ : PeriodicLatticeSite L → ℝ) : WPair (SiteL2 L) where
  w := siteWt φ
  wi := siteWt (-φ)
  w_wi := siteWt_neg_cancel φ
  wi_w := siteWt_cancel_neg φ
  w_sym := siteWt_symm φ
  wi_sym := siteWt_symm (-φ)

noncomputable def bondWP (φ : PeriodicLatticeSite L → ℝ) : WPair (BondFnL2 L) where
  w := bondWt φ
  wi := bondWt (-φ)
  w_wi := bondWt_neg_cancel φ
  wi_w := bondWt_cancel_neg φ
  w_sym := bondWt_symm φ
  wi_sym := bondWt_symm (-φ)

theorem siteWP_inv (φ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) : (siteWP φ).inv.w f = siteWt (-φ) f := rfl
theorem siteWP_inv' (φ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) : (siteWP φ).inv.wi f = siteWt φ f := rfl

theorem WtLip_neg (θ' : ℝ) (φ : PeriodicLatticeSite L → ℝ) (h : WtLip θ' φ) : WtLip θ' (-φ) := by
  intro x μ
  have := h x μ
  simp only [Pi.neg_apply]
  rw [show -φ (periodicLatticeShift x μ) - -φ x = -(φ (periodicLatticeShift x μ) - φ x) by ring, abs_neg]
  exact this

theorem opnorm_le_of {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] (T : A →L[ℝ] B) (c : ℝ) (hc : 0 ≤ c) (h : ∀ x, ‖T x‖ ≤ c * ‖x‖) : ‖T‖ ≤ c :=
  ContinuousLinearMap.opNorm_le_bound _ hc h

/-- the gradient commutator in `WPair` form -/
theorem D_cjp_norm (U : Cfg L) (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) :
    ‖cjp (siteWP φ) (bondWP φ) (gradL2 U) - gradL2 U‖ ≤ Real.sqrt 3 * (Real.exp θ' - 1) := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have h1 : 0 ≤ Real.exp θ' - 1 := by linarith [Real.add_one_le_exp θ']
  refine opnorm_le_of _ _ (by positivity) (fun f => ?_)
  rw [ContinuousLinearMap.sub_apply, cjp_apply]
  exact grad_conj_err U φ θ' hφ f

theorem D_cjm_norm (U : Cfg L) (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) :
    ‖cjm (siteWP φ) (bondWP φ) (gradL2 U) - gradL2 U‖ ≤ Real.sqrt 3 * (Real.exp θ' - 1) := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have h1 : 0 ≤ Real.exp θ' - 1 := by linarith [Real.add_one_le_exp θ']
  refine opnorm_le_of _ _ (by positivity) (fun f => ?_)
  rw [ContinuousLinearMap.sub_apply]
  have e : cjm (siteWP φ) (bondWP φ) (gradL2 U) f = bondWt (-φ) (gradL2 U (siteWt (-(-φ)) f)) := by
    rw [neg_neg]; rfl
  rw [e]
  exact grad_conj_err U (-φ) θ' (WtLip_neg θ' φ hφ) f

end weights

/-! ## the coarse weight and the `Qtop` commutator (full tower) -/

section coarse
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent)

/-- multiplication by `e^{φ(y)}` on `L²(Λ_k)` -/
noncomputable def coarseWt (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) :
    coarseC (GF ell k Lu) →L[ℝ] coarseC (GF ell k Lu) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => WithLp.toLp 2 (fun y => Real.exp (φ y.1) • u y)
      map_add' := fun u v => by refine PiLp.ext (fun y => ?_); simp [smul_add]
      map_smul' := fun c u => by
        refine PiLp.ext (fun y => ?_)
        simp only [PiLp.smul_apply, RingHom.id_apply, PiLp.toLp_apply]
        exact smul_comm _ _ _ }

theorem coarseWt_apply (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (u : coarseC (GF ell k Lu))
    (y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}) :
    (coarseWt ell k Lu φ u) y = Real.exp (φ y.1) • u y := rfl

theorem coarseWt_neg_cancel (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (u : coarseC (GF ell k Lu)) :
    coarseWt ell k Lu φ (coarseWt ell k Lu (-φ) u) = u := by
  refine PiLp.ext (fun y => ?_)
  rw [coarseWt_apply, coarseWt_apply, smul_smul, ← Real.exp_add]
  simp

theorem coarseWt_cancel_neg (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (u : coarseC (GF ell k Lu)) :
    coarseWt ell k Lu (-φ) (coarseWt ell k Lu φ u) = u := by
  have := coarseWt_neg_cancel ell k Lu (-φ) u
  simpa using this

theorem coarseWt_symm (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (u v : coarseC (GF ell k Lu)) :
    ⟪coarseWt ell k Lu φ u, v⟫ = ⟪u, coarseWt ell k Lu φ v⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [coarseWt_apply, coarseWt_apply, real_inner_smul_left, real_inner_smul_right]

noncomputable def coarseWP (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) : WPair (coarseC (GF ell k Lu)) where
  w := coarseWt ell k Lu φ
  wi := coarseWt ell k Lu (-φ)
  w_wi := coarseWt_neg_cancel ell k Lu φ
  wi_w := coarseWt_cancel_neg ell k Lu φ
  w_sym := coarseWt_symm ell k Lu φ
  wi_sym := coarseWt_symm ell k Lu (-φ)

theorem Lam_k_dvd (y : PeriodicLatticeSite (scaleUp ell k Lu)) (hy : y ∈ (GF ell k Lu).Lam (GF ell k Lu).k) :
    ∀ μ, ell ^ k ∣ (y μ).val :=
  (fullTower_lam_k ell k Lu y).mp hy

/-- disjoint top-level boxes, summed over the subtype `Λ_k` -/
theorem sum_boxes_sub (f : SiteL2 (scaleUp ell k Lu)) :
    ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}, ∑ x ∈ boxF y.1 (ell ^ k), ‖f x‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  classical
  rw [← Finset.sum_biUnion]
  · rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => sq_nonneg _)
  · intro y _ y' _ hne
    have hne' : y.1 ≠ y'.1 := fun h => hne (Subtype.ext h)
    exact boxF_disjoint (Lam_k_dvd ell k Lu y.1 y.2) (Lam_k_dvd ell k Lu y'.1 y'.2) hne'

/-- `e^{φ(y)}` times a row on `e^{-φ}f` is the row on `e^{φ(y)−φ} f` -/
theorem Qlev_conj (U : Cfg (scaleUp ell k Lu)) (y : PeriodicLatticeSite (scaleUp ell k Lu))
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (f : SiteL2 (scaleUp ell k Lu)) :
    Real.exp (φ y) • Qlev (GF ell k Lu) U k y (siteWt (-φ) f)
      = Qlev (GF ell k Lu) U k y (siteWt (fun x => φ y - φ x) f) := by
  rw [Qlev_siteWt_shift (GF ell k Lu) U k y (-φ) (-φ y) f, smul_smul, ← Real.exp_add]
  have e1 : φ y + -φ y = 0 := by ring
  rw [e1, Real.exp_zero, one_smul]
  have hf : (fun x => (-φ) x - -φ y) = (fun x => φ y - φ x) := by
    funext x; simp only [Pi.neg_apply]; ring
  rw [hf]

theorem Q_conj_sq (U : Cfg (scaleUp ell k Lu)) (hell : 0 < ell) (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ)
    (δ : ℝ) (hbox : ∀ y ∈ (GF ell k Lu).Lam (GF ell k Lu).k, ∀ x ∈ boxF y (ell ^ k), |φ y - φ x| ≤ δ)
    (f : SiteL2 (scaleUp ell k Lu)) :
    ‖coarseWt ell k Lu φ (Qtop (GF ell k Lu) U (siteWt (-φ) f)) - Qtop (GF ell k Lu) U f‖ ^ 2
      ≤ ((1 / (ell : ℝ) ^ 3) ^ k * (Real.exp δ - 1) ^ 2) * ‖f‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  have hpt : ∀ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k},
      ‖(coarseWt ell k Lu φ (Qtop (GF ell k Lu) U (siteWt (-φ) f)) - Qtop (GF ell k Lu) U f) y‖ ^ 2
        ≤ ((1 / (ell : ℝ) ^ 3) ^ k * (Real.exp δ - 1) ^ 2) * ∑ x ∈ boxF y.1 (ell ^ k), ‖f x‖ ^ 2 := by
    intro y
    have e : (coarseWt ell k Lu φ (Qtop (GF ell k Lu) U (siteWt (-φ) f)) - Qtop (GF ell k Lu) U f) y
        = Qlev (GF ell k Lu) U k y.1 (siteWt (fun x => φ y.1 - φ x) f) - Qlev (GF ell k Lu) U k y.1 f := by
      rw [PiLp.sub_apply, coarseWt_apply]
      show Real.exp (φ y.1) • Qlev (GF ell k Lu) U (GF ell k Lu).k y.1 (siteWt (-φ) f) - Qlev (GF ell k Lu) U (GF ell k Lu).k y.1 f = _
      exact congrArg (· - Qlev (GF ell k Lu) U k y.1 f) (Qlev_conj ell k Lu U y.1 φ f)
    rw [e]
    have h := Qlev_err_sq (GF ell k Lu) U hell k y.1 (fun x => φ y.1 - φ x) δ (fun x hx => hbox y.1 y.2 x hx) f
    rw [mul_assoc] at h ⊢
    exact h
  calc ∑ y, ‖(coarseWt ell k Lu φ (Qtop (GF ell k Lu) U (siteWt (-φ) f)) - Qtop (GF ell k Lu) U f) y‖ ^ 2
      ≤ ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k},
          ((1 / (ell : ℝ) ^ 3) ^ k * (Real.exp δ - 1) ^ 2) * ∑ x ∈ boxF y.1 (ell ^ k), ‖f x‖ ^ 2 :=
        Finset.sum_le_sum (fun y _ => hpt y)
    _ = ((1 / (ell : ℝ) ^ 3) ^ k * (Real.exp δ - 1) ^ 2)
          * ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}, ∑ x ∈ boxF y.1 (ell ^ k), ‖f x‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ ((1 / (ell : ℝ) ^ 3) ^ k * (Real.exp δ - 1) ^ 2) * ‖f‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_boxes_sub ell k Lu f) (by positivity)

theorem Q_cjp_norm (U : Cfg (scaleUp ell k Lu)) (hell : 0 < ell) (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hbox : ∀ y ∈ (GF ell k Lu).Lam (GF ell k Lu).k, ∀ x ∈ boxF y (ell ^ k), |φ y - φ x| ≤ δ) :
    ‖cjp (siteWP φ) (coarseWP ell k Lu φ) (Qtop (GF ell k Lu) U) - Qtop (GF ell k Lu) U‖
      ≤ Real.sqrt ((1 / (ell : ℝ) ^ 3) ^ k) * (Real.exp δ - 1) := by
  have h1 : 0 ≤ Real.exp δ - 1 := by linarith [Real.add_one_le_exp δ]
  refine opnorm_le_of _ _ (by positivity) (fun f => ?_)
  rw [ContinuousLinearMap.sub_apply, cjp_apply]
  have h := Q_conj_sq ell k Lu U hell φ δ hbox f
  have e : ((1 / (ell : ℝ) ^ 3) ^ k * (Real.exp δ - 1) ^ 2) * ‖f‖ ^ 2
      = (Real.sqrt ((1 / (ell : ℝ) ^ 3) ^ k) * (Real.exp δ - 1) * ‖f‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  rw [e] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

theorem Q_cjm_norm (U : Cfg (scaleUp ell k Lu)) (hell : 0 < ell) (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hbox : ∀ y ∈ (GF ell k Lu).Lam (GF ell k Lu).k, ∀ x ∈ boxF y (ell ^ k), |φ y - φ x| ≤ δ) :
    ‖cjm (siteWP φ) (coarseWP ell k Lu φ) (Qtop (GF ell k Lu) U) - Qtop (GF ell k Lu) U‖
      ≤ Real.sqrt ((1 / (ell : ℝ) ^ 3) ^ k) * (Real.exp δ - 1) := by
  have hbox' : ∀ y ∈ (GF ell k Lu).Lam (GF ell k Lu).k, ∀ x ∈ boxF y (ell ^ k), |(-φ) y - (-φ) x| ≤ δ := by
    intro y hy x hx
    simp only [Pi.neg_apply]
    rw [show -φ y - -φ x = -(φ y - φ x) by ring, abs_neg]
    exact hbox y hy x hx
  have h := Q_cjp_norm ell k Lu U hell (-φ) δ hδ hbox'
  have e : cjm (siteWP φ) (coarseWP ell k Lu φ) (Qtop (GF ell k Lu) U)
      = cjp (siteWP (-φ)) (coarseWP ell k Lu (-φ)) (Qtop (GF ell k Lu) U) := by
    ext1 f
    show coarseWt ell k Lu (-φ) (Qtop (GF ell k Lu) U (siteWt φ f))
      = coarseWt ell k Lu (-φ) (Qtop (GF ell k Lu) U (siteWt (-(-φ)) f))
    rw [neg_neg]
  rw [e]; exact h

/-! ## `Δ'_a = D*D + m Qtop*Qtop` on the full tower -/

/-- the mass coefficient of the top level -/
noncomputable def mTop (a : ℝ) : ℝ := ajSeq a ell k * (ell : ℝ) ^ k

open Classical in
theorem inner_Qpa_bil (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (g f : SiteL2 (scaleUp ell k Lu)) :
    ⟪g, Qpa (GF ell k Lu) U a f⟫ = mTop ell k a * ⟪Qtop (GF ell k Lu) U g, Qtop (GF ell k Lu) U f⟫ := by
  simp only [Qpa, ContinuousLinearMap.sum_apply, inner_sum]
  rw [Finset.sum_range_succ]
  have hlow : ∑ j ∈ Finset.range (GF ell k Lu).k, ∑ y : PeriodicLatticeSite (scaleUp ell k Lu),
      ⟪g, (if y ∈ (GF ell k Lu).Lam j then (ajSeq a (GF ell k Lu).ell j * ((GF ell k Lu).ell : ℝ) ^ j) •
        ((ContinuousLinearMap.adjoint (Qlev (GF ell k Lu) U j y)).comp (Qlev (GF ell k Lu) U j y)) else 0) f⟫ = 0 := by
    refine Finset.sum_eq_zero (fun j hj => Finset.sum_eq_zero (fun y _ => ?_))
    have hy : y ∉ (GF ell k Lu).Lam j := by
      show y ∉ (geomOf ell k (fullTower ell k Lu)).Lam j
      rw [fullTower_lam_lt ell k Lu j (Finset.mem_range.mp hj)]; exact Set.notMem_empty y
    simp [hy]
  rw [hlow, zero_add]
  have hterm : ∀ y : PeriodicLatticeSite (scaleUp ell k Lu),
      ⟪g, (if y ∈ (GF ell k Lu).Lam (GF ell k Lu).k then (ajSeq a (GF ell k Lu).ell (GF ell k Lu).k
          * ((GF ell k Lu).ell : ℝ) ^ (GF ell k Lu).k) •
        ((ContinuousLinearMap.adjoint (Qlev (GF ell k Lu) U (GF ell k Lu).k y)).comp
          (Qlev (GF ell k Lu) U (GF ell k Lu).k y)) else 0) f⟫
      = if y ∈ (GF ell k Lu).Lam (GF ell k Lu).k then mTop ell k a *
          ⟪Qlev (GF ell k Lu) U (GF ell k Lu).k y g, Qlev (GF ell k Lu) U (GF ell k Lu).k y f⟫ else 0 := by
    intro y
    split_ifs
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, real_inner_smul_right,
        ContinuousLinearMap.adjoint_inner_right]
      rfl
    · simp
  rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.sum_filter]
  rw [PiLp.inner_apply, Finset.mul_sum]
  exact Finset.sum_subtype (p := fun y => y ∈ (GF ell k Lu).Lam (GF ell k Lu).k) _ (fun y => by simp)
    (fun y => mTop ell k a * ⟪Qlev (GF ell k Lu) U (GF ell k Lu).k y g, Qlev (GF ell k Lu) U (GF ell k Lu).k y f⟫)

theorem DelpA_eq_L (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (f : SiteL2 (scaleUp ell k Lu)) :
    DelpA (GF ell k Lu) U a f
      = (ContinuousLinearMap.adjoint (gradL2 U) ∘L gradL2 U
          + mTop ell k a • (ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U) ∘L Qtop (GF ell k Lu) U)) f := by
  rw [DelpA_univ (GF ell k Lu) (AdalyFormal.SliceCoerc.fullTower_Om0 ell k Lu) U a f]
  refine ext_inner_left ℝ (fun g => ?_)
  rw [inner_add_right, inner_Qpa_bil]
  simp only [lapFull, gradAdj, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, inner_add_right, real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right]

/-- `G'` is a two-sided inverse of `Δ'_a` -/
theorem Gp_right (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
    (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0))) (x : SiteL2 (scaleUp ell k Lu)) :
    DelpA (GF ell k Lu) U a (Gp (GF ell k Lu) U a x) = x := by
  rw [(Gp_spec (GF ell k Lu) U a hu x).2, AdalyFormal.SliceCoerc.fullTower_Om0]
  exact siteMask_univ x

theorem Gp_left (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
    (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0))) (x : SiteL2 (scaleUp ell k Lu)) :
    Gp (GF ell k Lu) U a (DelpA (GF ell k Lu) U a x) = x := by
  have hm : ∀ v : SiteL2 (scaleUp ell k Lu), siteMask (GF ell k Lu).Om0 v = v := fun v => by
    rw [AdalyFormal.SliceCoerc.fullTower_Om0]; exact siteMask_univ v
  have hX : (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)) x = DelpA (GF ell k Lu) U a x := by
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, hm, ContinuousLinearMap.one_apply, sub_self,
      add_zero]
  show (Ring.inverse (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
      (siteMask (GF ell k Lu).Om0 (DelpA (GF ell k Lu) U a x)) = x
  rw [hm, ← hX, ← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hu, ContinuousLinearMap.one_apply]

end coarse

#print axioms siteWP
#print axioms bondWP
#print axioms WtLip_neg
#print axioms D_cjp_norm
#print axioms D_cjm_norm
#print axioms coarseWP
#print axioms sum_boxes_sub
#print axioms Qlev_conj
#print axioms Q_conj_sq
#print axioms Q_cjp_norm
#print axioms Q_cjm_norm
#print axioms inner_Qpa_bil
#print axioms DelpA_eq_L
#print axioms Gp_right
#print axioms Gp_left

end AdalyFormal.DLayer
