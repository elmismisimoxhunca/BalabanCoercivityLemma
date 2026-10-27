import MI26
import MI15

/-!
# MI27 -- the SHARP row bound `hγ : ‖ℓ^{strat} u‖ ≤ γ ‖X u‖` (M1 lane E, 2026-10-13)

* `gamma_lower_approx` (abstract, any DL10 `SiteHyp`): if `‖Qp‖ ≤ q`, `(1−η)‖u‖² ≤ ⟪Qp g, u⟫` and `⟪g, L g⟫ ≤ b‖u‖²`
  then `(1−η)² ‖u‖ ≤ q b ‖G' Qp* u‖` (DL10 `gamma_lower` with an approximate right inverse).
* `QpP_siteWt_sig` : `Q' e^{σ} = e^{σ} Q'` EXACTLY (`σ = strat · ln ℓ` is constant on every constraint block, `0` off `Ω₀`);
  `Qh_opnorm` : `‖Q' e^{σ}‖ ≤ √(max a 1)`.
* `hatX_eq` : the hatted `X̂ = L̂⁻¹ Q̂*` is `e^{−σ} X`.
* **`gamma_sharp`** : on `G = geomOf ell k S` (admissible), with `HatPack`, lane C's gauge hypotheses `hU`, `hT` (ρ),
  `12ρ ≤ 1` and the smallness `q b ε_X < (1 − 12ρ)²`:
  `‖ℓ^{strat} u‖ ≤ γ ‖X u‖`, `γ = ℓ q b / ((1−12ρ)² − q b ε_X)`, `q = √(max a 1)`, `b = (1+12ρ)² + (512ρ² + 4704)/a`,
  `ε_X` the DL12 constant of the `ψ`-weighted hatted chain. All constants are free of `k`, `L` and the tower.
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
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

/-! ## 1. the abstract approximate Γ lower bound -/

section abstract
variable {S E Y : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y]

theorem gamma_lower_approx (H : SiteHyp S E Y) (q b η : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hη : η ≤ 1)
    (hQ : ‖H.Qp‖ ≤ q) (u : Y) (g : S)
    (hrow : (1 - η) * ‖u‖ ^ 2 ≤ ⟪H.Qp g, u⟫) (hgL : ⟪g, H.L g⟫ ≤ b * ‖u‖ ^ 2) :
    (1 - η) ^ 2 * ‖u‖ ≤ q * b * ‖H.X u‖ := by
  set x := H.X u with hx
  have hLx : H.L x = ContinuousLinearMap.adjoint H.Qp u := by rw [hx, H.X_apply]; exact H.L_Linv _
  have hpos : ∀ y, 0 ≤ ⟪y, H.L y⟫ := fun y => by rw [H.L_form]; have := H.hm; positivity
  have e1 : ⟪H.Qp g, u⟫ = ⟪x, H.L g⟫ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← hLx, ← H.L_sym]
    exact real_inner_comm _ _
  have hCS : ⟪x, H.L g⟫ ^ 2 ≤ ⟪x, H.L x⟫ * ⟪g, H.L g⟫ := by
    have hq' : ∀ t : ℝ, 0 ≤ ⟪x, H.L x⟫ + 2 * t * ⟪x, H.L g⟫ + t ^ 2 * ⟪g, H.L g⟫ := by
      intro t
      have := hpos (x + t • g)
      have e : ⟪x + t • g, H.L (x + t • g)⟫ = ⟪x, H.L x⟫ + 2 * t * ⟪x, H.L g⟫ + t ^ 2 * ⟪g, H.L g⟫ := by
        simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
        have : ⟪g, H.L x⟫ = ⟪x, H.L g⟫ := by rw [← H.L_sym, real_inner_comm]
        rw [this]; ring
      rw [e] at this; exact this
    by_cases hg0 : ⟪g, H.L g⟫ = 0
    · have hx0 : ⟪x, H.L g⟫ = 0 := by
        by_contra hne
        have ht := hq' (-(⟪x, H.L x⟫ + 1) / (2 * ⟪x, H.L g⟫))
        have e : 2 * (-(⟪x, H.L x⟫ + 1) / (2 * ⟪x, H.L g⟫)) * ⟪x, H.L g⟫ = -(⟪x, H.L x⟫ + 1) := by
          field_simp
        rw [hg0, e] at ht
        linarith [ht, mul_zero ((-(⟪x, H.L x⟫ + 1) / (2 * ⟪x, H.L g⟫)) ^ 2)]
      rw [hx0, hg0]; simp
    · have hgpos : 0 < ⟪g, H.L g⟫ := lt_of_le_of_ne (hpos g) (Ne.symm hg0)
      have := hq' (-⟪x, H.L g⟫ / ⟪g, H.L g⟫)
      have e : ⟪x, H.L x⟫ + 2 * (-⟪x, H.L g⟫ / ⟪g, H.L g⟫) * ⟪x, H.L g⟫
          + (-⟪x, H.L g⟫ / ⟪g, H.L g⟫) ^ 2 * ⟪g, H.L g⟫
          = ⟪x, H.L x⟫ - ⟪x, H.L g⟫ ^ 2 / ⟪g, H.L g⟫ := by field_simp; ring
      rw [e] at this
      have h2 : ⟪x, H.L g⟫ ^ 2 / ⟪g, H.L g⟫ ≤ ⟪x, H.L x⟫ := by linarith
      rwa [div_le_iff₀ hgpos] at h2
  have hxLx : ⟪x, H.L x⟫ ≤ q * ‖x‖ * ‖u‖ := by
    rw [hLx, ContinuousLinearMap.adjoint_inner_right]
    refine (real_inner_le_norm _ _).trans ?_
    have := H.Qp.le_opNorm x
    have h2 : ‖H.Qp x‖ ≤ q * ‖x‖ := this.trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have h1η : 0 ≤ 1 - η := by linarith
  have hP0 : 0 ≤ (1 - η) * ‖u‖ ^ 2 := by positivity
  have hu4 : ((1 - η) * ‖u‖ ^ 2) ^ 2 ≤ (q * ‖x‖ * ‖u‖) * (b * ‖u‖ ^ 2) := by
    have h1 : ((1 - η) * ‖u‖ ^ 2) ^ 2 ≤ ⟪H.Qp g, u⟫ ^ 2 := pow_le_pow_left₀ hP0 hrow 2
    rw [e1] at h1
    calc ((1 - η) * ‖u‖ ^ 2) ^ 2 ≤ ⟪x, H.L g⟫ ^ 2 := h1
      _ ≤ ⟪x, H.L x⟫ * ⟪g, H.L g⟫ := hCS
      _ ≤ (q * ‖x‖ * ‖u‖) * (b * ‖u‖ ^ 2) := mul_le_mul hxLx hgL (hpos g) (by positivity)
  by_cases hu0 : ‖u‖ = 0
  · rw [hu0, mul_zero]; exact mul_nonneg (mul_nonneg hq hb) (norm_nonneg _)
  have hupos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu0)
  have hu3 : 0 < ‖u‖ ^ 3 := by positivity
  have : ((1 - η) ^ 2 * ‖u‖) * ‖u‖ ^ 3 ≤ (q * b * ‖x‖) * ‖u‖ ^ 3 := by
    calc ((1 - η) ^ 2 * ‖u‖) * ‖u‖ ^ 3 = ((1 - η) * ‖u‖ ^ 2) ^ 2 := by ring
      _ ≤ (q * ‖x‖ * ‖u‖) * (b * ‖u‖ ^ 2) := hu4
      _ = (q * b * ‖x‖) * ‖u‖ ^ 3 := by ring
  exact le_of_mul_le_mul_right this hu3

end abstract

/-! ## 2. the hatted chain: exact commutation, norm, `X̂` -/

section hat
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} {W : ℕ}

theorem ypWt_le_of (G : TowerGeom Lf) (φ χ : PeriodicLatticeSite Lf → ℝ) (h : ∀ x, φ x ≤ χ x) (v : YP G) :
    ‖ypWt G φ v‖ ≤ ‖ypWt G χ v‖ := by
  have hsq : ‖ypWt G φ v‖ ^ 2 ≤ ‖ypWt G χ v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum (fun p _ => ?_)
    rw [ypWt_apply, ypWt_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (h (rowSite p))) (norm_nonneg _)) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

theorem ypWt_add_const (G : TowerGeom Lf) (φ : PeriodicLatticeSite Lf → ℝ) (c : ℝ) (v : YP G) :
    ypWt G (fun x => φ x + c) v = Real.exp c • ypWt G φ v := by
  refine PiLp.ext (fun p => ?_)
  rw [PiLp.smul_apply, ypWt_apply, ypWt_apply, smul_smul, ← Real.exp_add, add_comm c]

theorem siteWt_zero_fn (f : SiteL2 Lf) : siteWt (fun _ => (0 : ℝ)) f = f := by
  refine PiLp.ext (fun x => ?_)
  rw [siteWt_apply, Real.exp_zero, one_smul]

/-- `Q' e^{σ} = e^{σ} Q'` exactly. -/
theorem QpP_siteWt_sig (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (U : Cfg Lf) (a : ℝ) (f : SiteL2 Lf) :
    QpP (geomOf ell k S) U a (siteWt (sigG (geomOf ell k S)) f)
      = ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (QpP (geomOf ell k S) U a f) := by
  classical
  have hell0 : 0 < ell := by omega
  have hP := properTower_geomOf hell0 hS
  refine PiLp.ext (fun p => ?_)
  cases p with
  | inl q =>
    rw [QpP_inl, ypWt_apply, QpP_inl]
    have hj : jq q ≤ k := jq_le q
    have hy : yq q ∈ (geomOf ell k S).Lam (jq q) := yq_mem q
    have hyy : yq q ∈ blockOf (yq q) (ell ^ jq q) := by
      rw [mem_blockOf]; intro μ; exact ⟨le_rfl, by have := Nat.one_le_pow (jq q) ell hell0; omega⟩
    have hsy : stratG (geomOf ell k S) (yq q) = jq q := stratG_eq hP hj hy hyy
    have hloc : Qlev (geomOf ell k S) U q.1.1.val q.1.2 (siteMask (geomOf ell k S).Om0 (siteWt (sigG (geomOf ell k S)) f))
        = Qlev (geomOf ell k S) U q.1.1.val q.1.2
            (Real.exp (sigG (geomOf ell k S) (yq q)) • siteMask (geomOf ell k S).Om0 f) := by
      refine Qlev_congr_box (geomOf ell k S) U (jq q) (yq q) _ _ (fun x hx => ?_)
      rw [show (geomOf ell k S).ell = ell from rfl, boxF_eq_blockOf] at hx
      have hO := block_Om0 hP q hx
      rw [PiLp.smul_apply, siteMask_on _ _ _ hO, siteMask_on _ _ _ hO, siteWt_apply]
      have hsx : stratG (geomOf ell k S) x = jq q := stratG_eq hP hj hy hx
      unfold sigG
      rw [hsx, hsy]
    rw [hloc, map_smul, smul_comm]
    rfl
  | inr x => rfl

theorem Qh_le (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (U : Cfg Lf) (a : ℝ) (ha : 0 < a) (f : SiteL2 Lf) :
    ‖Qh (geomOf ell k S) U a f‖ ≤ Real.sqrt (max a 1) * ‖f‖ := by
  have e : Qh (geomOf ell k S) U a f = ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (QpP (geomOf ell k S) U a f) :=
    QpP_siteWt_sig hS hell U a f
  rw [e]
  have h := Q_row_bound hS hell U a ha f
  have hm : 0 ≤ max a 1 := le_trans zero_le_one (le_max_right _ _)
  have h2 : ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (QpP (geomOf ell k S) U a f)‖ ^ 2
      ≤ (Real.sqrt (max a 1) * ‖f‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hm]; exact h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

theorem Qh_opnorm (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (U : Cfg Lf) (a : ℝ) (ha : 0 < a) :
    ‖Qh (geomOf ell k S) U a‖ ≤ Real.sqrt (max a 1) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (Qh_le hS hell U a ha)

variable (hS : Admissible ell M R k S) (hW : 1 ≤ W) (hell : 2 ≤ ell) (hR : 1 ≤ R) (hM : 1 ≤ M) (hWR : W ≤ R * M * ell)

/-- `X̂ = e^{−σ} X`. -/
theorem hatX_eq (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (u : YP (geomOf ell k S)) :
    (psiHypP hS hW hell hR hM hWR U a cs hp).X u = siteWt (-sigG (geomOf ell k S)) (Xop (geomOf ell k S) U a u) := by
  show Linvh (geomOf ell k S) U a (ContinuousLinearMap.adjoint (Qh (geomOf ell k S) U a) u) = _
  simp only [Linvh, Qh, Xop, ContinuousLinearMap.adjoint_comp, siteWt_adjoint, ContinuousLinearMap.comp_apply]
  rw [siteWt_cancel_neg]

include hS hW hell hR hM hWR in
/-- `ℓ^{strat}` vs `e^{ψ}` on rows. -/
theorem yp_sig_le_psi (u : YP (geomOf ell k S)) :
    ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ≤ (ell : ℝ) * ‖ypWt (geomOf ell k S) (psiW S W ell k) u‖ := by
  have h := ypWt_le_of (geomOf ell k S) (sigG (geomOf ell k S)) (fun x => psiW S W ell k x + Real.log ell)
    (fun x => (sig_psi hS hW hell hR hM hWR x).2) u
  rw [ypWt_add_const, norm_exp_log_smul (show 0 < ell by omega)] at h
  exact h

/-- the tent right inverse, hatted: row and energy. -/
theorem hat_ext (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hU : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
    (hT : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j),
      z ∈ CoarseLattice Lf (ell ^ i) → ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower (geomOf ell k S) U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)
    (u : YP (geomOf ell k S)) :
    (1 - 12 * ρ) * ‖u‖ ^ 2
        ≤ ⟪(psiHypP hS hW hell hR hM hWR U a cs hp).Qp
            (siteWt (-sigG (geomOf ell k S)) (extT (geomOf ell k S) ell a u)), u⟫
      ∧ ⟪siteWt (-sigG (geomOf ell k S)) (extT (geomOf ell k S) ell a u),
          (psiHypP hS hW hell hR hM hWR U a cs hp).L (siteWt (-sigG (geomOf ell k S)) (extT (geomOf ell k S) ell a u))⟫
        ≤ ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a) * ‖u‖ ^ 2 := by
  classical
  have hell0 : 0 < ell := by omega
  have hP := properTower_geomOf hell0 hS
  have hdvd := hdvd_of_admissible hS
  have ha := hp.ha
  have hw : ∀ j, 0 ≤ wq (geomOf ell k S) a j := fun j => (wq_pos hell hP a j ha).le
  have hQg : (psiHypP hS hW hell hR hM hWR U a cs hp).Qp
        (siteWt (-sigG (geomOf ell k S)) (extT (geomOf ell k S) ell a u))
      = QpP (geomOf ell k S) U a (extT (geomOf ell k S) ell a u) := by
    show QpP (geomOf ell k S) U a (siteWt (sigG (geomOf ell k S))
      (siteWt (-sigG (geomOf ell k S)) (extT (geomOf ell k S) ell a u))) = _
    rw [siteWt_neg_cancel]
  have hDg : (psiHypP hS hW hell hR hM hWR U a cs hp).D
        (siteWt (-sigG (geomOf ell k S)) (extT (geomOf ell k S) ell a u))
      = Dm (geomOf ell k S) U (extT (geomOf ell k S) ell a u) := by
    show Dm (geomOf ell k S) U (siteWt (sigG (geomOf ell k S))
      (siteWt (-sigG (geomOf ell k S)) (extT (geomOf ell k S) ell a u))) = _
    rw [siteWt_neg_cancel]
  refine ⟨?_, ?_⟩
  · rw [hQg, PiLp.inner_apply, Fintype.sum_sum_type]
    have hun : ‖u‖ ^ 2 = ∑ q : QIdx (geomOf ell k S), ‖u (Sum.inl q)‖ ^ 2
        + ∑ x : OffIdx (geomOf ell k S), ‖u (Sum.inr x)‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
    have hrow : ∀ q : QIdx (geomOf ell k S), (1 - 12 * ρ) * ‖u (Sum.inl q)‖ ^ 2
        ≤ ⟪QpP (geomOf ell k S) U a (extT (geomOf ell k S) ell a u) (Sum.inl q), u (Sum.inl q)⟫ := by
      intro q
      have h1 := extT_row hell hP hdvd U a ha ρ hρ hT u q
      have h2 : ⟪QpP (geomOf ell k S) U a (extT (geomOf ell k S) ell a u) (Sum.inl q), u (Sum.inl q)⟫
          = ‖u (Sum.inl q)‖ ^ 2 + ⟪QpP (geomOf ell k S) U a (extT (geomOf ell k S) ell a u) (Sum.inl q)
              - u (Sum.inl q), u (Sum.inl q)⟫ := by
        rw [inner_sub_left, real_inner_self_eq_norm_sq]; ring
      have h3 : -(12 * ρ * ‖u (Sum.inl q)‖ * ‖u (Sum.inl q)‖)
          ≤ ⟪QpP (geomOf ell k S) U a (extT (geomOf ell k S) ell a u) (Sum.inl q) - u (Sum.inl q), u (Sum.inl q)⟫ := by
        have := abs_real_inner_le_norm
          (QpP (geomOf ell k S) U a (extT (geomOf ell k S) ell a u) (Sum.inl q) - u (Sum.inl q)) (u (Sum.inl q))
        have h4 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (u (Sum.inl q)))
        have := (abs_le.mp this).1
        linarith
      rw [h2]; linarith
    have hpad : ∀ x : OffIdx (geomOf ell k S),
        ⟪QpP (geomOf ell k S) U a (extT (geomOf ell k S) ell a u) (Sum.inr x), u (Sum.inr x)⟫ = ‖u (Sum.inr x)‖ ^ 2 := by
      intro x; rw [QpP_extT_inr hP a U u x, real_inner_self_eq_norm_sq]
    rw [hun, Finset.sum_congr rfl (fun x _ => hpad x)]
    have hs1 := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => hrow q)
    rw [← Finset.mul_sum] at hs1
    have hs2 : 0 ≤ ∑ x : OffIdx (geomOf ell k S), ‖u (Sum.inr x)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h12 : 0 ≤ 12 * ρ * ∑ x : OffIdx (geomOf ell k S), ‖u (Sum.inr x)‖ ^ 2 := by positivity
    linarith
  · rw [SiteHyp.L_form, hQg, hDg]
    have hE := extT_energy hell hP hdvd U a ha ρ hρ hU hT u
    rw [inner_LP (geomOf ell k S) U a hw, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hE
    have hm : (psiHypP hS hW hell hR hM hWR U a cs hp).m = 1 := rfl
    rw [hm, one_mul]
    exact hE

/-- **the sharp row bound**. -/
theorem gamma_sharp (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (h12 : 12 * ρ ≤ 1)
    (hU : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
    (hT : ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j),
      z ∈ CoarseLattice Lf (ell ^ i) → ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower (geomOf ell k S) U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)
    (hsm : Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a)
        * (psiHypP hS hW hell hR hM hWR U a cs hp).epsX (Real.sqrt (max a 1)) < (1 - 12 * ρ) ^ 2)
    (u : YP (geomOf ell k S)) :
    ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖
      ≤ (ell : ℝ) * (Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a))
          / ((1 - 12 * ρ) ^ 2 - Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a)
              * (psiHypP hS hW hell hR hM hWR U a cs hp).epsX (Real.sqrt (max a 1)))
        * ‖Xop (geomOf ell k S) U a u‖ := by
  have ha := hp.ha
  have hq0 : 0 ≤ Real.sqrt (max a 1) := Real.sqrt_nonneg _
  have hb0 : 0 ≤ (1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a := by positivity
  have hQ : ‖(psiHypP hS hW hell hR hM hWR U a cs hp).Qp‖ ≤ Real.sqrt (max a 1) := Qh_opnorm hS hell U a ha
  obtain ⟨hrow, hgL⟩ := hat_ext hS hW hell hR hM hWR U a cs hp ρ hρ hU hT
    (ypWt (geomOf ell k S) (psiW S W ell k) u)
  have hgl := gamma_lower_approx (psiHypP hS hW hell hR hM hWR U a cs hp) (Real.sqrt (max a 1))
    ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a) (12 * ρ) hq0 hb0 h12 hQ
    (ypWt (geomOf ell k S) (psiW S W ell k) u) _ hrow hgL
  have hXd := ((psiHypP hS hW hell hR hM hWR U a cs hp).Xdiff (Real.sqrt (max a 1)) hq0 hQ
    (ypWt (geomOf ell k S) (psiW S W ell k) u)).1
  have hcj : cjp (psiHypP hS hW hell hR hM hWR U a cs hp).ωY (psiHypP hS hW hell hR hM hWR U a cs hp).ωS
        (psiHypP hS hW hell hR hM hWR U a cs hp).X (ypWt (geomOf ell k S) (psiW S W ell k) u)
      = siteWt (psiW S W ell k) (siteWt (-sigG (geomOf ell k S)) (Xop (geomOf ell k S) U a u)) := by
    rw [cjp_apply]
    show siteWt (psiW S W ell k) ((psiHypP hS hW hell hR hM hWR U a cs hp).X
      (ypWt (geomOf ell k S) (-psiW S W ell k) (ypWt (geomOf ell k S) (psiW S W ell k) u))) = _
    rw [ypWt_cancel_neg, hatX_eq hS hW hell hR hM hWR U a cs hp u]
  have hcjn : ‖cjp (psiHypP hS hW hell hR hM hWR U a cs hp).ωY (psiHypP hS hW hell hR hM hWR U a cs hp).ωS
        (psiHypP hS hW hell hR hM hWR U a cs hp).X (ypWt (geomOf ell k S) (psiW S W ell k) u)‖
      ≤ ‖Xop (geomOf ell k S) U a u‖ := by
    rw [hcj, siteWt_mul]
    have := siteWt_le_of (psiW S W ell k + -sigG (geomOf ell k S)) (fun _ => (0 : ℝ))
      (fun x => by
        simp only [Pi.add_apply, Pi.neg_apply]
        linarith [(sig_psi hS hW hell hR hM hWR x).1]) (Xop (geomOf ell k S) U a u)
    rwa [siteWt_zero_fn] at this
  have hXv : ‖(psiHypP hS hW hell hR hM hWR U a cs hp).X (ypWt (geomOf ell k S) (psiW S W ell k) u)‖
      ≤ ‖Xop (geomOf ell k S) U a u‖
        + (psiHypP hS hW hell hR hM hWR U a cs hp).epsX (Real.sqrt (max a 1))
          * ‖ypWt (geomOf ell k S) (psiW S W ell k) u‖ := by
    have h2 := norm_sub_le
      (cjp (psiHypP hS hW hell hR hM hWR U a cs hp).ωY (psiHypP hS hW hell hR hM hWR U a cs hp).ωS
        (psiHypP hS hW hell hR hM hWR U a cs hp).X (ypWt (geomOf ell k S) (psiW S W ell k) u))
      (cjp (psiHypP hS hW hell hR hM hWR U a cs hp).ωY (psiHypP hS hW hell hR hM hWR U a cs hp).ωS
        (psiHypP hS hW hell hR hM hWR U a cs hp).X (ypWt (geomOf ell k S) (psiW S W ell k) u)
        - (psiHypP hS hW hell hR hM hWR U a cs hp).X (ypWt (geomOf ell k S) (psiW S W ell k) u))
    rw [sub_sub_cancel] at h2
    linarith [hcjn, hXd]
  have hD : 0 < (1 - 12 * ρ) ^ 2 - Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a)
      * (psiHypP hS hW hell hR hM hWR U a cs hp).epsX (Real.sqrt (max a 1)) := by linarith
  have h3 : (1 - 12 * ρ) ^ 2 * ‖ypWt (geomOf ell k S) (psiW S W ell k) u‖
      ≤ Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a)
        * (‖Xop (geomOf ell k S) U a u‖ + (psiHypP hS hW hell hR hM hWR U a cs hp).epsX (Real.sqrt (max a 1))
          * ‖ypWt (geomOf ell k S) (psiW S W ell k) u‖) :=
    hgl.trans (mul_le_mul_of_nonneg_left hXv (by positivity))
  have hvb : ‖ypWt (geomOf ell k S) (psiW S W ell k) u‖
      ≤ Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a) * ‖Xop (geomOf ell k S) U a u‖
        / ((1 - 12 * ρ) ^ 2 - Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a)
          * (psiHypP hS hW hell hR hM hWR U a cs hp).epsX (Real.sqrt (max a 1))) := by
    rw [le_div_iff₀ hD]
    linarith [h3]
  have hsig := yp_sig_le_psi hS hW hell hR hM hWR u
  have hell0 : (0 : ℝ) ≤ ell := Nat.cast_nonneg _
  calc ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖
      ≤ (ell : ℝ) * ‖ypWt (geomOf ell k S) (psiW S W ell k) u‖ := hsig
    _ ≤ (ell : ℝ) * (Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a) * ‖Xop (geomOf ell k S) U a u‖
        / ((1 - 12 * ρ) ^ 2 - Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a)
          * (psiHypP hS hW hell hR hM hWR U a cs hp).epsX (Real.sqrt (max a 1)))) :=
        mul_le_mul_of_nonneg_left hvb hell0
    _ = _ := by ring

end hat

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.gamma_lower_approx
#print axioms AdalyFormal.M1IMS.ypWt_le_of
#print axioms AdalyFormal.M1IMS.ypWt_add_const
#print axioms AdalyFormal.M1IMS.siteWt_zero_fn
#print axioms AdalyFormal.M1IMS.QpP_siteWt_sig
#print axioms AdalyFormal.M1IMS.Qh_le
#print axioms AdalyFormal.M1IMS.Qh_opnorm
#print axioms AdalyFormal.M1IMS.hatX_eq
#print axioms AdalyFormal.M1IMS.yp_sig_le_psi
#print axioms AdalyFormal.M1IMS.hat_ext
#print axioms AdalyFormal.M1IMS.gamma_sharp
