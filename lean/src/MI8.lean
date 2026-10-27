import MI7

/-!
# MI8 -- the `ψ`-weighted hatted `SiteHyp` instances and the stratified bounds on the genuine `G' = LinvP` (M1 lane E)

On `G = geomOf ell k S` with S1 (`cs · wNormSq ≤ ⟪·, Δ'_a ·⟫`, `0 < cs ≤ 1`), `IsUnit LP`, and the smallness
`24 (δD² + δQ²) ≤ cs`, `4 δD² ≤ cs`, `δD = √3 (e^θ − 1)`, `δQ = √a (e^{δ₀} − 1)` (`θ = 2ℓ² ln ℓ/W`, `δ₀ = 3ℓ ln ℓ/W`):
* `psiHypP`, `psiHypN` : DL10 `SiteHyp` at the weights `e^{+ψ}`, `e^{−ψ}`;
* the weight comparisons `ψ ≤ σ ≤ ψ + ln ℓ` (`sig_psi`);
* the bounds on the GENUINE operators (`σ = strat · ln ℓ`, so `e^{σ} = ℓ^{strat}`; bond weights at the tail):
  `g1`  : `‖G' y‖ ≤ (4ℓ/cs) ‖ℓ^{2 strat} y‖`;
  `g1'` : `‖ℓ^{−2 strat} G' y‖ ≤ (4ℓ/cs) ‖y‖`;
  `g2`  : `‖G' D* w‖ ≤ ℓ √(48/cs) ‖ℓ^{strat} w‖`;
  `g3`  : `‖ℓ^{strat} D G' y‖ ≤ ℓ (√(12/cs) + 4δD/cs) ‖ℓ^{2 strat} y‖`;
  `g5`  : `‖ℓ^{−strat} D G' y‖ ≤ ℓ (√(12/cs) + 4δD/cs) ‖y‖`   (`G' = LinvP`, `D = Dm`).
All constants are free of `k`, the torus and the tower.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

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

variable {L : PeriodicLatticeExtent}

/-! ## 0. weight comparisons -/

theorem siteWt_le_of (φ χ : PeriodicLatticeSite L → ℝ) (h : ∀ x, φ x ≤ χ x) (f : SiteL2 L) :
    ‖siteWt φ f‖ ≤ ‖siteWt χ f‖ := by
  have hsq : ‖siteWt φ f‖ ^ 2 ≤ ‖siteWt χ f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum (fun x _ => ?_)
    rw [siteWt_apply, siteWt_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (h x)) (norm_nonneg _)) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

theorem bondWt_le_of (φ χ : PeriodicLatticeSite L → ℝ) (h : ∀ x, φ x ≤ χ x) (f : BondFnL2 L) :
    ‖bondWt φ f‖ ≤ ‖bondWt χ f‖ := by
  have hsq : ‖bondWt φ f‖ ^ 2 ≤ ‖bondWt χ f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum (fun b _ => ?_)
    rw [bondWt_apply, bondWt_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (h b.1)) (norm_nonneg _)) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

theorem siteWt_add_const (φ : PeriodicLatticeSite L → ℝ) (c : ℝ) (f : SiteL2 L) :
    siteWt (fun x => φ x + c) f = Real.exp c • siteWt φ f := by
  refine PiLp.ext (fun x => ?_)
  rw [PiLp.smul_apply, siteWt_apply, siteWt_apply, smul_smul, ← Real.exp_add, add_comm c]

theorem bondWt_add_const (φ : PeriodicLatticeSite L → ℝ) (c : ℝ) (f : BondFnL2 L) :
    bondWt (fun x => φ x + c) f = Real.exp c • bondWt φ f := by
  refine PiLp.ext (fun b => ?_)
  rw [PiLp.smul_apply, bondWt_apply, bondWt_apply, smul_smul, ← Real.exp_add, add_comm c]

theorem siteWt_mul (φ χ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) :
    siteWt φ (siteWt χ f) = siteWt (φ + χ) f := by
  refine PiLp.ext (fun x => ?_)
  rw [siteWt_apply, siteWt_apply, siteWt_apply, smul_smul, ← Real.exp_add, Pi.add_apply]

theorem bondWt_adjoint (φ : PeriodicLatticeSite L → ℝ) :
    ContinuousLinearMap.adjoint (bondWt φ) = bondWt φ := by
  ext1 f
  refine ext_inner_left ℝ (fun g => ?_)
  rw [ContinuousLinearMap.adjoint_inner_right, bondWt_symm]

theorem norm_exp_log_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ell : ℕ} (hell : 0 < ell) (v : V) :
    ‖Real.exp (Real.log ell) • v‖ = (ell : ℝ) * ‖v‖ := by
  rw [Real.exp_log (by exact_mod_cast hell), norm_smul, Real.norm_eq_abs, abs_of_pos (by exact_mod_cast hell)]

/-! ## 1. the instances -/

section inst
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} {W : ℕ}

/-- the S1 constant and smallness package -/
structure HatPack (U : Cfg Lf) (a : ℝ) (cs : ℝ) : Prop where
  ha : 0 < a
  hu : IsUnit (LP (geomOf ell k S) U a)
  hcs : 0 < cs
  hcs1 : cs ≤ 1
  hS1 : ∀ f, cs * wNormSq (geomOf ell k S) f ≤ ⟪f, DelpA (geomOf ell k S) U a f⟫
  hsm : 24 * ((Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2
          + 1 * (Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1)) ^ 2) ≤ cs
  hsmD : 4 * (Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2 ≤ cs

variable (hS : Admissible ell M R k S) (hW : 1 ≤ W) (hell : 2 ≤ ell) (hR : 1 ≤ R) (hM : 1 ≤ M) (hWR : W ≤ R * M * ell)
include hS hW hell hR hM hWR

/-- `ψ ≤ σ ≤ ψ + ln ℓ` (`σ = stratG · ln ℓ`). -/
theorem sig_psi (x : PeriodicLatticeSite Lf) :
    psiW S W ell k x ≤ sigG (geomOf ell k S) x ∧ sigG (geomOf ell k S) x ≤ psiW S W ell k x + Real.log ell := by
  have h := psiW_bounds hS hW (show 1 ≤ ell by omega) hWR x
  have hg := strat_eq_stratG (show 0 < ell by omega) hS x
  unfold sigG
  show psiW S W ell k x ≤ (stratG (geomOf ell k S) x : ℝ) * Real.log ell ∧
    (stratG (geomOf ell k S) x : ℝ) * Real.log ell ≤ psiW S W ell k x + Real.log ell
  rw [← hg]
  constructor
  · exact h.2.1
  · linarith [h.2.2]


theorem hw_of (a : ℝ) (ha : 0 < a) : ∀ j, 0 ≤ wq (geomOf ell k S) a j :=
  fun j => (wq_pos hell (properTower_geomOf (show 0 < ell by omega) hS) a j ha).le

theorem dD_nonneg : 0 ≤ Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) := by
  have := theta_nonneg hS hW hell hR hM hWR
  have : 0 ≤ Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1 := by linarith [Real.add_one_le_exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W)]
  positivity

theorem dQ_nonneg (a : ℝ) : 0 ≤ Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1) := by
  have := delta0_nonneg hS hW hell hR hM hWR
  have : 0 ≤ Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1 := by linarith [Real.add_one_le_exp (3 * (ell : ℝ) * Real.log ell / W)]
  positivity

/-- the instance at `e^{+ψ}` -/
noncomputable def psiHypP (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs) :
    SiteHyp (SiteL2 Lf) (BondFnL2 Lf) (YP (geomOf ell k S)) :=
  hatSiteHyp (geomOf ell k S) U a (hw_of hS hW hell hR hM hWR a hp.ha) hp.hu (psiW S W ell k) cs
    (Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1))
    (Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1)) hp.hcs
    (dD_nonneg hS hW hell hR hM hWR) (dQ_nonneg hS hW hell hR hM hWR a)
    (hatCoer (properTower_geomOf (show 0 < ell by omega) hS) (show 0 < ell by omega) U a cs hp.hcs1 hp.hS1)
    (psi_hD hS hW hell hR hM hWR U).1 (psi_hD hS hW hell hR hM hWR U).2
    (psi_hQ hS hW hell hR hM hWR U a hp.ha).1 (psi_hQ hS hW hell hR hM hWR U a hp.ha).2 hp.hsm hp.hsmD

theorem cjp_neg_site_bond (φ : PeriodicLatticeSite Lf → ℝ) (T : SiteL2 Lf →L[ℝ] BondFnL2 Lf) :
    cjp (siteWP (-φ)) (bondWP (-φ)) T = cjm (siteWP φ) (bondWP φ) T := (cjm_site_bond φ T).symm

theorem cjm_neg_site_bond (φ : PeriodicLatticeSite Lf → ℝ) (T : SiteL2 Lf →L[ℝ] BondFnL2 Lf) :
    cjm (siteWP (-φ)) (bondWP (-φ)) T = cjp (siteWP φ) (bondWP φ) T := by
  rw [cjm_site_bond, neg_neg]

theorem cjp_neg_site_yp (φ : PeriodicLatticeSite Lf → ℝ) (T : SiteL2 Lf →L[ℝ] YP (geomOf ell k S)) :
    cjp (siteWP (-φ)) (ypWP (geomOf ell k S) (-φ)) T = cjm (siteWP φ) (ypWP (geomOf ell k S) φ) T :=
  (cjm_site_yp (geomOf ell k S) φ T).symm

theorem cjm_neg_site_yp (φ : PeriodicLatticeSite Lf → ℝ) (T : SiteL2 Lf →L[ℝ] YP (geomOf ell k S)) :
    cjm (siteWP (-φ)) (ypWP (geomOf ell k S) (-φ)) T = cjp (siteWP φ) (ypWP (geomOf ell k S) φ) T := by
  rw [cjm_site_yp, neg_neg]

/-- the instance at `e^{−ψ}` -/
noncomputable def psiHypN (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs) :
    SiteHyp (SiteL2 Lf) (BondFnL2 Lf) (YP (geomOf ell k S)) :=
  hatSiteHyp (geomOf ell k S) U a (hw_of hS hW hell hR hM hWR a hp.ha) hp.hu (-psiW S W ell k) cs
    (Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1))
    (Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1)) hp.hcs
    (dD_nonneg hS hW hell hR hM hWR) (dQ_nonneg hS hW hell hR hM hWR a)
    (hatCoer (properTower_geomOf (show 0 < ell by omega) hS) (show 0 < ell by omega) U a cs hp.hcs1 hp.hS1)
    (by rw [cjp_neg_site_bond hS hW hell hR hM hWR]; exact (psi_hD hS hW hell hR hM hWR U).2)
    (by rw [cjm_neg_site_bond hS hW hell hR hM hWR]; exact (psi_hD hS hW hell hR hM hWR U).1)
    (by rw [cjp_neg_site_yp hS hW hell hR hM hWR]; exact (psi_hQ hS hW hell hR hM hWR U a hp.ha).2)
    (by rw [cjm_neg_site_yp hS hW hell hR hM hWR]; exact (psi_hQ hS hW hell hR hM hWR U a hp.ha).1) hp.hsm hp.hsmD

/-! ## 2. bounds on the genuine `G' = LinvP` -/

theorem LinvP_eq (U : Cfg Lf) (a : ℝ) (y : SiteL2 Lf) :
    LinvP (geomOf ell k S) U a y
      = siteWt (sigG (geomOf ell k S)) (Linvh (geomOf ell k S) U a (siteWt (sigG (geomOf ell k S)) y)) := by
  simp only [Linvh, ContinuousLinearMap.comp_apply]
  rw [siteWt_cancel_neg, siteWt_neg_cancel]

/-- `e^{σ} ≤ ℓ e^{ψ}` as norms -/
theorem sig_le_psi_norm (f : SiteL2 Lf) :
    ‖siteWt (sigG (geomOf ell k S)) f‖ ≤ (ell : ℝ) * ‖siteWt (psiW S W ell k) f‖ := by
  have h := siteWt_le_of (sigG (geomOf ell k S)) (fun x => psiW S W ell k x + Real.log ell)
    (fun x => (sig_psi hS hW hell hR hM hWR x).2) f
  rw [siteWt_add_const, norm_exp_log_smul (show 0 < ell by omega)] at h
  exact h

theorem bsig_le_psi_norm (f : BondFnL2 Lf) :
    ‖bondWt (sigG (geomOf ell k S)) f‖ ≤ (ell : ℝ) * ‖bondWt (psiW S W ell k) f‖ := by
  have h := bondWt_le_of (sigG (geomOf ell k S)) (fun x => psiW S W ell k x + Real.log ell)
    (fun x => (sig_psi hS hW hell hR hM hWR x).2) f
  rw [bondWt_add_const, norm_exp_log_smul (show 0 < ell by omega)] at h
  exact h

theorem cjp_Linv_apply (H : SiteHyp (SiteL2 Lf) (BondFnL2 Lf) (YP (geomOf ell k S))) (φ : PeriodicLatticeSite Lf → ℝ)
    (hωS : H.ωS = siteWP φ) (w : SiteL2 Lf) :
    siteWt φ (H.Linv w) = cjp H.ωS H.ωS H.Linv (siteWt φ w) := by
  rw [cjp_apply, hωS]
  show siteWt φ (H.Linv w) = siteWt φ (H.Linv (siteWt (-φ) (siteWt φ w)))
  rw [siteWt_cancel_neg]

/-- **g1** -/
theorem g1 (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs) (y : SiteL2 Lf) :
    ‖LinvP (geomOf ell k S) U a y‖
      ≤ (4 * ell / cs) * ‖siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S)) y‖ := by
  set H := psiHypP hS hW hell hR hM hWR U a cs hp
  set σ := sigG (geomOf ell k S)
  set ψ := psiW S W ell k
  rw [LinvP_eq hS hW hell hR hM hWR]
  refine (sig_le_psi_norm hS hW hell hR hM hWR _).trans ?_
  have e : siteWt ψ (Linvh (geomOf ell k S) U a (siteWt σ y)) = cjp H.ωS H.ωS H.Linv (siteWt ψ (siteWt σ y)) :=
    cjp_Linv_apply hS hW hell hR hM hWR H ψ rfl _
  rw [e]
  have h1 := H.cjpLinv_le (siteWt ψ (siteWt σ y))
  have hc : H.c = cs := rfl
  rw [hc] at h1
  have h2 : ‖siteWt ψ (siteWt σ y)‖ ≤ ‖siteWt (σ + σ) y‖ := by
    rw [siteWt_mul]
    exact siteWt_le_of _ _ (fun x => by simp only [Pi.add_apply]; linarith [(sig_psi hS hW hell hR hM hWR x).1]) y
  have hell0 : (0 : ℝ) ≤ ell := by positivity
  have hcs := hp.hcs
  calc (ell : ℝ) * ‖cjp H.ωS H.ωS H.Linv (siteWt ψ (siteWt σ y))‖
      ≤ (ell : ℝ) * ((4 / cs) * ‖siteWt ψ (siteWt σ y)‖) := mul_le_mul_of_nonneg_left h1 hell0
    _ ≤ (ell : ℝ) * ((4 / cs) * ‖siteWt (σ + σ) y‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) hell0
    _ = (4 * ell / cs) * ‖siteWt (σ + σ) y‖ := by ring

/-- **g1'** -/
theorem g1' (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs) (y : SiteL2 Lf) :
    ‖siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S))) (LinvP (geomOf ell k S) U a y)‖
      ≤ (4 * ell / cs) * ‖y‖ := by
  set H := psiHypN hS hW hell hR hM hWR U a cs hp
  set σ := sigG (geomOf ell k S)
  set ψ := psiW S W ell k
  rw [LinvP_eq hS hW hell hR hM hWR, siteWt_mul]
  have e0 : (-(σ + σ)) + σ = -σ := by ring
  rw [e0]
  refine (siteWt_le_of (-σ) (-ψ) (fun x => by simp only [Pi.neg_apply]; linarith [(sig_psi hS hW hell hR hM hWR x).1]) _).trans ?_
  have e : siteWt (-ψ) (Linvh (geomOf ell k S) U a (siteWt σ y)) = cjp H.ωS H.ωS H.Linv (siteWt (-ψ) (siteWt σ y)) :=
    cjp_Linv_apply hS hW hell hR hM hWR H (-ψ) rfl _
  rw [e]
  have h1 := H.cjpLinv_le (siteWt (-ψ) (siteWt σ y))
  have hc : H.c = cs := rfl
  rw [hc] at h1
  have h2 : ‖siteWt (-ψ) (siteWt σ y)‖ ≤ (ell : ℝ) * ‖y‖ := by
    rw [siteWt_mul]
    have := siteWt_le_of ((-ψ) + σ) (fun x => (fun _ => (0 : ℝ)) x + Real.log ell)
      (fun x => by simp only [Pi.add_apply, Pi.neg_apply]; linarith [(sig_psi hS hW hell hR hM hWR x).2]) y
    rw [siteWt_add_const, norm_exp_log_smul (show 0 < ell by omega)] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    have : siteWt (fun _ => (0 : ℝ)) y = y := by
      refine PiLp.ext (fun x => ?_); rw [siteWt_apply]; simp
    rw [this]
  have hcs := hp.hcs
  calc ‖cjp H.ωS H.ωS H.Linv (siteWt (-ψ) (siteWt σ y))‖ ≤ (4 / cs) * ‖siteWt (-ψ) (siteWt σ y)‖ := h1
    _ ≤ (4 / cs) * ((ell : ℝ) * ‖y‖) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (4 * ell / cs) * ‖y‖ := by ring

theorem Dh_adjoint (U : Cfg Lf) :
    ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U)
      = siteWt (sigG (geomOf ell k S)) ∘L ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) := by
  unfold Dh
  rw [ContinuousLinearMap.adjoint_comp, siteWt_adjoint]

/-- **g2** -/
theorem g2 (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs) (w : BondFnL2 Lf) :
    ‖LinvP (geomOf ell k S) U a (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) w)‖
      ≤ (ell : ℝ) * Real.sqrt (48 / cs) * ‖bondWt (sigG (geomOf ell k S)) w‖ := by
  set H := psiHypP hS hW hell hR hM hWR U a cs hp
  set σ := sigG (geomOf ell k S)
  set ψ := psiW S W ell k
  rw [LinvP_eq hS hW hell hR hM hWR]
  refine (sig_le_psi_norm hS hW hell hR hM hWR _).trans ?_
  have eD : siteWt σ (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) w)
      = ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) w := by
    rw [Dh_adjoint hS hW hell hR hM hWR]; rfl
  rw [eD]
  -- LinvDadj_cjp at v = bondWt ψ w
  have hL := (H.LinvDadj_cjp (bondWt ψ w)).1
  have e2 : cjp H.ωS H.ωS H.Linv (ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D) (bondWt ψ w))
      = siteWt ψ (Linvh (geomOf ell k S) U a (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) w)) := by
    have ecjm : cjm H.ωS H.ωE H.D = bondWt (-ψ) ∘L Dh (geomOf ell k S) U ∘L siteWt ψ := rfl
    rw [ecjm, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, siteWt_adjoint, bondWt_adjoint]
    rw [cjp_apply]
    show siteWt ψ (Linvh (geomOf ell k S) U a (siteWt (-ψ) (siteWt ψ (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U)
      (bondWt (-ψ) (bondWt ψ w)))))) = _
    rw [siteWt_cancel_neg, bondWt_cancel_neg]
  rw [e2] at hL
  have hc : H.c = cs := rfl
  rw [hc] at hL
  have hcs := hp.hcs
  have h3 : ‖siteWt ψ (Linvh (geomOf ell k S) U a (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) w))‖
      ≤ Real.sqrt (48 / cs) * ‖bondWt ψ w‖ := by
    have hr : 0 ≤ Real.sqrt (48 / cs) * ‖bondWt ψ w‖ := by positivity
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hr, mul_pow, Real.sq_sqrt (by positivity)]
    exact Real.sqrt_le_sqrt hL
  have h4 : ‖bondWt ψ w‖ ≤ ‖bondWt σ w‖ :=
    bondWt_le_of ψ σ (fun x => (sig_psi hS hW hell hR hM hWR x).1) w
  have hell0 : (0 : ℝ) ≤ ell := by positivity
  calc (ell : ℝ) * ‖siteWt ψ (Linvh (geomOf ell k S) U a (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) w))‖
      ≤ (ell : ℝ) * (Real.sqrt (48 / cs) * ‖bondWt ψ w‖) := mul_le_mul_of_nonneg_left h3 hell0
    _ ≤ (ell : ℝ) * (Real.sqrt (48 / cs) * ‖bondWt σ w‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)) hell0
    _ = _ := by ring

theorem DmLinvP_eq (U : Cfg Lf) (a : ℝ) (y : SiteL2 Lf) :
    Dm (geomOf ell k S) U (LinvP (geomOf ell k S) U a y)
      = Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a (siteWt (sigG (geomOf ell k S)) y)) := by
  rw [LinvP_eq hS hW hell hR hM hWR]; rfl

/-- the weighted gradient of a conjugated resolvent, generic over the instance. -/
theorem wD_bound (H : SiteHyp (SiteL2 Lf) (BondFnL2 Lf) (YP (geomOf ell k S))) (U : Cfg Lf) (a : ℝ)
    (φ : PeriodicLatticeSite Lf → ℝ)
    (hωS : H.ωS = siteWP φ) (hωE : H.ωE = bondWP φ) (hD : H.D = Dh (geomOf ell k S) U)
    (hLinv : H.Linv = Linvh (geomOf ell k S) U a) (w : SiteL2 Lf) :
    ‖bondWt φ (Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a w))‖
      ≤ (Real.sqrt (12 / H.c) + H.δD * (4 / H.c)) * ‖siteWt φ w‖ := by
  set h := cjp H.ωS H.ωS H.Linv (siteWt φ w) with hh
  have e1 : h = siteWt φ (Linvh (geomOf ell k S) U a w) := by
    rw [hh, cjp_apply, hωS, hLinv]
    show siteWt φ (Linvh (geomOf ell k S) U a (siteWt (-φ) (siteWt φ w))) = _
    rw [siteWt_cancel_neg]
  have e2 : bondWt φ (Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a w)) = cjp H.ωS H.ωE H.D h := by
    rw [cjp_apply, hωS, hωE, hD, e1]
    show _ = bondWt φ (Dh (geomOf ell k S) U (siteWt (-φ) (siteWt φ (Linvh (geomOf ell k S) U a w))))
    rw [siteWt_cancel_neg]
  rw [e2]
  have h1 : ‖cjp H.ωS H.ωE H.D h‖ ≤ ‖H.D h‖ + ‖(cjp H.ωS H.ωE H.D - H.D) h‖ := by
    have : cjp H.ωS H.ωE H.D h = H.D h + (cjp H.ωS H.ωE H.D - H.D) h := by
      rw [ContinuousLinearMap.sub_apply]; abel
    rw [this]; exact norm_add_le _ _
  have h2 : ‖H.D h‖ ≤ Real.sqrt (12 / H.c) * ‖siteWt φ w‖ := H.D_cjpLinv_le _
  have h3 : ‖(cjp H.ωS H.ωE H.D - H.D) h‖ ≤ H.δD * ‖h‖ :=
    ((cjp H.ωS H.ωE H.D - H.D).le_opNorm h).trans (mul_le_mul_of_nonneg_right H.hDp (norm_nonneg _))
  have h4 : ‖h‖ ≤ (4 / H.c) * ‖siteWt φ w‖ := H.cjpLinv_le _
  have h5 : H.δD * ‖h‖ ≤ H.δD * ((4 / H.c) * ‖siteWt φ w‖) := mul_le_mul_of_nonneg_left h4 H.hδD
  nlinarith

/-- **g3** -/
theorem g3 (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs) (y : SiteL2 Lf) :
    ‖bondWt (sigG (geomOf ell k S)) (Dm (geomOf ell k S) U (LinvP (geomOf ell k S) U a y))‖
      ≤ (ell : ℝ) * (Real.sqrt (12 / cs)
          + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))
        * ‖siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S)) y‖ := by
  set H := psiHypP hS hW hell hR hM hWR U a cs hp
  set σ := sigG (geomOf ell k S)
  set ψ := psiW S W ell k
  rw [DmLinvP_eq hS hW hell hR hM hWR]
  refine (bsig_le_psi_norm hS hW hell hR hM hWR _).trans ?_
  have h := wD_bound hS hW hell hR hM hWR H U a ψ rfl rfl rfl rfl (siteWt σ y)
  have hc : H.c = cs := rfl
  have hd : H.δD = Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) := rfl
  rw [hc, hd] at h
  have h2 : ‖siteWt ψ (siteWt σ y)‖ ≤ ‖siteWt (σ + σ) y‖ := by
    rw [siteWt_mul]
    exact siteWt_le_of _ _ (fun x => by simp only [Pi.add_apply]; linarith [(sig_psi hS hW hell hR hM hWR x).1]) y
  have hK : 0 ≤ Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs) := by
    have := dD_nonneg hS hW hell hR hM hWR; have := hp.hcs; positivity
  have hell0 : (0 : ℝ) ≤ ell := by positivity
  calc (ell : ℝ) * ‖bondWt ψ (Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a (siteWt σ y)))‖
      ≤ (ell : ℝ) * ((Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))
          * ‖siteWt ψ (siteWt σ y)‖) := mul_le_mul_of_nonneg_left h hell0
    _ ≤ (ell : ℝ) * ((Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))
          * ‖siteWt (σ + σ) y‖) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hK) hell0
    _ = _ := by ring

/-- **g5** -/
theorem g5 (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs) (y : SiteL2 Lf) :
    ‖bondWt (-sigG (geomOf ell k S)) (Dm (geomOf ell k S) U (LinvP (geomOf ell k S) U a y))‖
      ≤ (ell : ℝ) * (Real.sqrt (12 / cs)
          + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs)) * ‖y‖ := by
  set H := psiHypN hS hW hell hR hM hWR U a cs hp
  set σ := sigG (geomOf ell k S)
  set ψ := psiW S W ell k
  rw [DmLinvP_eq hS hW hell hR hM hWR]
  refine (bondWt_le_of (-σ) (-ψ) (fun x => by simp only [Pi.neg_apply]; linarith [(sig_psi hS hW hell hR hM hWR x).1]) _).trans ?_
  have h := wD_bound hS hW hell hR hM hWR H U a (-ψ) rfl rfl rfl rfl (siteWt σ y)
  have hc : H.c = cs := rfl
  have hd : H.δD = Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) := rfl
  rw [hc, hd] at h
  have h2 : ‖siteWt (-ψ) (siteWt σ y)‖ ≤ (ell : ℝ) * ‖y‖ := by
    rw [siteWt_mul]
    have := siteWt_le_of ((-ψ) + σ) (fun x => (fun _ => (0 : ℝ)) x + Real.log ell)
      (fun x => by simp only [Pi.add_apply, Pi.neg_apply]; linarith [(sig_psi hS hW hell hR hM hWR x).2]) y
    rw [siteWt_add_const, norm_exp_log_smul (show 0 < ell by omega)] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    have : siteWt (fun _ => (0 : ℝ)) y = y := by
      refine PiLp.ext (fun x => ?_); rw [siteWt_apply]; simp
    rw [this]
  have hK : 0 ≤ Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs) := by
    have := dD_nonneg hS hW hell hR hM hWR; have := hp.hcs; positivity
  calc ‖bondWt (-ψ) (Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a (siteWt σ y)))‖
      ≤ (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))
          * ‖siteWt (-ψ) (siteWt σ y)‖ := h
    _ ≤ (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))
          * ((ell : ℝ) * ‖y‖) := mul_le_mul_of_nonneg_left h2 hK
    _ = _ := by ring

end inst

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.siteWt_le_of
#print axioms AdalyFormal.M1IMS.bondWt_le_of
#print axioms AdalyFormal.M1IMS.siteWt_add_const
#print axioms AdalyFormal.M1IMS.bondWt_add_const
#print axioms AdalyFormal.M1IMS.siteWt_mul
#print axioms AdalyFormal.M1IMS.bondWt_adjoint
#print axioms AdalyFormal.M1IMS.norm_exp_log_smul
#print axioms AdalyFormal.M1IMS.sig_psi
#print axioms AdalyFormal.M1IMS.hw_of
#print axioms AdalyFormal.M1IMS.dD_nonneg
#print axioms AdalyFormal.M1IMS.dQ_nonneg
#print axioms AdalyFormal.M1IMS.cjp_neg_site_bond
#print axioms AdalyFormal.M1IMS.cjm_neg_site_bond
#print axioms AdalyFormal.M1IMS.cjp_neg_site_yp
#print axioms AdalyFormal.M1IMS.cjm_neg_site_yp
#print axioms AdalyFormal.M1IMS.LinvP_eq
#print axioms AdalyFormal.M1IMS.sig_le_psi_norm
#print axioms AdalyFormal.M1IMS.bsig_le_psi_norm
#print axioms AdalyFormal.M1IMS.cjp_Linv_apply
#print axioms AdalyFormal.M1IMS.g1
#print axioms AdalyFormal.M1IMS.g1'
#print axioms AdalyFormal.M1IMS.Dh_adjoint
#print axioms AdalyFormal.M1IMS.g2
#print axioms AdalyFormal.M1IMS.DmLinvP_eq
#print axioms AdalyFormal.M1IMS.wD_bound
#print axioms AdalyFormal.M1IMS.g3
#print axioms AdalyFormal.M1IMS.g5
#print axioms AdalyFormal.M1IMS.HatPack
#print axioms AdalyFormal.M1IMS.psiHypP
#print axioms AdalyFormal.M1IMS.psiHypN
