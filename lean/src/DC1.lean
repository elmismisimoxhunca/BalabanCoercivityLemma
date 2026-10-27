import MI33
import DS2

/-!
# DC1 -- the gauge-fixing map `W` is bounded in the stratum-weighted norm (DParts.hW) (M1 D-layer lane, 2026-10-13)

On `G = geomOf ℓ k S` (admissible, `1 ≤ W ≤ R M ℓ`), with lane E's hatted chain (`HatPack U a cs`, the `SiteHyp` instances
`psiHypP`, `psiHypN` at the weights `e^{±ψ}`), a right inverse `Gi` of `Γ = X*X` (`X = Xop = LinvP QpP*`) and the
gauge-invariant row bound `‖ℓ^{strat} u‖ ≤ γ ‖X u‖` (lane E `gamma_sharp` is of this form):
* **`W_wbound`** : `‖e^{-σ} W B‖ ≤ CWc · ‖e^{-σ} B‖` for EVERY bond field `B` (`σ = strat · ln ℓ`, bond weight at the tail);
* **`W_wnormSq`** : `wnormSq (W B) ≤ ℓ² CWc² · wnormSq B` (lane B's `wnormSq`, both-endpoint stratum).
Route (all identities are on the genuine objects): `W B = B − Dm G' T B`, `G' T B = LinvP Dm* B − LinvP X Gi X* Dm* B`
(lane C `Rproj_eq_strat` + the masks), `Dm LinvP = D̂ L̂⁻¹ e^{σ}`, `Dm X = D̂ X̂`, `e^{σ} X = e^{2σ} X̂`; term 1 is the
conjugated `L̂⁻¹ D̂*` sandwich of DL10 at `e^{-ψ}`; term 2 is `D̂ L̂⁻¹` (DL10 at `e^{-ψ}`) ∘ `e^{2σ−ψ} X̂` (DL12 at `e^{+ψ}`,
`2σ − ψ ≤ ψ + 2 ln ℓ`) ∘ `Gi` (`‖e^{τ} Gi w‖ ≤ γ² ‖e^{-τ} w‖`) ∘ `X̂* D̂*` (DL12 at `e^{+ψ}`, by duality).
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
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

/-! ## 0. generic weight helpers -/

section gen
variable {L : PeriodicLatticeExtent}

theorem siteWt_le_shift (φ χ : PeriodicLatticeSite L → ℝ) (c : ℝ) (h : ∀ x, φ x ≤ χ x + c) (f : SiteL2 L) :
    ‖siteWt φ f‖ ≤ Real.exp c * ‖siteWt χ f‖ := by
  have h1 := siteWt_le_of φ (fun x => χ x + c) h f
  rw [siteWt_add_const, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  exact h1

theorem bondWt_le_shift (φ χ : PeriodicLatticeSite L → ℝ) (c : ℝ) (h : ∀ x, φ x ≤ χ x + c) (f : BondFnL2 L) :
    ‖bondWt φ f‖ ≤ Real.exp c * ‖bondWt χ f‖ := by
  have h1 := bondWt_le_of φ (fun x => χ x + c) h f
  rw [bondWt_add_const, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  exact h1

theorem ypWt_mul (G : TowerGeom L) (φ χ : PeriodicLatticeSite L → ℝ) (v : YP G) :
    ypWt G φ (ypWt G χ v) = ypWt G (φ + χ) v := by
  refine PiLp.ext (fun p => ?_)
  rw [ypWt_apply, ypWt_apply, ypWt_apply, smul_smul, ← Real.exp_add, Pi.add_apply]

theorem ypWt_le_shift (G : TowerGeom L) (φ χ : PeriodicLatticeSite L → ℝ) (c : ℝ) (h : ∀ x, φ x ≤ χ x + c) (v : YP G) :
    ‖ypWt G φ v‖ ≤ Real.exp c * ‖ypWt G χ v‖ := by
  have h1 := ypWt_le_of G φ (fun x => χ x + c) h v
  rw [ypWt_add_const, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  exact h1

theorem ypWt_zero_fn (G : TowerGeom L) (v : YP G) : ypWt G (fun _ => (0 : ℝ)) v = v := by
  refine PiLp.ext (fun p => ?_)
  rw [ypWt_apply, Real.exp_zero, one_smul]

theorem Dm_adj (G : TowerGeom L) (U : Cfg L) :
    ContinuousLinearMap.adjoint (Dm G U) = siteMask G.Om0 ∘L gradAdj U := by
  rw [Dm, ContinuousLinearMap.adjoint_comp, siteMask_adjoint]
  rfl

/-- `‖T⁺ v‖ ≤ ‖T v‖ + δ ‖v‖` -/
theorem norm_cj_le {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] (T T' : A →L[ℝ] B) (δ : ℝ) (h : ‖T' - T‖ ≤ δ) (v : A) :
    ‖T' v‖ ≤ ‖T v‖ + δ * ‖v‖ := by
  have e : T' v = T v + (T' - T) v := by rw [ContinuousLinearMap.sub_apply]; abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (SiteHyp.norm_op_le _ _ h v))

/-- `W B = B − Dm(G'(T B))` (lane E MI18 `Wop_eq`, for any geometry) -/
theorem Wop_eq_gen (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hu : IsUnit (LP G U a)) (B : BondFnL2 L) :
    Wop G U a B = B - Dm G U (Gp G U a (Tfull G U B)) := by
  have h1 : Wop G U a B = B - gradL2 U (Gp G U a (Tfull G U B)) := rfl
  have h2 := (Gp_spec G U a hu (Tfull G U B)).1
  rw [h1]
  conv_lhs => rw [← h2]
  rfl

/-- the genuine `G' T`: `Gp (Tfull B) = LinvP Dm* B − LinvP X Gi X* Dm* B` -/
theorem GpT_eq (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 < wq G a j) (hu : IsUnit (LP G U a))
    (Gi : YP G →L[ℝ] YP G)
    (hG1 : ∀ u, (ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a) (Gi u) = u) (B : BondFnL2 L) :
    Gp G U a (Tfull G U B) = LinvP G U a (ContinuousLinearMap.adjoint (Dm G U) B)
      - LinvP G U a (Xop G U a (Gi (ContinuousLinearMap.adjoint (Xop G U a) (ContinuousLinearMap.adjoint (Dm G U) B)))) := by
  rw [Gp_eq, ContinuousLinearMap.comp_apply]
  have e1 : Tfull G U B = Rproj G U (gradAdj U B) := rfl
  rw [e1, Rproj_mask_left, ← Rproj_mask_right]
  have e2 : siteMask G.Om0 (gradAdj U B) = ContinuousLinearMap.adjoint (Dm G U) B := by
    rw [Dm_adj]; rfl
  rw [e2, Rproj_eq_strat G U a hw hu Gi hG1, map_sub]

end gen

#print axioms siteWt_le_shift
#print axioms bondWt_le_shift
#print axioms ypWt_mul
#print axioms ypWt_le_shift
#print axioms ypWt_zero_fn
#print axioms Dm_adj
#print axioms Wop_eq_gen
#print axioms norm_cj_le
#print axioms GpT_eq

/-! ## 1. the hatted pieces -/

section inst
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} {W : ℕ}
variable (hS : Admissible ell M R k S) (hW : 1 ≤ W) (hell : 2 ≤ ell) (hR : 1 ≤ R) (hM : 1 ≤ M) (hWR : W ≤ R * M * ell)
include hS hW hell hR hM hWR

/-- `Dm ∘ X = D̂ ∘ X̂` -/
theorem DmX_eq (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (u : YP (geomOf ell k S)) :
    Dm (geomOf ell k S) U (Xop (geomOf ell k S) U a u)
      = Dh (geomOf ell k S) U ((psiHypP hS hW hell hR hM hWR U a cs hp).X u) := by
  have e1 : Xop (geomOf ell k S) U a u
      = LinvP (geomOf ell k S) U a (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) u) := rfl
  rw [e1, DmLinvP_eq hS hW hell hR hM hWR]
  have e2 : (psiHypP hS hW hell hR hM hWR U a cs hp).X u
      = Linvh (geomOf ell k S) U a (ContinuousLinearMap.adjoint (Qh (geomOf ell k S) U a) u) := rfl
  rw [e2]
  congr 2
  unfold Qh
  rw [ContinuousLinearMap.adjoint_comp, siteWt_adjoint]
  rfl

/-- `X = e^{σ} X̂` -/
theorem Xop_eq_hat (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (u : YP (geomOf ell k S)) :
    Xop (geomOf ell k S) U a u = siteWt (sigG (geomOf ell k S)) ((psiHypP hS hW hell hR hM hWR U a cs hp).X u) := by
  rw [hatX_eq hS hW hell hR hM hWR U a cs hp, siteWt_neg_cancel]

/-- **term 1**: `‖e^{-ψ} D̂ L̂⁻¹ D̂* B‖ ≤ (√24 + δD √(48/c)) ‖e^{-ψ} B‖` -/
theorem term1_bound (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (B : BondFnL2 Lf) :
    ‖bondWt (-psiW S W ell k) (Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a
        (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) B)))‖
      ≤ (Real.sqrt 24 + (psiHypN hS hW hell hR hM hWR U a cs hp).δD
          * Real.sqrt (48 / (psiHypN hS hW hell hR hM hWR U a cs hp).c))
        * ‖bondWt (-psiW S W ell k) B‖ := by
  set H := psiHypN hS hW hell hR hM hWR U a cs hp with hH
  set ψ := psiW S W ell k with hψ
  set v := bondWt (-ψ) B with hv
  have e1 : ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D) v
      = siteWt (-ψ) (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) B) := by
    have ec : cjm H.ωS H.ωE H.D = bondWt (-(-ψ)) ∘L Dh (geomOf ell k S) U ∘L siteWt (-ψ) := rfl
    rw [ec, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, siteWt_adjoint, bondWt_adjoint]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hv, bondWt_cancel_neg]
  have e2 : cjp H.ωS H.ωS H.Linv (siteWt (-ψ) (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) B))
      = siteWt (-ψ) (Linvh (geomOf ell k S) U a (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) B)) := by
    show siteWt (-ψ) (Linvh (geomOf ell k S) U a (siteWt (-(-ψ)) (siteWt (-ψ)
      (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) B)))) = _
    rw [siteWt_cancel_neg]
  have e3 : cjp H.ωS H.ωE H.D (siteWt (-ψ) (Linvh (geomOf ell k S) U a
        (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) B)))
      = bondWt (-ψ) (Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a
          (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) B))) := by
    show bondWt (-ψ) (Dh (geomOf ell k S) U (siteWt (-(-ψ)) (siteWt (-ψ) (Linvh (geomOf ell k S) U a
      (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) B))))) = _
    rw [siteWt_cancel_neg]
  obtain ⟨h1, h2⟩ := H.cjpLinvDadj_le v
  rw [e1, e2] at h1 h2
  have hD : H.D = Dh (geomOf ell k S) U := rfl
  rw [hD] at h2
  rw [← e3]
  have h3 := norm_cj_le (H.D) (cjp H.ωS H.ωE H.D) H.δD H.hDp
    (siteWt (-ψ) (Linvh (geomOf ell k S) U a (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) B)))
  rw [hD] at h3
  have hδ := H.hδD
  calc _ ≤ _ := h3
    _ ≤ Real.sqrt 24 * ‖v‖ + H.δD * (Real.sqrt (48 / H.c) * ‖v‖) :=
        add_le_add h2 (mul_le_mul_of_nonneg_left h1 hδ)
    _ = _ := by ring

/-- the conjugated `X̂` at `e^{+ψ}`: `‖e^{ψ} X̂ u‖ ≤ (4/c)(q + δQ) ‖e^{ψ} u‖` -/
theorem Xhat_psi_bound (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (q : ℝ) (hq : ‖Qh (geomOf ell k S) U a‖ ≤ q) (u : YP (geomOf ell k S)) :
    ‖siteWt (psiW S W ell k) ((psiHypP hS hW hell hR hM hWR U a cs hp).X u)‖
      ≤ (4 / (psiHypP hS hW hell hR hM hWR U a cs hp).c) * ((q + (psiHypP hS hW hell hR hM hWR U a cs hp).δQ)
          * ‖ypWt (geomOf ell k S) (psiW S W ell k) u‖) := by
  set H := psiHypP hS hW hell hR hM hWR U a cs hp with hH
  set ψ := psiW S W ell k with hψ
  have e : siteWt ψ (H.X u) = cjp H.ωY H.ωS H.X (ypWt (geomOf ell k S) ψ u) := by
    show _ = siteWt ψ (H.X (ypWt (geomOf ell k S) (-ψ) (ypWt (geomOf ell k S) ψ u)))
    rw [ypWt_cancel_neg]
  rw [e, SiteHyp.cjpX_eq, ContinuousLinearMap.comp_apply]
  refine (H.cjpLinv_le _).trans (mul_le_mul_of_nonneg_left ?_ (by have := H.hc; positivity))
  refine SiteHyp.norm_adj_sub_le _ _ ?_ _
  have hQ : H.Qp = Qh (geomOf ell k S) U a := rfl
  have := norm_cj_le H.Qp (cjm H.ωS H.ωY H.Qp) H.δQ H.hQm
  calc ‖cjm H.ωS H.ωY H.Qp‖ ≤ ‖H.Qp‖ + H.δQ := by
        refine (ContinuousLinearMap.opNorm_le_bound _ (by have := H.hδQ; positivity) (fun v => ?_))
        refine (this v).trans ?_
        rw [add_mul]
        exact add_le_add_left (H.Qp.le_opNorm v) _
    _ ≤ q + H.δQ := by rw [hQ]; linarith

/-- **term 2, left factor**: `‖e^{-ψ} D̂ L̂⁻¹ e^{2σ} X̂ u‖ ≤ Kw · ℓ² · (4/c)(q+δQ) · ‖e^{σ} u‖` -/
theorem term2_left (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (q : ℝ) (hq : ‖Qh (geomOf ell k S) U a‖ ≤ q) (u : YP (geomOf ell k S)) :
    ‖bondWt (-psiW S W ell k) (Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a
        (siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S)) ((psiHypP hS hW hell hR hM hWR U a cs hp).X u))))‖
      ≤ (Real.sqrt (12 / (psiHypN hS hW hell hR hM hWR U a cs hp).c)
          + (psiHypN hS hW hell hR hM hWR U a cs hp).δD * (4 / (psiHypN hS hW hell hR hM hWR U a cs hp).c))
        * ((ell : ℝ) ^ 2 * ((4 / (psiHypP hS hW hell hR hM hWR U a cs hp).c)
          * ((q + (psiHypP hS hW hell hR hM hWR U a cs hp).δQ)
            * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖))) := by
  set HN := psiHypN hS hW hell hR hM hWR U a cs hp with hHN
  set HP := psiHypP hS hW hell hR hM hWR U a cs hp with hHP
  set ψ := psiW S W ell k with hψ
  set σ := sigG (geomOf ell k S) with hσ
  have h1 := wD_bound hS hW hell hR hM hWR HN U a (-ψ) rfl rfl rfl rfl (siteWt (σ + σ) (HP.X u))
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by have := HN.hc; have := HN.hδD; positivity))
  -- `e^{-ψ + 2σ} ≤ ℓ² e^{ψ}`
  have h2 : ‖siteWt (-ψ) (siteWt (σ + σ) (HP.X u))‖ ≤ (ell : ℝ) ^ 2 * ‖siteWt ψ (HP.X u)‖ := by
    rw [siteWt_mul]
    have hsh := siteWt_le_shift ((-ψ) + (σ + σ)) ψ (2 * Real.log ell)
      (fun x => by
        have := (sig_psi hS hW hell hR hM hWR x).2
        simp only [Pi.add_apply, Pi.neg_apply]; linarith) (HP.X u)
    have he : Real.exp (2 * Real.log ell) = (ell : ℝ) ^ 2 := by
      rw [show 2 * Real.log ell = (2 : ℕ) * Real.log ell by norm_num, Real.exp_nat_mul,
        Real.exp_log (Nat.cast_pos.mpr (by omega))]
    rwa [he] at hsh
  refine h2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine (Xhat_psi_bound hS hW hell hR hM hWR U a cs hp q hq u).trans ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ ?_) (by have := HP.hc; positivity)
  · exact ypWt_le_of _ _ _ (fun x => (sig_psi hS hW hell hR hM hWR x).1) u
  · have := HP.hδQ; have : 0 ≤ q := le_trans (norm_nonneg (Qh (geomOf ell k S) U a)) hq; positivity

/-- **term 2, right factor (duality)**: `‖e^{-σ} X̂* D̂* B‖ ≤ K3 ‖e^{-ψ} B‖` -/
theorem term2_right (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (q : ℝ) (hq : ‖Qh (geomOf ell k S) U a‖ ≤ q) (B : BondFnL2 Lf) :
    ‖ypWt (geomOf ell k S) (-sigG (geomOf ell k S))
        (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U ∘L (psiHypP hS hW hell hR hM hWR U a cs hp).X) B)‖
      ≤ ((Real.sqrt (12 / (psiHypP hS hW hell hR hM hWR U a cs hp).c)
            + (psiHypP hS hW hell hR hM hWR U a cs hp).δD * (4 / (psiHypP hS hW hell hR hM hWR U a cs hp).c))
          * (q + (psiHypP hS hW hell hR hM hWR U a cs hp).δQ))
        * ‖bondWt (-psiW S W ell k) B‖ := by
  set H := psiHypP hS hW hell hR hM hWR U a cs hp with hH
  set ψ := psiW S W ell k with hψ
  set σ := sigG (geomOf ell k S) with hσ
  have hq0 : 0 ≤ q := le_trans (norm_nonneg (Qh (geomOf ell k S) U a)) hq
  have hc := H.hc
  have hδD := H.hδD
  have hδQ := H.hδQ
  have hK : 0 ≤ (Real.sqrt (12 / H.c) + H.δD * (4 / H.c)) * (q + H.δQ) := by positivity
  refine norm_le_of_pair _ _ (mul_nonneg hK (norm_nonneg _)) (fun z => ?_)
  set z' := ypWt (geomOf ell k S) (-σ) z with hz'
  have e1 : ⟪ypWt (geomOf ell k S) (-σ) (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U ∘L H.X) B), z⟫
      = ⟪bondWt (-ψ) B, bondWt ψ (Dh (geomOf ell k S) U (H.X z'))⟫ := by
    rw [ypWt_symm, ContinuousLinearMap.adjoint_inner_left, ← bondWt_symm, bondWt_neg_cancel]
    rfl
  rw [e1]
  refine (real_inner_le_norm _ _).trans ?_
  rw [mul_comm ((Real.sqrt (12 / H.c) + H.δD * (4 / H.c)) * (q + H.δQ)) ‖bondWt (-ψ) B‖, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  -- `e^{ψ} D̂ X̂ z' = D̂⁺ X̂⁺ (e^{ψ} z')`
  set g := ContinuousLinearMap.adjoint (cjm H.ωS H.ωY H.Qp) (ypWt (geomOf ell k S) ψ z') with hg
  have eX : siteWt ψ (H.X z') = cjp H.ωS H.ωS H.Linv g := by
    have : siteWt ψ (H.X z') = cjp H.ωY H.ωS H.X (ypWt (geomOf ell k S) ψ z') := by
      show _ = siteWt ψ (H.X (ypWt (geomOf ell k S) (-ψ) (ypWt (geomOf ell k S) ψ z')))
      rw [ypWt_cancel_neg]
    rw [this, SiteHyp.cjpX_eq]; rfl
  have eD : bondWt ψ (Dh (geomOf ell k S) U (H.X z')) = cjp H.ωS H.ωE H.D (siteWt ψ (H.X z')) := by
    show _ = bondWt ψ (Dh (geomOf ell k S) U (siteWt (-ψ) (siteWt ψ (H.X z'))))
    rw [siteWt_cancel_neg]
  rw [eD, eX]
  have hD : H.D = Dh (geomOf ell k S) U := rfl
  have h3 := norm_cj_le H.D (cjp H.ωS H.ωE H.D) H.δD H.hDp (cjp H.ωS H.ωS H.Linv g)
  have h4 := H.D_cjpLinv_le g
  have h5 := H.cjpLinv_le g
  have hgn : ‖g‖ ≤ (q + H.δQ) * ‖z‖ := by
    have hQ : H.Qp = Qh (geomOf ell k S) U a := rfl
    have hnorm : ‖cjm H.ωS H.ωY H.Qp‖ ≤ q + H.δQ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
      refine (norm_cj_le H.Qp (cjm H.ωS H.ωY H.Qp) H.δQ H.hQm v).trans ?_
      rw [add_mul]
      refine add_le_add_left ((H.Qp.le_opNorm v).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))) _
      rw [hQ]; exact hq
    refine (SiteHyp.norm_adj_sub_le _ _ hnorm _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [hz', ypWt_mul]
    refine (ypWt_le_of (geomOf ell k S) (ψ + -σ) (fun _ => (0 : ℝ))
      (fun x => by have := (sig_psi hS hW hell hR hM hWR x).1; simp only [Pi.add_apply, Pi.neg_apply]; linarith) z).trans ?_
    rw [ypWt_zero_fn (geomOf ell k S)]
  calc ‖cjp H.ωS H.ωE H.D (cjp H.ωS H.ωS H.Linv g)‖
      ≤ ‖H.D (cjp H.ωS H.ωS H.Linv g)‖ + H.δD * ‖cjp H.ωS H.ωS H.Linv g‖ := h3
    _ ≤ Real.sqrt (12 / H.c) * ‖g‖ + H.δD * ((4 / H.c) * ‖g‖) :=
        add_le_add h4 (mul_le_mul_of_nonneg_left h5 hδD)
    _ = (Real.sqrt (12 / H.c) + H.δD * (4 / H.c)) * ‖g‖ := by ring
    _ ≤ (Real.sqrt (12 / H.c) + H.δD * (4 / H.c)) * ((q + H.δQ) * ‖z‖) :=
        mul_le_mul_of_nonneg_left hgn (by positivity)
    _ = _ := by ring

/-- **the row inverse**: `‖e^{τ} Gi w‖ ≤ γ² ‖e^{-τ} w‖` from `‖e^{τ} u‖ ≤ γ ‖X u‖` -/
theorem gami_w (U : Cfg Lf) (a : ℝ) (Gi : YP (geomOf ell k S) →L[ℝ] YP (geomOf ell k S))
    (hG1 : ∀ u, (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) (Gi u) = u)
    (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ : ∀ u, ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ≤ γ * ‖Xop (geomOf ell k S) U a u‖)
    (w : YP (geomOf ell k S)) :
    ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (Gi w)‖
      ≤ γ ^ 2 * ‖ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) w‖ := by
  have hGw := hG1 w
  rw [ContinuousLinearMap.comp_apply] at hGw
  have hX : ‖Xop (geomOf ell k S) U a (Gi w)‖ ^ 2 = ⟪Gi w, w⟫ := by
    rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_right, hGw]
  have hin : ⟪Gi w, w⟫ ≤ ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (Gi w)‖
      * ‖ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) w‖ := by
    have e : ⟪Gi w, w⟫ = ⟪ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (Gi w),
        ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) w⟫ := by
      rw [ypWt_symm, ypWt_neg_cancel]
    rw [e]; exact real_inner_le_norm _ _
  have h1 := hγ (Gi w)
  have h2 : ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (Gi w)‖ ^ 2
      ≤ γ ^ 2 * (‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (Gi w)‖
        * ‖ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) w‖) := by
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, hX] at this
    exact this.trans (mul_le_mul_of_nonneg_left hin (by positivity))
  by_cases h0 : ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (Gi w)‖ = 0
  · rw [h0]; positivity
  have hpos : 0 < ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (Gi w)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have : ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (Gi w)‖ * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (Gi w)‖
      ≤ (γ ^ 2 * ‖ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) w‖)
        * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (Gi w)‖ := by nlinarith
  exact le_of_mul_le_mul_right this hpos

/-- the constant of the weighted `W` bound -/
noncomputable def CWc (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (q γ : ℝ) : ℝ :=
  1 + (ell : ℝ) * ((Real.sqrt 24 + (psiHypN hS hW hell hR hM hWR U a cs hp).δD
          * Real.sqrt (48 / (psiHypN hS hW hell hR hM hWR U a cs hp).c))
      + (Real.sqrt (12 / (psiHypN hS hW hell hR hM hWR U a cs hp).c)
          + (psiHypN hS hW hell hR hM hWR U a cs hp).δD * (4 / (psiHypN hS hW hell hR hM hWR U a cs hp).c))
        * ((ell : ℝ) ^ 2 * ((4 / (psiHypP hS hW hell hR hM hWR U a cs hp).c)
          * ((q + (psiHypP hS hW hell hR hM hWR U a cs hp).δQ)
            * (γ ^ 2 * ((Real.sqrt (12 / (psiHypP hS hW hell hR hM hWR U a cs hp).c)
              + (psiHypP hS hW hell hR hM hWR U a cs hp).δD * (4 / (psiHypP hS hW hell hR hM hWR U a cs hp).c))
              * (q + (psiHypP hS hW hell hR hM hWR U a cs hp).δQ)))))))

/-- the decomposition of `W` in hatted pieces -/
theorem W_decomp (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (Gi : YP (geomOf ell k S) →L[ℝ] YP (geomOf ell k S))
    (hG1 : ∀ u, (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) (Gi u) = u)
    (B : BondFnL2 Lf) :
    Wop (geomOf ell k S) U a B = B - (Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a
        (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) B))
      - Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a (siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S))
          ((psiHypP hS hW hell hR hM hWR U a cs hp).X (Gi (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a)
            (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) B))))))) := by
  have hP := properTower_geomOf (show 0 < ell by omega) hS
  have hw : ∀ j, 0 < wq (geomOf ell k S) a j := fun j => wq_pos hell hP a j hp.ha
  have e1 := Wop_eq_gen (geomOf ell k S) U a hp.hu B
  have e2 := GpT_eq (geomOf ell k S) U a hw hp.hu Gi hG1 B
  have e3 : ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) B
      = siteWt (sigG (geomOf ell k S)) (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) B) := by
    rw [Dh_adjoint hS hW hell hR hM hWR]; rfl
  rw [e1, e2, map_sub, DmLinvP_eq hS hW hell hR hM hWR, DmLinvP_eq hS hW hell hR hM hWR, e3,
    Xop_eq_hat hS hW hell hR hM hWR U a cs hp, siteWt_mul]

theorem adj_DmX (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (B : BondFnL2 Lf) :
    ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) B)
      = ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U ∘L (psiHypP hS hW hell hR hM hWR U a cs hp).X) B := by
  have hc : Dm (geomOf ell k S) U ∘L Xop (geomOf ell k S) U a
      = Dh (geomOf ell k S) U ∘L (psiHypP hS hW hell hR hM hWR U a cs hp).X := by
    ext1 v; exact DmX_eq hS hW hell hR hM hWR U a cs hp v
  rw [← hc, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]

/-- **the weighted bound of the genuine gauge-fixing map** -/
theorem W_wbound (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (Gi : YP (geomOf ell k S) →L[ℝ] YP (geomOf ell k S))
    (hG1 : ∀ u, (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) (Gi u) = u)
    (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ : ∀ u, ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ≤ γ * ‖Xop (geomOf ell k S) U a u‖)
    (B : BondFnL2 Lf) :
    ‖bondWt (-sigG (geomOf ell k S)) (Wop (geomOf ell k S) U a B)‖
      ≤ CWc hS hW hell hR hM hWR U a cs hp (Real.sqrt (max a 1)) γ * ‖bondWt (-sigG (geomOf ell k S)) B‖ := by
  have hq : ‖Qh (geomOf ell k S) U a‖ ≤ Real.sqrt (max a 1) := Qh_opnorm hS hell U a hp.ha
  have hq0 : 0 ≤ Real.sqrt (max a 1) := Real.sqrt_nonneg _
  set HN := psiHypN hS hW hell hR hM hWR U a cs hp with hHN
  set HP := psiHypP hS hW hell hR hM hWR U a cs hp with hHP
  have hcN := HN.hc
  have hcP := HP.hc
  have hδDN := HN.hδD
  have hδDP := HP.hδD
  have hδQP := HP.hδQ
  set K1 := Real.sqrt 24 + HN.δD * Real.sqrt (48 / HN.c) with hK1
  set Kw := Real.sqrt (12 / HN.c) + HN.δD * (4 / HN.c) with hKw
  set nX := (4 / HP.c) * (Real.sqrt (max a 1) + HP.δQ) with hnX
  set K3 := (Real.sqrt (12 / HP.c) + HP.δD * (4 / HP.c)) * (Real.sqrt (max a 1) + HP.δQ) with hK3
  have hK1p : 0 ≤ K1 := add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hδDN (Real.sqrt_nonneg _))
  have hKwp : 0 ≤ Kw := add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hδDN (div_nonneg (by norm_num) hcN.le))
  have hnXp : 0 ≤ nX := mul_nonneg (div_nonneg (by norm_num) hcP.le) (add_nonneg hq0 hδQP)
  have hK3p : 0 ≤ K3 := mul_nonneg (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hδDP (div_nonneg (by norm_num) hcP.le)))
    (add_nonneg hq0 hδQP)
  have hC : CWc hS hW hell hR hM hWR U a cs hp (Real.sqrt (max a 1)) γ
      = 1 + (ell : ℝ) * (K1 + Kw * ((ell : ℝ) ^ 2 * (nX * (γ ^ 2 * K3)))) := by
    unfold CWc; ring
  rw [hC, W_decomp hS hW hell hR hM hWR U a cs hp Gi hG1 B]
  -- names for the pieces
  obtain ⟨T1, hT1⟩ : ∃ T1, T1 = Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a
      (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) B)) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = Gi (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a)
      (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) B)) := ⟨_, rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ T2, T2 = Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a
      (siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S)) ((psiHypP hS hW hell hR hM hWR U a cs hp).X u))) := ⟨_, rfl⟩
  rw [← hu, ← hT1, ← hT2]
  set nB := ‖bondWt (-sigG (geomOf ell k S)) B‖ with hnB
  set nBψ := ‖bondWt (-psiW S W ell k) B‖ with hnBψ
  have hB0 : 0 ≤ nB := norm_nonneg _
  have hσψ : ∀ y : BondFnL2 Lf, ‖bondWt (-sigG (geomOf ell k S)) y‖ ≤ ‖bondWt (-psiW S W ell k) y‖ := fun y =>
    bondWt_le_of _ _ (fun x => by have := (sig_psi hS hW hell hR hM hWR x).1; simp only [Pi.neg_apply]; linarith) y
  have hψσ : nBψ ≤ (ell : ℝ) * nB := by
    have h := bondWt_le_shift (-psiW S W ell k) (-sigG (geomOf ell k S)) (Real.log ell)
      (fun x => by have := (sig_psi hS hW hell hR hM hWR x).2; simp only [Pi.neg_apply]; linarith) B
    rwa [Real.exp_log (Nat.cast_pos.mpr (by omega))] at h
  have t1 : ‖bondWt (-sigG (geomOf ell k S)) T1‖ ≤ K1 * nBψ := by
    rw [hT1]; exact (hσψ _).trans (term1_bound hS hW hell hR hM hWR U a cs hp B)
  have tg : ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ≤ γ ^ 2 * (K3 * nBψ) := by
    have h1 := gami_w hS hW hell hR hM hWR U a Gi hG1 γ hγ0 hγ
      (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) B))
    rw [← hu, adj_DmX hS hW hell hR hM hWR U a cs hp B] at h1
    have h2 := term2_right hS hW hell hR hM hWR U a cs hp (Real.sqrt (max a 1)) hq B
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg γ))
  have t2 : ‖bondWt (-sigG (geomOf ell k S)) T2‖ ≤ Kw * ((ell : ℝ) ^ 2 * (nX * (γ ^ 2 * (K3 * nBψ)))) := by
    have h1 := term2_left hS hW hell hR hM hWR U a cs hp (Real.sqrt (max a 1)) hq u
    rw [← hT2] at h1
    have e : (4 / HP.c) * ((Real.sqrt (max a 1) + HP.δQ) * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖)
        = nX * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ := by rw [hnX]; ring
    rw [e] at h1
    refine (hσψ _).trans (h1.trans ?_)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left tg hnXp)
      (sq_nonneg _)) hKwp
  have hsplit : ‖bondWt (-sigG (geomOf ell k S)) (B - (T1 - T2))‖
      ≤ nB + ‖bondWt (-sigG (geomOf ell k S)) T1‖ + ‖bondWt (-sigG (geomOf ell k S)) T2‖ := by
    rw [map_sub, map_sub]
    refine (norm_sub_le _ _).trans ?_
    have := norm_sub_le (bondWt (-sigG (geomOf ell k S)) T1) (bondWt (-sigG (geomOf ell k S)) T2)
    linarith
  have hb1 : K1 * nBψ ≤ K1 * ((ell : ℝ) * nB) := mul_le_mul_of_nonneg_left hψσ hK1p
  have hb2 : Kw * ((ell : ℝ) ^ 2 * (nX * (γ ^ 2 * (K3 * nBψ))))
      ≤ Kw * ((ell : ℝ) ^ 2 * (nX * (γ ^ 2 * (K3 * ((ell : ℝ) * nB))))) := by
    have h3 : K3 * nBψ ≤ K3 * ((ell : ℝ) * nB) := mul_le_mul_of_nonneg_left hψσ hK3p
    have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg γ)
    have h5 := mul_le_mul_of_nonneg_left h4 hnXp
    have h6 := mul_le_mul_of_nonneg_left h5 (sq_nonneg (ell : ℝ))
    exact mul_le_mul_of_nonneg_left h6 hKwp
  have efin : nB + K1 * ((ell : ℝ) * nB) + Kw * ((ell : ℝ) ^ 2 * (nX * (γ ^ 2 * (K3 * ((ell : ℝ) * nB)))))
      = (1 + (ell : ℝ) * (K1 + Kw * ((ell : ℝ) ^ 2 * (nX * (γ ^ 2 * K3))))) * nB := by ring
  calc ‖bondWt (-sigG (geomOf ell k S)) (B - (T1 - T2))‖
      ≤ nB + ‖bondWt (-sigG (geomOf ell k S)) T1‖ + ‖bondWt (-sigG (geomOf ell k S)) T2‖ := hsplit
    _ ≤ nB + K1 * ((ell : ℝ) * nB) + Kw * ((ell : ℝ) ^ 2 * (nX * (γ ^ 2 * (K3 * ((ell : ℝ) * nB))))) :=
        add_le_add (add_le_add le_rfl (t1.trans hb1)) (t2.trans hb2)
    _ = _ := efin

/-- `wnormSq ≤ ℓ² ‖e^{-σ} ·‖²` (adjacent strata differ by at most one) -/
theorem wnorm_le_N (B : BondFnL2 Lf) :
    AdalyFormal.M1.wnormSq S ell k B ≤ (ell : ℝ) ^ 2 * ‖bondWt (-sigG (geomOf ell k S)) B‖ ^ 2 := by
  have hell0 : 0 < ell := by omega
  rw [PiLp.norm_sq_eq_of_L2]
  unfold AdalyFormal.M1.wnormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun b _ => ?_)
  rw [bondWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  show _ ≤ (ell : ℝ) ^ 2 * Real.exp (-(sigG (geomOf ell k S) b.1)) ^ 2
  have hexp : Real.exp (-(sigG (geomOf ell k S) b.1)) = ((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1)⁻¹ := by
    rw [Real.exp_neg, exp_sig (geomOf ell k S) hell0, ← strat_eq_stratG hell0 hS]; rfl
  rw [hexp]
  have hadj := (AdalyFormal.M1.strat_adj hS hR hM (by omega) b.1 b.2).2
  have hb : AdalyFormal.M1.strat S k b.1 ≤ AdalyFormal.M1.bstrat S k b + 1 := by
    unfold AdalyFormal.M1.bstrat; omega
  have h1 : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have h2 : (0 : ℝ) < (ell : ℝ) ^ AdalyFormal.M1.bstrat S k b := by positivity
  have h3 : (ell : ℝ) ^ AdalyFormal.M1.strat S k b.1 ≤ (ell : ℝ) ^ (AdalyFormal.M1.bstrat S k b + 1) :=
    pow_le_pow_right₀ h1 hb
  have h4 : (0 : ℝ) < (ell : ℝ) ^ AdalyFormal.M1.strat S k b.1 := by positivity
  rw [pow_succ] at h3
  have h5 : ((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1) ^ 2 ≤ ((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b * ell) ^ 2 :=
    pow_le_pow_left₀ h4.le h3 2
  rw [inv_pow, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc (((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b) ^ 2)⁻¹ * ((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1) ^ 2
      ≤ (((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b) ^ 2)⁻¹ * ((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b * ell) ^ 2 :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = (ell : ℝ) ^ 2 := by field_simp

/-- **`DParts.hW`**: `wnormSq (W B) ≤ ℓ² CWc² · wnormSq B` -/
theorem W_wnormSq (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (Gi : YP (geomOf ell k S) →L[ℝ] YP (geomOf ell k S))
    (hG1 : ∀ u, (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) (Gi u) = u)
    (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ : ∀ u, ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ≤ γ * ‖Xop (geomOf ell k S) U a u‖)
    (B : BondFnL2 Lf) :
    AdalyFormal.M1.wnormSq S ell k (Wop (geomOf ell k S) U a B)
      ≤ ((ell : ℝ) ^ 2 * CWc hS hW hell hR hM hWR U a cs hp (Real.sqrt (max a 1)) γ ^ 2)
        * AdalyFormal.M1.wnormSq S ell k B := by
  have h1 := wnorm_le_N hS hW hell hR hM hWR (Wop (geomOf ell k S) U a B)
  have h2 := W_wbound hS hW hell hR hM hWR U a cs hp Gi hG1 γ hγ0 hγ B
  have h3 := N_le_wnorm hS (show 0 < ell by omega) B
  have h4 : ‖bondWt (-sigG (geomOf ell k S)) (Wop (geomOf ell k S) U a B)‖ ^ 2
      ≤ (CWc hS hW hell hR hM hWR U a cs hp (Real.sqrt (max a 1)) γ * ‖bondWt (-sigG (geomOf ell k S)) B‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  calc _ ≤ (ell : ℝ) ^ 2 * ‖bondWt (-sigG (geomOf ell k S)) (Wop (geomOf ell k S) U a B)‖ ^ 2 := h1
    _ ≤ (ell : ℝ) ^ 2 * (CWc hS hW hell hR hM hWR U a cs hp (Real.sqrt (max a 1)) γ
          * ‖bondWt (-sigG (geomOf ell k S)) B‖) ^ 2 := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = ((ell : ℝ) ^ 2 * CWc hS hW hell hR hM hWR U a cs hp (Real.sqrt (max a 1)) γ ^ 2)
          * ‖bondWt (-sigG (geomOf ell k S)) B‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

end inst

#print axioms DmX_eq
#print axioms Xop_eq_hat
#print axioms term1_bound
#print axioms Xhat_psi_bound
#print axioms term2_left
#print axioms term2_right
#print axioms gami_w
#print axioms CWc
#print axioms W_decomp
#print axioms adj_DmX
#print axioms W_wbound
#print axioms wnorm_le_N
#print axioms W_wnormSq

end AdalyFormal.M1DStrat
