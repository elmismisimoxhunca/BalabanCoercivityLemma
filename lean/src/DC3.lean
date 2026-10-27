import DC1

/-!
# DC3 -- the hatted site chain at an ARBITRARY stratified weight, and its conjugated bounds (M1 D-layer lane, 2026-10-13)

`WtOK φ θ δ₀` : the two hypotheses of lane E's commutator lemmas (MI6 `hatD_comm`, `hatQ_comm`): on every bond whose head lies in
`Ω₀`, `|φ(tail) − φ(head)| ≤ θ/ℓ^{strat(head)}`; on every constraint block, `|φ(y_q) − φ(x)| ≤ δ₀`.  Closed under `−φ` and sums;
lane E's `ψ` satisfies it (`psiOK`).
`wHyp … φ θ δ₀` : lane E's `hatSiteHyp` at the weight `φ` (D̂ = Dm e^{σ}, Q̂ = QpP e^{σ}, L̂⁻¹ = e^{−σ} LinvP e^{−σ}).
Conjugated bounds, for `H = wHyp … χ …` (all constants k-free; `Xh = L̂⁻¹ Q̂*`):
* `g_DLD`  : `‖e^{χ} D̂ L̂⁻¹ D̂* e^{−χ} B‖ ≤ (√24 + δD √(48/c)) ‖B‖`;   `g_LD` : `‖e^{χ} L̂⁻¹ D̂* e^{−χ} B‖ ≤ √(48/c) ‖B‖`;
* `g_DL`   : `‖e^{χ} D̂ L̂⁻¹ e^{−χ} g‖ ≤ (√(12/c) + δD·4/c) ‖g‖`;   `g_L`  : `‖e^{χ} L̂⁻¹ e^{−χ} g‖ ≤ (4/c) ‖g‖`;
* `g_X`    : `‖e^{χ} Xh e^{−χ} u‖ ≤ (4/c)(q+δQ) ‖u‖`;   `g_DX` : `‖e^{χ} D̂ Xh e^{−χ} u‖ ≤ (√(12/c)+δD·4/c)(q+δQ) ‖u‖`;
* `g_Xd`   : `‖e^{χ} Xh e^{−χ} u − Xh u‖ ≤ εX ‖u‖`;  `g_DXd` : `‖e^{χ} D̂ Xh e^{−χ} u − D̂ Xh u‖ ≤ (δD(4/c)(q+δQ) + εDX) ‖u‖`.
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
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

section wt
variable {L : PeriodicLatticeExtent}

/-- the weight conditions of the hatted commutator lemmas -/
def WtOK (G : TowerGeom L) (ell : ℕ) (φ : PeriodicLatticeSite L → ℝ) (θ δ0 : ℝ) : Prop :=
  (∀ b : Bond L, periodicLatticeShift b.1 b.2 ∈ G.Om0 →
      |φ b.1 - φ (periodicLatticeShift b.1 b.2)| ≤ θ / (ell : ℝ) ^ stratG G (periodicLatticeShift b.1 b.2)) ∧
  (∀ q : QIdx G, ∀ x ∈ blockOf (yq q) (ell ^ jq q), |φ (yq q) - φ x| ≤ δ0)

theorem WtOK.neg {G : TowerGeom L} {ell : ℕ} {φ : PeriodicLatticeSite L → ℝ} {θ δ0 : ℝ} (h : WtOK G ell φ θ δ0) :
    WtOK G ell (-φ) θ δ0 := by
  refine ⟨fun b hb => ?_, fun q x hx => ?_⟩
  · have := h.1 b hb
    simp only [Pi.neg_apply]
    rwa [show -φ b.1 - -φ (periodicLatticeShift b.1 b.2) = -(φ b.1 - φ (periodicLatticeShift b.1 b.2)) by ring, abs_neg]
  · have := h.2 q x hx
    simp only [Pi.neg_apply]
    rwa [show -φ (yq q) - -φ x = -(φ (yq q) - φ x) by ring, abs_neg]

theorem WtOK.add {G : TowerGeom L} {ell : ℕ} {φ χ : PeriodicLatticeSite L → ℝ} {θ δ0 θ' δ0' : ℝ}
    (h : WtOK G ell φ θ δ0) (h' : WtOK G ell χ θ' δ0') : WtOK G ell (φ + χ) (θ + θ') (δ0 + δ0') := by
  refine ⟨fun b hb => ?_, fun q x hx => ?_⟩
  · have a := h.1 b hb
    have c := h'.1 b hb
    simp only [Pi.add_apply]
    rw [add_div]
    calc |φ b.1 + χ b.1 - (φ (periodicLatticeShift b.1 b.2) + χ (periodicLatticeShift b.1 b.2))|
        = |(φ b.1 - φ (periodicLatticeShift b.1 b.2)) + (χ b.1 - χ (periodicLatticeShift b.1 b.2))| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add a c)
  · have a := h.2 q x hx
    have c := h'.2 q x hx
    simp only [Pi.add_apply]
    calc |φ (yq q) + χ (yq q) - (φ x + χ x)| = |(φ (yq q) - φ x) + (χ (yq q) - χ x)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add a c)

theorem WtOK.sub {G : TowerGeom L} {ell : ℕ} {φ χ : PeriodicLatticeSite L → ℝ} {θ δ0 θ' δ0' : ℝ}
    (h : WtOK G ell φ θ δ0) (h' : WtOK G ell χ θ' δ0') : WtOK G ell (φ - χ) (θ + θ') (δ0 + δ0') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

/-- the hatted `X̂ = L̂⁻¹ Q̂*` (independent of the weight) -/
noncomputable def Xh (G : TowerGeom L) (U : Cfg L) (a : ℝ) : YP G →L[ℝ] SiteL2 L :=
  Linvh G U a ∘L ContinuousLinearMap.adjoint (Qh G U a)

end wt

#print axioms WtOK
#print axioms WtOK.neg
#print axioms WtOK.add
#print axioms WtOK.sub

section inst
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} {W : ℕ}
variable (hS : Admissible ell M R k S) (hW : 1 ≤ W) (hell : 2 ≤ ell) (hR : 1 ≤ R) (hM : 1 ≤ M) (hWR : W ≤ R * M * ell)
include hS hW hell hR hM hWR

/-- lane E's `ψ` satisfies the weight conditions -/
theorem psiOK : WtOK (geomOf ell k S) ell (psiW S W ell k) (2 * (ell : ℝ) ^ 2 * Real.log ell / W)
    (3 * (ell : ℝ) * Real.log ell / W) :=
  ⟨fun b _ => psi_bond hS hW hell hR hM hWR b, fun q x hx => psi_block hS hW hell hR hM hWR q x hx⟩

/-- the hatted `SiteHyp` at the weight `φ` -/
noncomputable def wHyp (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (φ : PeriodicLatticeSite Lf → ℝ) (θ δ0 : ℝ) (hθ : 0 ≤ θ) (hδ0 : 0 ≤ δ0) (hok : WtOK (geomOf ell k S) ell φ θ δ0)
    (hsm : 24 * ((Real.sqrt 3 * (Real.exp θ - 1)) ^ 2 + 1 * (Real.sqrt a * (Real.exp δ0 - 1)) ^ 2) ≤ cs)
    (hsmD : 4 * (Real.sqrt 3 * (Real.exp θ - 1)) ^ 2 ≤ cs) :
    SiteHyp (SiteL2 Lf) (BondFnL2 Lf) (YP (geomOf ell k S)) :=
  hatSiteHyp (geomOf ell k S) U a (hw_of hS hW hell hR hM hWR a hp.ha) hp.hu φ cs
    (Real.sqrt 3 * (Real.exp θ - 1)) (Real.sqrt a * (Real.exp δ0 - 1)) hp.hcs
    (mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.add_one_le_exp θ]))
    (mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.add_one_le_exp δ0]))
    (hatCoer (properTower_geomOf (show 0 < ell by omega) hS) (show 0 < ell by omega) U a cs hp.hcs1 hp.hS1)
    (opnorm_le_of _ _ (mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.add_one_le_exp θ]))
      (fun f => hatD_comm (properTower_geomOf (show 0 < ell by omega) hS) (show 0 < ell by omega) U φ θ hθ hok.1 f))
    (by
      rw [cjm_site_bond]
      exact opnorm_le_of _ _ (mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.add_one_le_exp θ]))
        (fun f => hatD_comm (properTower_geomOf (show 0 < ell by omega) hS) (show 0 < ell by omega) U (-φ) θ hθ
          hok.neg.1 f))
    (opnorm_le_of _ _ (mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.add_one_le_exp δ0]))
      (fun f => hatQ_comm (properTower_geomOf (show 0 < ell by omega) hS) hell U a hp.ha φ δ0 hδ0 hok.2 f))
    (by
      rw [cjm_site_yp]
      exact opnorm_le_of _ _ (mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.add_one_le_exp δ0]))
        (fun f => hatQ_comm (properTower_geomOf (show 0 < ell by omega) hS) hell U a hp.ha (-φ) δ0 hδ0 hok.neg.2 f))
    hsm hsmD

variable (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
  (φ : PeriodicLatticeSite Lf → ℝ) (θ δ0 : ℝ) (hθ : 0 ≤ θ) (hδ0 : 0 ≤ δ0) (hok : WtOK (geomOf ell k S) ell φ θ δ0)
  (hsm : 24 * ((Real.sqrt 3 * (Real.exp θ - 1)) ^ 2 + 1 * (Real.sqrt a * (Real.exp δ0 - 1)) ^ 2) ≤ cs)
  (hsmD : 4 * (Real.sqrt 3 * (Real.exp θ - 1)) ^ 2 ≤ cs)

theorem wHyp_X : (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).X
    = Xh (geomOf ell k S) U a := rfl

/-- `‖e^{χ} D̂ L̂⁻¹ D̂* e^{−χ} B‖ ≤ (√24 + δD √(48/c)) ‖B‖` -/
theorem g_DLD (B : BondFnL2 Lf) :
    ‖bondWt φ (Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a
        (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) (bondWt (-φ) B))))‖
      ≤ (Real.sqrt 24 + (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).δD
          * Real.sqrt (48 / (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).c)) * ‖B‖ := by
  set H := wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD with hH
  have e1 : ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D) B
      = siteWt φ (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) (bondWt (-φ) B)) := by
    have ec : cjm H.ωS H.ωE H.D = bondWt (-φ) ∘L Dh (geomOf ell k S) U ∘L siteWt φ := rfl
    rw [ec, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, siteWt_adjoint, bondWt_adjoint]
    rfl
  have e2 : cjp H.ωS H.ωS H.Linv (siteWt φ (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) (bondWt (-φ) B)))
      = siteWt φ (Linvh (geomOf ell k S) U a (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) (bondWt (-φ) B))) := by
    show siteWt φ (Linvh (geomOf ell k S) U a (siteWt (-φ) (siteWt φ
      (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) (bondWt (-φ) B))))) = _
    rw [siteWt_cancel_neg]
  have e3 : cjp H.ωS H.ωE H.D (siteWt φ (Linvh (geomOf ell k S) U a
        (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) (bondWt (-φ) B))))
      = bondWt φ (Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a
          (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) (bondWt (-φ) B)))) := by
    show bondWt φ (Dh (geomOf ell k S) U (siteWt (-φ) (siteWt φ (Linvh (geomOf ell k S) U a
      (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) (bondWt (-φ) B)))))) = _
    rw [siteWt_cancel_neg]
  obtain ⟨h1, h2⟩ := H.cjpLinvDadj_le B
  rw [e1, e2] at h1 h2
  rw [← e3]
  have h3 := norm_cj_le H.D (cjp H.ωS H.ωE H.D) H.δD H.hDp
    (siteWt φ (Linvh (geomOf ell k S) U a (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) (bondWt (-φ) B))))
  have hδ := H.hδD
  calc _ ≤ _ := h3
    _ ≤ Real.sqrt 24 * ‖B‖ + H.δD * (Real.sqrt (48 / H.c) * ‖B‖) := add_le_add h2 (mul_le_mul_of_nonneg_left h1 hδ)
    _ = _ := by ring

/-- `‖e^{χ} L̂⁻¹ D̂* e^{−χ} B‖ ≤ √(48/c) ‖B‖` -/
theorem g_LD (B : BondFnL2 Lf) :
    ‖siteWt φ (Linvh (geomOf ell k S) U a (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) (bondWt (-φ) B)))‖
      ≤ Real.sqrt (48 / (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).c) * ‖B‖ := by
  set H := wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD with hH
  have e1 : ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D) B
      = siteWt φ (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) (bondWt (-φ) B)) := by
    have ec : cjm H.ωS H.ωE H.D = bondWt (-φ) ∘L Dh (geomOf ell k S) U ∘L siteWt φ := rfl
    rw [ec, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, siteWt_adjoint, bondWt_adjoint]
    rfl
  have e2 : cjp H.ωS H.ωS H.Linv (siteWt φ (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) (bondWt (-φ) B)))
      = siteWt φ (Linvh (geomOf ell k S) U a (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) (bondWt (-φ) B))) := by
    show siteWt φ (Linvh (geomOf ell k S) U a (siteWt (-φ) (siteWt φ
      (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) U) (bondWt (-φ) B))))) = _
    rw [siteWt_cancel_neg]
  have h1 := (H.cjpLinvDadj_le B).1
  rw [e1, e2] at h1
  exact h1

/-- `‖e^{χ} D̂ L̂⁻¹ e^{−χ} g‖ ≤ (√(12/c) + δD·4/c) ‖g‖` -/
theorem g_DL (g : SiteL2 Lf) :
    ‖bondWt φ (Dh (geomOf ell k S) U (Linvh (geomOf ell k S) U a (siteWt (-φ) g)))‖
      ≤ (Real.sqrt (12 / (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).c)
          + (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).δD
            * (4 / (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).c)) * ‖g‖ := by
  set H := wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD with hH
  have h := wD_bound hS hW hell hR hM hWR H U a φ rfl rfl rfl rfl (siteWt (-φ) g)
  rwa [siteWt_neg_cancel] at h

/-- `‖e^{χ} L̂⁻¹ e^{−χ} g‖ ≤ (4/c) ‖g‖` -/
theorem g_L (g : SiteL2 Lf) :
    ‖siteWt φ (Linvh (geomOf ell k S) U a (siteWt (-φ) g))‖
      ≤ (4 / (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).c) * ‖g‖ := by
  set H := wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD with hH
  exact H.cjpLinv_le g

/-- the conjugated row adjoint: `‖(Q̂⁻)*‖ ≤ q + δQ` -/
theorem g_Qadj (q : ℝ) (hq : ‖Qh (geomOf ell k S) U a‖ ≤ q) :
    ‖cjm (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).ωS
        (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).ωY
        (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).Qp‖
      ≤ q + (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).δQ := by
  set H := wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD with hH
  have hQ : H.Qp = Qh (geomOf ell k S) U a := rfl
  have hq0 : 0 ≤ q := le_trans (norm_nonneg (Qh (geomOf ell k S) U a)) hq
  have hδQ := H.hδQ
  refine ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hq0 hδQ) (fun v => ?_)
  refine (norm_cj_le H.Qp (cjm H.ωS H.ωY H.Qp) H.δQ H.hQm v).trans ?_
  rw [add_mul]
  refine add_le_add ((H.Qp.le_opNorm v).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))) le_rfl
  rw [hQ]; exact hq

/-- `‖e^{χ} X̂ e^{−χ} u‖ ≤ (4/c)(q+δQ) ‖u‖` -/
theorem g_X (q : ℝ) (hq : ‖Qh (geomOf ell k S) U a‖ ≤ q) (u : YP (geomOf ell k S)) :
    ‖siteWt φ (Xh (geomOf ell k S) U a (ypWt (geomOf ell k S) (-φ) u))‖
      ≤ (4 / (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).c)
        * ((q + (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).δQ) * ‖u‖) := by
  set H := wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD with hH
  have e : siteWt φ (Xh (geomOf ell k S) U a (ypWt (geomOf ell k S) (-φ) u)) = cjp H.ωY H.ωS H.X u := rfl
  rw [e, SiteHyp.cjpX_eq, ContinuousLinearMap.comp_apply]
  refine (H.cjpLinv_le _).trans (mul_le_mul_of_nonneg_left ?_ (by have := H.hc; positivity))
  exact SiteHyp.norm_adj_sub_le _ _ (g_Qadj hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD q hq) u

/-- `‖e^{χ} D̂ X̂ e^{−χ} u‖ ≤ (√(12/c)+δD·4/c)(q+δQ) ‖u‖` -/
theorem g_DX (q : ℝ) (hq : ‖Qh (geomOf ell k S) U a‖ ≤ q) (u : YP (geomOf ell k S)) :
    ‖bondWt φ (Dh (geomOf ell k S) U (Xh (geomOf ell k S) U a (ypWt (geomOf ell k S) (-φ) u)))‖
      ≤ ((Real.sqrt (12 / (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).c)
          + (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).δD
            * (4 / (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).c))
          * (q + (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).δQ)) * ‖u‖ := by
  set H := wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD with hH
  set g := ContinuousLinearMap.adjoint (cjm H.ωS H.ωY H.Qp) u with hg
  have eX : siteWt φ (Xh (geomOf ell k S) U a (ypWt (geomOf ell k S) (-φ) u)) = cjp H.ωS H.ωS H.Linv g := by
    have : siteWt φ (Xh (geomOf ell k S) U a (ypWt (geomOf ell k S) (-φ) u)) = cjp H.ωY H.ωS H.X u := rfl
    rw [this, SiteHyp.cjpX_eq]; rfl
  have eD : bondWt φ (Dh (geomOf ell k S) U (Xh (geomOf ell k S) U a (ypWt (geomOf ell k S) (-φ) u)))
      = cjp H.ωS H.ωE H.D (siteWt φ (Xh (geomOf ell k S) U a (ypWt (geomOf ell k S) (-φ) u))) := by
    show _ = bondWt φ (Dh (geomOf ell k S) U (siteWt (-φ) (siteWt φ
      (Xh (geomOf ell k S) U a (ypWt (geomOf ell k S) (-φ) u)))))
    rw [siteWt_cancel_neg]
  rw [eD, eX]
  have h3 := norm_cj_le H.D (cjp H.ωS H.ωE H.D) H.δD H.hDp (cjp H.ωS H.ωS H.Linv g)
  have h4 := H.D_cjpLinv_le g
  have h5 := H.cjpLinv_le g
  have hgn : ‖g‖ ≤ (q + H.δQ) * ‖u‖ :=
    SiteHyp.norm_adj_sub_le _ _ (g_Qadj hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD q hq) u
  have hδD := H.hδD
  have hc := H.hc
  calc ‖cjp H.ωS H.ωE H.D (cjp H.ωS H.ωS H.Linv g)‖
      ≤ ‖H.D (cjp H.ωS H.ωS H.Linv g)‖ + H.δD * ‖cjp H.ωS H.ωS H.Linv g‖ := h3
    _ ≤ Real.sqrt (12 / H.c) * ‖g‖ + H.δD * ((4 / H.c) * ‖g‖) := add_le_add h4 (mul_le_mul_of_nonneg_left h5 hδD)
    _ = (Real.sqrt (12 / H.c) + H.δD * (4 / H.c)) * ‖g‖ := by ring
    _ ≤ (Real.sqrt (12 / H.c) + H.δD * (4 / H.c)) * ((q + H.δQ) * ‖u‖) :=
        mul_le_mul_of_nonneg_left hgn (by positivity)
    _ = _ := by ring

/-- `‖e^{χ} X̂ e^{−χ} u − X̂ u‖ ≤ εX ‖u‖` and the gradient of the difference -/
theorem g_Xd (q : ℝ) (hq0 : 0 ≤ q) (hq : ‖Qh (geomOf ell k S) U a‖ ≤ q) (u : YP (geomOf ell k S)) :
    ‖siteWt φ (Xh (geomOf ell k S) U a (ypWt (geomOf ell k S) (-φ) u)) - Xh (geomOf ell k S) U a u‖
        ≤ (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).epsX q * ‖u‖ ∧
      ‖Dh (geomOf ell k S) U (siteWt φ (Xh (geomOf ell k S) U a (ypWt (geomOf ell k S) (-φ) u))
          - Xh (geomOf ell k S) U a u)‖
        ≤ (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).epsDX q * ‖u‖ := by
  set H := wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD with hH
  exact H.Xdiff q hq0 hq u

/-- `‖e^{χ} D̂ X̂ e^{−χ} u − D̂ X̂ u‖ ≤ (δD (4/c)(q+δQ) + εDX) ‖u‖` -/
theorem g_DXd (q : ℝ) (hq0 : 0 ≤ q) (hq : ‖Qh (geomOf ell k S) U a‖ ≤ q) (u : YP (geomOf ell k S)) :
    ‖bondWt φ (Dh (geomOf ell k S) U (Xh (geomOf ell k S) U a (ypWt (geomOf ell k S) (-φ) u)))
        - Dh (geomOf ell k S) U (Xh (geomOf ell k S) U a u)‖
      ≤ ((wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).δD
          * ((4 / (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).c)
            * (q + (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).δQ))
        + (wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD).epsDX q) * ‖u‖ := by
  set H := wHyp hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD with hH
  set xp := siteWt φ (Xh (geomOf ell k S) U a (ypWt (geomOf ell k S) (-φ) u)) with hxp
  have eD : bondWt φ (Dh (geomOf ell k S) U (Xh (geomOf ell k S) U a (ypWt (geomOf ell k S) (-φ) u)))
      = cjp H.ωS H.ωE H.D xp := by
    show _ = bondWt φ (Dh (geomOf ell k S) U (siteWt (-φ) xp))
    rw [hxp, siteWt_cancel_neg]
  have hD : H.D = Dh (geomOf ell k S) U := rfl
  rw [eD]
  have e : cjp H.ωS H.ωE H.D xp - Dh (geomOf ell k S) U (Xh (geomOf ell k S) U a u)
      = (cjp H.ωS H.ωE H.D - H.D) xp + Dh (geomOf ell k S) U (xp - Xh (geomOf ell k S) U a u) := by
    rw [ContinuousLinearMap.sub_apply, map_sub, hD]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 := SiteHyp.norm_op_le _ _ H.hDp xp
  have h2 := g_X hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD q hq u
  have h3 := (g_Xd hS hW hell hR hM hWR U a cs hp φ θ δ0 hθ hδ0 hok hsm hsmD q hq0 hq u).2
  have hδD := H.hδD
  calc _ ≤ H.δD * ‖xp‖ + H.epsDX q * ‖u‖ := add_le_add h1 h3
    _ ≤ H.δD * ((4 / H.c) * ((q + H.δQ) * ‖u‖)) + H.epsDX q * ‖u‖ :=
        add_le_add (mul_le_mul_of_nonneg_left h2 hδD) le_rfl
    _ = _ := by ring

end inst

#print axioms psiOK
#print axioms wHyp
#print axioms Xh
#print axioms wHyp_X
#print axioms g_DLD
#print axioms g_LD
#print axioms g_DL
#print axioms g_L
#print axioms g_Qadj
#print axioms g_X
#print axioms g_DX
#print axioms g_Xd
#print axioms g_DXd

end AdalyFormal.M1DStrat
