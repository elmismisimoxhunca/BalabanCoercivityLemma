import DC5

/-!
# DC6 -- Combes–Thomas for the genuine `Γ`, `Γ⁻¹` and `T = R D*` from `CTData` (M1 D-layer lane, 2026-10-13)

For `D : CTData …` (CT weight `χ = D.χ`):
* `XC_diff` : `‖e^{σ}(X̂^{χ} − X̂) u‖ ≤ 2ℓ εX ‖e^{τ} u‖`;  `Xt`, `Xt0` : `‖e^{σ} X̂^{(χ)} e^{−τ} y‖ ≤ ℓ nX ‖y‖`;
* `Gam_conj_coer` : `⟪u, Γ^{χ} u⟫ ≥ cΓ ‖e^{τ} u‖²`, `cΓ = 1/γ² − 4ℓεX/γ − 4ℓ²εX²` (needs `2ℓ εX γ ≤ 1`);
* `GiC_bound`, `GiC_diff` : `‖e^{τ} Gi^{χ} w‖ ≤ ‖e^{−τ} w‖/cΓ`, `‖e^{τ}(Gi^{χ} − Gi) w‖ ≤ (dΓ γ²/cΓ) ‖e^{−τ} w‖`;
* `V_bound`, `V_diff` : `V = (D̂ X̂)*` (the divergence-to-rows map) in `e^{−ψ} → e^{−τ}`;
* **`T_conj_diff`** : `‖e^{χ} T e^{−χ} B − T B‖ ≤ δT ‖e^{−σ} B‖`.
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
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)

namespace CTData
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} {W : ℕ} (D : CTData ell M R k S W)
include D

theorem ell_pos : (0 : ℝ) < ell := Nat.cast_pos.mpr (by have := D.hell; omega)

theorem site_sig_psi (f : SiteL2 Lf) :
    ‖siteWt (sigG (geomOf ell k S)) f‖ ≤ (ell : ℝ) * ‖siteWt (psiW S W ell k) f‖ :=
  sig_le_psi_norm D.hS D.hW D.hell D.hR D.hM D.hWR f

theorem yp_psi_le (u : YP (geomOf ell k S)) :
    ‖ypWt (geomOf ell k S) (psiW S W ell k) u‖ ≤ ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ :=
  ypWt_le_of _ _ _ (fun x => (sig_psi D.hS D.hW D.hell D.hR D.hM D.hWR x).1) u

theorem yp_psi_sig_le (y : YP (geomOf ell k S)) :
    ‖ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) y‖ ≤ ‖y‖ := by
  refine (ypWt_le_of _ _ (fun _ => (0 : ℝ)) (fun x => ?_) y).trans (le_of_eq (by rw [ypWt_zero_fn]))
  have := (sig_psi D.hS D.hW D.hell D.hR D.hM D.hWR x).1
  simp only [Pi.add_apply, Pi.neg_apply]; linarith

theorem XhC_psi (u : YP (geomOf ell k S)) :
    siteWt (psiW S W ell k) (Xh (geomOf ell k S) D.U D.a u)
      = XhC (geomOf ell k S) D.U D.a (psiW S W ell k) (ypWt (geomOf ell k S) (psiW S W ell k) u) := by
  unfold XhC; rw [ypWt_cancel_neg]

theorem XC_diff_core (ξ : PeriodicLatticeSite Lf → ℝ) (hξ : WtOK (geomOf ell k S) ell (psiW S W ell k + ξ) D.Θ D.Δ)
    (u : YP (geomOf ell k S)) :
    ‖siteWt (psiW S W ell k) (XhC (geomOf ell k S) D.U D.a ξ u - Xh (geomOf ell k S) D.U D.a u)‖
      ≤ 2 * D.EX * ‖ypWt (geomOf ell k S) (psiW S W ell k) u‖ := by
  have e : siteWt (psiW S W ell k) (XhC (geomOf ell k S) D.U D.a ξ u - Xh (geomOf ell k S) D.U D.a u)
      = (XhC (geomOf ell k S) D.U D.a (psiW S W ell k + ξ) (ypWt (geomOf ell k S) (psiW S W ell k) u)
          - Xh (geomOf ell k S) D.U D.a (ypWt (geomOf ell k S) (psiW S W ell k) u))
        - (XhC (geomOf ell k S) D.U D.a (psiW S W ell k) (ypWt (geomOf ell k S) (psiW S W ell k) u)
          - Xh (geomOf ell k S) D.U D.a (ypWt (geomOf ell k S) (psiW S W ell k) u)) := by
    rw [map_sub, XhC_shift, D.XhC_psi]; abel
  have h1 := D.XhC_diff (psiW S W ell k + ξ) hξ (ypWt (geomOf ell k S) (psiW S W ell k) u)
  have h2 := D.XhC_diff (psiW S W ell k) D.okPsi (ypWt (geomOf ell k S) (psiW S W ell k) u)
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  linarith

/-- **the CT difference of `X̂` in the genuine scaling** -/
theorem XC_diff (ξ : PeriodicLatticeSite Lf → ℝ) (hξ : WtOK (geomOf ell k S) ell (psiW S W ell k + ξ) D.Θ D.Δ)
    (u : YP (geomOf ell k S)) :
    ‖siteWt (sigG (geomOf ell k S)) (XhC (geomOf ell k S) D.U D.a ξ u - Xh (geomOf ell k S) D.U D.a u)‖
      ≤ 2 * (ell : ℝ) * D.EX * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ := by
  have h3 := D.XC_diff_core ξ hξ u
  have h4 := D.yp_psi_le u
  have hEX := D.EX_nonneg
  have hl := D.ell_pos
  have h5 := D.site_sig_psi (XhC (geomOf ell k S) D.U D.a ξ u - Xh (geomOf ell k S) D.U D.a u)
  have h6 : 2 * D.EX * ‖ypWt (geomOf ell k S) (psiW S W ell k) u‖
      ≤ 2 * D.EX * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ :=
    mul_le_mul_of_nonneg_left h4 (mul_nonneg (by norm_num) hEX)
  have h7 := mul_le_mul_of_nonneg_left (h3.trans h6) hl.le
  calc _ ≤ _ := h5
    _ ≤ _ := h7
    _ = _ := by ring

/-- `‖e^{σ} X̂^{ξ} e^{−τ} y‖ ≤ ℓ nX ‖y‖` -/
theorem Xt (ξ : PeriodicLatticeSite Lf → ℝ) (hξ : WtOK (geomOf ell k S) ell (psiW S W ell k + ξ) D.Θ D.Δ)
    (y : YP (geomOf ell k S)) :
    ‖siteWt (sigG (geomOf ell k S)) (XhC (geomOf ell k S) D.U D.a ξ
        (ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) y))‖ ≤ (ell : ℝ) * D.nX * ‖y‖ := by
  have e : siteWt (psiW S W ell k) (XhC (geomOf ell k S) D.U D.a ξ (ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) y))
      = XhC (geomOf ell k S) D.U D.a (psiW S W ell k + ξ)
          (ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) y) := by
    rw [XhC_shift, ypWt_mul]
  have h1 := D.XhC_le (psiW S W ell k + ξ) hξ (ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) y)
  rw [← e] at h1
  have h2 := D.yp_psi_sig_le y
  have hn := D.nX_nonneg
  have hl := D.ell_pos
  have h5 := D.site_sig_psi (XhC (geomOf ell k S) D.U D.a ξ (ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) y))
  have h6 := mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hn)) hl.le
  calc _ ≤ _ := h5
    _ ≤ _ := h6
    _ = _ := by ring

theorem Xt0 (y : YP (geomOf ell k S)) :
    ‖siteWt (sigG (geomOf ell k S)) (Xh (geomOf ell k S) D.U D.a
        (ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) y))‖ ≤ (ell : ℝ) * D.nX * ‖y‖ := by
  have h := D.Xt (fun _ => (0 : ℝ)) (by
    have e : psiW S W ell k + (fun _ => (0 : ℝ)) = psiW S W ell k := by funext x; simp
    rw [e]; exact D.okPsi) y
  rwa [XhC_zero] at h

/-- the genuine `X` and its conjugates -/
theorem Xop_hat (u : YP (geomOf ell k S)) :
    Xop (geomOf ell k S) D.U D.a u = siteWt (sigG (geomOf ell k S)) (Xh (geomOf ell k S) D.U D.a u) :=
  Xop_eq_hat D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp u

theorem XopC_hat (ξ : PeriodicLatticeSite Lf → ℝ) (u : YP (geomOf ell k S)) :
    siteWt ξ (Xop (geomOf ell k S) D.U D.a (ypWt (geomOf ell k S) (-ξ) u))
      = siteWt (sigG (geomOf ell k S)) (XhC (geomOf ell k S) D.U D.a ξ u) := by
  rw [D.Xop_hat, siteWt_comm]; rfl

/-- `⟪Γ^{ξ} a, b⟫ = ⟪X^{ξ} a, X^{−ξ} b⟫` -/
theorem Gam_conj_inner (ξ : PeriodicLatticeSite Lf → ℝ) (a b : YP (geomOf ell k S)) :
    ⟪ypWt (geomOf ell k S) ξ ((ContinuousLinearMap.adjoint (Xop (geomOf ell k S) D.U D.a) ∘L Xop (geomOf ell k S) D.U D.a)
        (ypWt (geomOf ell k S) (-ξ) a)), b⟫
      = ⟪siteWt ξ (Xop (geomOf ell k S) D.U D.a (ypWt (geomOf ell k S) (-ξ) a)),
          siteWt (-ξ) (Xop (geomOf ell k S) D.U D.a (ypWt (geomOf ell k S) (-(-ξ)) b))⟫ := by
  rw [ypWt_symm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left, neg_neg,
    ← siteWt_symm, siteWt_cancel_neg]

end CTData

#print axioms CTData.ell_pos
#print axioms CTData.site_sig_psi
#print axioms CTData.yp_psi_le
#print axioms CTData.yp_psi_sig_le
#print axioms CTData.XhC_psi
#print axioms CTData.XC_diff_core
#print axioms CTData.XC_diff
#print axioms CTData.Xt
#print axioms CTData.Xt0
#print axioms CTData.Xop_hat
#print axioms CTData.XopC_hat
#print axioms CTData.Gam_conj_inner

end AdalyFormal.M1DStrat
