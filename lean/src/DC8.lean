import DC7

/-!
# DC8 -- Combes–Thomas for the genuine gauge-fixing divergence `T = R D*`, and the conjugated bounds of
`Z = G' T` and `W = 1 − Dm Z` (M1 D-layer lane, 2026-10-14)

For `D : CTData …`, a weight `ξ` with `WtOK (ψ ± ξ) Θ Δ`, `WtOK ξ θξ δξ`, and `0 < cΓ` (DC7):
`TC ξ B = e^{ξ} T e^{−ξ} B`, `ZC ξ B = e^{ξ} G'(T(e^{−ξ} B))`, `WC ξ B = e^{ξ} W (e^{−ξ} B)` (sites/bonds at the tail).
* `T_split` : `T B = Dm* B − X Γ⁻¹ (D̂X̂)* B` (lane C `Rproj_eq_strat`; the projection does not see the mask);
* **`TC_diff`** : `‖TC ξ B − T B‖ ≤ dT ‖e^{−σ} B‖`;
* **`ZC_bound`** : `‖e^{−2σ} ZC ξ B‖ ≤ kZ ‖e^{−σ} B‖`;
* **`WC_bound`** : `‖e^{−σ} WC ξ B‖ ≤ kW ‖e^{−σ} B‖`;
with `dT, kZ, kW` explicit in `ℓ, cs, dD, nX, K3, EX, EDX', cΓ, dΓ, γ` (all free of `k`, the torus and the tower).
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

/-! ## 0. the hatted bounds with the common constants -/

theorem gLD (φ : PeriodicLatticeSite Lf → ℝ) (hφ : WtOK (geomOf ell k S) ell φ D.Θ D.Δ) (B : BondFnL2 Lf) :
    ‖siteWt φ (Linvh (geomOf ell k S) D.U D.a
        (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) D.U) (bondWt (-φ) B)))‖
      ≤ Real.sqrt (48 / D.cs) * ‖B‖ :=
  g_LD D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp φ D.Θ D.Δ D.Θ0 D.Δ0 hφ D.hsm D.hsmD B

theorem gL (φ : PeriodicLatticeSite Lf → ℝ) (hφ : WtOK (geomOf ell k S) ell φ D.Θ D.Δ) (g : SiteL2 Lf) :
    ‖siteWt φ (Linvh (geomOf ell k S) D.U D.a (siteWt (-φ) g))‖ ≤ (4 / D.cs) * ‖g‖ :=
  g_L D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp φ D.Θ D.Δ D.Θ0 D.Δ0 hφ D.hsm D.hsmD g

theorem gDLD (φ : PeriodicLatticeSite Lf → ℝ) (hφ : WtOK (geomOf ell k S) ell φ D.Θ D.Δ) (B : BondFnL2 Lf) :
    ‖bondWt φ (Dh (geomOf ell k S) D.U (Linvh (geomOf ell k S) D.U D.a
        (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) D.U) (bondWt (-φ) B))))‖
      ≤ (Real.sqrt 24 + D.dD * Real.sqrt (48 / D.cs)) * ‖B‖ :=
  g_DLD D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp φ D.Θ D.Δ D.Θ0 D.Δ0 hφ D.hsm D.hsmD B

theorem gDL (φ : PeriodicLatticeSite Lf → ℝ) (hφ : WtOK (geomOf ell k S) ell φ D.Θ D.Δ) (g : SiteL2 Lf) :
    ‖bondWt φ (Dh (geomOf ell k S) D.U (Linvh (geomOf ell k S) D.U D.a (siteWt (-φ) g)))‖
      ≤ (Real.sqrt (12 / D.cs) + D.dD * (4 / D.cs)) * ‖g‖ :=
  g_DL D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp φ D.Θ D.Δ D.Θ0 D.Δ0 hφ D.hsm D.hsmD g

/-- `‖e^{−ψ} B‖ ≤ ℓ ‖e^{−σ} B‖` -/
theorem psiN_le (B : BondFnL2 Lf) :
    ‖bondWt (-psiW S W ell k) B‖ ≤ (ell : ℝ) * ‖bondWt (-sigG (geomOf ell k S)) B‖ := by
  have h := bondWt_le_shift (-psiW S W ell k) (-sigG (geomOf ell k S)) (Real.log ell)
    (fun x => by have := (sig_psi D.hS D.hW D.hell D.hR D.hM D.hWR x).2; simp only [Pi.neg_apply]; linarith) B
  rwa [Real.exp_log D.ell_pos] at h

/-- `‖e^{ψ − σ} f‖ ≤ ‖f‖` (sites) and `‖e^{σ − ψ} f‖ ≤ ℓ ‖f‖` -/
theorem site_psi_sig_le (f : SiteL2 Lf) : ‖siteWt (psiW S W ell k + -sigG (geomOf ell k S)) f‖ ≤ ‖f‖ := by
  refine (siteWt_le_of _ (fun _ => (0 : ℝ)) (fun x => ?_) f).trans (le_of_eq (by rw [siteWt_zero_fn]))
  have := (sig_psi D.hS D.hW D.hell D.hR D.hM D.hWR x).1
  simp only [Pi.add_apply, Pi.neg_apply]; linarith

theorem site_sig_psi_le (f : SiteL2 Lf) :
    ‖siteWt (sigG (geomOf ell k S) + -psiW S W ell k) f‖ ≤ (ell : ℝ) * ‖f‖ := by
  have h := siteWt_le_shift (sigG (geomOf ell k S) + -psiW S W ell k) (fun _ => (0 : ℝ)) (Real.log ell)
    (fun x => by have := (sig_psi D.hS D.hW D.hell D.hR D.hM D.hWR x).2; simp only [Pi.add_apply, Pi.neg_apply]; linarith) f
  rwa [siteWt_zero_fn, Real.exp_log D.ell_pos] at h

theorem bond_psi_sig_le (f : BondFnL2 Lf) : ‖bondWt (psiW S W ell k + -sigG (geomOf ell k S)) f‖ ≤ ‖f‖ := by
  refine (bondWt_le_of _ (fun _ => (0 : ℝ)) (fun x => ?_) f).trans (le_of_eq (by rw [bondWt_zero_fn]))
  have := (sig_psi D.hS D.hW D.hell D.hR D.hM D.hWR x).1
  simp only [Pi.add_apply, Pi.neg_apply]; linarith

/-! ## 1. the split of `T` -/

theorem hwq : ∀ j, 0 < wq (geomOf ell k S) D.a j :=
  fun j => wq_pos D.hell (properTower_geomOf (show 0 < ell by have := D.hell; omega) D.hS) D.a j D.hp.ha

/-- `(Dm X)* = (D̂ X̂)*` -/
theorem adjDmX (B : BondFnL2 Lf) :
    ContinuousLinearMap.adjoint (Xop (geomOf ell k S) D.U D.a) (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) D.U) B)
      = VC (geomOf ell k S) D.U D.a (fun _ => (0 : ℝ)) B := by
  rw [D.VC_zero]
  exact adj_DmX D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp B

theorem T_split (B : BondFnL2 Lf) :
    Tfull (geomOf ell k S) D.U B = ContinuousLinearMap.adjoint (Dm (geomOf ell k S) D.U) B
      - Xop (geomOf ell k S) D.U D.a (D.Gi (VC (geomOf ell k S) D.U D.a (fun _ => (0 : ℝ)) B)) := by
  have e1 : Tfull (geomOf ell k S) D.U B = Rproj (geomOf ell k S) D.U (gradAdj D.U B) := rfl
  have e2 : ContinuousLinearMap.adjoint (Dm (geomOf ell k S) D.U) B = siteMask (geomOf ell k S).Om0 (gradAdj D.U B) := by
    rw [Dm_adj]; rfl
  rw [e1, ← Rproj_mask_right, ← e2, Rproj_eq_strat (geomOf ell k S) D.U D.a D.hwq D.hp.hu D.Gi D.hG1, D.adjDmX]

/-- the conjugated `T` -/
noncomputable def TC (ξ : PeriodicLatticeSite Lf → ℝ) (B : BondFnL2 Lf) : SiteL2 Lf :=
  siteWt ξ (Tfull (geomOf ell k S) D.U (bondWt (-ξ) B))

theorem XGV_conj (ξ : PeriodicLatticeSite Lf → ℝ) (B : BondFnL2 Lf) :
    siteWt ξ (Xop (geomOf ell k S) D.U D.a (D.Gi (VC (geomOf ell k S) D.U D.a (fun _ => (0 : ℝ)) (bondWt (-ξ) B))))
      = D.Xcj ξ (GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B)) := by
  have e : (-(fun _ : PeriodicLatticeSite Lf => (0 : ℝ))) = fun _ => (0 : ℝ) := by funext x; simp
  unfold Xcj GiC VC
  rw [e, bondWt_zero_fn, ypWt_zero_fn, ypWt_cancel_neg, ypWt_cancel_neg]

theorem TC_split (ξ : PeriodicLatticeSite Lf → ℝ) (B : BondFnL2 Lf) :
    D.TC ξ B = siteWt ξ (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) D.U) (bondWt (-ξ) B))
      - D.Xcj ξ (GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B)) := by
  unfold TC
  rw [D.T_split, map_sub, D.XGV_conj]

/-- the `T` CT constant -/
noncomputable def dTc (θξ : ℝ) : ℝ :=
  Real.sqrt 3 * (ell : ℝ) * (Real.exp θξ - 1)
    + 2 * (ell : ℝ) * D.EX * ((ell : ℝ) * D.K3 / D.cG)
    + (ell : ℝ) * D.nX * (D.dG * D.γ ^ 2 * ((ell : ℝ) * D.K3) / D.cG + D.γ ^ 2 * (2 * (ell : ℝ) * D.EDX'))

/-- **the CT difference of the genuine `T`** -/
theorem TC_diff (ξ : PeriodicLatticeSite Lf → ℝ) (θξ δξ : ℝ) (hθξ : 0 ≤ θξ)
    (hξ : WtOK (geomOf ell k S) ell ξ θξ δξ)
    (hp : WtOK (geomOf ell k S) ell (psiW S W ell k + ξ) D.Θ D.Δ)
    (hm : WtOK (geomOf ell k S) ell (psiW S W ell k + -ξ) D.Θ D.Δ)
    (hεγ : D.epsG * D.γ ≤ 1) (hcG : 0 < D.cG) (B : BondFnL2 Lf) :
    ‖D.TC ξ B - Tfull (geomOf ell k S) D.U B‖ ≤ D.dTc θξ * ‖bondWt (-sigG (geomOf ell k S)) B‖ := by
  have e : D.TC ξ B - Tfull (geomOf ell k S) D.U B
      = (siteWt ξ (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) D.U) (bondWt (-ξ) B))
          - ContinuousLinearMap.adjoint (Dm (geomOf ell k S) D.U) B)
        - ((D.Xcj ξ (GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B))
              - Xop (geomOf ell k S) D.U D.a (GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B)))
          + Xop (geomOf ell k S) D.U D.a ((GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B)
              - D.Gi (VC (geomOf ell k S) D.U D.a ξ B))
            + D.Gi (VC (geomOf ell k S) D.U D.a ξ B - VC (geomOf ell k S) D.U D.a (fun _ => (0 : ℝ)) B))) := by
    rw [D.TC_split, D.T_split]
    simp only [map_add, map_sub]
    abel
  rw [e]
  set NB := ‖bondWt (-sigG (geomOf ell k S)) B‖ with hNB
  set v' := VC (geomOf ell k S) D.U D.a ξ B with hv'
  set v := VC (geomOf ell k S) D.U D.a (fun _ => (0 : ℝ)) B with hv
  set g' := GiC (geomOf ell k S) D.Gi ξ v' with hg'
  have hNB0 : 0 ≤ NB := norm_nonneg _
  have hl := D.ell_pos
  have hK3 := D.K3_nonneg
  have hEX := D.EX_nonneg
  have hnX := D.nX_nonneg
  have hEDX := D.EDX'_nonneg
  have hdG := D.dG_nonneg
  have hγ0 := D.hγ0
  -- pieces
  have p1 := Ds_comm D.hS D.hell D.hR D.hM D.U ξ θξ δξ hθξ hξ B
  have hv'b : ‖ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) v'‖ ≤ (ell : ℝ) * D.K3 * NB := D.VC_bound ξ hm B
  have hg'b : ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) g'‖ ≤ (ell : ℝ) * D.K3 * NB / D.cG := by
    have := D.GiC_bound ξ hp hm hεγ v'
    rw [le_div_iff₀ hcG]; linarith
  have p2 : ‖D.Xcj ξ g' - Xop (geomOf ell k S) D.U D.a g'‖ ≤ 2 * (ell : ℝ) * D.EX * ((ell : ℝ) * D.K3 * NB / D.cG) :=
    (D.Xcj_diff ξ hp g').trans (mul_le_mul_of_nonneg_left hg'b (by positivity))
  have hd1 : ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (g' - D.Gi v')‖
      ≤ D.dG * D.γ ^ 2 * ((ell : ℝ) * D.K3 * NB) / D.cG := by
    have := D.GiC_diff ξ hp hm hεγ v'
    rw [le_div_iff₀ hcG]
    have h2 := mul_le_mul_of_nonneg_left hv'b (show 0 ≤ D.dG * D.γ ^ 2 by positivity)
    linarith
  have hd2 : ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (D.Gi (v' - v))‖ ≤ D.γ ^ 2 * (2 * (ell : ℝ) * D.EDX' * NB) := by
    have h1 := gami_w D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.Gi D.hG1 D.γ D.hγ0.le D.hγ (v' - v)
    have h2 := D.VC_diff ξ hm B
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have p3 : ‖Xop (geomOf ell k S) D.U D.a ((g' - D.Gi v') + D.Gi (v' - v))‖
      ≤ (ell : ℝ) * D.nX * (D.dG * D.γ ^ 2 * ((ell : ℝ) * D.K3 * NB) / D.cG + D.γ ^ 2 * (2 * (ell : ℝ) * D.EDX' * NB)) := by
    refine (D.X_le _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add hd1 hd2)
  calc _ ≤ ‖siteWt ξ (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) D.U) (bondWt (-ξ) B))
          - ContinuousLinearMap.adjoint (Dm (geomOf ell k S) D.U) B‖
        + (‖D.Xcj ξ g' - Xop (geomOf ell k S) D.U D.a g'‖
          + ‖Xop (geomOf ell k S) D.U D.a ((g' - D.Gi v') + D.Gi (v' - v))‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ Real.sqrt 3 * (ell : ℝ) * (Real.exp θξ - 1) * NB
        + (2 * (ell : ℝ) * D.EX * ((ell : ℝ) * D.K3 * NB / D.cG)
          + (ell : ℝ) * D.nX * (D.dG * D.γ ^ 2 * ((ell : ℝ) * D.K3 * NB) / D.cG
            + D.γ ^ 2 * (2 * (ell : ℝ) * D.EDX' * NB))) := add_le_add p1 (add_le_add p2 p3)
    _ = D.dTc θξ * NB := by unfold dTc; ring

/-! ## 2. `Z = G' T` and `W` conjugated -/

/-- the conjugated `Z = G' T` -/
noncomputable def ZC (ξ : PeriodicLatticeSite Lf → ℝ) (B : BondFnL2 Lf) : SiteL2 Lf :=
  siteWt ξ (Gp (geomOf ell k S) D.U D.a (Tfull (geomOf ell k S) D.U (bondWt (-ξ) B)))

/-- the conjugated `W` -/
noncomputable def WC (ξ : PeriodicLatticeSite Lf → ℝ) (B : BondFnL2 Lf) : BondFnL2 Lf :=
  bondWt ξ (Wop (geomOf ell k S) D.U D.a (bondWt (-ξ) B))

theorem Gp_split (B : BondFnL2 Lf) :
    Gp (geomOf ell k S) D.U D.a (Tfull (geomOf ell k S) D.U B)
      = LinvP (geomOf ell k S) D.U D.a (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) D.U) B)
        - LinvP (geomOf ell k S) D.U D.a (Xop (geomOf ell k S) D.U D.a
            (D.Gi (VC (geomOf ell k S) D.U D.a (fun _ => (0 : ℝ)) B))) := by
  rw [GpT_eq (geomOf ell k S) D.U D.a D.hwq D.hp.hu D.Gi D.hG1 B, D.adjDmX]

/-- the two hatted forms of the conjugated pieces -/
theorem LD_form (ξ : PeriodicLatticeSite Lf → ℝ) (B : BondFnL2 Lf) :
    siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S)))
        (siteWt ξ (LinvP (geomOf ell k S) D.U D.a (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) D.U) (bondWt (-ξ) B))))
      = siteWt (psiW S W ell k + -sigG (geomOf ell k S)) (siteWt (ξ + -psiW S W ell k) (Linvh (geomOf ell k S) D.U D.a
          (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) D.U)
            (bondWt (-(ξ + -psiW S W ell k)) (bondWt (-psiW S W ell k) B))))) := by
  rw [LinvP_eq D.hS D.hW D.hell D.hR D.hM D.hWR, Dh_adjoint D.hS D.hW D.hell D.hR D.hM D.hWR,
    ContinuousLinearMap.comp_apply, bondWt_mul (-(ξ + -psiW S W ell k)) (-psiW S W ell k) B,
    siteWt_mul ξ (sigG (geomOf ell k S)),
    siteWt_mul (-(sigG (geomOf ell k S) + sigG (geomOf ell k S))) (ξ + sigG (geomOf ell k S)),
    siteWt_mul (psiW S W ell k + -sigG (geomOf ell k S)) (ξ + -psiW S W ell k)]
  rw [show (-(ξ + -psiW S W ell k) + -psiW S W ell k) = -ξ from
      funext fun x => by simp only [Pi.add_apply, Pi.neg_apply]; ring,
    show (-(sigG (geomOf ell k S) + sigG (geomOf ell k S)) + (ξ + sigG (geomOf ell k S)))
      = (psiW S W ell k + -sigG (geomOf ell k S) + (ξ + -psiW S W ell k)) from
      funext fun x => by simp only [Pi.add_apply, Pi.neg_apply]; ring]

theorem LX_form (ξ : PeriodicLatticeSite Lf → ℝ) (y : SiteL2 Lf) :
    siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S)))
        (siteWt ξ (LinvP (geomOf ell k S) D.U D.a (siteWt (-ξ) y)))
      = siteWt (psiW S W ell k + -sigG (geomOf ell k S)) (siteWt (ξ + -psiW S W ell k) (Linvh (geomOf ell k S) D.U D.a
          (siteWt (-(ξ + -psiW S W ell k)) (siteWt (sigG (geomOf ell k S) + -psiW S W ell k) y)))) := by
  rw [LinvP_eq D.hS D.hW D.hell D.hR D.hM D.hWR,
    siteWt_mul ξ (sigG (geomOf ell k S)),
    siteWt_mul (-(sigG (geomOf ell k S) + sigG (geomOf ell k S))) (ξ + sigG (geomOf ell k S)),
    siteWt_mul (psiW S W ell k + -sigG (geomOf ell k S)) (ξ + -psiW S W ell k),
    siteWt_mul (sigG (geomOf ell k S)) (-ξ),
    siteWt_mul (-(ξ + -psiW S W ell k)) (sigG (geomOf ell k S) + -psiW S W ell k)]
  rw [show (-(ξ + -psiW S W ell k) + (sigG (geomOf ell k S) + -psiW S W ell k)) = sigG (geomOf ell k S) + -ξ from
      funext fun x => by simp only [Pi.add_apply, Pi.neg_apply]; ring,
    show (-(sigG (geomOf ell k S) + sigG (geomOf ell k S)) + (ξ + sigG (geomOf ell k S)))
      = (psiW S W ell k + -sigG (geomOf ell k S) + (ξ + -psiW S W ell k)) from
      funext fun x => by simp only [Pi.add_apply, Pi.neg_apply]; ring]

/-- `Xop (Gi (V (e^{−ξ} B))) = e^{−ξ} (Xcj ξ (GiC ξ (VC ξ B)))` -/
theorem XGV_eq (ξ : PeriodicLatticeSite Lf → ℝ) (B : BondFnL2 Lf) :
    Xop (geomOf ell k S) D.U D.a (D.Gi (VC (geomOf ell k S) D.U D.a (fun _ => (0 : ℝ)) (bondWt (-ξ) B)))
      = siteWt (-ξ) (D.Xcj ξ (GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B))) := by
  rw [← D.XGV_conj, siteWt_cancel_neg]

/-- the `Z` constant -/
noncomputable def kZc : ℝ :=
  (ell : ℝ) * Real.sqrt (48 / D.cs) + (4 / D.cs) * ((ell : ℝ) * ((ell : ℝ) * D.nX * ((ell : ℝ) * D.K3 / D.cG)))

/-- the bound of `Xcj ξ (GiC ξ (VC ξ B))` -/
theorem XGV_le (ξ : PeriodicLatticeSite Lf → ℝ)
    (hp : WtOK (geomOf ell k S) ell (psiW S W ell k + ξ) D.Θ D.Δ)
    (hm : WtOK (geomOf ell k S) ell (psiW S W ell k + -ξ) D.Θ D.Δ)
    (hεγ : D.epsG * D.γ ≤ 1) (hcG : 0 < D.cG) (B : BondFnL2 Lf) :
    ‖D.Xcj ξ (GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B))‖
      ≤ (ell : ℝ) * D.nX * ((ell : ℝ) * D.K3 / D.cG) * ‖bondWt (-sigG (geomOf ell k S)) B‖ := by
  have h1 := D.Xcj_le ξ hp (GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B))
  have h2 := D.GiC_bound ξ hp hm hεγ (VC (geomOf ell k S) D.U D.a ξ B)
  have h3 := D.VC_bound ξ hm B
  have hl := D.ell_pos
  have hnX := D.nX_nonneg
  have hK3 := D.K3_nonneg
  have h4 : ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B))‖
      ≤ (ell : ℝ) * D.K3 / D.cG * ‖bondWt (-sigG (geomOf ell k S)) B‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcG]; linarith
  calc _ ≤ (ell : ℝ) * D.nX * ((ell : ℝ) * D.K3 / D.cG * ‖bondWt (-sigG (geomOf ell k S)) B‖) :=
        h1.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
    _ = _ := by ring

/-- **the conjugated `Z` bound** -/
theorem ZC_bound (ξ : PeriodicLatticeSite Lf → ℝ)
    (hp : WtOK (geomOf ell k S) ell (psiW S W ell k + ξ) D.Θ D.Δ)
    (hm : WtOK (geomOf ell k S) ell (psiW S W ell k + -ξ) D.Θ D.Δ)
    (hn : WtOK (geomOf ell k S) ell (ξ + -psiW S W ell k) D.Θ D.Δ)
    (hεγ : D.epsG * D.γ ≤ 1) (hcG : 0 < D.cG) (B : BondFnL2 Lf) :
    ‖siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S))) (D.ZC ξ B)‖
      ≤ D.kZc * ‖bondWt (-sigG (geomOf ell k S)) B‖ := by
  have e : siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S))) (D.ZC ξ B)
      = siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S)))
          (siteWt ξ (LinvP (geomOf ell k S) D.U D.a (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) D.U) (bondWt (-ξ) B))))
        - siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S)))
          (siteWt ξ (LinvP (geomOf ell k S) D.U D.a
            (siteWt (-ξ) (D.Xcj ξ (GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B)))))) := by
    unfold ZC
    rw [D.Gp_split, D.XGV_eq]
    simp only [map_sub]
  rw [e, D.LD_form, D.LX_form]
  refine (norm_sub_le _ _).trans ?_
  have hl := D.ell_pos
  have a1 := (D.site_psi_sig_le _).trans (D.gLD (ξ + -psiW S W ell k) hn (bondWt (-psiW S W ell k) B))
  have a2 := D.psiN_le B
  have b1 := (D.site_psi_sig_le _).trans (D.gL (ξ + -psiW S W ell k) hn
    (siteWt (sigG (geomOf ell k S) + -psiW S W ell k)
      (D.Xcj ξ (GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B)))))
  have b2 := D.site_sig_psi_le (D.Xcj ξ (GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B)))
  have b3 := D.XGV_le ξ hp hm hεγ hcG B
  have hcs := D.cs_pos
  have hs48 : 0 ≤ Real.sqrt (48 / D.cs) := Real.sqrt_nonneg _
  have h4 : (0 : ℝ) ≤ 4 / D.cs := by positivity
  set NB := ‖bondWt (-sigG (geomOf ell k S)) B‖
  calc _ ≤ Real.sqrt (48 / D.cs) * ((ell : ℝ) * NB)
        + (4 / D.cs) * ((ell : ℝ) * ((ell : ℝ) * D.nX * ((ell : ℝ) * D.K3 / D.cG) * NB)) := by
        refine add_le_add (a1.trans (mul_le_mul_of_nonneg_left a2 hs48))
          (b1.trans (mul_le_mul_of_nonneg_left (b2.trans (mul_le_mul_of_nonneg_left b3 hl.le)) h4))
    _ = D.kZc * NB := by unfold kZc; ring

/-- the bond forms of the conjugated pieces of `W` -/
theorem DLD_form (ξ : PeriodicLatticeSite Lf → ℝ) (B : BondFnL2 Lf) :
    bondWt (-sigG (geomOf ell k S)) (bondWt ξ (Dm (geomOf ell k S) D.U (LinvP (geomOf ell k S) D.U D.a
        (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) D.U) (bondWt (-ξ) B)))))
      = bondWt (psiW S W ell k + -sigG (geomOf ell k S)) (bondWt (ξ + -psiW S W ell k) (Dh (geomOf ell k S) D.U
          (Linvh (geomOf ell k S) D.U D.a (ContinuousLinearMap.adjoint (Dh (geomOf ell k S) D.U)
            (bondWt (-(ξ + -psiW S W ell k)) (bondWt (-psiW S W ell k) B)))))) := by
  rw [DmLinvP_eq D.hS D.hW D.hell D.hR D.hM D.hWR, Dh_adjoint D.hS D.hW D.hell D.hR D.hM D.hWR,
    ContinuousLinearMap.comp_apply, bondWt_mul (-(ξ + -psiW S W ell k)) (-psiW S W ell k) B,
    bondWt_mul (-sigG (geomOf ell k S)) ξ,
    bondWt_mul (psiW S W ell k + -sigG (geomOf ell k S)) (ξ + -psiW S W ell k)]
  rw [show (-(ξ + -psiW S W ell k) + -psiW S W ell k) = -ξ from
      funext fun x => by simp only [Pi.add_apply, Pi.neg_apply]; ring,
    show (-sigG (geomOf ell k S) + ξ) = (psiW S W ell k + -sigG (geomOf ell k S) + (ξ + -psiW S W ell k)) from
      funext fun x => by simp only [Pi.add_apply, Pi.neg_apply]; ring]

theorem DLX_form (ξ : PeriodicLatticeSite Lf → ℝ) (y : SiteL2 Lf) :
    bondWt (-sigG (geomOf ell k S)) (bondWt ξ (Dm (geomOf ell k S) D.U (LinvP (geomOf ell k S) D.U D.a
        (siteWt (-ξ) y))))
      = bondWt (psiW S W ell k + -sigG (geomOf ell k S)) (bondWt (ξ + -psiW S W ell k) (Dh (geomOf ell k S) D.U
          (Linvh (geomOf ell k S) D.U D.a (siteWt (-(ξ + -psiW S W ell k)) (siteWt (sigG (geomOf ell k S) + -psiW S W ell k) y))))) := by
  rw [DmLinvP_eq D.hS D.hW D.hell D.hR D.hM D.hWR,
    bondWt_mul (-sigG (geomOf ell k S)) ξ,
    bondWt_mul (psiW S W ell k + -sigG (geomOf ell k S)) (ξ + -psiW S W ell k),
    siteWt_mul (sigG (geomOf ell k S)) (-ξ),
    siteWt_mul (-(ξ + -psiW S W ell k)) (sigG (geomOf ell k S) + -psiW S W ell k)]
  rw [show (-(ξ + -psiW S W ell k) + (sigG (geomOf ell k S) + -psiW S W ell k)) = sigG (geomOf ell k S) + -ξ from
      funext fun x => by simp only [Pi.add_apply, Pi.neg_apply]; ring,
    show (-sigG (geomOf ell k S) + ξ) = (psiW S W ell k + -sigG (geomOf ell k S) + (ξ + -psiW S W ell k)) from
      funext fun x => by simp only [Pi.add_apply, Pi.neg_apply]; ring]

/-- the `W` constant -/
noncomputable def kWc : ℝ :=
  1 + (ell : ℝ) * (Real.sqrt 24 + D.dD * Real.sqrt (48 / D.cs))
    + (Real.sqrt (12 / D.cs) + D.dD * (4 / D.cs)) * ((ell : ℝ) * ((ell : ℝ) * D.nX * ((ell : ℝ) * D.K3 / D.cG)))

/-- **the conjugated `W` bound** -/
theorem WC_bound (ξ : PeriodicLatticeSite Lf → ℝ)
    (hp : WtOK (geomOf ell k S) ell (psiW S W ell k + ξ) D.Θ D.Δ)
    (hm : WtOK (geomOf ell k S) ell (psiW S W ell k + -ξ) D.Θ D.Δ)
    (hn : WtOK (geomOf ell k S) ell (ξ + -psiW S W ell k) D.Θ D.Δ)
    (hεγ : D.epsG * D.γ ≤ 1) (hcG : 0 < D.cG) (B : BondFnL2 Lf) :
    ‖bondWt (-sigG (geomOf ell k S)) (D.WC ξ B)‖ ≤ D.kWc * ‖bondWt (-sigG (geomOf ell k S)) B‖ := by
  have e : bondWt (-sigG (geomOf ell k S)) (D.WC ξ B)
      = bondWt (-sigG (geomOf ell k S)) B
        - (bondWt (-sigG (geomOf ell k S)) (bondWt ξ (Dm (geomOf ell k S) D.U (LinvP (geomOf ell k S) D.U D.a
            (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) D.U) (bondWt (-ξ) B)))))
          - bondWt (-sigG (geomOf ell k S)) (bondWt ξ (Dm (geomOf ell k S) D.U (LinvP (geomOf ell k S) D.U D.a
            (siteWt (-ξ) (D.Xcj ξ (GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B)))))))) := by
    unfold WC
    rw [Wop_eq_gen (geomOf ell k S) D.U D.a D.hp.hu, D.Gp_split, D.XGV_eq]
    simp only [map_sub, bondWt_neg_cancel]
  rw [e, D.DLD_form, D.DLX_form]
  have hl := D.ell_pos
  have a1 := (D.bond_psi_sig_le _).trans (D.gDLD (ξ + -psiW S W ell k) hn (bondWt (-psiW S W ell k) B))
  have a2 := D.psiN_le B
  have b1 := (D.bond_psi_sig_le _).trans (D.gDL (ξ + -psiW S W ell k) hn
    (siteWt (sigG (geomOf ell k S) + -psiW S W ell k)
      (D.Xcj ξ (GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B)))))
  have b2 := D.site_sig_psi_le (D.Xcj ξ (GiC (geomOf ell k S) D.Gi ξ (VC (geomOf ell k S) D.U D.a ξ B)))
  have b3 := D.XGV_le ξ hp hm hεγ hcG B
  have hcs := D.cs_pos
  have hdD := D.dD_nonneg
  have hA : 0 ≤ Real.sqrt 24 + D.dD * Real.sqrt (48 / D.cs) := by positivity
  have hB : 0 ≤ Real.sqrt (12 / D.cs) + D.dD * (4 / D.cs) := by positivity
  set NB := ‖bondWt (-sigG (geomOf ell k S)) B‖
  calc _ ≤ NB + ((Real.sqrt 24 + D.dD * Real.sqrt (48 / D.cs)) * ((ell : ℝ) * NB)
          + (Real.sqrt (12 / D.cs) + D.dD * (4 / D.cs)) * ((ell : ℝ) * ((ell : ℝ) * D.nX * ((ell : ℝ) * D.K3 / D.cG) * NB))) := by
        refine (norm_sub_le _ _).trans (add_le_add le_rfl ((norm_sub_le _ _).trans (add_le_add ?_ ?_)))
        · exact a1.trans (mul_le_mul_of_nonneg_left a2 hA)
        · exact b1.trans (mul_le_mul_of_nonneg_left (b2.trans (mul_le_mul_of_nonneg_left b3 hl.le)) hB)
    _ = D.kWc * NB := by unfold kWc; ring

end CTData

#print axioms CTData.gLD
#print axioms CTData.gL
#print axioms CTData.gDLD
#print axioms CTData.gDL
#print axioms CTData.psiN_le
#print axioms CTData.site_psi_sig_le
#print axioms CTData.site_sig_psi_le
#print axioms CTData.bond_psi_sig_le
#print axioms CTData.hwq
#print axioms CTData.adjDmX
#print axioms CTData.T_split
#print axioms CTData.TC
#print axioms CTData.XGV_conj
#print axioms CTData.TC_split
#print axioms CTData.dTc
#print axioms CTData.TC_diff
#print axioms CTData.ZC
#print axioms CTData.WC
#print axioms CTData.Gp_split
#print axioms CTData.LD_form
#print axioms CTData.LX_form
#print axioms CTData.XGV_eq
#print axioms CTData.kZc
#print axioms CTData.XGV_le
#print axioms CTData.ZC_bound
#print axioms CTData.DLD_form
#print axioms CTData.DLX_form
#print axioms CTData.kWc
#print axioms CTData.WC_bound

end AdalyFormal.M1DStrat
