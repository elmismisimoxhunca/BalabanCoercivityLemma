import DG2a
import DG1

/-!
# DG2b -- the genuine `Ginv` as a `GSplit` (DG1): the form-relative Combes–Thomas bound `hHB` on a proper tower
(M1 D-layer lane, 2026-10-14)

Data: `D : CTData …` (the hatted CT chain at the CT weight `ξ = D.χ`, `Gi`, `γ`), `HolRegime ρ` (curvature),
`RegData … Sstar` (regional tower class for the bond `Q`), the stratified Lipschitz bound of `ξ`
(`|ξ(x+e_μ) − ξ(x)| ≤ θ'/ℓ^{strat x}`), `εγ ≤ 1`, `cΓ > 0`, and W4 (`cw · wnormSq ≤ ⟪·, Ginv ·⟫`).
* `Kz_le`, `dp_le`, `Wb_le`, `Y1_le` : the `ξ = 0` bounds (`‖Kz x‖ ≤ κK kZ ‖Nx‖`, `|Δ'(u,v)| ≤ ν ‖Nu‖‖Nv‖`, …);
* `Kz_cj` : `‖e^{±ξ} Kz e^{∓ξ} x‖ ≤ e^{2θ'} κK kZ ‖Nx‖`;
* **`gsplit`** : the `GSplit` instance (pieces `χ_P C`, `T`, `√w Q`; remainder `Δg`); its `kap` is explicit;
* **`hHB_genuine`** : `|⟪x, (Ginv)⁺ y⟫ − ⟪x, Ginv y⟫| ≤ κ √⟪x,Ginv x⟫ √⟪y,Ginv y⟫` — the `hHB` field of DC2's `WSchur`.
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
open AdalyFormal.TowerLoc (RegData Estar)
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply plaqMask_symm deltaPrimeBilL2NormLoc)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

namespace CTData
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {W : ℕ}
  (D : CTData ell M R k S W)
include D

/-! ## 0. weight bookkeeping -/

theorem okP : WtOK (geomOf ell k S) ell (psiW S W ell k + D.χ) D.Θ D.Δ := D.okPlus
theorem okM : WtOK (geomOf ell k S) ell (psiW S W ell k + -D.χ) D.Θ D.Δ := by
  rw [← sub_eq_add_neg]; exact D.okMinus
theorem okMM : WtOK (geomOf ell k S) ell (psiW S W ell k + -(-D.χ)) D.Θ D.Δ := by
  rw [neg_neg]; exact D.okPlus
theorem okN1 : WtOK (geomOf ell k S) ell (D.χ + -psiW S W ell k) D.Θ D.Δ := by
  have h := D.okM.neg
  rwa [show -(psiW S W ell k + -D.χ) = D.χ + -psiW S W ell k from by
    funext x; simp only [Pi.neg_apply, Pi.add_apply]; ring] at h
theorem okN2 : WtOK (geomOf ell k S) ell (-D.χ + -psiW S W ell k) D.Θ D.Δ := by
  have h := D.okP.neg
  rwa [show -(psiW S W ell k + D.χ) = -D.χ + -psiW S W ell k from by
    funext x; simp only [Pi.neg_apply, Pi.add_apply]; ring] at h
theorem ok0P : WtOK (geomOf ell k S) ell (psiW S W ell k + fun _ => (0 : ℝ)) D.Θ D.Δ := by
  rw [show (psiW S W ell k + fun _ => (0 : ℝ)) = psiW S W ell k from by funext x; simp]; exact D.okPsi
theorem ok0M : WtOK (geomOf ell k S) ell (psiW S W ell k + -fun _ => (0 : ℝ)) D.Θ D.Δ := by
  rw [show (psiW S W ell k + -fun _ => (0 : ℝ)) = psiW S W ell k from by funext x; simp]; exact D.okPsi
theorem ok0N : WtOK (geomOf ell k S) ell ((fun _ => (0 : ℝ)) + -psiW S W ell k) D.Θ D.Δ := by
  rw [show ((fun _ => (0 : ℝ)) + -psiW S W ell k) = -psiW S W ell k from by funext x; simp]; exact D.okPsi.neg

theorem ZC_zero (B : BondFnL2 (scaleUp ell k Lu)) :
    D.ZC (fun _ => (0 : ℝ)) B = Gp (geomOf ell k S) D.U D.a (Tfull (geomOf ell k S) D.U B) := by
  unfold ZC
  rw [show (-(fun _ : PeriodicLatticeSite (scaleUp ell k Lu) => (0 : ℝ))) = fun _ => (0 : ℝ) from by funext x; simp,
    bondWt_zero_fn, siteWt_zero_fn]

theorem WC_zero (B : BondFnL2 (scaleUp ell k Lu)) :
    D.WC (fun _ => (0 : ℝ)) B = Wop (geomOf ell k S) D.U D.a B := by
  unfold WC
  rw [show (-(fun _ : PeriodicLatticeSite (scaleUp ell k Lu) => (0 : ℝ))) = fun _ => (0 : ℝ) from by funext x; simp,
    bondWt_zero_fn, bondWt_zero_fn]

/-- `Gp(T(e^{−ξ}B)) = e^{−ξ} ZC ξ B` -/
theorem GpT_conj (ξ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (B : BondFnL2 (scaleUp ell k Lu)) :
    Gp (geomOf ell k S) D.U D.a (Tfull (geomOf ell k S) D.U (bondWt (-ξ) B)) = siteWt (-ξ) (D.ZC ξ B) := by
  unfold ZC; rw [siteWt_cancel_neg]

/-- `W(e^{ξ}B) = e^{ξ} WC(−ξ) B` -/
theorem W_conj (ξ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (B : BondFnL2 (scaleUp ell k Lu)) :
    Wop (geomOf ell k S) D.U D.a (bondWt ξ B) = bondWt ξ (D.WC (-ξ) B) := by
  unfold WC; rw [neg_neg, bondWt_neg_cancel]

end CTData

/-! ## 1. the constants -/

/-- the curvature factor `√12 ρ ℓ⁴` and the `Δ'` factor `(17/√2)·12 ρ ℓ⁴` -/
noncomputable def kapK (ell : ℕ) (ρ : ℝ) : ℝ := Real.sqrt 12 * ρ * (ell : ℝ) ^ 4
noncomputable def nuD (ell : ℕ) (ρ : ℝ) : ℝ := (17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)

/-- `‖Y1 x‖ ≤ cY √E` -/
noncomputable def cYc (ell : ℕ) (ρ cw kZ kW : ℝ) : ℝ :=
  Real.sqrt (1 + nuD ell ρ * kW ^ 2 / cw) + kapK ell ρ * kZ / Real.sqrt cw

noncomputable def cDc (ell : ℕ) (ρ cw kZ kW : ℝ) : ℝ :=
  2 * cYc ell ρ cw kZ kW * (kapK ell ρ * kZ / Real.sqrt cw) + (kapK ell ρ * kZ) ^ 2 / cw + nuD ell ρ * kW ^ 2 / cw

noncomputable def cDc' (ell : ℕ) (ρ cw kZ kW θ' d1 : ℝ) : ℝ :=
  2 * (cYc ell ρ cw kZ kW + d1 / Real.sqrt cw) * (Real.exp (2 * θ') * kapK ell ρ * kZ / Real.sqrt cw)
    + (Real.exp (2 * θ') * kapK ell ρ * kZ) ^ 2 / cw + Real.exp (2 * θ') * nuD ell ρ * kW ^ 2 / cw

noncomputable def d1c (ell : ℕ) (θ' : ℝ) : ℝ := Real.sqrt 12 * (ell : ℝ) * (Real.exp θ' - 1)

noncomputable def d3c (ell : ℕ) (a Sstar θ' : ℝ) : ℝ :=
  Real.sqrt (a * Estar ell Sstar ^ 2 * (Real.exp (6 * (ell : ℝ) * θ') - 1) ^ 2 * (1944 * (ell : ℝ) ^ 2))

theorem kapK_nonneg (ell : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) : 0 ≤ kapK ell ρ := by unfold kapK; positivity
theorem nuD_nonneg (ell : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) : 0 ≤ nuD ell ρ := by unfold nuD; positivity

/-! ## 2. the bounds at one configuration -/

/-- the `e^{−σ}` norm on `E₀` -/
noncomputable def NnE {L : PeriodicLatticeExtent} (G : TowerGeom L) (x : ↥(bondSupp G)) : ℝ :=
  ‖bondWt (-sigG G) (iE G x)‖

namespace CTData
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {W : ℕ}
  (D : CTData ell M R k S W) (hell0 : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu))
  (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k D.U ρ)
  (hεγ : D.epsG * D.γ ≤ 1) (hcG : 0 < D.cG)
include D

theorem kZc_nonneg (hcG : 0 < D.cG) : 0 ≤ D.kZc := by
  unfold kZc; have := D.cs_pos; have := D.nX_nonneg; have := D.K3_nonneg; have := D.ell_pos; positivity

theorem kWc_nonneg (hcG : 0 < D.cG) : 0 ≤ D.kWc := by
  unfold kWc; have := D.cs_pos; have := D.nX_nonneg; have := D.K3_nonneg; have := D.ell_pos; have := D.dD_nonneg
  positivity

include hρ hreg hεγ hcG in
theorem Kz_le (x : ↥(bondSupp (geomOf ell k S))) :
    ‖Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) x‖ ≤ kapK ell ρ * D.kZc * NnE (geomOf ell k S) x := by
  have hc := curv_strat D.hS D.hell D.hR D.hM D.U ρ hρ hreg
    (Gp (geomOf ell k S) D.U D.a (Tfull (geomOf ell k S) D.U (iE (geomOf ell k S) x)))
  have hz := D.ZC_bound (fun _ => (0 : ℝ)) D.ok0P D.ok0M D.ok0N hεγ hcG (iE (geomOf ell k S) x)
  rw [D.ZC_zero] at hz
  have e : Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) x
      = plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 D.U (Dm (geomOf ell k S) D.U
          (Gp (geomOf ell k S) D.U D.a (Tfull (geomOf ell k S) D.U (iE (geomOf ell k S) x))))) := rfl
  rw [e]
  have hk0 : 0 ≤ Real.sqrt 12 * ρ * (ell : ℝ) ^ 4 := by positivity
  have h1 : ‖plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 D.U (Dm (geomOf ell k S) D.U
          (Gp (geomOf ell k S) D.U D.a (Tfull (geomOf ell k S) D.U (iE (geomOf ell k S) x)))))‖
      ≤ Real.sqrt 12 * ρ * (ell : ℝ) ^ 4 * ‖siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S)))
          (Gp (geomOf ell k S) D.U D.a (Tfull (geomOf ell k S) D.U (iE (geomOf ell k S) x)))‖ := by
    have hR : 0 ≤ Real.sqrt 12 * ρ * (ell : ℝ) ^ 4 * ‖siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S)))
          (Gp (geomOf ell k S) D.U D.a (Tfull (geomOf ell k S) D.U (iE (geomOf ell k S) x)))‖ := by positivity
    have hsq : (Real.sqrt 12 * ρ * (ell : ℝ) ^ 4 * ‖siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S)))
          (Gp (geomOf ell k S) D.U D.a (Tfull (geomOf ell k S) D.U (iE (geomOf ell k S) x)))‖) ^ 2
        = 12 * ρ ^ 2 * (ell : ℝ) ^ 8 * ‖siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S)))
          (Gp (geomOf ell k S) D.U D.a (Tfull (geomOf ell k S) D.U (iE (geomOf ell k S) x)))‖ ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]; ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).mp (hc.trans hsq.symm.le)
  refine h1.trans ?_
  unfold kapK NnE
  calc Real.sqrt 12 * ρ * (ell : ℝ) ^ 4 * ‖siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S)))
          (Gp (geomOf ell k S) D.U D.a (Tfull (geomOf ell k S) D.U (iE (geomOf ell k S) x)))‖
      ≤ Real.sqrt 12 * ρ * (ell : ℝ) ^ 4 * (D.kZc * ‖bondWt (-sigG (geomOf ell k S)) (iE (geomOf ell k S) x)‖) :=
        mul_le_mul_of_nonneg_left hz hk0
    _ = _ := by ring

include hρ hreg in
theorem dp_le (u v : BondFnL2 (scaleUp ell k Lu)) :
    |deltaPrimeBilL2NormLoc D.U (plaqIn (S.Om 0)) u v|
      ≤ nuD ell ρ * (‖bondWt (-sigG (geomOf ell k S)) u‖ * ‖bondWt (-sigG (geomOf ell k S)) v‖) := by
  have h := dp_cj D.hS D.hell D.hR D.hM D.U ρ hρ hreg (fun _ => (0 : ℝ)) 0 (fun x μ => by simp) u v
  rw [show (-(fun _ : PeriodicLatticeSite (scaleUp ell k Lu) => (0 : ℝ))) = fun _ => (0 : ℝ) from by funext x; simp,
    bondWt_zero_fn, bondWt_zero_fn, mul_zero, Real.exp_zero, one_mul] at h
  unfold nuD; exact h

include hεγ hcG in
theorem Wb_le (x : ↥(bondSupp (geomOf ell k S))) :
    ‖bondWt (-sigG (geomOf ell k S)) (Wb (geomOf ell k S) D.U D.a x)‖ ≤ D.kWc * NnE (geomOf ell k S) x := by
  have h := D.WC_bound (fun _ => (0 : ℝ)) D.ok0P D.ok0M D.ok0N hεγ hcG (iE (geomOf ell k S) x)
  rw [D.WC_zero] at h
  exact h


/-! ## 3. W4 and the form bounds -/

section form
variable (cw : ℝ) (hcw : 0 < cw)
  (hW4 : ∀ A : ↥(bondSupp (geomOf ell k S)),
    cw * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv A⟫)
include hcw hW4

theorem NE (x : ↥(bondSupp (geomOf ell k S))) :
    cw * NnE (geomOf ell k S) x ^ 2 ≤ ⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv x⟫ := by
  have h1 := N_le_wnorm D.hS hell0 (iE (geomOf ell k S) x)
  have h2 := hW4 x
  unfold NnE
  have : cw * ‖bondWt (-sigG (geomOf ell k S)) (iE (geomOf ell k S) x)‖ ^ 2
      ≤ cw * AdalyFormal.M1.wnormSq S ell k (x : BondFnL2 (scaleUp ell k Lu)) := mul_le_mul_of_nonneg_left h1 hcw.le
  linarith

theorem E_nonneg (x : ↥(bondSupp (geomOf ell k S))) :
    0 ≤ ⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv x⟫ :=
  le_trans (by have := NnE (geomOf ell k S) x; positivity) (D.NE hell0 Lam cw hcw hW4 x)

theorem Nn_le (x : ↥(bondSupp (geomOf ell k S))) :
    NnE (geomOf ell k S) x ≤ Real.sqrt ⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv x⟫ / Real.sqrt cw := by
  have h := D.NE hell0 Lam cw hcw hW4 x
  have hsc : 0 < Real.sqrt cw := Real.sqrt_pos.mpr hcw
  rw [le_div_iff₀ hsc]
  rw [← Real.sqrt_sq (show 0 ≤ NnE (geomOf ell k S) x from norm_nonneg _), ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (by rw [mul_comm]; exact h)

include hρ hreg hεγ hcG in
/-- **`‖Y1 x‖ ≤ cY √E`** -/
theorem Y1_le (x : ↥(bondSupp (geomOf ell k S))) :
    ‖Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) x‖
      ≤ cYc ell ρ cw D.kZc D.kWc * Real.sqrt ⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv x⟫ := by
  set E := ⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv x⟫ with hE
  have hE0 : 0 ≤ E := D.E_nonneg hell0 Lam cw hcw hW4 x
  have hbil := ginv_bil hell0 S D.U D.a D.hp.ha.le Lam D.hp.hu x x
  rw [← hE] at hbil
  set y1 := Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) x
  set kz := Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) x
  have hdp := D.dp_le ρ hρ hreg (Wb (geomOf ell k S) D.U D.a x) (Wb (geomOf ell k S) D.U D.a x)
  have hwb := D.Wb_le hεγ hcG x
  have hN := D.Nn_le hell0 Lam cw hcw hW4 x
  have hNE := D.NE hell0 Lam cw hcw hW4 x
  have hkz := D.Kz_le ρ hρ hreg hεγ hcG x
  have hnu := nuD_nonneg ell ρ hρ
  have hkW := norm_nonneg (bondWt (-sigG (geomOf ell k S)) (Wb (geomOf ell k S) D.U D.a x))
  have hNn0 : 0 ≤ NnE (geomOf ell k S) x := norm_nonneg _
  -- ‖y1 − kz‖² ≤ E + |Δ'| ≤ (1 + ν kW²/cw) E
  have hsq : ‖y1 - kz‖ ^ 2 ≤ (1 + nuD ell ρ * D.kWc ^ 2 / cw) * E := by
    have e1 : ‖y1 - kz‖ ^ 2 = ‖y1‖ ^ 2 - 2 * ⟪y1, kz⟫ + ‖kz‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm kz y1]; ring
    have e2 : E = ‖y1‖ ^ 2 + ‖Y2 (geomOf ell k S) D.U x‖ ^ 2 + ‖Y3 (geomOf ell k S) D.U D.a x‖ ^ 2
        + (-2 * ⟪y1, kz⟫ + ‖kz‖ ^ 2
          + deltaPrimeBilL2NormLoc D.U (plaqIn (S.Om 0)) (Wb (geomOf ell k S) D.U D.a x) (Wb (geomOf ell k S) D.U D.a x)) := by
      rw [hbil, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      unfold Δg
      rw [real_inner_self_eq_norm_sq, real_inner_comm kz y1]; ring
    have hdp' : |deltaPrimeBilL2NormLoc D.U (plaqIn (S.Om 0)) (Wb (geomOf ell k S) D.U D.a x) (Wb (geomOf ell k S) D.U D.a x)|
        ≤ nuD ell ρ * D.kWc ^ 2 * NnE (geomOf ell k S) x ^ 2 := by
      refine hdp.trans ?_
      have := mul_le_mul hwb hwb hkW (mul_nonneg (D.kWc_nonneg hcG) hNn0)
      calc nuD ell ρ * (‖bondWt (-sigG (geomOf ell k S)) (Wb (geomOf ell k S) D.U D.a x)‖
            * ‖bondWt (-sigG (geomOf ell k S)) (Wb (geomOf ell k S) D.U D.a x)‖)
          ≤ nuD ell ρ * (D.kWc * NnE (geomOf ell k S) x * (D.kWc * NnE (geomOf ell k S) x)) := mul_le_mul_of_nonneg_left this hnu
        _ = _ := by ring
    have hN2 : NnE (geomOf ell k S) x ^ 2 ≤ E / cw := by rw [le_div_iff₀ hcw]; linarith
    have hfin : nuD ell ρ * D.kWc ^ 2 * NnE (geomOf ell k S) x ^ 2 ≤ nuD ell ρ * D.kWc ^ 2 / cw * E := by
      have := mul_le_mul_of_nonneg_left hN2 (show 0 ≤ nuD ell ρ * D.kWc ^ 2 by positivity)
      calc _ ≤ nuD ell ρ * D.kWc ^ 2 * (E / cw) := this
        _ = _ := by ring
    have hab := (abs_le.mp hdp').1
    have hy2 := sq_nonneg ‖Y2 (geomOf ell k S) D.U x‖
    have hy3 := sq_nonneg ‖Y3 (geomOf ell k S) D.U D.a x‖
    rw [e1]
    nlinarith
  have hq : 0 ≤ 1 + nuD ell ρ * D.kWc ^ 2 / cw := by positivity
  have h1 : ‖y1 - kz‖ ≤ Real.sqrt (1 + nuD ell ρ * D.kWc ^ 2 / cw) * Real.sqrt E := by
    rw [← Real.sqrt_mul hq, ← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hsq
  have h2 : ‖kz‖ ≤ kapK ell ρ * D.kZc / Real.sqrt cw * Real.sqrt E := by
    refine hkz.trans ?_
    have hk0 : 0 ≤ kapK ell ρ * D.kZc := mul_nonneg (kapK_nonneg ell ρ hρ) (D.kZc_nonneg hcG)
    calc kapK ell ρ * D.kZc * NnE (geomOf ell k S) x ≤ kapK ell ρ * D.kZc * (Real.sqrt E / Real.sqrt cw) :=
          mul_le_mul_of_nonneg_left hN hk0
      _ = _ := by ring
  have h3 : ‖y1‖ ≤ ‖y1 - kz‖ + ‖kz‖ := by
    have := norm_add_le (y1 - kz) kz; rwa [sub_add_cancel] at this
  unfold cYc
  calc ‖y1‖ ≤ ‖y1 - kz‖ + ‖kz‖ := h3
    _ ≤ Real.sqrt (1 + nuD ell ρ * D.kWc ^ 2 / cw) * Real.sqrt E + kapK ell ρ * D.kZc / Real.sqrt cw * Real.sqrt E :=
        add_le_add h1 h2
    _ = _ := by ring

end form

/-! ## 4. the conjugated pieces and the differences -/

section conj
variable (θ' : ℝ) (hθ' : 0 ≤ θ')
  (hL : ∀ (x : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3),
    |D.χ (periodicLatticeShift x μ) - D.χ x| ≤ θ' / (ell : ℝ) ^ AdalyFormal.M1.strat S k x)
include hθ' hL

theorem hL_G (ξ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (hξ : ξ = D.χ ∨ ξ = -D.χ)
    (x : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3) :
    |ξ x - ξ (periodicLatticeShift x μ)| ≤ θ' / (ell : ℝ) ^ stratG (geomOf ell k S) x := by
  have h := hL x μ
  rw [strat_eq_stratG (show 0 < ell by have := D.hell; omega) D.hS] at h
  rcases hξ with rfl | rfl
  · rw [abs_sub_comm]; exact h
  · simp only [Pi.neg_apply]; rw [show -D.χ x - -D.χ (periodicLatticeShift x μ) = D.χ (periodicLatticeShift x μ) - D.χ x by ring]
    exact h

theorem hL_c (ξ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (hξ : ξ = D.χ ∨ ξ = -D.χ)
    (x : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3) : |ξ x - ξ (periodicLatticeShift x μ)| ≤ θ' := by
  refine (D.hL_G θ' hθ' hL ξ hξ x μ).trans ?_
  rw [div_le_iff₀ (by have := D.ell_pos; positivity)]
  have := one_le_pow₀ (n := stratG (geomOf ell k S) x) (show (1 : ℝ) ≤ ell by exact_mod_cast (show 1 ≤ ell by have := D.hell; omega))
  nlinarith

theorem hL_s (ξ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (hξ : ξ = D.χ ∨ ξ = -D.χ)
    (x : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3) :
    |ξ (periodicLatticeShift x μ) - ξ x| ≤ θ' / (ell : ℝ) ^ AdalyFormal.M1.strat S k x := by
  rcases hξ with rfl | rfl
  · exact hL x μ
  · simp only [Pi.neg_apply]; rw [show -D.χ (periodicLatticeShift x μ) - -D.χ x = -(D.χ (periodicLatticeShift x μ) - D.χ x) by ring,
      abs_neg]; exact hL x μ

include hρ hreg hεγ hcG in
/-- `‖e^{ξ} Kz e^{−ξ} y‖ ≤ e^{2θ'} κK kZ ‖Ny‖` -/
theorem Kz_cjp (y : ↥(bondSupp (geomOf ell k S))) :
    ‖plaqWt D.χ (Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) (eW (geomOf ell k S) (-D.χ) y))‖
      ≤ Real.exp (2 * θ') * kapK ell ρ * D.kZc * NnE (geomOf ell k S) y := by
  have e : plaqWt D.χ (Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) (eW (geomOf ell k S) (-D.χ) y))
      = plaqMul (fun q => Real.exp (D.χ q.1)) (plaqMask (plaqIn (S.Om 0))
          (curlCovariantLM_L2 D.U (Dm (geomOf ell k S) D.U (siteWt (-D.χ) (D.ZC D.χ (iE (geomOf ell k S) y)))))) := by
    rw [plaqWt_eq_plaqMul, ← D.GpT_conj, ← iE_eW]; rfl
  rw [e]
  refine (curv_cj D.hS D.hell D.hR D.hM D.U ρ hρ hreg D.χ θ' (D.hL_c θ' hθ' hL D.χ (Or.inl rfl)) _).trans ?_
  have hz := D.ZC_bound D.χ D.okP D.okM D.okN1 hεγ hcG (iE (geomOf ell k S) y)
  have h0 : 0 ≤ Real.exp (2 * θ') * (Real.sqrt 12 * ρ * (ell : ℝ) ^ 4) := by positivity
  calc Real.exp (2 * θ') * (Real.sqrt 12 * ρ * (ell : ℝ) ^ 4)
        * ‖siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S))) (D.ZC D.χ (iE (geomOf ell k S) y))‖
      ≤ Real.exp (2 * θ') * (Real.sqrt 12 * ρ * (ell : ℝ) ^ 4) * (D.kZc * NnE (geomOf ell k S) y) := mul_le_mul_of_nonneg_left hz h0
    _ = _ := by unfold kapK; ring

include hρ hreg hεγ hcG in
theorem Kz_cjm (x : ↥(bondSupp (geomOf ell k S))) :
    ‖plaqWt (-D.χ) (Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) (eW (geomOf ell k S) D.χ x))‖
      ≤ Real.exp (2 * θ') * kapK ell ρ * D.kZc * NnE (geomOf ell k S) x := by
  have e : plaqWt (-D.χ) (Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) (eW (geomOf ell k S) D.χ x))
      = plaqMul (fun q => Real.exp ((-D.χ) q.1)) (plaqMask (plaqIn (S.Om 0))
          (curlCovariantLM_L2 D.U (Dm (geomOf ell k S) D.U (siteWt (-(-D.χ)) (D.ZC (-D.χ) (iE (geomOf ell k S) x)))))) := by
    rw [plaqWt_eq_plaqMul, ← D.GpT_conj, neg_neg, ← iE_eW]; rfl
  rw [e]
  refine (curv_cj D.hS D.hell D.hR D.hM D.U ρ hρ hreg (-D.χ) θ' (D.hL_c θ' hθ' hL (-D.χ) (Or.inr rfl)) _).trans ?_
  have hz := D.ZC_bound (-D.χ) D.okM D.okMM D.okN2 hεγ hcG (iE (geomOf ell k S) x)
  have h0 : 0 ≤ Real.exp (2 * θ') * (Real.sqrt 12 * ρ * (ell : ℝ) ^ 4) := by positivity
  calc Real.exp (2 * θ') * (Real.sqrt 12 * ρ * (ell : ℝ) ^ 4)
        * ‖siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S))) (D.ZC (-D.χ) (iE (geomOf ell k S) x))‖
      ≤ Real.exp (2 * θ') * (Real.sqrt 12 * ρ * (ell : ℝ) ^ 4) * (D.kZc * NnE (geomOf ell k S) x) := mul_le_mul_of_nonneg_left hz h0
    _ = _ := by unfold kapK; ring

include hρ hreg hεγ hcG in
/-- the conjugated `Δ'(W·, W·)` -/
theorem dpW_cj (x y : ↥(bondSupp (geomOf ell k S))) :
    |deltaPrimeBilL2NormLoc D.U (plaqIn (S.Om 0)) (Wb (geomOf ell k S) D.U D.a (eW (geomOf ell k S) D.χ x))
        (Wb (geomOf ell k S) D.U D.a (eW (geomOf ell k S) (-D.χ) y))|
      ≤ Real.exp (2 * θ') * nuD ell ρ * D.kWc ^ 2 * (NnE (geomOf ell k S) x * NnE (geomOf ell k S) y) := by
  have e1 : Wb (geomOf ell k S) D.U D.a (eW (geomOf ell k S) D.χ x)
      = bondWt D.χ (D.WC (-D.χ) (iE (geomOf ell k S) x)) := by
    show Wop (geomOf ell k S) D.U D.a (iE (geomOf ell k S) (eW (geomOf ell k S) D.χ x)) = _
    rw [iE_eW, D.W_conj]
  have e2 : Wb (geomOf ell k S) D.U D.a (eW (geomOf ell k S) (-D.χ) y)
      = bondWt (-D.χ) (D.WC D.χ (iE (geomOf ell k S) y)) := by
    show Wop (geomOf ell k S) D.U D.a (iE (geomOf ell k S) (eW (geomOf ell k S) (-D.χ) y)) = _
    rw [iE_eW, D.W_conj, neg_neg]
  rw [e1, e2]
  refine (dp_cj D.hS D.hell D.hR D.hM D.U ρ hρ hreg D.χ θ' (D.hL_c θ' hθ' hL D.χ (Or.inl rfl)) _ _).trans ?_
  have w1 := D.WC_bound (-D.χ) D.okM D.okMM D.okN2 hεγ hcG (iE (geomOf ell k S) x)
  have w2 := D.WC_bound D.χ D.okP D.okM D.okN1 hεγ hcG (iE (geomOf ell k S) y)
  have hkW := D.kWc_nonneg hcG
  have h0 : 0 ≤ Real.exp (2 * θ') * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) := by positivity
  have hm := mul_le_mul w1 w2 (norm_nonneg _) (mul_nonneg hkW (norm_nonneg _))
  calc Real.exp (2 * θ') * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4))
        * (‖bondWt (-sigG (geomOf ell k S)) (D.WC (-D.χ) (iE (geomOf ell k S) x))‖
          * ‖bondWt (-sigG (geomOf ell k S)) (D.WC D.χ (iE (geomOf ell k S) y))‖)
      ≤ Real.exp (2 * θ') * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) * (D.kWc * NnE (geomOf ell k S) x * (D.kWc * NnE (geomOf ell k S) y)) :=
        mul_le_mul_of_nonneg_left hm h0
    _ = _ := by unfold nuD; ring

/-- the curl difference -/
theorem Y1_diff (ξ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (hξ : ξ = D.χ ∨ ξ = -D.χ)
    (x : ↥(bondSupp (geomOf ell k S))) :
    ‖plaqWt ξ (Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) (eW (geomOf ell k S) (-ξ) x))
        - Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) x‖ ≤ d1c ell θ' * NnE (geomOf ell k S) x := by
  have e : plaqWt ξ (Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) (eW (geomOf ell k S) (-ξ) x))
        - Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) x
      = plaqMul (fun q => Real.exp (ξ q.1)) (plaqMask (plaqIn (S.Om 0))
            (curlCovariantLM_L2 D.U (bondWt (-ξ) (iE (geomOf ell k S) x))))
        - plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 D.U (iE (geomOf ell k S) x)) := by
    rw [plaqWt_eq_plaqMul, ← iE_eW]; rfl
  rw [e]
  exact curl_cj_diff D.hS D.hell D.hR D.hM D.U ξ θ' hθ' (D.hL_G θ' hθ' hL ξ hξ) _

end conj

/-! ## 5. the split -/

theorem pair_plaq (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (u v : PlaqFnL2 (scaleUp ell k Lu)) :
    ⟪u, v⟫ = ⟪plaqWt (-φ) u, plaqWt φ v⟫ := by
  rw [plaqWt_symm, plaqWt_cancel_neg]

theorem Nn_eq (x : ↥(bondSupp (geomOf ell k S))) :
    ‖eW (geomOf ell k S) (-sigG (geomOf ell k S)) x‖ = NnE (geomOf ell k S) x := by
  rw [norm_E, iE_eW]; rfl

section split
variable (cw : ℝ) (hcw : 0 < cw)
  (hW4 : ∀ A : ↥(bondSupp (geomOf ell k S)),
    cw * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv A⟫)
  (θ' : ℝ) (hθ' : 0 ≤ θ')
  (hL : ∀ (x : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3),
    |D.χ (periodicLatticeShift x μ) - D.χ x| ≤ θ' / (ell : ℝ) ^ AdalyFormal.M1.strat S k x)
  (hR8 : 8 * ell ≤ R) (Sstar : ℝ) (Dr : RegData ell k Lu S D.U Sstar)

include hρ hreg hεγ hcG hcw hW4 hθ' hL in
/-- the form-relative remainder bound -/
theorem Dg0 (x y : ↥(bondSupp (geomOf ell k S))) :
    |Δg (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) x y|
      ≤ cDc ell ρ cw D.kZc D.kWc
        * (Real.sqrt ⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv x⟫
          * Real.sqrt ⟪y, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv y⟫) := by
  set Ex := Real.sqrt ⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv x⟫
  set Ey := Real.sqrt ⟪y, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv y⟫
  have hEx : 0 ≤ Ex := Real.sqrt_nonneg _
  have hEy : 0 ≤ Ey := Real.sqrt_nonneg _
  have hsc : 0 < Real.sqrt cw := Real.sqrt_pos.mpr hcw
  have hY1x := D.Y1_le hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 x
  have hY1y := D.Y1_le hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 y
  have hKx := D.Kz_le ρ hρ hreg hεγ hcG x
  have hKy := D.Kz_le ρ hρ hreg hεγ hcG y
  have hNx := D.Nn_le hell0 Lam cw hcw hW4 x
  have hNy := D.Nn_le hell0 Lam cw hcw hW4 y
  have hdp := D.dp_le ρ hρ hreg (Wb (geomOf ell k S) D.U D.a x) (Wb (geomOf ell k S) D.U D.a y)
  have hWx := D.Wb_le hεγ hcG x
  have hWy := D.Wb_le hεγ hcG y
  have hk := mul_nonneg (kapK_nonneg ell ρ hρ) (D.kZc_nonneg hcG)
  have hkW := D.kWc_nonneg hcG
  have hnu := nuD_nonneg ell ρ hρ
  have hcY : 0 ≤ cYc ell ρ cw D.kZc D.kWc := by unfold cYc; positivity
  -- Kz in √E
  have hKx' : ‖Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) x‖ ≤ (kapK ell ρ * D.kZc) / Real.sqrt cw * Ex := by
    refine hKx.trans ?_
    calc (kapK ell ρ * D.kZc) * NnE (geomOf ell k S) x ≤ (kapK ell ρ * D.kZc) * (Ex / Real.sqrt cw) := mul_le_mul_of_nonneg_left hNx hk
      _ = _ := by ring
  have hKy' : ‖Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) y‖ ≤ (kapK ell ρ * D.kZc) / Real.sqrt cw * Ey := by
    refine hKy.trans ?_
    calc (kapK ell ρ * D.kZc) * NnE (geomOf ell k S) y ≤ (kapK ell ρ * D.kZc) * (Ey / Real.sqrt cw) := mul_le_mul_of_nonneg_left hNy hk
      _ = _ := by ring
  have hWW : nuD ell ρ * (‖bondWt (-sigG (geomOf ell k S)) (Wb (geomOf ell k S) D.U D.a x)‖
        * ‖bondWt (-sigG (geomOf ell k S)) (Wb (geomOf ell k S) D.U D.a y)‖)
      ≤ nuD ell ρ * D.kWc ^ 2 / cw * (Ex * Ey) := by
    have h1 := mul_le_mul hWx hWy (norm_nonneg _) (mul_nonneg hkW (norm_nonneg _))
    have h2 := mul_le_mul hNx hNy (norm_nonneg _) (div_nonneg hEx hsc.le)
    have hcw' : Real.sqrt cw * Real.sqrt cw = cw := Real.mul_self_sqrt hcw.le
    calc _ ≤ nuD ell ρ * (D.kWc * NnE (geomOf ell k S) x * (D.kWc * NnE (geomOf ell k S) y)) := mul_le_mul_of_nonneg_left h1 hnu
      _ = nuD ell ρ * D.kWc ^ 2 * (NnE (geomOf ell k S) x * NnE (geomOf ell k S) y) := by ring
      _ ≤ nuD ell ρ * D.kWc ^ 2 * (Ex / Real.sqrt cw * (Ey / Real.sqrt cw)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by rw [div_mul_div_comm, Real.mul_self_sqrt hcw.le]; ring
  unfold Δg
  have i1 := abs_real_inner_le_norm (Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) x) (Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) y)
  have i2 := abs_real_inner_le_norm (Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) x) (Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) y)
  have i3 := abs_real_inner_le_norm (Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) x) (Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) y)
  have m1 := mul_le_mul hY1x hKy' (norm_nonneg _) (by positivity)
  have m2 := mul_le_mul hKx' hY1y (norm_nonneg _) (by positivity)
  have m3 := mul_le_mul hKx' hKy' (norm_nonneg _) (by positivity)
  have hfin : cDc ell ρ cw D.kZc D.kWc * (Ex * Ey)
      = cYc ell ρ cw D.kZc D.kWc * Ex * ((kapK ell ρ * D.kZc) / Real.sqrt cw * Ey) + (kapK ell ρ * D.kZc) / Real.sqrt cw * Ex * (cYc ell ρ cw D.kZc D.kWc * Ey)
        + (kapK ell ρ * D.kZc) / Real.sqrt cw * Ex * ((kapK ell ρ * D.kZc) / Real.sqrt cw * Ey) + nuD ell ρ * D.kWc ^ 2 / cw * (Ex * Ey) := by
    have hsq : (kapK ell ρ * D.kZc) ^ 2 / cw = (kapK ell ρ * D.kZc) / Real.sqrt cw * ((kapK ell ρ * D.kZc) / Real.sqrt cw) := by
      rw [div_mul_div_comm, Real.mul_self_sqrt hcw.le, sq]
    unfold cDc
    rw [hsq]; ring
  rw [hfin]
  have t := abs_add_le (-⟪Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) x, Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) y⟫
      - ⟪Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) x, Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) y⟫
      + ⟪Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) x, Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) y⟫)
    (deltaPrimeBilL2NormLoc D.U (plaqIn (S.Om 0)) (Wb (geomOf ell k S) D.U D.a x) (Wb (geomOf ell k S) D.U D.a y))
  have t2 := abs_add_le (-⟪Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) x, Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) y⟫
      - ⟪Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) x, Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) y⟫)
    ⟪Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) x, Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) y⟫
  have t3 := abs_sub (-⟪Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) x, Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) y⟫)
    ⟪Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) x, Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) y⟫
  rw [abs_neg] at t3
  linarith [hdp.trans hWW]

include hρ hreg hεγ hcG hcw hW4 hθ' hL in
/-- the conjugated remainder bound -/
theorem Dg1 (x y : ↥(bondSupp (geomOf ell k S))) :
    |Δg (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) (eW (geomOf ell k S) D.χ x) (eW (geomOf ell k S) (-D.χ) y)|
      ≤ cDc' ell ρ cw D.kZc D.kWc θ' (d1c ell θ')
        * (Real.sqrt ⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv x⟫
          * Real.sqrt ⟪y, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv y⟫) := by
  set Ex := Real.sqrt ⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv x⟫
  set Ey := Real.sqrt ⟪y, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv y⟫
  have hEx : 0 ≤ Ex := Real.sqrt_nonneg _
  have hEy : 0 ≤ Ey := Real.sqrt_nonneg _
  have hsc : 0 < Real.sqrt cw := Real.sqrt_pos.mpr hcw
  set y1x := plaqWt (-D.χ) (Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) (eW (geomOf ell k S) D.χ x))
  set y1y := plaqWt D.χ (Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) (eW (geomOf ell k S) (-D.χ) y))
  set kx := plaqWt (-D.χ) (Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) (eW (geomOf ell k S) D.χ x))
  set ky := plaqWt D.χ (Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) (eW (geomOf ell k S) (-D.χ) y))
  have hcY : 0 ≤ cYc ell ρ cw D.kZc D.kWc := by
    unfold cYc; have := kapK_nonneg ell ρ hρ; have := D.kZc_nonneg hcG; have := nuD_nonneg ell ρ hρ; positivity
  have hd1 : 0 ≤ d1c ell θ' :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) D.ell_pos.le) (by linarith [Real.add_one_le_exp θ'])
  -- the four pieces
  have hy1x : ‖y1x‖ ≤ (cYc ell ρ cw D.kZc D.kWc + d1c ell θ' / Real.sqrt cw) * Ex := by
    have h1 := D.Y1_diff θ' hθ' hL (-D.χ) (Or.inr rfl) x
    rw [neg_neg] at h1
    have h2 := D.Y1_le hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 x
    have h3 := D.Nn_le hell0 Lam cw hcw hW4 x
    have h4 : ‖y1x‖ ≤ ‖Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) x‖ + d1c ell θ' * NnE (geomOf ell k S) x := by
      have := norm_add_le (y1x - Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) x) (Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) x)
      rw [sub_add_cancel] at this; linarith
    calc ‖y1x‖ ≤ ‖Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) x‖ + d1c ell θ' * NnE (geomOf ell k S) x := h4
      _ ≤ cYc ell ρ cw D.kZc D.kWc * Ex + d1c ell θ' * (Ex / Real.sqrt cw) :=
          add_le_add h2 (mul_le_mul_of_nonneg_left h3 hd1)
      _ = _ := by ring
  have hy1y : ‖y1y‖ ≤ (cYc ell ρ cw D.kZc D.kWc + d1c ell θ' / Real.sqrt cw) * Ey := by
    have h1 := D.Y1_diff θ' hθ' hL D.χ (Or.inl rfl) y
    have h2 := D.Y1_le hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 y
    have h3 := D.Nn_le hell0 Lam cw hcw hW4 y
    have h4 : ‖y1y‖ ≤ ‖Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) y‖ + d1c ell θ' * NnE (geomOf ell k S) y := by
      have := norm_add_le (y1y - Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) y) (Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) y)
      rw [sub_add_cancel] at this; linarith
    calc ‖y1y‖ ≤ ‖Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) y‖ + d1c ell θ' * NnE (geomOf ell k S) y := h4
      _ ≤ cYc ell ρ cw D.kZc D.kWc * Ey + d1c ell θ' * (Ey / Real.sqrt cw) :=
          add_le_add h2 (mul_le_mul_of_nonneg_left h3 hd1)
      _ = _ := by ring
  have hk0 : 0 ≤ Real.exp (2 * θ') * kapK ell ρ * D.kZc := by
    have := kapK_nonneg ell ρ hρ; have := D.kZc_nonneg hcG; positivity
  have hkx : ‖kx‖ ≤ Real.exp (2 * θ') * kapK ell ρ * D.kZc / Real.sqrt cw * Ex := by
    refine (D.Kz_cjm ρ hρ hreg hεγ hcG θ' hθ' hL x).trans ?_
    calc Real.exp (2 * θ') * kapK ell ρ * D.kZc * NnE (geomOf ell k S) x
        ≤ Real.exp (2 * θ') * kapK ell ρ * D.kZc * (Ex / Real.sqrt cw) :=
          mul_le_mul_of_nonneg_left (D.Nn_le hell0 Lam cw hcw hW4 x) hk0
      _ = _ := by ring
  have hky : ‖ky‖ ≤ Real.exp (2 * θ') * kapK ell ρ * D.kZc / Real.sqrt cw * Ey := by
    refine (D.Kz_cjp ρ hρ hreg hεγ hcG θ' hθ' hL y).trans ?_
    calc Real.exp (2 * θ') * kapK ell ρ * D.kZc * NnE (geomOf ell k S) y
        ≤ Real.exp (2 * θ') * kapK ell ρ * D.kZc * (Ey / Real.sqrt cw) :=
          mul_le_mul_of_nonneg_left (D.Nn_le hell0 Lam cw hcw hW4 y) hk0
      _ = _ := by ring
  have hdpW := D.dpW_cj ρ hρ hreg hεγ hcG θ' hθ' hL x y
  have hNN : NnE (geomOf ell k S) x * NnE (geomOf ell k S) y ≤ Ex * Ey / cw := by
    have := mul_le_mul (D.Nn_le hell0 Lam cw hcw hW4 x) (D.Nn_le hell0 Lam cw hcw hW4 y) (norm_nonneg _)
      (div_nonneg hEx hsc.le)
    have hcw' : Real.sqrt cw * Real.sqrt cw = cw := Real.mul_self_sqrt hcw.le
    calc NnE (geomOf ell k S) x * NnE (geomOf ell k S) y ≤ Ex / Real.sqrt cw * (Ey / Real.sqrt cw) := this
      _ = Ex * Ey / cw := by rw [div_mul_div_comm, Real.mul_self_sqrt hcw.le]
  have hdpW' : |deltaPrimeBilL2NormLoc D.U (plaqIn (S.Om 0)) (Wb (geomOf ell k S) D.U D.a (eW (geomOf ell k S) D.χ x)) (Wb (geomOf ell k S) D.U D.a (eW (geomOf ell k S) (-D.χ) y))|
      ≤ Real.exp (2 * θ') * nuD ell ρ * D.kWc ^ 2 * (Ex * Ey / cw) :=
    hdpW.trans (mul_le_mul_of_nonneg_left hNN (by have := nuD_nonneg ell ρ hρ; positivity))
  -- rewrite the three plaquette pairings with the weights
  unfold Δg
  rw [D.pair_plaq D.χ (Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) (eW (geomOf ell k S) D.χ x)) (Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) (eW (geomOf ell k S) (-D.χ) y)),
    D.pair_plaq D.χ (Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) (eW (geomOf ell k S) D.χ x)) (Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0)) (eW (geomOf ell k S) (-D.χ) y)),
    D.pair_plaq D.χ (Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) (eW (geomOf ell k S) D.χ x)) (Kz (geomOf ell k S) D.U D.a (plaqIn (S.Om 0)) (eW (geomOf ell k S) (-D.χ) y))]
  have i1 := abs_real_inner_le_norm y1x ky
  have i2 := abs_real_inner_le_norm kx y1y
  have i3 := abs_real_inner_le_norm kx ky
  have hA : 0 ≤ cYc ell ρ cw D.kZc D.kWc + d1c ell θ' / Real.sqrt cw := by positivity
  have m1 := mul_le_mul hy1x hky (norm_nonneg _) (by positivity)
  have m2 := mul_le_mul hkx hy1y (norm_nonneg _) (by positivity)
  have m3 := mul_le_mul hkx hky (norm_nonneg _) (by positivity)
  have hfin : cDc' ell ρ cw D.kZc D.kWc θ' (d1c ell θ') * (Ex * Ey)
      = (cYc ell ρ cw D.kZc D.kWc + d1c ell θ' / Real.sqrt cw) * Ex
          * (Real.exp (2 * θ') * kapK ell ρ * D.kZc / Real.sqrt cw * Ey)
        + Real.exp (2 * θ') * kapK ell ρ * D.kZc / Real.sqrt cw * Ex
          * ((cYc ell ρ cw D.kZc D.kWc + d1c ell θ' / Real.sqrt cw) * Ey)
        + Real.exp (2 * θ') * kapK ell ρ * D.kZc / Real.sqrt cw * Ex
          * (Real.exp (2 * θ') * kapK ell ρ * D.kZc / Real.sqrt cw * Ey)
        + Real.exp (2 * θ') * nuD ell ρ * D.kWc ^ 2 * (Ex * Ey / cw) := by
    have hsq : (Real.exp (2 * θ') * kapK ell ρ * D.kZc) ^ 2 / cw
        = Real.exp (2 * θ') * kapK ell ρ * D.kZc / Real.sqrt cw * (Real.exp (2 * θ') * kapK ell ρ * D.kZc / Real.sqrt cw) := by
      rw [div_mul_div_comm, Real.mul_self_sqrt hcw.le, sq]
    unfold cDc'
    rw [hsq]; ring
  rw [hfin]
  have t := abs_add_le (-⟪y1x, ky⟫ - ⟪kx, y1y⟫ + ⟪kx, ky⟫)
    (deltaPrimeBilL2NormLoc D.U (plaqIn (S.Om 0)) (Wb (geomOf ell k S) D.U D.a (eW (geomOf ell k S) D.χ x)) (Wb (geomOf ell k S) D.U D.a (eW (geomOf ell k S) (-D.χ) y)))
  have t2 := abs_add_le (-⟪y1x, ky⟫ - ⟪kx, y1y⟫) ⟪kx, ky⟫
  have t3 := abs_sub (-⟪y1x, ky⟫) ⟪kx, y1y⟫
  rw [abs_neg] at t3
  linarith

end split

/-! ## 6. the `GSplit` instance and `hHB` -/

section inst
variable (cw : ℝ) (hcw : 0 < cw)
  (hW4 : ∀ A : ↥(bondSupp (geomOf ell k S)),
    cw * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv A⟫)
  (θ' : ℝ) (hθ' : 0 ≤ θ')
  (hL : ∀ (x : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3),
    |D.χ (periodicLatticeShift x μ) - D.χ x| ≤ θ' / (ell : ℝ) ^ AdalyFormal.M1.strat S k x)
  (hR8 : 8 * ell ≤ R) (Sstar : ℝ) (Dr : RegData ell k Lu S D.U Sstar)

theorem d1c_nonneg (θ' : ℝ) (hθ' : 0 ≤ θ') : 0 ≤ d1c ell θ' := by
  unfold d1c; have := Real.add_one_le_exp θ'; have := D.ell_pos
  have : 0 ≤ Real.exp θ' - 1 := by linarith
  positivity

theorem dTc_nonneg (hcG : 0 < D.cG) : 0 ≤ D.dTc D.θχ := by
  unfold dTc
  have := D.EX_nonneg; have := D.nX_nonneg; have := D.K3_nonneg; have := D.ell_pos; have := D.dG_nonneg
  have := D.EDX'_nonneg; have := D.hθχ
  have : 0 ≤ Real.exp D.θχ - 1 := by linarith [Real.add_one_le_exp D.θχ]
  positivity

include hεγ hcG in
theorem T_diffE (ξ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (hξ : ξ = D.χ ∨ ξ = -D.χ)
    (x : ↥(bondSupp (geomOf ell k S))) :
    ‖siteWt ξ (Tfull (geomOf ell k S) D.U (iE (geomOf ell k S) (eW (geomOf ell k S) (-ξ) x)))
        - Tfull (geomOf ell k S) D.U (iE (geomOf ell k S) x)‖ ≤ D.dTc D.θχ * NnE (geomOf ell k S) x := by
  rw [iE_eW]
  rcases hξ with rfl | rfl
  · exact D.TC_diff D.χ D.θχ D.δχ D.hθχ D.hχ D.okP D.okM hεγ hcG (iE (geomOf ell k S) x)
  · exact D.TC_diff (-D.χ) D.θχ D.δχ D.hθχ D.hχ.neg D.okM D.okMM hεγ hcG (iE (geomOf ell k S) x)

include hR8 hθ' hL in
theorem M_diffE (Sstar : ℝ) (Dr : RegData ell k Lu S D.U Sstar)
    (ξ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (hξ : ξ = D.χ ∨ ξ = -D.χ)
    (x : ↥(bondSupp (geomOf ell k S))) :
    ‖rowWt (geomOf ell k S) ξ (Ymass (geomOf ell k S) D.U D.a (iE (geomOf ell k S) (eW (geomOf ell k S) (-ξ) x)))
        - Ymass (geomOf ell k S) D.U D.a (iE (geomOf ell k S) x)‖ ≤ d3c ell D.a Sstar θ' * NnE (geomOf ell k S) x := by
  rw [iE_eW]
  have h := mass_cj_diff D.hS (show 0 < 1 by norm_num) (show 0 < M by have := D.hM; omega) D.hell D.hR
    (show (5 + 3) * 1 * ell ≤ R by omega) (le_refl 5) D.U Sstar Dr D.a D.hp.ha.le ξ θ' hθ'
    (D.hL_s θ' hθ' hL ξ hξ) (iE (geomOf ell k S) x)
  have hR : 0 ≤ d3c ell D.a Sstar θ' * NnE (geomOf ell k S) x := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).mp (h.trans (le_of_eq ?_))
  unfold d3c NnE
  rw [mul_pow, Real.sq_sqrt (by have := D.hp.ha; positivity)]

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 in
/-- **the genuine `Ginv` as a `GSplit`** -/
noncomputable def gsplit : GSplit ↥(bondSupp (geomOf ell k S)) (PlaqFnL2 (scaleUp ell k Lu))
    (SiteL2 (scaleUp ell k Lu)) (FSp (geomOf ell k S)) where
  Ginv := (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv
  Nw := eW (geomOf ell k S) (-sigG (geomOf ell k S))
  ωE := EWP (geomOf ell k S) D.χ
  Y1 := Y1 (geomOf ell k S) D.U (plaqIn (S.Om 0))
  Y2 := Y2 (geomOf ell k S) D.U
  Y3 := Y3 (geomOf ell k S) D.U D.a
  ω1 := plaqWP D.χ
  ω2 := siteWP D.χ
  ω3 := rowWP (geomOf ell k S) D.χ
  Δ := Δg (geomOf ell k S) D.U D.a (plaqIn (S.Om 0))
  cw := cw
  cΔ := cDc ell ρ cw D.kZc D.kWc
  cΔ' := cDc' ell ρ cw D.kZc D.kWc θ' (d1c ell θ')
  d1 := d1c ell θ'
  d2 := D.dTc D.θχ
  d3 := d3c ell D.a Sstar θ'
  hcw := hcw
  hcΔ := by
    unfold cDc cYc; have := kapK_nonneg ell ρ hρ; have := D.kZc_nonneg hcG; have := nuD_nonneg ell ρ hρ; positivity
  hcΔ' := by
    unfold cDc' cYc; have := kapK_nonneg ell ρ hρ; have := D.kZc_nonneg hcG; have := nuD_nonneg ell ρ hρ
    have := D.d1c_nonneg θ' hθ'; positivity
  hd1 := D.d1c_nonneg θ' hθ'
  hd2 := D.dTc_nonneg hcG
  hd3 := Real.sqrt_nonneg _
  hdec := fun x y => ginv_bil hell0 S D.U D.a D.hp.ha.le Lam D.hp.hu x y
  hcoer := fun f => by rw [D.Nn_eq]; exact D.NE hell0 Lam cw hcw hW4 f
  hΔ0 := fun x y => D.Dg0 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL x y
  hΔ1 := fun x y => D.Dg1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL x y
  hp1 := fun x => by
    rw [D.Nn_eq, ContinuousLinearMap.sub_apply, cjp_apply]
    exact D.Y1_diff θ' hθ' hL D.χ (Or.inl rfl) x
  hm1 := fun x => by
    rw [D.Nn_eq, ContinuousLinearMap.sub_apply]
    have h := D.Y1_diff θ' hθ' hL (-D.χ) (Or.inr rfl) x
    rw [neg_neg] at h
    exact h
  hp2 := fun x => by
    rw [D.Nn_eq, ContinuousLinearMap.sub_apply, cjp_apply]
    exact D.T_diffE hεγ hcG D.χ (Or.inl rfl) x
  hm2 := fun x => by
    rw [D.Nn_eq, ContinuousLinearMap.sub_apply]
    have h := D.T_diffE hεγ hcG (-D.χ) (Or.inr rfl) x
    rw [neg_neg] at h
    exact h
  hp3 := fun x => by
    rw [D.Nn_eq, ContinuousLinearMap.sub_apply, cjp_apply]
    exact D.M_diffE θ' hθ' hL hR8 Sstar Dr D.χ (Or.inl rfl) x
  hm3 := fun x => by
    rw [D.Nn_eq, ContinuousLinearMap.sub_apply]
    have h := D.M_diffE θ' hθ' hL hR8 Sstar Dr (-D.χ) (Or.inr rfl) x
    rw [neg_neg] at h
    exact h

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 in
/-- **the form-relative Combes–Thomas bound of the genuine `Ginv`** (`hHB` of DC2) -/
theorem hHB_genuine (x y : ↥(bondSupp (geomOf ell k S))) :
    |⟪x, cjp (EWP (geomOf ell k S) D.χ) (EWP (geomOf ell k S) D.χ)
          (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv y⟫
        - ⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv y⟫|
      ≤ (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap
        * (Real.sqrt ⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv x⟫
          * Real.sqrt ⟪y, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv y⟫) :=
  (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).hHB_of_split x y

end inst
end CTData

#print axioms CTData.okP
#print axioms CTData.okM
#print axioms CTData.okMM
#print axioms CTData.okN1
#print axioms CTData.okN2
#print axioms CTData.ok0P
#print axioms CTData.ok0M
#print axioms CTData.ok0N
#print axioms CTData.ZC_zero
#print axioms CTData.WC_zero
#print axioms CTData.GpT_conj
#print axioms CTData.W_conj
#print axioms kapK
#print axioms nuD
#print axioms cYc
#print axioms cDc
#print axioms cDc'
#print axioms d1c
#print axioms d3c
#print axioms CTData.kZc_nonneg
#print axioms CTData.kWc_nonneg
#print axioms NnE
#print axioms CTData.Kz_le
#print axioms CTData.dp_le
#print axioms CTData.Wb_le
#print axioms CTData.NE
#print axioms CTData.E_nonneg
#print axioms CTData.Nn_le
#print axioms CTData.Y1_le
#print axioms CTData.hL_G
#print axioms CTData.hL_c
#print axioms CTData.hL_s
#print axioms CTData.Kz_cjp
#print axioms CTData.Kz_cjm
#print axioms CTData.dpW_cj
#print axioms CTData.Y1_diff
#print axioms CTData.pair_plaq
#print axioms CTData.Nn_eq
#print axioms CTData.Dg0
#print axioms CTData.Dg1
#print axioms CTData.d1c_nonneg
#print axioms CTData.dTc_nonneg
#print axioms CTData.T_diffE
#print axioms CTData.M_diffE
#print axioms CTData.gsplit
#print axioms CTData.hHB_genuine

end AdalyFormal.M1DStrat
