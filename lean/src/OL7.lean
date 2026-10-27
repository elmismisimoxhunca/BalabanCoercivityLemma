import OL6

/-!
# OL7 -- `G₁⁻¹ = G⁻¹ − Δ⁽²⁾`: split and Schur instance with `RowQ` in place of `RegData` (lane m2_oplayer_20261015)

DY4b (text copy from `gsplit1` on, every declaration renamed `…R`, `D.gsplit` → OL5 `gsplitR`).
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
open AdalyFormal.TowerLoc (Estar)
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply plaqMask_symm deltaPrimeBilL2NormLoc)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

section g1
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {W : ℕ}
  (D : CTData ell M R k S W) (hell0 : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu))
  (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k D.U ρ)
  (hεγ : D.epsG * D.γ ≤ 1) (hcG : 0 < D.cG)
  (cw : ℝ) (hcw : 0 < cw)
  (hW4 : ∀ A : ↥(bondSupp (geomOf ell k S)),
    cw * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv A⟫)
  (θ' : ℝ) (hθ' : 0 ≤ θ')
  (hL : ∀ (x : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3),
    |D.χ (periodicLatticeShift x μ) - D.χ x| ≤ θ' / (ell : ℝ) ^ AdalyFormal.M1.strat S k x)
  (hR8 : 8 * ell ≤ R) (Sstar : ℝ) (Dr : ∀ p : BIdx (geomOf ell k S), AdalyFormal.M2F123.RowQ ell k Lu S D.U Sstar p)
  (bN : ℝ) (hbN : 0 < bN)
  (hext : ∀ v : FSp (geomOf ell k S), ∃ g : ↥(bondSupp (geomOf ell k S)),
    (gparams ell k Lu hell0 S D.U D.a Lam).data.Q g = v ∧
      ⟪g, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv g⟫
        ≤ bN * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) D.a p)) v‖ ^ 2)
  (hQs : Function.Injective (gparams ell k Lu hell0 S D.U D.a Lam).data.Qs)
  (δ0 δ1 : ℝ) (hδ0 : 0 ≤ δ0) (hδ1 : 0 ≤ δ1) (hlt : δ0 < cw)
  (hD0 : ∀ x y : ↥(bondSupp (geomOf ell k S)), |⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws y⟫|
    ≤ δ0 * (nq S ell k (geomOf ell k S) x * nq S ell k (geomOf ell k S) y))
  (hD1 : ∀ x y : ↥(bondSupp (geomOf ell k S)),
    |⟪(EWP (geomOf ell k S) D.χ).w x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws ((EWP (geomOf ell k S) D.χ).wi y)⟫|
      ≤ δ1 * (nq S ell k (geomOf ell k S) x * nq S ell k (geomOf ell k S) y))
include D

/-- the perturbed split -/
noncomputable def gsplit1R : GSplit ↥(bondSupp (geomOf ell k S)) (PlaqFnL2 (scaleUp ell k Lu))
    (SiteL2 (scaleUp ell k Lu)) (FSp (geomOf ell k S)) :=
  (gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).pert ((gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws)
    (nq S ell k (geomOf ell k S)) cw δ0 δ1 (fun x => D.nq_nonneg x) (fun x => D.Nw_le_nq hell0 x)
    (fun x => D.W4_nq hell0 Lam cw hW4 x) hD0 hδ0 hlt hD1 hδ1

theorem gsplit1_GinvR : (gsplit1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0
    hD1).Ginv = (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws := rfl

include hcw hW4 hδ0 hδ1 hlt hD0 hD1 in
theorem G1_symmR (x y : ↥(bondSupp (geomOf ell k S))) :
    ⟪((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) x, y⟫ = ⟪x, ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) y⟫ := by
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  rw [((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv_symm (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) x y,
    ((gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2_spec (gparams ell k Lu hell0 S D.U D.a Lam).data_laws).1 x y]

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 Dr hδ0 hδ1 hlt hD0 hD1 in
theorem G1_coerR (x : ↥(bondSupp (geomOf ell k S))) :
    (cw - δ0) * (((ell : ℝ) ^ k)⁻¹) ^ 2 * ‖x‖ ^ 2 ≤ ⟪x, ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) x⟫ := by
  have h := (gsplit1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).hcoer x
  have h2 := D.sig_lower (iE (geomOf ell k S) x)
  have hc : 0 ≤ cw - δ0 := by linarith
  have hN : ‖eW (geomOf ell k S) (-sigG (geomOf ell k S)) x‖ = ‖bondWt (-sigG (geomOf ell k S)) (iE (geomOf ell k S) x)‖ := by
    rw [norm_E, iE_eW]
  have h3 : (((ell : ℝ) ^ k)⁻¹ * ‖x‖) ^ 2 ≤ ‖eW (geomOf ell k S) (-sigG (geomOf ell k S)) x‖ ^ 2 := by
    rw [hN, norm_E]; exact pow_le_pow_left₀ (by have := D.ell_pos; positivity) h2 2
  calc (cw - δ0) * (((ell : ℝ) ^ k)⁻¹) ^ 2 * ‖x‖ ^ 2 = (cw - δ0) * (((ell : ℝ) ^ k)⁻¹ * ‖x‖) ^ 2 := by ring
    _ ≤ (cw - δ0) * ‖eW (geomOf ell k S) (-sigG (geomOf ell k S)) x‖ ^ 2 := mul_le_mul_of_nonneg_left h3 hc
    _ ≤ _ := h

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 Dr hδ0 hδ1 hlt hD0 hD1 in
theorem G1_unitR : IsUnit ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) := by
  have hc : 0 < (cw - δ0) * (((ell : ℝ) ^ k)⁻¹) ^ 2 := by
    have := D.ell_pos
    have : 0 < cw - δ0 := by linarith
    positivity
  have hinj : Function.Injective ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h := G1_coerR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1 x
    rw [hx, inner_zero_right] at h
    have : ‖x‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖x‖]
    exact norm_le_zero_iff.mp (by nlinarith [norm_nonneg x])
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) :
      ↥(bondSupp (geomOf ell k S)) →ₗ[ℝ] ↥(bondSupp (geomOf ell k S))))).mp hinj⟩

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 Dr hQs hδ0 hδ1 hlt hD0 hD1 in
theorem N1_unitR : IsUnit (((gparams ell k Lu hell0 S D.U D.a Lam).data.Q.comp (Ring.inverse ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws))).comp
    (gparams ell k Lu hell0 S D.U D.a Lam).data.Qs) := by
  have hc : 0 < (cw - δ0) * (((ell : ℝ) ^ k)⁻¹) ^ 2 := by
    have := D.ell_pos
    have : 0 < cw - δ0 := by linarith
    positivity
  exact isUnit_Q_inv_Qs (G1_symmR D hell0 Lam cw hcw hW4 δ0 δ1 hδ0 hδ1 hlt hD0 hD1) hc
    (fun x => G1_coerR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1 x)
    (gparams ell k Lu hell0 S D.U D.a Lam).data.Q_adj hQs

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 hbN hext hQs hδ0 hδ1 hlt hD0 hD1 in
/-- **the `WSchur` instance of `H₁`** -/
noncomputable def wschur1R
    (hκ1 : (gsplit1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).kap < 1) :
    WSchur ↥(bondSupp (geomOf ell k S)) (FSp (geomOf ell k S)) where
  Ginv := (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws
  Gi := Ring.inverse ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws)
  Q := (gparams ell k Lu hell0 S D.U D.a Lam).data.Q
  Ninv := Ring.inverse (((gparams ell k Lu hell0 S D.U D.a Lam).data.Q.comp (Ring.inverse ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws))).comp
    (gparams ell k Lu hell0 S D.U D.a Lam).data.Qs)
  ωE := EWP (geomOf ell k S) D.χ
  ωF := rowWP (geomOf ell k S) D.χ
  Nw := eW (geomOf ell k S) (-sigG (geomOf ell k S))
  Mw := massWP (geomOf ell k S) D.a D.hp.ha hell0
  cw := cw - δ0
  κ := (gsplit1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).kap
  CQ := (gsplit1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).ss
  dB := d3c ell D.a Sstar θ'
  bN := (1 + δ0 / cw) * bN
  hcw := by linarith
  hκ0 := (gsplit1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).kap_nonneg
  hκ1 := hκ1
  hCQ := (gsplit1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).ss_nonneg
  hdB := Real.sqrt_nonneg _
  hbN := by positivity
  hsym := G1_symmR D hell0 Lam cw hcw hW4 δ0 δ1 hδ0 hδ1 hlt hD0 hD1
  hGi1 := fun x => by
    have h := Ring.mul_inverse_cancel _
      (G1_unitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1)
    exact ContinuousLinearMap.ext_iff.mp h x
  hGi2 := fun x => by
    have h := Ring.inverse_mul_cancel _
      (G1_unitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1)
    exact ContinuousLinearMap.ext_iff.mp h x
  hcoer := (gsplit1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).hcoer
  hHB := (gsplit1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).hHB_of_split
  hQ := fun h => by
    set J := gsplit1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1
    have h1 := J.sq_sum_le h
    have h0 : ‖J.Y3 h‖ ^ 2 ≤ (1 + J.cΔ) * J.En h := by
      have := sq_nonneg ‖J.Y1 h‖; have := sq_nonneg ‖J.Y2 h‖; linarith
    have hq : 0 ≤ 1 + J.cΔ := by have := J.hcΔ; linarith
    show ‖J.Y3 h‖ ≤ J.ss * Real.sqrt (J.En h)
    unfold GSplit.ss
    rw [← Real.sqrt_mul hq, ← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt h0
  hQp := fun h => by
    set J := gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr
    have h1 := J.hp3 h
    rw [ContinuousLinearMap.sub_apply, cjp_apply] at h1 ⊢
    show ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) D.a p))
      (rowWt (geomOf ell k S) D.χ ((gparams ell k Lu hell0 S D.U D.a Lam).data.Q (eW (geomOf ell k S) (-D.χ) h))
        - (gparams ell k Lu hell0 S D.U D.a Lam).data.Q h)‖ ≤ _
    rw [map_sub, D.diagW_rowWt]
    exact h1
  hQm := fun h => by
    set J := gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr
    have h1 := J.hm3 h
    rw [ContinuousLinearMap.sub_apply] at h1 ⊢
    show ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) D.a p))
      (rowWt (geomOf ell k S) (-D.χ) ((gparams ell k Lu hell0 S D.U D.a Lam).data.Q (eW (geomOf ell k S) D.χ h))
        - (gparams ell k Lu hell0 S D.U D.a Lam).data.Q h)‖ ≤ _
    rw [map_sub, D.diagW_rowWt]
    exact h1
  hext := fun v => by
    obtain ⟨g, hg, hE⟩ := hext v
    refine ⟨g, hg, ?_⟩
    have h1 := hD0 g g
    have h2 := D.W4_nq hell0 Lam cw hW4 g
    have hn := D.nq_nonneg (ell := ell) g
    have hM := sq_nonneg ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) D.a p)) v‖
    show ⟪g, ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) g⟫ ≤ (1 + δ0 / cw) * bN
      * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) D.a p)) v‖ ^ 2
    rw [ContinuousLinearMap.sub_apply, inner_sub_right]
    have h3 : -⟪g, (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws g⟫ ≤ δ0 * (nq S ell k (geomOf ell k S) g * nq S ell k (geomOf ell k S) g) :=
      (neg_le_abs _).trans h1
    have h4 : δ0 * (nq S ell k (geomOf ell k S) g * nq S ell k (geomOf ell k S) g)
        ≤ δ0 / cw * ⟪g, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv g⟫ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hcw]
      have := mul_le_mul_of_nonneg_left h2 hδ0
      nlinarith
    have hE0 : 0 ≤ ⟪g, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv g⟫ := le_trans (by positivity) h2
    have h5 : δ0 / cw * ⟪g, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv g⟫
        ≤ δ0 / cw * (bN * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) D.a p)) v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    nlinarith
  hN1 := fun u => by
    have h := Ring.mul_inverse_cancel _
      (N1_unitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1)
    exact ContinuousLinearMap.ext_iff.mp h u
  hN2 := fun u => by
    have h := Ring.inverse_mul_cancel _
      (N1_unitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1)
    exact ContinuousLinearMap.ext_iff.mp h u

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 hbN hext hQs hδ0 hδ1 hlt hD0 hD1 in
/-- **the weighted-`ℓ²` column of the `H₁` Schur instance** (the `hH1L2` shape of MZ5 `OpLayer`, centre `rowBase p`) -/
theorem H1_l2_colR
    (hκ1 : (gsplit1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).kap < 1)
    (hcN : 0 < 1 / (wschur1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1).bN
      - (wschur1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1).EN)
    (p : BIdx (geomOf ell k S)) (v : SuTwo)
    (hc0 : D.χ (rowBase (geomOf ell k S) p) = 0)
    (hlev : (p.1 : ℕ) ≤ AdalyFormal.M1.strat S k (rowBase (geomOf ell k S) p) + 1) :
    ∑ b : Bond (scaleUp ell k Lu), ((((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1)⁻¹) * Real.exp (D.χ b.1)
        * ‖(iE (geomOf ell k S) ((wschur1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1).H
          (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S)))) b‖) ^ 2
      ≤ ((wschur1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1).CHw ^ 2
          * (D.a * ell)) * (ell : ℝ) ^ AdalyFormal.M1.strat S k (rowBase (geomOf ell k S) p) * ‖v‖ ^ 2 := by
  set J := wschur1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1 with hJ
  have hell1 : 1 ≤ ell := by have := D.hell; omega
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have hl0 : (0 : ℝ) < ell := D.ell_pos
  have hH := J.H_cjp_w hcN (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S))
  have hrw : rowWt (geomOf ell k S) (-D.χ) (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S))
      = WithLp.toLp 2 (Pi.single p v) := by
    refine PiLp.ext (fun q => ?_)
    rw [rowWt_apply]
    by_cases hq : q = p
    · subst hq; simp [hc0]
    · simp [Pi.single_apply, hq]
  have e1 : J.Nw (cjp J.ωF J.ωE J.H (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S)))
      = eW (geomOf ell k S) (-sigG (geomOf ell k S)) (eW (geomOf ell k S) D.χ
          (J.H (WithLp.toLp 2 (Pi.single p v)))) := by
    rw [cjp_apply]
    show eW (geomOf ell k S) (-sigG (geomOf ell k S)) (eW (geomOf ell k S) D.χ
      (J.H (rowWt (geomOf ell k S) (-D.χ) (WithLp.toLp 2 (Pi.single p v))))) = _
    rw [hrw]
  have e2 : ‖J.Mw.w (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S))‖
      = Real.sqrt (massW (geomOf ell k S) D.a p) * ‖v‖ := by
    show ‖diagW (geomOf ell k S) (fun q => Real.sqrt (massW (geomOf ell k S) D.a q))
      (WithLp.toLp 2 (Pi.single p v))‖ = _
    have : diagW (geomOf ell k S) (fun q => Real.sqrt (massW (geomOf ell k S) D.a q)) (WithLp.toLp 2 (Pi.single p v))
        = (WithLp.toLp 2 (Pi.single p (Real.sqrt (massW (geomOf ell k S) D.a p) • v)) : FSp (geomOf ell k S)) := by
      refine PiLp.ext (fun q => ?_)
      rw [diagW_apply']
      by_cases hq : q = p
      · subst hq; simp
      · simp [Pi.single_apply, hq]
    rw [this, norm_single, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [e1, e2, norm_E, iE_eW, iE_eW] at hH
  set h := iE (geomOf ell k S) (J.H (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S))) with hh
  have hsite : ∀ x : PeriodicLatticeSite (scaleUp ell k Lu),
      Real.exp (sigG (geomOf ell k S) x) = (ell : ℝ) ^ AdalyFormal.M1.strat S k x := by
    intro x; rw [exp_sig (geomOf ell k S) hell0, ← strat_eq_stratG hell0 D.hS]; rfl
  have hpt : ∀ b : Bond (scaleUp ell k Lu), (((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1)⁻¹) * Real.exp (D.χ b.1) * ‖h b‖
      = ‖(bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)) b‖ := by
    intro b
    rw [bondWt_apply, bondWt_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    simp only [Pi.neg_apply]
    rw [Real.exp_neg, hsite]
    ring
  have hnorm : ∑ b : Bond (scaleUp ell k Lu), ‖(bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)) b‖ ^ 2
      = ‖bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ _).symm
  rw [Finset.sum_congr rfl (fun b _ => by rw [hpt b]), hnorm]
  have hCHw : 0 ≤ J.CHw := by
    unfold WSchur.CHw; have := J.Cy_nonneg; have := J.hcw; positivity
  have hN0 : 0 ≤ ‖bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)‖ := norm_nonneg _
  have h2 := pow_le_pow_left₀ hN0 hH 2
  set sc := AdalyFormal.M1.strat S k (rowBase (geomOf ell k S) p)
  have hmw : massW (geomOf ell k S) D.a p = D.a * (ell : ℝ) ^ (p.1 : ℕ) := rfl
  have ha := D.hp.ha
  have hlevr : (ell : ℝ) ^ (p.1 : ℕ) ≤ ell * (ell : ℝ) ^ sc := by
    rw [← pow_succ']; exact pow_le_pow_right₀ hellr hlev
  calc ‖bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)‖ ^ 2
      ≤ (J.CHw * (Real.sqrt (massW (geomOf ell k S) D.a p) * ‖v‖)) ^ 2 := h2
    _ = J.CHw ^ 2 * (D.a * (ell : ℝ) ^ (p.1 : ℕ)) * ‖v‖ ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by rw [hmw]; positivity), hmw]; ring
    _ ≤ J.CHw ^ 2 * (D.a * (ell * (ell : ℝ) ^ sc)) * ‖v‖ ^ 2 := by gcongr
    _ = _ := by ring


/-- the Schur `H` of `wschur1R` is the printed `H₁` (DY5b `H1_eq`, text copy) -/
theorem H1_eqR (hκ1 : (gsplit1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).kap < 1) :
    (gparams ell k Lu hell0 S D.U D.a Lam).data.H1 (gparams ell k Lu hell0 S D.U D.a Lam).G1inv
      = (wschur1R D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1).H := by
  have hG1 : (gparams ell k Lu hell0 S D.U D.a Lam).G1inv = (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws :=
    (gparams ell k Lu hell0 S D.U D.a Lam).data.G1inv_unique (gparams ell k Lu hell0 S D.U D.a Lam).G1inv_spec ((gparams ell k Lu hell0 S D.U D.a Lam).data.isG1inv_sub (gparams ell k Lu hell0 S D.U D.a Lam).data_laws)
  rw [hG1]
  ext1 x; rfl

end g1

end AdalyFormal.M1DStrat
#print axioms AdalyFormal.M1DStrat.gsplit1_GinvR
#print axioms AdalyFormal.M1DStrat.gsplit1R
#print axioms AdalyFormal.M1DStrat.G1_symmR
#print axioms AdalyFormal.M1DStrat.G1_coerR
#print axioms AdalyFormal.M1DStrat.G1_unitR
#print axioms AdalyFormal.M1DStrat.N1_unitR
#print axioms AdalyFormal.M1DStrat.wschur1R
#print axioms AdalyFormal.M1DStrat.H1_l2_colR
#print axioms AdalyFormal.M1DStrat.H1_eqR
