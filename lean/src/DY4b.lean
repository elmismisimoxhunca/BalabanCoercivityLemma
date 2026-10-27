import DY3
import DY4a

/-!
# DY4b -- `G₁⁻¹ = G⁻¹ − Δ⁽²⁾`: its split, its weighted Schur instance and the weighted columns of `H₁`
(M1 D-layer lane, clause 2, 2026-10-14)

At a `CTData D` (the D2 setting of DH1) with the two bilinear bounds of `Δ⁽²⁾` relative to `n(x) = ‖wq ιx‖`
(`|⟪x,Δ⁽²⁾y⟫| ≤ δ₀ n n`, `|⟪e^{χ}x, Δ⁽²⁾ e^{−χ}y⟫| ≤ δ₁ n n`, `δ₀ < cw`):
* `gsplit1` : DY4a's perturbed split of DG2b's `gsplit`;
* `G1_unit`, `N1_unit` : `G⁻¹ − Δ⁽²⁾` and `Q G₁ Q*` are invertible;
* **`wschur1`** : the `WSchur` instance with `Ginv := G⁻¹ − Δ⁽²⁾`, `cw := cw − δ₀`, `bN := (1 + δ₀/cw) bN`;
* **`H1_col`** : the weighted column bound of its `H` (DH1 `H_col` verbatim for `wschur1`);
* **`H1_eq`** : that `H` is the printed `H₁ = G₁Q*(QG₁Q*)⁻¹` of the ingredient family (`G1inv` is unique).
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

/-- the size `n(x) = ‖wq ιx‖ = √(wnormSq ιx)` -/
noncomputable def nq {L : PeriodicLatticeExtent} (S : Tower L) (ell k : ℕ) (G : TowerGeom L) (x : ↥(bondSupp G)) : ℝ :=
  ‖wq S ell k (iE G x)‖

namespace CTData
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
  (hR8 : 8 * ell ≤ R) (Sstar : ℝ) (Dr : RegData ell k Lu S D.U Sstar)
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

theorem nq_nonneg (x : ↥(bondSupp (geomOf ell k S))) : 0 ≤ nq S ell k (geomOf ell k S) x := norm_nonneg _

include hell0 in
theorem Nw_le_nq (x : ↥(bondSupp (geomOf ell k S))) :
    ‖eW (geomOf ell k S) (-sigG (geomOf ell k S)) x‖ ≤ nq S ell k (geomOf ell k S) x := by
  rw [D.Nn_eq]
  unfold NnE nq
  have h := N_le_wnorm D.hS hell0 (iE (geomOf ell k S) x)
  rw [← wq_normSq] at h
  exact le_of_sq_le' (norm_nonneg _) (norm_nonneg _) h

include hW4 in
theorem W4_nq (x : ↥(bondSupp (geomOf ell k S))) :
    cw * nq S ell k (geomOf ell k S) x ^ 2 ≤ ⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv x⟫ := by
  unfold nq; rw [wq_normSq]; exact hW4 x

/-- the perturbed split -/
noncomputable def gsplit1 : GSplit ↥(bondSupp (geomOf ell k S)) (PlaqFnL2 (scaleUp ell k Lu))
    (SiteL2 (scaleUp ell k Lu)) (FSp (geomOf ell k S)) :=
  (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).pert ((gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws)
    (nq S ell k (geomOf ell k S)) cw δ0 δ1 (fun x => D.nq_nonneg x) (fun x => D.Nw_le_nq hell0 x)
    (fun x => D.W4_nq hell0 Lam cw hW4 x) hD0 hδ0 hlt hD1 hδ1

theorem gsplit1_Ginv : (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0
    hD1).Ginv = (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws := rfl

include hcw hW4 hδ0 hδ1 hlt hD0 hD1 in
theorem G1_symm (x y : ↥(bondSupp (geomOf ell k S))) :
    ⟪((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) x, y⟫ = ⟪x, ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) y⟫ := by
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  rw [((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv_symm (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) x y,
    ((gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2_spec (gparams ell k Lu hell0 S D.U D.a Lam).data_laws).1 x y]

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 Dr hδ0 hδ1 hlt hD0 hD1 in
theorem G1_coer (x : ↥(bondSupp (geomOf ell k S))) :
    (cw - δ0) * (((ell : ℝ) ^ k)⁻¹) ^ 2 * ‖x‖ ^ 2 ≤ ⟪x, ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) x⟫ := by
  have h := (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).hcoer x
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
theorem G1_unit : IsUnit ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) := by
  have hc : 0 < (cw - δ0) * (((ell : ℝ) ^ k)⁻¹) ^ 2 := by
    have := D.ell_pos
    have : 0 < cw - δ0 := by linarith
    positivity
  have hinj : Function.Injective ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h := D.G1_coer hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1 x
    rw [hx, inner_zero_right] at h
    have : ‖x‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖x‖]
    exact norm_le_zero_iff.mp (by nlinarith [norm_nonneg x])
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws) :
      ↥(bondSupp (geomOf ell k S)) →ₗ[ℝ] ↥(bondSupp (geomOf ell k S))))).mp hinj⟩

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 Dr hQs hδ0 hδ1 hlt hD0 hD1 in
theorem N1_unit : IsUnit (((gparams ell k Lu hell0 S D.U D.a Lam).data.Q.comp (Ring.inverse ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv - (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2 (gparams ell k Lu hell0 S D.U D.a Lam).data_laws))).comp
    (gparams ell k Lu hell0 S D.U D.a Lam).data.Qs) := by
  have hc : 0 < (cw - δ0) * (((ell : ℝ) ^ k)⁻¹) ^ 2 := by
    have := D.ell_pos
    have : 0 < cw - δ0 := by linarith
    positivity
  exact isUnit_Q_inv_Qs (D.G1_symm hell0 Lam cw hcw hW4 δ0 δ1 hδ0 hδ1 hlt hD0 hD1) hc
    (fun x => D.G1_coer hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1 x)
    (gparams ell k Lu hell0 S D.U D.a Lam).data.Q_adj hQs

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 hbN hext hQs hδ0 hδ1 hlt hD0 hD1 in
/-- **the `WSchur` instance of `H₁`** -/
noncomputable def wschur1
    (hκ1 : (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).kap < 1) :
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
  κ := (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).kap
  CQ := (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).ss
  dB := d3c ell D.a Sstar θ'
  bN := (1 + δ0 / cw) * bN
  hcw := by linarith
  hκ0 := (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).kap_nonneg
  hκ1 := hκ1
  hCQ := (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).ss_nonneg
  hdB := Real.sqrt_nonneg _
  hbN := by positivity
  hsym := D.G1_symm hell0 Lam cw hcw hW4 δ0 δ1 hδ0 hδ1 hlt hD0 hD1
  hGi1 := fun x => by
    have h := Ring.mul_inverse_cancel _
      (D.G1_unit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1)
    exact ContinuousLinearMap.ext_iff.mp h x
  hGi2 := fun x => by
    have h := Ring.inverse_mul_cancel _
      (D.G1_unit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1)
    exact ContinuousLinearMap.ext_iff.mp h x
  hcoer := (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).hcoer
  hHB := (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).hHB_of_split
  hQ := fun h => by
    set J := D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1
    have h1 := J.sq_sum_le h
    have h0 : ‖J.Y3 h‖ ^ 2 ≤ (1 + J.cΔ) * J.En h := by
      have := sq_nonneg ‖J.Y1 h‖; have := sq_nonneg ‖J.Y2 h‖; linarith
    have hq : 0 ≤ 1 + J.cΔ := by have := J.hcΔ; linarith
    show ‖J.Y3 h‖ ≤ J.ss * Real.sqrt (J.En h)
    unfold GSplit.ss
    rw [← Real.sqrt_mul hq, ← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt h0
  hQp := fun h => by
    set J := D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr
    have h1 := J.hp3 h
    rw [ContinuousLinearMap.sub_apply, cjp_apply] at h1 ⊢
    show ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) D.a p))
      (rowWt (geomOf ell k S) D.χ ((gparams ell k Lu hell0 S D.U D.a Lam).data.Q (eW (geomOf ell k S) (-D.χ) h))
        - (gparams ell k Lu hell0 S D.U D.a Lam).data.Q h)‖ ≤ _
    rw [map_sub, D.diagW_rowWt]
    exact h1
  hQm := fun h => by
    set J := D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr
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
      (D.N1_unit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1)
    exact ContinuousLinearMap.ext_iff.mp h u
  hN2 := fun u => by
    have h := Ring.inverse_mul_cancel _
      (D.N1_unit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1)
    exact ContinuousLinearMap.ext_iff.mp h u

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 hbN hext hQs hδ0 hδ1 hlt hD0 hD1 in
/-- **the weighted column bound of `H₁`** -/
theorem H1_col
    (hκ1 : (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).kap < 1)
    (hcN : 0 < 1 / (D.wschur1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1).bN
      - (D.wschur1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1).EN)
    (p : BIdx (geomOf ell k S)) (v : SuTwo)
    (hc0 : D.χ (rowBase (geomOf ell k S) p) = 0)
    (Cg : ℝ) (hCg0 : 0 ≤ Cg)
    (hCg : ∑ x : PeriodicLatticeSite (scaleUp ell k Lu),
        (((ell : ℝ) ^ AdalyFormal.M1.strat S k x)⁻¹) ^ 4 * Real.exp (-(2 * D.χ x))
      ≤ Cg * ((ell : ℝ) ^ AdalyFormal.M1.strat S k (rowBase (geomOf ell k S) p))⁻¹)
    (hlev : (p.1 : ℕ) ≤ AdalyFormal.M1.strat S k (rowBase (geomOf ell k S) p) + 1) :
    ∑ b, omJ S ell k b * ‖(iE (geomOf ell k S) ((D.wschur1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1).H
        (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S)))) b‖
      ≤ Real.sqrt (3 * (ell : ℝ) ^ 7 * D.a * Cg)
        * (D.wschur1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1).CHw * ‖v‖ := by
  set J := D.wschur1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1 with hJ
  have hell1 : 1 ≤ ell := by have := D.hell; omega
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have hl0 : (0 : ℝ) < ell := D.ell_pos
  -- the weighted ℓ² bound
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
          ((D.wschur1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1).H (WithLp.toLp 2 (Pi.single p v)))) := by
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
  -- Cauchy–Schwarz
  set h := iE (geomOf ell k S) ((D.wschur1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1).H
    (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S))) with hh
  have hpt : ∀ b : Bond (scaleUp ell k Lu), omJ S ell k b * ‖h b‖
      = (omJ S ell k b * Real.exp (sigG (geomOf ell k S) b.1 - D.χ b.1))
        * ‖(bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)) b‖ := by
    intro b
    rw [bondWt_apply, bondWt_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have : Real.exp (sigG (geomOf ell k S) b.1 - D.χ b.1) * (Real.exp ((-sigG (geomOf ell k S)) b.1) * Real.exp (D.χ b.1)) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; simp only [Pi.neg_apply]; ring_nf; simp
    calc omJ S ell k b * ‖h b‖ = omJ S ell k b * (Real.exp (sigG (geomOf ell k S) b.1 - D.χ b.1)
          * (Real.exp ((-sigG (geomOf ell k S)) b.1) * Real.exp (D.χ b.1))) * ‖h b‖ := by rw [this, mul_one]
      _ = _ := by ring
  rw [Finset.sum_congr rfl (fun b _ => hpt b)]
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun b : Bond (scaleUp ell k Lu) => omJ S ell k b * Real.exp (sigG (geomOf ell k S) b.1 - D.χ b.1))
    (fun b => ‖(bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)) b‖)
  have hnorm : ∑ b : Bond (scaleUp ell k Lu), ‖(bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)) b‖ ^ 2
      = ‖bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ _).symm
  rw [hnorm, Real.sqrt_sq (norm_nonneg _)] at hCS
  refine hCS.trans ?_
  -- the weight sum
  have hsite : ∀ x : PeriodicLatticeSite (scaleUp ell k Lu),
      Real.exp (sigG (geomOf ell k S) x) = (ell : ℝ) ^ AdalyFormal.M1.strat S k x := by
    intro x; rw [exp_sig (geomOf ell k S) hell0, ← strat_eq_stratG hell0 D.hS]; rfl
  have hwb : ∀ b : Bond (scaleUp ell k Lu),
      (omJ S ell k b * Real.exp (sigG (geomOf ell k S) b.1 - D.χ b.1)) ^ 2
        ≤ (ell : ℝ) ^ 6 * ((((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1)⁻¹) ^ 4 * Real.exp (-(2 * D.χ b.1))) := by
    intro b
    have h1 := omJ_sq_le D.hS D.hR D.hM hell1 b
    have e1 : Real.exp (sigG (geomOf ell k S) b.1 - D.χ b.1) ^ 2
        = ((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1) ^ 2 * Real.exp (-(2 * D.χ b.1)) := by
      rw [← hsite, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; push_cast; ring
    rw [mul_pow, e1]
    have hE := Real.exp_pos (-(2 * D.χ b.1))
    calc omJ S ell k b ^ 2 * (((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1) ^ 2 * Real.exp (-(2 * D.χ b.1)))
        = (omJ S ell k b ^ 2 * ((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1) ^ 2) * Real.exp (-(2 * D.χ b.1)) := by ring
      _ ≤ ((ell : ℝ) ^ 6 * (((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1)⁻¹) ^ 4) * Real.exp (-(2 * D.χ b.1)) :=
          mul_le_mul_of_nonneg_right h1 hE.le
      _ = _ := by ring
  have hsumb : ∑ b : Bond (scaleUp ell k Lu), (omJ S ell k b * Real.exp (sigG (geomOf ell k S) b.1 - D.χ b.1)) ^ 2
      ≤ 3 * (ell : ℝ) ^ 6 * (Cg * ((ell : ℝ) ^ AdalyFormal.M1.strat S k (rowBase (geomOf ell k S) p))⁻¹) := by
    refine (Finset.sum_le_sum (fun b _ => hwb b)).trans ?_
    rw [← Finset.mul_sum]
    have hb : ∑ b : Bond (scaleUp ell k Lu),
        (((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1)⁻¹) ^ 4 * Real.exp (-(2 * D.χ b.1))
        = 3 * ∑ x : PeriodicLatticeSite (scaleUp ell k Lu),
            (((ell : ℝ) ^ AdalyFormal.M1.strat S k x)⁻¹) ^ 4 * Real.exp (-(2 * D.χ x)) := by
      rw [show (Finset.univ : Finset (Bond (scaleUp ell k Lu))) = Finset.univ ×ˢ Finset.univ from rfl,
        Finset.sum_product]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.mul_sum]; push_cast; rfl
    rw [hb]
    have := mul_le_mul_of_nonneg_left hCg (show (0 : ℝ) ≤ 3 by norm_num)
    calc (ell : ℝ) ^ 6 * (3 * ∑ x : PeriodicLatticeSite (scaleUp ell k Lu),
            (((ell : ℝ) ^ AdalyFormal.M1.strat S k x)⁻¹) ^ 4 * Real.exp (-(2 * D.χ x)))
        ≤ (ell : ℝ) ^ 6 * (3 * (Cg * ((ell : ℝ) ^ AdalyFormal.M1.strat S k (rowBase (geomOf ell k S) p))⁻¹)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  -- the level factor `ℓ^{j} ℓ^{-s} ≤ ℓ`
  set sc := AdalyFormal.M1.strat S k (rowBase (geomOf ell k S) p)
  have hmw : massW (geomOf ell k S) D.a p = D.a * (ell : ℝ) ^ (p.1 : ℕ) := rfl
  have hlevr : (ell : ℝ) ^ (p.1 : ℕ) * ((ell : ℝ) ^ sc)⁻¹ ≤ ell := by
    have hp : (0 : ℝ) < (ell : ℝ) ^ sc := by have := one_le_pow₀ (n := sc) hellr; positivity
    rw [← div_eq_mul_inv, div_le_iff₀ hp, ← pow_succ']
    exact pow_le_pow_right₀ hellr hlev
  have ha := D.hp.ha
  have hCHw : 0 ≤ J.CHw := by
    unfold WSchur.CHw; have := J.Cy_nonneg; have := J.hcw; positivity
  have hN2 : ‖bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)‖
      ≤ J.CHw * (Real.sqrt (massW (geomOf ell k S) D.a p) * ‖v‖) := hH
  calc Real.sqrt (∑ b : Bond (scaleUp ell k Lu), (omJ S ell k b * Real.exp (sigG (geomOf ell k S) b.1 - D.χ b.1)) ^ 2)
        * ‖bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)‖
      ≤ Real.sqrt (3 * (ell : ℝ) ^ 6 * (Cg * ((ell : ℝ) ^ sc)⁻¹))
        * (J.CHw * (Real.sqrt (massW (geomOf ell k S) D.a p) * ‖v‖)) :=
        mul_le_mul (Real.sqrt_le_sqrt hsumb) hN2 (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (3 * (ell : ℝ) ^ 6 * Cg * D.a * ((ell : ℝ) ^ (p.1 : ℕ) * ((ell : ℝ) ^ sc)⁻¹)) * J.CHw * ‖v‖ := by
        have hsq : Real.sqrt (3 * (ell : ℝ) ^ 6 * (Cg * ((ell : ℝ) ^ sc)⁻¹))
            * Real.sqrt (massW (geomOf ell k S) D.a p)
            = Real.sqrt (3 * (ell : ℝ) ^ 6 * Cg * D.a * ((ell : ℝ) ^ (p.1 : ℕ) * ((ell : ℝ) ^ sc)⁻¹)) := by
          rw [← Real.sqrt_mul (by positivity), hmw]; congr 1; ring
        rw [← hsq]; ring
    _ ≤ Real.sqrt (3 * (ell : ℝ) ^ 7 * D.a * Cg) * J.CHw * ‖v‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) hCHw) (norm_nonneg _)
        have := mul_le_mul_of_nonneg_left hlevr (show 0 ≤ 3 * (ell : ℝ) ^ 6 * Cg * D.a by positivity)
        calc 3 * (ell : ℝ) ^ 6 * Cg * D.a * ((ell : ℝ) ^ (p.1 : ℕ) * ((ell : ℝ) ^ sc)⁻¹)
            ≤ 3 * (ell : ℝ) ^ 6 * Cg * D.a * ell := this
          _ = 3 * (ell : ℝ) ^ 7 * D.a * Cg := by ring


end CTData

#print axioms nq
#print axioms CTData.nq_nonneg
#print axioms CTData.Nw_le_nq
#print axioms CTData.W4_nq
#print axioms CTData.gsplit1
#print axioms CTData.gsplit1_Ginv
#print axioms CTData.G1_symm
#print axioms CTData.G1_coer
#print axioms CTData.G1_unit
#print axioms CTData.N1_unit
#print axioms CTData.wschur1
#print axioms CTData.H1_col

end AdalyFormal.M1DStrat
