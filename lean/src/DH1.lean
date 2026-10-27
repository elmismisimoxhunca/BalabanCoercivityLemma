import DG2b
import DC2

/-!
# DH1 -- the genuine `H = G Q* (Q G Q*)⁻¹` under the stratified Combes–Thomas weight: DC2's `WSchur` instance and
the WEIGHTED COLUMN bound `DParts.hHcol` (M1 D-layer lane, 2026-10-14)

At one configuration, from: the `GSplit` data of DG2b (CTData `D` with CT weight `ξ = D.χ`, holonomy regime, regional
tower data, W4 constant `cw`, the stratified Lipschitz bound of `ξ`), `κ < 1` for the split, the energy right
inverse of the bond `Q` (`hext`, constant `bN`; plan node W6) and `Q*` injective:
* `massWP` : the row weight pair `√w = √(a ℓ^j)`;
* `Ginv_unit`, `N_unit` : `G⁻¹` and `N = Q G Q*` are units;
* **`wschur`** : the `WSchur` instance; `wschur_H` : its `H` is the genuine `data.H`;
* **`H_col`** : if moreover `ξ(rowBase p) = 0`, `Σ_x ℓ^{-4 strat x} e^{-2ξ(x)} ≤ Cg ℓ^{-strat(rowBase p)}` and
  `level p ≤ strat(rowBase p) + 1`, then
  `Σ_b ℓ^{-3 bstrat b} ‖(H δ_p v)(b)‖ ≤ √(3 ℓ⁷ a Cg) · CHw · ‖v‖`   (`CHw` = DC2's constant, `1/bN > EN`).
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

/-! ## 0. the mass weight pair -/

section mw
variable {L : PeriodicLatticeExtent} (G : TowerGeom L)

theorem diagW_apply' (w : BIdx G → ℝ) (f : FSp G) (p : BIdx G) : diagW G w f p = w p • f p := rfl

theorem diagW_mul (w w' : BIdx G → ℝ) (f : FSp G) : diagW G w (diagW G w' f) = diagW G (fun p => w p * w' p) f := by
  refine PiLp.ext (fun p => ?_)
  rw [diagW_apply', diagW_apply', diagW_apply', smul_smul]

theorem diagW_one (f : FSp G) : diagW G (fun _ => 1) f = f := by
  refine PiLp.ext (fun p => ?_)
  rw [diagW_apply', one_smul]

/-- `√w` with `w = a ℓ^j`, as a weight pair (`a > 0`) -/
theorem sqrt_massW_pos (a : ℝ) (ha : 0 < a) (hG : 0 < G.ell) (p : BIdx G) : 0 < Real.sqrt (massW G a p) := by
  apply Real.sqrt_pos.mpr
  unfold massW
  have h : (0 : ℝ) < G.ell := by exact_mod_cast hG
  positivity

noncomputable def massWP (a : ℝ) (ha : 0 < a) (hG : 0 < G.ell) : WPair (FSp G) where
  w := diagW G (fun p => Real.sqrt (massW G a p))
  wi := diagW G (fun p => (Real.sqrt (massW G a p))⁻¹)
  w_wi := fun f => by
    rw [diagW_mul]
    have : (fun p => Real.sqrt (massW G a p) * (Real.sqrt (massW G a p))⁻¹) = fun _ => (1 : ℝ) := by
      funext p
      exact mul_inv_cancel₀ (sqrt_massW_pos G a ha hG p).ne'
    rw [this, diagW_one]
  wi_w := fun f => by
    rw [diagW_mul]
    have : (fun p => (Real.sqrt (massW G a p))⁻¹ * Real.sqrt (massW G a p)) = fun _ => (1 : ℝ) := by
      funext p
      exact inv_mul_cancel₀ (sqrt_massW_pos G a ha hG p).ne'
    rw [this, diagW_one]
  w_sym := diagW_symm G _
  wi_sym := diagW_symm G _

theorem norm_single (p : BIdx G) (v : SuTwo) : ‖(WithLp.toLp 2 (Pi.single p v) : FSp G)‖ = ‖v‖ := by
  rw [← Real.sqrt_sq (norm_nonneg ((WithLp.toLp 2 (Pi.single p v) : FSp G))), PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq; simp [Pi.single_apply, hq]
  · simp

end mw

/-! ## 1. the instance -/

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
include D

/-- `‖e^{−σ} B‖ ≥ ℓ^{-k} ‖B‖` -/
theorem sig_lower (B : BondFnL2 (scaleUp ell k Lu)) :
    ((ell : ℝ) ^ k)⁻¹ * ‖B‖ ≤ ‖bondWt (-sigG (geomOf ell k S)) B‖ := by
  have hell1 : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by have := D.hell; omega)
  have hl0 : (0 : ℝ) < ell := D.ell_pos
  have h := bondWt_le_of (fun _ => -((k : ℝ) * Real.log ell)) (-sigG (geomOf ell k S)) (fun x => by
    have hs := stratG_le (geomOf ell k S) x
    simp only [Pi.neg_apply]
    have : sigG (geomOf ell k S) x ≤ (k : ℝ) * Real.log ell := by
      unfold sigG
      rw [show (((geomOf ell k S).ell : ℕ) : ℝ) = (ell : ℝ) from rfl]
      have hlog : 0 ≤ Real.log ell := Real.log_nonneg hell1
      have : (stratG (geomOf ell k S) x : ℝ) ≤ k := by exact_mod_cast hs
      nlinarith
    linarith) B
  have e : bondWt (fun _ => -((k : ℝ) * Real.log ell)) B = Real.exp (-((k : ℝ) * Real.log ell)) • B := by
    refine PiLp.ext (fun b => ?_)
    rw [bondWt_apply]; rfl
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
  have e2 : Real.exp (-((k : ℝ) * Real.log ell)) = ((ell : ℝ) ^ k)⁻¹ := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hl0]
  rw [e2] at h
  exact h


include hcw hW4 in
theorem Ginv_inj : Function.Injective (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h := D.NE hell0 Lam cw hcw hW4 x
  rw [hx, inner_zero_right] at h
  have hN : NnE (geomOf ell k S) x = 0 := by
    have : NnE (geomOf ell k S) x ^ 2 ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
  have h2 := D.sig_lower (iE (geomOf ell k S) x)
  unfold NnE at hN
  rw [hN] at h2
  have hp : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by have := D.ell_pos; positivity
  have h3 : ‖iE (geomOf ell k S) x‖ ≤ 0 := by nlinarith [norm_nonneg (iE (geomOf ell k S) x)]
  have h4 : iE (geomOf ell k S) x = 0 := norm_le_zero_iff.mp h3
  exact Subtype.ext h4

include hcw hW4 in
theorem Ginv_unit : IsUnit (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv := by
  have hinj := D.Ginv_inj hell0 Lam cw hcw hW4
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv :
      ↥(bondSupp (geomOf ell k S)) →ₗ[ℝ] ↥(bondSupp (geomOf ell k S))))).mp hinj⟩

include hcw hW4 in
theorem Ginv_G (x : ↥(bondSupp (geomOf ell k S))) :
    (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv ((gparams ell k Lu hell0 S D.U D.a Lam).data.G x) = x := by
  have h := Ring.mul_inverse_cancel _ (D.Ginv_unit hell0 Lam cw hcw hW4)
  exact ContinuousLinearMap.ext_iff.mp h x

include hcw hW4 in
theorem G_Ginv (x : ↥(bondSupp (geomOf ell k S))) :
    (gparams ell k Lu hell0 S D.U D.a Lam).data.G ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv x) = x := by
  have h := Ring.inverse_mul_cancel _ (D.Ginv_unit hell0 Lam cw hcw hW4)
  exact ContinuousLinearMap.ext_iff.mp h x

include hcw hW4 hQs in
theorem N_unit : IsUnit (((gparams ell k Lu hell0 S D.U D.a Lam).data.Q.comp
    (gparams ell k Lu hell0 S D.U D.a Lam).data.G).comp (gparams ell k Lu hell0 S D.U D.a Lam).data.Qs) := by
  have hc : 0 < cw * (((ell : ℝ) ^ k)⁻¹) ^ 2 := by have := D.ell_pos; positivity
  refine isUnit_Q_inv_Qs ((gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv_symm (gparams ell k Lu hell0 S D.U D.a Lam).data_laws)
    hc (fun x => ?_) (gparams ell k Lu hell0 S D.U D.a Lam).data.Q_adj hQs
  have h1 := D.NE hell0 Lam cw hcw hW4 x
  have h2 := D.sig_lower (iE (geomOf ell k S) x)
  have h3 : (((ell : ℝ) ^ k)⁻¹ * ‖x‖) ^ 2 ≤ NnE (geomOf ell k S) x ^ 2 := pow_le_pow_left₀ (by have := D.ell_pos; positivity) h2 2
  calc cw * (((ell : ℝ) ^ k)⁻¹) ^ 2 * ‖x‖ ^ 2 = cw * (((ell : ℝ) ^ k)⁻¹ * ‖x‖) ^ 2 := by ring
    _ ≤ cw * NnE (geomOf ell k S) x ^ 2 := mul_le_mul_of_nonneg_left h3 hcw.le
    _ ≤ _ := h1

/-- diagonals commute -/
theorem diagW_rowWt (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (f : FSp (geomOf ell k S)) :
    diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) D.a p)) (rowWt (geomOf ell k S) φ f)
      = rowWt (geomOf ell k S) φ (diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) D.a p)) f) := by
  refine PiLp.ext (fun p => ?_)
  rw [diagW_apply', rowWt_apply, rowWt_apply, diagW_apply', smul_comm]

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 hbN hext hQs in
/-- **the `WSchur` instance of the genuine `H`** -/
noncomputable def wschur
    (hκ1 : (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap < 1) :
    WSchur ↥(bondSupp (geomOf ell k S)) (FSp (geomOf ell k S)) where
  Ginv := (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv
  Gi := (gparams ell k Lu hell0 S D.U D.a Lam).data.G
  Q := (gparams ell k Lu hell0 S D.U D.a Lam).data.Q
  Ninv := Ring.inverse (((gparams ell k Lu hell0 S D.U D.a Lam).data.Q.comp
    (gparams ell k Lu hell0 S D.U D.a Lam).data.G).comp (gparams ell k Lu hell0 S D.U D.a Lam).data.Qs)
  ωE := EWP (geomOf ell k S) D.χ
  ωF := rowWP (geomOf ell k S) D.χ
  Nw := eW (geomOf ell k S) (-sigG (geomOf ell k S))
  Mw := massWP (geomOf ell k S) D.a D.hp.ha hell0
  cw := cw
  κ := (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap
  CQ := (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).ss
  dB := d3c ell D.a Sstar θ'
  bN := bN
  hcw := hcw
  hκ0 := (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap_nonneg
  hκ1 := hκ1
  hCQ := (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).ss_nonneg
  hdB := Real.sqrt_nonneg _
  hbN := hbN
  hsym := (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv_symm (gparams ell k Lu hell0 S D.U D.a Lam).data_laws
  hGi1 := D.Ginv_G hell0 Lam cw hcw hW4
  hGi2 := D.G_Ginv hell0 Lam cw hcw hW4
  hcoer := (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).hcoer
  hHB := D.hHB_genuine hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr
  hQ := fun h => by
    set J := D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr
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
  hext := hext
  hN1 := fun u => by
    have h := Ring.mul_inverse_cancel _ (D.N_unit hell0 Lam cw hcw hW4 hQs)
    exact ContinuousLinearMap.ext_iff.mp h u
  hN2 := fun u => by
    have h := Ring.inverse_mul_cancel _ (D.N_unit hell0 Lam cw hcw hW4 hQs)
    exact ContinuousLinearMap.ext_iff.mp h u

theorem wschur_H (hκ1 : (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap < 1) :
    (D.wschur hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs hκ1).H
      = (gparams ell k Lu hell0 S D.U D.a Lam).data.H := by
  ext1 x; rfl


/-! ## 2. the column bound -/

omit D in
theorem omJ_sq_le {ell M R k : ℕ} {L : PeriodicLatticeExtent} {S : Tower L} (hS : Admissible ell M R k S)
    (hR : 1 ≤ R) (hM : 1 ≤ M) (hell : 1 ≤ ell) (b : Bond L) :
    (omJ S ell k b) ^ 2 * ((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1) ^ 2
      ≤ (ell : ℝ) ^ 6 * (((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1)⁻¹) ^ 4 := by
  have hb := AdalyFormal.M1.bstrat_ge hS hR hM hell b
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  set s := AdalyFormal.M1.strat S k b.1
  set t := AdalyFormal.M1.bstrat S k b
  have hp : ∀ n : ℕ, (0 : ℝ) < (ell : ℝ) ^ n := fun n => by have := one_le_pow₀ (n := n) hellr; positivity
  -- ℓ^{-t} ≤ ℓ · ℓ^{-s}
  have h1 : ((ell : ℝ) ^ t)⁻¹ ≤ (ell : ℝ) * ((ell : ℝ) ^ s)⁻¹ := by
    rw [inv_le_comm₀ (hp t) (by have h1 := hp s; have h2 : (0:ℝ) < ell := (by linarith); positivity), mul_inv, inv_inv]
    have : (ell : ℝ) ^ s ≤ (ell : ℝ) ^ (t + 1) := pow_le_pow_right₀ hellr hb
    rw [pow_succ] at this
    have hl0 : (0 : ℝ) < ell := by linarith
    calc (ell : ℝ)⁻¹ * (ell : ℝ) ^ s ≤ (ell : ℝ)⁻¹ * ((ell : ℝ) ^ t * ell) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = (ell : ℝ) ^ t := by field_simp
  have h2 : (omJ S ell k b) ≤ (ell : ℝ) ^ 3 * (((ell : ℝ) ^ s)⁻¹) ^ 3 := by
    unfold omJ
    have := pow_le_pow_left₀ (inv_nonneg.mpr (hp t).le) h1 3
    rw [mul_pow] at this; exact this
  have h0 : 0 ≤ omJ S ell k b := by unfold omJ; have := hp t; positivity
  have h3 := pow_le_pow_left₀ h0 h2 2
  have hs : ((ell : ℝ) ^ s) ^ 2 * (((ell : ℝ) ^ s)⁻¹) ^ 6 = (((ell : ℝ) ^ s)⁻¹) ^ 4 := by
    have := hp s; field_simp
  calc (omJ S ell k b) ^ 2 * ((ell : ℝ) ^ s) ^ 2 ≤ ((ell : ℝ) ^ 3 * (((ell : ℝ) ^ s)⁻¹) ^ 3) ^ 2 * ((ell : ℝ) ^ s) ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = (ell : ℝ) ^ 6 * (((ell : ℝ) ^ s) ^ 2 * (((ell : ℝ) ^ s)⁻¹) ^ 6) := by ring
    _ = _ := by rw [hs]

include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 hbN hext hQs in
/-- **the weighted column bound of the genuine `H`** (`DParts.hHcol` at one row) -/
theorem H_col
    (hκ1 : (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap < 1)
    (hcN : 0 < 1 / (D.wschur hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs hκ1).bN
      - (D.wschur hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs hκ1).EN)
    (p : BIdx (geomOf ell k S)) (v : SuTwo)
    (hc0 : D.χ (rowBase (geomOf ell k S) p) = 0)
    (Cg : ℝ) (hCg0 : 0 ≤ Cg)
    (hCg : ∑ x : PeriodicLatticeSite (scaleUp ell k Lu),
        (((ell : ℝ) ^ AdalyFormal.M1.strat S k x)⁻¹) ^ 4 * Real.exp (-(2 * D.χ x))
      ≤ Cg * ((ell : ℝ) ^ AdalyFormal.M1.strat S k (rowBase (geomOf ell k S) p))⁻¹)
    (hlev : (p.1 : ℕ) ≤ AdalyFormal.M1.strat S k (rowBase (geomOf ell k S) p) + 1) :
    ∑ b, omJ S ell k b * ‖(iE (geomOf ell k S) ((gparams ell k Lu hell0 S D.U D.a Lam).data.H
        (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S)))) b‖
      ≤ Real.sqrt (3 * (ell : ℝ) ^ 7 * D.a * Cg)
        * (D.wschur hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs hκ1).CHw * ‖v‖ := by
  set J := D.wschur hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs hκ1 with hJ
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
          ((gparams ell k Lu hell0 S D.U D.a Lam).data.H (WithLp.toLp 2 (Pi.single p v)))) := by
    rw [cjp_apply]
    show eW (geomOf ell k S) (-sigG (geomOf ell k S)) (eW (geomOf ell k S) D.χ
      (J.H (rowWt (geomOf ell k S) (-D.χ) (WithLp.toLp 2 (Pi.single p v))))) = _
    rw [hrw, D.wschur_H]
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
  set h := iE (geomOf ell k S) ((gparams ell k Lu hell0 S D.U D.a Lam).data.H
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

#print axioms diagW_apply'
#print axioms diagW_mul
#print axioms diagW_one
#print axioms sqrt_massW_pos
#print axioms massWP
#print axioms norm_single
#print axioms CTData.sig_lower
#print axioms CTData.Ginv_inj
#print axioms CTData.Ginv_unit
#print axioms CTData.Ginv_G
#print axioms CTData.G_Ginv
#print axioms CTData.N_unit
#print axioms CTData.diagW_rowWt
#print axioms CTData.wschur
#print axioms CTData.wschur_H
#print axioms CTData.omJ_sq_le
#print axioms CTData.H_col

end AdalyFormal.M1DStrat
