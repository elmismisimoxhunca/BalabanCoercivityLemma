import DLR80

/-!
# DL81 -- the genuine `G₁⁻¹` of (3.128) in fine-bond form: `G₁⁻¹ = P(GinvFull − W* M_ψ W)ι`, and its scaled CT instance

* `C2full_diag` : `β(x,x) = C2fullOf x`;  `Mpsi_diag` : `⟨x, M_ψ x⟩ = 2⟨C2fullOf x, ψ⟩`;
* **`dataDelta2_eq`** : `Δ⁽²⁾ = P W* M_ψ W ι` for `ψ = psiD P = H*J` (the statement's `Delta2`, by `symm_unique`);
* **`dataG1inv_eq`** : the statement's `G1inv` (`Classical.choose` of `exists_G1inv`) equals `P (GinvFull − W*M_ψW) ι`
  (`G1inv_unique` + `isG1inv_sub` + DL51 `dataGinv_eq`);
* `G1Full`; `ginv1M0` := `(ginvM0 ..).pert (n²•M_ψ)` (DL80); **`ginv1M0_eq`** : `ginv1M0.Ginv = n² • G1Full`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU PlaqFnL2)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.AsmM0 (M0RegimeR rhoM0 Mc KhatM0 phiC ThetaM0)
open AdalyFormal.BondComposite (rr TowerClass thetaOf)
open AdalyFormal.M0Finish (PU)

theorem C2full_diag {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (x : BondFnL2 L) :
    polar G U x x = C2fullOf G U x := by
  rw [polar_eq, (C2fullOf_quad G U).choose_spec x, ← two_smul ℝ, smul_smul]; norm_num

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))

theorem Mpsi_diag (ψ : FSp (GF ell k Lu)) (x : BondFnL2 (scaleUp ell k Lu)) :
    ⟪x, Mpsi ell k Lu U ψ x⟫ = 2 * ⟪C2fullOf (GF ell k Lu) U x, ψ⟫ := by
  rw [Mpsi_inner, C2full_diag]

/-- **the statement's `Δ⁽²⁾` in fine-bond form** -/
theorem dataDelta2_eq :
    (PU ell k Lu hell U a Lam).data.Delta2 (PU ell k Lu hell U a Lam).data_laws
      = pE (GF ell k Lu) ∘L (ContinuousLinearMap.adjoint (Wop (GF ell k Lu) U a)
          ∘L Mpsi ell k Lu U (psiD (PU ell k Lu hell U a Lam)) ∘L Wop (GF ell k Lu) U a) ∘L iE (GF ell k Lu) := by
  set P := PU ell k Lu hell U a Lam with hP
  set ψ := psiD P with hψ
  obtain ⟨hs, hf⟩ := P.data.Delta2_spec P.data_laws
  refine symm_unique hs (fun x y => ?_) (fun A => ?_)
  · simp only [ContinuousLinearMap.comp_apply]
    rw [pE_inner_left, pE_inner_right, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right,
      Mpsi_symm]
  · rw [hf A]
    simp only [ContinuousLinearMap.comp_apply]
    rw [pE_inner_right, ContinuousLinearMap.adjoint_inner_right, Mpsi_diag]
    have e1 : ⟪P.data.H (P.data.C2 A), P.data.J⟫ = ⟪P.data.C2 A, ψ⟫ := by
      rw [hψ, psiD, ContinuousLinearMap.adjoint_inner_right]
    rw [e1]
    rfl

/-- the unscaled `G₁⁻¹` on fine bonds -/
noncomputable def G1Full (ψ : FSp (GF ell k Lu)) : BondFnL2 (scaleUp ell k Lu) →L[ℝ] BondFnL2 (scaleUp ell k Lu) :=
  GinvFull ell k Lu U a - ContinuousLinearMap.adjoint (Wop (GF ell k Lu) U a)
    ∘L Mpsi ell k Lu U ψ ∘L Wop (GF ell k Lu) U a

/-- **the statement's `G₁⁻¹` in fine-bond form** -/
theorem dataG1inv_eq :
    (PU ell k Lu hell U a Lam).G1inv
      = pE (GF ell k Lu) ∘L G1Full ell k Lu U a (psiD (PU ell k Lu hell U a Lam)) ∘L iE (GF ell k Lu) := by
  set P := PU ell k Lu hell U a Lam with hP
  have h1 : P.G1inv = P.data.Ginv - P.data.Delta2 P.data_laws :=
    P.data.G1inv_unique P.G1inv_spec (P.data.isG1inv_sub P.data_laws)
  rw [h1, dataGinv_eq, dataDelta2_eq]
  ext1 z
  simp only [G1Full, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub]

end

/-! ## the scaled perturbed instance -/

theorem gamM0_W (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
    (R : M0RegimeR ell k Lu U a t e q0) (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ)
    (hφ : WtLip (θ / (ell : ℝ) ^ k) φ) (hc : CondM0 ell a (rhoM0 ell k e q0) θ) :
    (gamM0 ell k Lu U a t e q0 R φ θ hφ hc).W = Wop (GF ell k Lu) U a := by
  have hs : ((ell : ℝ) ^ k) ≠ 0 := by have := R.hell; positivity
  have hmpos := m0_mTop_pos ell k Lu U a t e q0 R
  have hsq : Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k ≠ 0 := by
    have := Real.sqrt_pos.mpr hmpos; positivity
  exact Wop_eq_W_scaled ell k Lu U a (m0_hu ell k Lu U a t e q0 R) (gamM0 ell k Lu U a t e q0 R φ θ hφ hc)
    ((ell : ℝ) ^ k) (Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k) hs hsq rfl rfl rfl

theorem Mpsi_scaled_norm (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu))
    (ψ : FSp (GF ell k Lu)) (S K νψ : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) (hψ : ∀ p, ‖ψ p‖ ≤ S)
    (hC : ∀ z : BondFnL2 (scaleUp ell k Lu), ∑ p, ‖C2fullOf (GF ell k Lu) U z p‖ ≤ K * ‖z‖ ^ 2)
    (hνψ : ((ell : ℝ) ^ k) ^ 2 * (2 * S * K) ≤ νψ) :
    ‖((ell : ℝ) ^ k) ^ 2 • Mpsi ell k Lu U ψ‖ ≤ νψ := by
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left (Mpsi_norm ell k Lu U ψ S K hS hK hψ hC) (by positivity)).trans hνψ

theorem Mpsi_scaled_cjp (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
    (R : M0RegimeR ell k Lu U a t e q0) (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0))
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (hφ : WtLip (θ / (ell : ℝ) ^ k) φ)
    (ψ : FSp (GF ell k Lu)) (S K δψ : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) (hψ : ∀ p, ‖ψ p‖ ≤ S)
    (hC : ∀ z : BondFnL2 (scaleUp ell k Lu), ∑ p, ‖C2fullOf (GF ell k Lu) U z p‖ ≤ K * ‖z‖ ^ 2)
    (hδψ : ((ell : ℝ) ^ k) ^ 2 * (2 * S * K * 648 * ((Real.exp (5 * θ) - 1) * (Real.exp (5 * θ) + 1))) ≤ δψ) :
    ‖cjp (bondWP φ) (bondWP φ) (((ell : ℝ) ^ k) ^ 2 • Mpsi ell k Lu U ψ) - ((ell : ℝ) ^ k) ^ 2 • Mpsi ell k Lu U ψ‖
      ≤ δψ := by
  have hreg := AdalyFormal.RegBgKU.regTower_M0_kuniform ell k Lu R.hell U e q0 R.he0 R.hq0 R.hlinks R.hplaq H
  rw [cjp_smul, ← smul_sub]
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left (Mpsi_cjp ell k Lu U R.hell hreg ψ S K hS hK hψ hC φ θ hθ hφ)
    (by positivity)).trans hδψ

theorem Mpsi_scaled_cjm (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
    (R : M0RegimeR ell k Lu U a t e q0) (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0))
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (hφ : WtLip (θ / (ell : ℝ) ^ k) φ)
    (ψ : FSp (GF ell k Lu)) (S K δψ : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) (hψ : ∀ p, ‖ψ p‖ ≤ S)
    (hC : ∀ z : BondFnL2 (scaleUp ell k Lu), ∑ p, ‖C2fullOf (GF ell k Lu) U z p‖ ≤ K * ‖z‖ ^ 2)
    (hδψ : ((ell : ℝ) ^ k) ^ 2 * (2 * S * K * 648 * ((Real.exp (5 * θ) - 1) * (Real.exp (5 * θ) + 1))) ≤ δψ) :
    ‖cjm (bondWP φ) (bondWP φ) (((ell : ℝ) ^ k) ^ 2 • Mpsi ell k Lu U ψ) - ((ell : ℝ) ^ k) ^ 2 • Mpsi ell k Lu U ψ‖
      ≤ δψ := by
  have hreg := AdalyFormal.RegBgKU.regTower_M0_kuniform ell k Lu R.hell U e q0 R.he0 R.hq0 R.hlinks R.hplaq H
  rw [cjm_eq_cjp_inv, cjp_smul, ← cjm_eq_cjp_inv, ← smul_sub]
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left (Mpsi_cjm ell k Lu U R.hell hreg ψ S K hS hK hψ hC φ θ hθ hφ)
    (by positivity)).trans hδψ

theorem Mpsi_scaled_symm (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu))
    (ψ : FSp (GF ell k Lu)) (x y : BondFnL2 (scaleUp ell k Lu)) :
    ⟪(((ell : ℝ) ^ k) ^ 2 • Mpsi ell k Lu U ψ) x, y⟫ = ⟪x, (((ell : ℝ) ^ k) ^ 2 • Mpsi ell k Lu U ψ) y⟫ := by
  simp only [ContinuousLinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right, Mpsi_symm]

/-- **the scaled CT instance for `G₁⁻¹`** -/
noncomputable def ginv1M0 (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
    (R : M0RegimeR ell k Lu U a t e q0) (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0))
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ) (hφ : WtLip (θ / (ell : ℝ) ^ k) φ)
    (hc : CondM0 ell a (rhoM0 ell k e q0) θ)
    (ψ : FSp (GF ell k Lu)) (S K νψ δψ : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) (hψ : ∀ p, ‖ψ p‖ ≤ S)
    (hC : ∀ z : BondFnL2 (scaleUp ell k Lu), ∑ p, ‖C2fullOf (GF ell k Lu) U z p‖ ≤ K * ‖z‖ ^ 2)
    (hνψ : ((ell : ℝ) ^ k) ^ 2 * (2 * S * K) ≤ νψ)
    (hδψ : ((ell : ℝ) ^ k) ^ 2 * (2 * S * K * 648 * ((Real.exp (5 * θ) - 1) * (Real.exp (5 * θ) + 1))) ≤ δψ) :
    GinvHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu))
      (PlaqFnL2 (scaleUp ell k Lu)) (FSp (GF ell k Lu)) :=
  (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).pert (((ell : ℝ) ^ k) ^ 2 • Mpsi ell k Lu U ψ) νψ δψ
    ((ContinuousLinearMap.opNorm_nonneg _).trans (Mpsi_scaled_norm ell k Lu U ψ S K νψ hS hK hψ hC hνψ))
    ((ContinuousLinearMap.opNorm_nonneg _).trans (Mpsi_scaled_cjp ell k Lu U a t e q0 R H φ θ hc.hθ hφ ψ S K δψ hS hK hψ hC hδψ))
    (Mpsi_scaled_norm ell k Lu U ψ S K νψ hS hK hψ hC hνψ)
    (Mpsi_scaled_cjp ell k Lu U a t e q0 R H φ θ hc.hθ hφ ψ S K δψ hS hK hψ hC hδψ)
    (Mpsi_scaled_cjm ell k Lu U a t e q0 R H φ θ hc.hθ hφ ψ S K δψ hS hK hψ hC hδψ)
    (Mpsi_scaled_symm ell k Lu U ψ)

theorem ginv1M0_eq (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
    (R : M0RegimeR ell k Lu U a t e q0) (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0))
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ) (hφ : WtLip (θ / (ell : ℝ) ^ k) φ)
    (hc : CondM0 ell a (rhoM0 ell k e q0) θ)
    (ψ : FSp (GF ell k Lu)) (S K νψ δψ : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) (hψ : ∀ p, ‖ψ p‖ ≤ S)
    (hC : ∀ z : BondFnL2 (scaleUp ell k Lu), ∑ p, ‖C2fullOf (GF ell k Lu) U z p‖ ≤ K * ‖z‖ ^ 2)
    (hνψ : ((ell : ℝ) ^ k) ^ 2 * (2 * S * K) ≤ νψ)
    (hδψ : ((ell : ℝ) ^ k) ^ 2 * (2 * S * K * 648 * ((Real.exp (5 * θ) - 1) * (Real.exp (5 * θ) + 1))) ≤ δψ) :
    (ginv1M0 ell k Lu U a t e q0 R H φ θ hφ hc ψ S K νψ δψ hS hK hψ hC hνψ hδψ).Ginv
      = ((ell : ℝ) ^ k) ^ 2 • G1Full ell k Lu U a ψ := by
  unfold ginv1M0
  rw [GinvHyp.pert_Ginv, ginvM0_eq]
  have hW : (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Gm.W = Wop (GF ell k Lu) U a :=
    gamM0_W ell k Lu U a t e q0 R φ θ hφ hc
  rw [hW]
  ext1 x
  simp only [G1Full, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    map_smul, smul_sub]

#print axioms C2full_diag
#print axioms dataDelta2_eq
#print axioms dataG1inv_eq
#print axioms gamM0_W
#print axioms ginv1M0_eq

end AdalyFormal.DLayer
