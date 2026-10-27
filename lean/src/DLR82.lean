import DLR81

/-!
# DL82 -- the Schur-complement (N) structure for `G₁` at M0 and **`H1_CT_M0`** (weighted bound of the scaled `H₁`)

k-free model constants (`Z0` model structures, as in DL36/DL38/DL52):
* `CondM0.ginv1 νψ δψ` : the model `G⁻¹` structure perturbed by `ν + νψ`, `δν + δψ`;  `EGM1` its `EG`;
* `cg1 = 1/K̂ − νψ·nW²` (coercivity of the scaled `G₁⁻¹`), `bN1 = bNS·(1 + νψ nW² K̂)` (extension energy), `EN1free`.
Concrete: `ginv1M0_EG`, `ginv1M0_nW` (definitional), `coer1M0`, `G1Full_isUnit`, `GiM1`, `ext1M0`, `N1opM0`, `n1M0`,
**`H1_CT_M0`** : `‖e^φ H₁' e^{−φ} w‖ ≤ (2/cg1)(qBS + δBS)/(1/bN1 − EN1free)·‖w‖` under the k-free conditions
`0 < cg1`, `4·EGM1 ≤ cg1`, `EN1free < 1/bN1`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

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

/-- a model `N` structure from any model `G⁻¹` structure -/
noncomputable def modelNOf (I : GinvHyp Z0 Z0 Z0 Z0 Z0) (cg qb bN : ℝ) (hcg : 0 < cg) (hEG : 4 * I.EG ≤ cg)
    (hqb : 0 ≤ qb) (hbN : 0 < bN) : NHyp Z0 Z0 Z0 Z0 Z0 where
  toGinvHyp := I
  Gi := 0
  Ninv := 0
  cg := cg
  qb := qb
  bN := bN
  hGi1 := fun x => Z0_eq _ _
  hGi2 := fun x => Z0_eq _ _
  hcg := hcg
  hcoerG := fun f => by rw [Z0_zero f]; simp
  hEG := hEG
  hqb := hqb
  hQb := by
    have : I.Qb = 0 := ContinuousLinearMap.ext (fun x => Z0_eq _ _)
    rw [this, norm_zero]; exact hqb
  hbN := hbN
  extN := fun u => ⟨0, Z0_eq _ _, by rw [Z0_zero u]; simp⟩
  hN1 := fun u => Z0_eq _ _
  hN2 := fun u => Z0_eq _ _

namespace CondM0
variable {ell : ℕ} {a ρ θ : ℝ} (hc : CondM0 ell a ρ θ)

/-- the perturbed model `G⁻¹` structure -/
noncomputable def ginv1 (νψ δψ : ℝ) (hν : 0 ≤ νψ) (hδ : 0 ≤ δψ) : GinvHyp Z0 Z0 Z0 Z0 Z0 :=
  hc.ginv.pert 0 νψ δψ hν hδ (by rw [norm_zero]; exact hν) (norm_zero_op _ _ _ hδ) (norm_zero_opm _ _ _ hδ)
    (fun x y => by simp)

end CondM0

/-- the k-free constants of the `G₁` chain -/
noncomputable def EGM1 (ell : ℕ) (a ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ δψ : ℝ) (hν : 0 ≤ νψ) (hδ : 0 ≤ δψ) : ℝ :=
  (hc.ginv1 νψ δψ hν hδ).EG

noncomputable def cg1 (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ : ℝ) : ℝ :=
  1 / KhatM0 ell a t ρ - νψ * hc.ginv.nW ^ 2

noncomputable def bN1 (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ : ℝ) : ℝ :=
  bNS a ρ (δS ell ρ) * (1 + νψ * hc.ginv.nW ^ 2 * KhatM0 ell a t ρ)

theorem nW_model_nonneg {ell : ℕ} {a ρ θ : ℝ} (hc : CondM0 ell a ρ θ) : 0 ≤ hc.ginv.nW := by
  obtain ⟨-, hdDZ, -, hkDZ, -, -⟩ := hc.ginv.dZ_nonneg
  unfold GinvHyp.nW; linarith

theorem bN1_pos (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ : ℝ) (hν : 0 ≤ νψ) (hK : 0 < KhatM0 ell a t ρ) :
    0 < bN1 ell a t ρ θ hc νψ := by
  unfold bN1
  have := bNS_pos a ρ (δS ell ρ) hc.νS_nonneg
  have := nW_model_nonneg hc
  positivity

noncomputable def EN1free (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ δψ : ℝ) (hν : 0 ≤ νψ) (hδ : 0 ≤ δψ)
    (hK : 0 < KhatM0 ell a t ρ) (hcg : 0 < cg1 ell a t ρ θ hc νψ)
    (hEG : 4 * EGM1 ell a ρ θ hc νψ δψ hν hδ ≤ cg1 ell a t ρ θ hc νψ) : ℝ :=
  (modelNOf (hc.ginv1 νψ δψ hν hδ) (cg1 ell a t ρ θ hc νψ) (qBS ell a ρ) (bN1 ell a t ρ θ hc νψ) hcg hEG
    (by unfold qBS; positivity) (bN1_pos ell a t ρ θ hc νψ hν hK)).EN

/-- the bundle of `ψ`-data for the perturbation -/
structure PsiBd (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (θ : ℝ) where
  ψ : FSp (GF ell k Lu)
  S : ℝ
  K : ℝ
  νψ : ℝ
  δψ : ℝ
  hS : 0 ≤ S
  hK : 0 ≤ K
  hψ : ∀ p, ‖ψ p‖ ≤ S
  hC : ∀ z : BondFnL2 (scaleUp ell k Lu), ∑ p, ‖C2fullOf (GF ell k Lu) U z p‖ ≤ K * ‖z‖ ^ 2
  hνψ : ((ell : ℝ) ^ k) ^ 2 * (2 * S * K) ≤ νψ
  hδψ : ((ell : ℝ) ^ k) ^ 2 * (2 * S * K * 648 * ((Real.exp (5 * θ) - 1) * (Real.exp (5 * θ) + 1))) ≤ δψ

theorem PsiBd.νψ_nonneg {ell k : ℕ} {Lu : PeriodicLatticeExtent} {U : Cfg (scaleUp ell k Lu)} {θ : ℝ}
    (pd : PsiBd ell k Lu U θ) : 0 ≤ pd.νψ :=
  le_trans (by have := pd.hS; have := pd.hK; positivity) pd.hνψ

theorem PsiBd.δψ_nonneg {ell k : ℕ} {Lu : PeriodicLatticeExtent} {U : Cfg (scaleUp ell k Lu)} {θ : ℝ}
    (pd : PsiBd ell k Lu U θ) (hθ : 0 ≤ θ) : 0 ≤ pd.δψ := by
  refine le_trans ?_ pd.hδψ
  have : 0 ≤ Real.exp (5 * θ) - 1 := by linarith [Real.add_one_le_exp (5 * θ)]
  have := pd.hS; have := pd.hK
  positivity

/-- the scaled CT instance for `G₁⁻¹`, bundled -/
noncomputable def G1M0 (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
    (R : M0RegimeR ell k Lu U a t e q0) (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0))
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ) (hφ : WtLip (θ / (ell : ℝ) ^ k) φ)
    (hc : CondM0 ell a (rhoM0 ell k e q0) θ) (pd : PsiBd ell k Lu U θ) :
    GinvHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu))
      (PlaqFnL2 (scaleUp ell k Lu)) (FSp (GF ell k Lu)) :=
  ginv1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd.ψ pd.S pd.K pd.νψ pd.δψ pd.hS pd.hK pd.hψ pd.hC pd.hνψ pd.hδψ

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
  (R : M0RegimeR ell k Lu U a t e q0) (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0))
  (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ)
  (hφ : WtLip (θ / (ell : ℝ) ^ k) φ) (hc : CondM0 ell a (rhoM0 ell k e q0) θ) (pd : PsiBd ell k Lu U θ)

theorem G1M0_eq : (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).Ginv = ((ell : ℝ) ^ k) ^ 2 • G1Full ell k Lu U a pd.ψ :=
  ginv1M0_eq ell k Lu U a t e q0 R H φ θ hφ hc pd.ψ pd.S pd.K pd.νψ pd.δψ pd.hS pd.hK pd.hψ pd.hC pd.hνψ pd.hδψ

theorem G1M0_EG : (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).EG
    = EGM1 ell a (rhoM0 ell k e q0) θ hc pd.νψ pd.δψ pd.νψ_nonneg (pd.δψ_nonneg hc.hθ) := rfl

theorem G1M0_Qb : (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).Qb = (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Qb := rfl

theorem G1M0_ωE : (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).ωE = bondWP φ := rfl
theorem G1M0_ωB : (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).ωB = fspWP ell k Lu φ := rfl

theorem G1M0_lower (f : BondFnL2 (scaleUp ell k Lu)) :
    ⟪f, (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Ginv f⟫ - pd.νψ * hc.ginv.nW ^ 2 * ‖f‖ ^ 2
      ≤ ⟪f, (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).Ginv f⟫ := by
  unfold G1M0 ginv1M0
  exact GinvHyp.pert_form_lower _ _ _ _ _ _ _ _ _ _ f

theorem G1M0_upper (f : BondFnL2 (scaleUp ell k Lu)) :
    ⟪f, (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).Ginv f⟫
      ≤ ⟪f, (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Ginv f⟫ + pd.νψ * hc.ginv.nW ^ 2 * ‖f‖ ^ 2 := by
  unfold G1M0 ginv1M0
  exact GinvHyp.pert_form_upper _ _ _ _ _ _ _ _ _ _ f

theorem coer1M0 (f : BondFnL2 (scaleUp ell k Lu)) :
    cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ * ‖f‖ ^ 2 ≤ ⟪f, (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).Ginv f⟫ := by
  have h1 := G1M0_lower ell k Lu U a t e q0 R H φ θ hφ hc pd f
  have h2 := coerM0 ell k Lu U a t e q0 R H φ θ hφ hc f
  unfold cg1
  nlinarith

include R H hφ in
theorem G1Full_isUnit (hcg : 0 < cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ) : IsUnit (G1Full ell k Lu U a pd.ψ) := by
  have hn2 : (0 : ℝ) < ((ell : ℝ) ^ k) ^ 2 := by have := R.hell; positivity
  have hco : ∀ f, (cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ / ((ell : ℝ) ^ k) ^ 2) * ‖f‖ ^ 2
      ≤ ⟪f, G1Full ell k Lu U a pd.ψ f⟫ := by
    intro f
    have h := coer1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd f
    rw [G1M0_eq, ContinuousLinearMap.smul_apply, real_inner_smul_right] at h
    rw [div_mul_eq_mul_div, div_le_iff₀ hn2]; nlinarith
  exact coercive_isUnit _ (by positivity) hco

/-- the scaled `G₁` -/
noncomputable def GiM1 : BondFnL2 (scaleUp ell k Lu) →L[ℝ] BondFnL2 (scaleUp ell k Lu) :=
  (((ell : ℝ) ^ k) ^ 2)⁻¹ • Ring.inverse (G1Full ell k Lu U a pd.ψ)

theorem GiM1_1 (hcg : 0 < cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ) (x : BondFnL2 (scaleUp ell k Lu)) :
    (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).Ginv (GiM1 ell k Lu U a θ pd x) = x := by
  have hn2 : (0 : ℝ) < ((ell : ℝ) ^ k) ^ 2 := by have := R.hell; positivity
  have hu := G1Full_isUnit ell k Lu U a t e q0 R H φ θ hφ hc pd hcg
  rw [G1M0_eq, GiM1, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul,
    mul_inv_cancel₀ hn2.ne', one_smul, ← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hu,
    ContinuousLinearMap.one_apply]

theorem GiM1_2 (hcg : 0 < cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ) (x : BondFnL2 (scaleUp ell k Lu)) :
    GiM1 ell k Lu U a θ pd ((G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).Ginv x) = x := by
  have hn2 : (0 : ℝ) < ((ell : ℝ) ^ k) ^ 2 := by have := R.hell; positivity
  have hu := G1Full_isUnit ell k Lu U a t e q0 R H φ θ hφ hc pd hcg
  rw [G1M0_eq, GiM1, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul,
    inv_mul_cancel₀ hn2.ne', one_smul, ← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hu,
    ContinuousLinearMap.one_apply]

/-- the extension, now with the `G₁⁻¹` energy -/
theorem ext1M0 (u : FSp (GF ell k Lu)) :
    ∃ g : BondFnL2 (scaleUp ell k Lu), (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).Qb g = u ∧
      ⟪g, (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).Ginv g⟫ ≤ bN1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ * ‖u‖ ^ 2 := by
  obtain ⟨g, hg, hgE⟩ := bondExtM0 ell k Lu U a t e q0 R H φ θ hφ hc u
  refine ⟨g, hg, ?_⟩
  have h1 := G1M0_upper ell k Lu U a t e q0 R H φ θ hφ hc pd g
  have h2 := coerM0 ell k Lu U a t e q0 R H φ θ hφ hc g
  have hK0 := KhatM0_pos ell k Lu U a t e q0 R
  have hν0 := pd.νψ_nonneg
  have hW0 := nW_model_nonneg hc
  have hg2 : ‖g‖ ^ 2 ≤ KhatM0 ell a t (rhoM0 ell k e q0) * ⟪g, (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Ginv g⟫ := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hK0] at h2; linarith
  have hc1 : 0 ≤ pd.νψ * hc.ginv.nW ^ 2 := by positivity
  have h3 : pd.νψ * hc.ginv.nW ^ 2 * ‖g‖ ^ 2
      ≤ pd.νψ * hc.ginv.nW ^ 2 * KhatM0 ell a t (rhoM0 ell k e q0) * ⟪g, (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Ginv g⟫ := by
    have := mul_le_mul_of_nonneg_left hg2 hc1; linarith
  have hb : 0 ≤ 1 + pd.νψ * hc.ginv.nW ^ 2 * KhatM0 ell a t (rhoM0 ell k e q0) := by positivity
  have h4 := mul_le_mul_of_nonneg_left hgE hb
  unfold bN1
  nlinarith

/-- the scaled Schur complement of `G₁` -/
noncomputable def N1opM0 : FSp (GF ell k Lu) →L[ℝ] FSp (GF ell k Lu) :=
  (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).Qb ∘L GiM1 ell k Lu U a θ pd
    ∘L ContinuousLinearMap.adjoint (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).Qb

theorem N1opM0_coer (hcg : 0 < cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ) (u : FSp (GF ell k Lu)) :
    (1 / bN1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ) * ‖u‖ ^ 2 ≤ ⟪u, N1opM0 ell k Lu U a t e q0 R H φ θ hφ hc pd u⟫ := by
  have hK0 := KhatM0_pos ell k Lu U a t e q0 R
  have hb := bN1_pos ell a t (rhoM0 ell k e q0) θ hc pd.νψ pd.νψ_nonneg hK0
  have h := (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).N_lower_of (GiM1 ell k Lu U a θ pd)
    (GiM1_1 ell k Lu U a t e q0 R H φ θ hφ hc pd hcg) (cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ) hcg
    (coer1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd) (bN1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ) hb
    (ext1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd) u
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hb]
  have e1 : ⟪u, N1opM0 ell k Lu U a t e q0 R H φ θ hφ hc pd u⟫
      = ⟪u, ((G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).Qb ∘L GiM1 ell k Lu U a θ pd
          ∘L ContinuousLinearMap.adjoint (G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd).Qb) u⟫ := rfl
  rw [e1]; linarith

/-- **the M0 Schur-complement structure for `G₁`** -/
noncomputable def n1M0 (hcg : 0 < cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ)
    (hEG : 4 * EGM1 ell a (rhoM0 ell k e q0) θ hc pd.νψ pd.δψ pd.νψ_nonneg (pd.δψ_nonneg hc.hθ)
      ≤ cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ) :
    NHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu))
      (PlaqFnL2 (scaleUp ell k Lu)) (FSp (GF ell k Lu)) where
  toGinvHyp := G1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd
  Gi := GiM1 ell k Lu U a θ pd
  Ninv := Ring.inverse (N1opM0 ell k Lu U a t e q0 R H φ θ hφ hc pd)
  cg := cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ
  qb := qBS ell a (rhoM0 ell k e q0)
  bN := bN1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ
  hGi1 := GiM1_1 ell k Lu U a t e q0 R H φ θ hφ hc pd hcg
  hGi2 := GiM1_2 ell k Lu U a t e q0 R H φ θ hφ hc pd hcg
  hcg := hcg
  hcoerG := coer1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd
  hEG := by rw [G1M0_EG]; exact hEG
  hqb := by unfold qBS; positivity
  hQb := by rw [G1M0_Qb]; exact m0_hQbN ell k Lu U a t e q0 R H φ θ hφ hc
  hbN := bN1_pos ell a t (rhoM0 ell k e q0) θ hc pd.νψ pd.νψ_nonneg (KhatM0_pos ell k Lu U a t e q0 R)
  extN := ext1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd
  hN1 := fun u => by
    have hb := bN1_pos ell a t (rhoM0 ell k e q0) θ hc pd.νψ pd.νψ_nonneg (KhatM0_pos ell k Lu U a t e q0 R)
    exact coercive_apply_inverse _ (by positivity) (N1opM0_coer ell k Lu U a t e q0 R H φ θ hφ hc pd hcg) u
  hN2 := fun u => by
    have hb := bN1_pos ell a t (rhoM0 ell k e q0) θ hc pd.νψ pd.νψ_nonneg (KhatM0_pos ell k Lu U a t e q0 R)
    have hu := coercive_isUnit _ (by positivity : (0 : ℝ) < 1 / bN1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ)
      (N1opM0_coer ell k Lu U a t e q0 R H φ θ hφ hc pd hcg)
    show Ring.inverse (N1opM0 ell k Lu U a t e q0 R H φ θ hφ hc pd) (N1opM0 ell k Lu U a t e q0 R H φ θ hφ hc pd u) = u
    rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hu, ContinuousLinearMap.one_apply]

theorem n1M0_EN (hcg : 0 < cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ)
    (hEG : 4 * EGM1 ell a (rhoM0 ell k e q0) θ hc pd.νψ pd.δψ pd.νψ_nonneg (pd.δψ_nonneg hc.hθ)
      ≤ cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ) :
    (n1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd hcg hEG).EN
      = EN1free ell a t (rhoM0 ell k e q0) θ hc pd.νψ pd.δψ pd.νψ_nonneg (pd.δψ_nonneg hc.hθ)
          (KhatM0_pos ell k Lu U a t e q0 R) hcg hEG := rfl

/-- **`H1_CT_M0`: the weighted bound of the scaled `H₁`, k- and volume-uniform** -/
theorem H1_CT_M0 (hcg : 0 < cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ)
    (hEG : 4 * EGM1 ell a (rhoM0 ell k e q0) θ hc pd.νψ pd.δψ pd.νψ_nonneg (pd.δψ_nonneg hc.hθ)
      ≤ cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ)
    (hN : EN1free ell a t (rhoM0 ell k e q0) θ hc pd.νψ pd.δψ pd.νψ_nonneg (pd.δψ_nonneg hc.hθ)
      (KhatM0_pos ell k Lu U a t e q0 R) hcg hEG < 1 / bN1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ)
    (w : FSp (GF ell k Lu)) :
    ‖cjp (fspWP ell k Lu φ) (bondWP φ) (n1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd hcg hEG).H w‖
      ≤ (2 / cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ) * (qBS ell a (rhoM0 ell k e q0) + δBS ell a (rhoM0 ell k e q0) θ)
        / (1 / bN1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ
          - EN1free ell a t (rhoM0 ell k e q0) θ hc pd.νψ pd.δψ pd.νψ_nonneg (pd.δψ_nonneg hc.hθ)
              (KhatM0_pos ell k Lu U a t e q0 R) hcg hEG)
        * ‖w‖ := by
  have hcN : 0 < 1 / (n1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd hcg hEG).bN
      - (n1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd hcg hEG).EN := by
    rw [n1M0_EN]; show 0 < 1 / bN1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ - _; linarith
  have h := (n1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd hcg hEG).H_cjp hcN w
  rw [n1M0_EN] at h
  exact h

end

#print axioms modelNOf
#print axioms coer1M0
#print axioms G1Full_isUnit
#print axioms ext1M0
#print axioms N1opM0_coer
#print axioms n1M0
#print axioms H1_CT_M0

end AdalyFormal.DLayer
