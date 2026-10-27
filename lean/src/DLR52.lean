import DLR51

/-!
# DL52 -- the M0 Schur complement `N = Q G Q*` as an `NHyp` (DL18), and **`H_CT_M0`**: the k-uniform weighted bound of `H`

* `GinvHyp.Ginv_sym'`, `GinvHyp.N_lower_of` : `‖u‖² ≤ b_N ⟪u, Q_b G Q_b* u⟫` from any competitor (DL18 `N_lower` without `N⁻¹`).
* `qBS ℓ a ρ = √a e^{3600ℓρ/r}` (k-free bound of the scaled `‖Q_b‖`), `m0_hQbN`.
* `nM0` : the `NHyp` on the SCALED genuine instance (`Gi = n⁻² GinvFull⁻¹`, `N⁻¹ = Ring.inverse`, `cg = 1/K̂`, `qb = qBS`,
  `bN = bNS` (DL50), `extN = bondExtM0`).
* `CondM0.modelN`, `ENfree` : the Schur-complement error constant `E_N` of DL19 evaluated on the model structure — a function
  of `(ℓ, a, t, ρ, θ)` only; `nM0_EN` : the genuine `E_N` IS `ENfree` (rfl).
* **`H_CT_M0`** : `‖e^{φ} H' e^{−φ} w‖ ≤ 2K̂ (qBS + δBS)/(1/bNS − ENfree) ‖w‖` for the scaled `H' = n⁻²G (√(an³)Q)* N'⁻¹`.
* **`dataH_scaled`** : `ι(data.H w) = √(a n³) · H' w` (the genuine `H` of (3.126) is `√(a n³)` times the scaled one).
-/
set_option autoImplicit false
set_option maxHeartbeats 128000000
set_option maxRecDepth 200000

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

namespace GinvHyp

variable {S E Y P B : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]
variable (I : GinvHyp S E Y P B)

theorem Ginv_sym' (x y : E) : ⟪I.Ginv x, y⟫ = ⟪x, I.Ginv y⟫ := by
  simp only [Ginv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  rw [I.hDps]

/-- the sharp lower bound of `Q_b G Q_b*` from a competitor (no inverse of `N` needed) -/
theorem N_lower_of (Gi : E →L[ℝ] E) (hGi1 : ∀ x, I.Ginv (Gi x) = x) (cg : ℝ) (hcg : 0 < cg)
    (hcoerG : ∀ f, cg * ‖f‖ ^ 2 ≤ ⟪f, I.Ginv f⟫) (bN : ℝ) (hbN : 0 < bN)
    (extN : ∀ u : B, ∃ g : E, I.Qb g = u ∧ ⟪g, I.Ginv g⟫ ≤ bN * ‖u‖ ^ 2) (u : B) :
    ‖u‖ ^ 2 ≤ bN * ⟪u, (I.Qb ∘L Gi ∘L ContinuousLinearMap.adjoint I.Qb) u⟫ := by
  obtain ⟨g, hg, hgE⟩ := extN u
  set x := Gi (ContinuousLinearMap.adjoint I.Qb u)
  have hx : I.Ginv x = ContinuousLinearMap.adjoint I.Qb u := hGi1 _
  have hNu : ⟪u, (I.Qb ∘L Gi ∘L ContinuousLinearMap.adjoint I.Qb) u⟫ = ⟪x, I.Ginv x⟫ := by
    rw [hx, ContinuousLinearMap.adjoint_inner_right, real_inner_comm]; rfl
  have e1 : ‖u‖ ^ 2 = ⟪x, I.Ginv g⟫ := by
    rw [← I.Ginv_sym', hx, ContinuousLinearMap.adjoint_inner_left, hg, real_inner_self_eq_norm_sq]
  have hpos : ∀ y, 0 ≤ ⟪y, I.Ginv y⟫ := fun y => le_trans (by positivity) (hcoerG y)
  have hCS : ⟪x, I.Ginv g⟫ ^ 2 ≤ ⟪x, I.Ginv x⟫ * ⟪g, I.Ginv g⟫ := by
    have hq' : ∀ t : ℝ, 0 ≤ ⟪x, I.Ginv x⟫ + 2 * t * ⟪x, I.Ginv g⟫ + t ^ 2 * ⟪g, I.Ginv g⟫ := by
      intro t
      have := hpos (x + t • g)
      have e : ⟪x + t • g, I.Ginv (x + t • g)⟫
          = ⟪x, I.Ginv x⟫ + 2 * t * ⟪x, I.Ginv g⟫ + t ^ 2 * ⟪g, I.Ginv g⟫ := by
        simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
        have : ⟪g, I.Ginv x⟫ = ⟪x, I.Ginv g⟫ := by rw [← I.Ginv_sym', real_inner_comm]
        rw [this]; ring
      rw [e] at this; exact this
    by_cases hg0 : ⟪g, I.Ginv g⟫ = 0
    · have hx0 : ⟪x, I.Ginv g⟫ = 0 := by
        by_contra hne
        have ht := hq' (-(⟪x, I.Ginv x⟫ + 1) / (2 * ⟪x, I.Ginv g⟫))
        have e : 2 * (-(⟪x, I.Ginv x⟫ + 1) / (2 * ⟪x, I.Ginv g⟫)) * ⟪x, I.Ginv g⟫
            = -(⟪x, I.Ginv x⟫ + 1) := by field_simp
        rw [hg0, e] at ht
        linarith [ht, mul_zero ((-(⟪x, I.Ginv x⟫ + 1) / (2 * ⟪x, I.Ginv g⟫)) ^ 2)]
      rw [hx0, hg0]; simp
    · have hgpos : 0 < ⟪g, I.Ginv g⟫ := lt_of_le_of_ne (hpos g) (Ne.symm hg0)
      have := hq' (-⟪x, I.Ginv g⟫ / ⟪g, I.Ginv g⟫)
      have e : ⟪x, I.Ginv x⟫ + 2 * (-⟪x, I.Ginv g⟫ / ⟪g, I.Ginv g⟫) * ⟪x, I.Ginv g⟫
          + (-⟪x, I.Ginv g⟫ / ⟪g, I.Ginv g⟫) ^ 2 * ⟪g, I.Ginv g⟫
          = ⟪x, I.Ginv x⟫ - ⟪x, I.Ginv g⟫ ^ 2 / ⟪g, I.Ginv g⟫ := by field_simp; ring
      rw [e] at this
      have h2 : ⟪x, I.Ginv g⟫ ^ 2 / ⟪g, I.Ginv g⟫ ≤ ⟪x, I.Ginv x⟫ := by linarith
      rwa [div_le_iff₀ hgpos] at h2
  have h4 : ‖u‖ ^ 4 ≤ ⟪x, I.Ginv x⟫ * (bN * ‖u‖ ^ 2) := by
    have : ‖u‖ ^ 4 = ⟪x, I.Ginv g⟫ ^ 2 := by rw [← e1]; ring
    rw [this]
    exact hCS.trans (mul_le_mul_of_nonneg_left hgE (hpos x))
  rw [hNu]
  by_cases hu : ‖u‖ = 0
  · rw [hu]
    have h0 : (0:ℝ) ^ 2 = 0 := by norm_num
    rw [h0]; exact mul_nonneg hbN.le (hpos x)
  have hu2 : 0 < ‖u‖ ^ 2 := by have := norm_nonneg u; positivity
  nlinarith

end GinvHyp

/-- the k-free bound of the scaled bond map -/
noncomputable def qBS (ell : ℕ) (a ρ : ℝ) : ℝ := Real.sqrt a * Real.exp (3600 * (ell : ℝ) * ρ / rr ell)

theorem bNS_pos (a ρ δ : ℝ) (hν : 0 ≤ νS ρ) : 0 < bNS a ρ δ := by
  unfold bNS
  have := sq_nonneg (cNS a ρ δ + κS ρ * (dNS a ρ δ / cS a ρ))
  have := mul_nonneg hν (sq_nonneg (gNS a δ + dNS a ρ δ / Real.sqrt (cS a ρ)))
  have := sq_nonneg (dNS a ρ δ)
  linarith

/-- the model Schur-complement structure of the k-free parameters -/
noncomputable def CondM0.modelN {ell : ℕ} {a ρ θ : ℝ} (hc : CondM0 ell a ρ θ) (cg qb bN : ℝ) (hcg : 0 < cg)
    (hEG : 4 * hc.ginv.EG ≤ cg) (hqb : 0 ≤ qb) (hbN : 0 < bN) : NHyp Z0 Z0 Z0 Z0 Z0 where
  toGinvHyp := hc.ginv
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
  hQb := by show ‖(0 : Z0 →L[ℝ] Z0)‖ ≤ qb; rw [norm_zero]; exact hqb
  hbN := hbN
  extN := fun u => ⟨0, Z0_eq _ _, by rw [Z0_zero u]; simp⟩
  hN1 := fun u => Z0_eq _ _
  hN2 := fun u => Z0_eq _ _

/-- **the k-free Schur-complement error constant** (`E_N` of DL19 on the model structure: a function of `(ℓ,a,t,ρ,θ)`) -/
noncomputable def ENfree (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (hK : 0 < KhatM0 ell a t ρ)
    (hEG : 4 * EGM0 ell a ρ θ hc ≤ 1 / KhatM0 ell a t ρ) : ℝ :=
  (hc.modelN (1 / KhatM0 ell a t ρ) (qBS ell a ρ) (bNS a ρ (δS ell ρ)) (by positivity) hEG
    (by unfold qBS; positivity) (bNS_pos a ρ (δS ell ρ) hc.νS_nonneg)).EN

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
  (R : M0RegimeR ell k Lu U a t e q0) (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0))
  (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ)
  (hφ : WtLip (θ / (ell : ℝ) ^ k) φ) (hc : CondM0 ell a (rhoM0 ell k e q0) θ)

include R H in
theorem m0_qbM_le : Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) * qbM ell k (epsCl ell e q0) ≤ qBS ell a (rhoM0 ell k e q0) := by
  have hell := R.hell
  have hell0 : 0 < ell := by omega
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  have hrr : 0 < rr ell := Real.sqrt_pos.mpr (by positivity)
  have hrr2 : rr ell ^ 2 = 1 / (ell : ℝ) := AdalyFormal.BondComposite.rr_sq ell hell0
  have hsc : Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) * (((ell : ℝ) ^ k)⁻¹ * rr ell ^ k) = Real.sqrt a := by
    have h0 : 0 ≤ Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) * (((ell : ℝ) ^ k)⁻¹ * rr ell ^ k) := by
      have := rr ell; positivity
    have hrk : (rr ell ^ k) ^ 2 = 1 / (ell : ℝ) ^ k := by
      rw [← pow_mul, mul_comm, pow_mul, hrr2, div_pow, one_pow]
    rw [← Real.sqrt_sq h0]
    congr 1
    rw [mul_pow, Real.sq_sqrt (by have := R.ha; positivity), mul_pow, hrk]
    field_simp
  have hS := m0_S ell k Lu U a t e q0 R
  have hexp : Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (epsCl ell e q0 i)) / rr ell)
      ≤ Real.exp (3600 * (ell : ℝ) * rhoM0 ell k e q0 / rr ell) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hS hrr.le)
  unfold qbM qBS
  calc Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3)
        * (((ell : ℝ) ^ k)⁻¹ * (rr ell ^ k * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (epsCl ell e q0 i)) / rr ell)))
      = (Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) * (((ell : ℝ) ^ k)⁻¹ * rr ell ^ k))
          * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (epsCl ell e q0 i)) / rr ell) := by ring
    _ = Real.sqrt a * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (epsCl ell e q0 i)) / rr ell) := by rw [hsc]
    _ ≤ Real.sqrt a * Real.exp (3600 * (ell : ℝ) * rhoM0 ell k e q0 / rr ell) :=
        mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)

include R H in
theorem m0_hQbN : ‖(ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Qb‖ ≤ qBS ell a (rhoM0 ell k e q0) := by
  have hell0 : 0 < ell := by have := R.hell; omega
  have hq := m0_qbM_le ell k Lu U a t e q0 R H
  have hq0 : 0 ≤ qBS ell a (rhoM0 ell k e q0) := by unfold qBS; positivity
  refine opnorm_le_of _ _ hq0 (fun x => ?_)
  show ‖(Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) • (bondSectorOf (GF ell k Lu) U).Qfull) x‖ ≤ _
  rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := Qfull_norm_le ell k Lu hell0 U (epsCl ell e q0)
    (AdalyFormal.RegBgKU.regTower_M0_kuniform ell k Lu R.hell U e q0 R.he0 R.hq0 R.hlinks R.hplaq H)
    (m0_cl ell k Lu U a t e q0 R) (m0_hε0 ell k Lu U a t e q0 R) (m0_hsm ell k Lu U a t e q0 R) x
  calc Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) * ‖(bondSectorOf (GF ell k Lu) U).Qfull x‖
      ≤ Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) * (qbM ell k (epsCl ell e q0) * ‖x‖) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = (Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) * qbM ell k (epsCl ell e q0)) * ‖x‖ := by ring
    _ ≤ qBS ell a (rhoM0 ell k e q0) * ‖x‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)

/-- the scaled `G` -/
noncomputable def GiM0 : BondFnL2 (scaleUp ell k Lu) →L[ℝ] BondFnL2 (scaleUp ell k Lu) :=
  (((ell : ℝ) ^ k) ^ 2)⁻¹ • Ring.inverse (GinvFull ell k Lu U a)

include H in
theorem GiM0_1 (x : BondFnL2 (scaleUp ell k Lu)) :
    (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Ginv (GiM0 ell k Lu U a x) = x := by
  have hn2 : (0 : ℝ) < ((ell : ℝ) ^ k) ^ 2 := by have := R.hell; positivity
  have hu := GinvFull_isUnit ell k Lu U a t e q0 R H
  rw [ginvM0_eq, GiM0, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul,
    mul_inv_cancel₀ hn2.ne', one_smul, ← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hu,
    ContinuousLinearMap.one_apply]

include H in
theorem GiM0_2 (x : BondFnL2 (scaleUp ell k Lu)) :
    GiM0 ell k Lu U a ((ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Ginv x) = x := by
  have hn2 : (0 : ℝ) < ((ell : ℝ) ^ k) ^ 2 := by have := R.hell; positivity
  have hu := GinvFull_isUnit ell k Lu U a t e q0 R H
  rw [ginvM0_eq, GiM0, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul,
    inv_mul_cancel₀ hn2.ne', one_smul, ← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hu,
    ContinuousLinearMap.one_apply]

theorem coerM0 (f : BondFnL2 (scaleUp ell k Lu)) :
    (1 / KhatM0 ell a t (rhoM0 ell k e q0)) * ‖f‖ ^ 2 ≤ ⟪f, (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Ginv f⟫ := by
  have hK := KhatM0_pos ell k Lu U a t e q0 R
  rw [ginvM0_eq, ContinuousLinearMap.smul_apply, real_inner_smul_right]
  have h := GinvFull_coercive ell k Lu U a t e q0 R H f
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hK]
  nlinarith [h]

/-- the scaled Schur complement -/
noncomputable def NopM0 : FSp (GF ell k Lu) →L[ℝ] FSp (GF ell k Lu) :=
  (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Qb ∘L GiM0 ell k Lu U a
    ∘L ContinuousLinearMap.adjoint (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Qb

theorem NopM0_coer (u : FSp (GF ell k Lu)) :
    (1 / bNS a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0))) * ‖u‖ ^ 2 ≤ ⟪u, NopM0 ell k Lu U a t e q0 R H φ θ hφ hc u⟫ := by
  have hb := bNS_pos a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0)) hc.νS_nonneg
  have hK := KhatM0_pos ell k Lu U a t e q0 R
  have h := (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).N_lower_of (GiM0 ell k Lu U a) (GiM0_1 ell k Lu U a t e q0 R H φ θ hφ hc)
    (1 / KhatM0 ell a t (rhoM0 ell k e q0)) (by positivity) (coerM0 ell k Lu U a t e q0 R H φ θ hφ hc)
    (bNS a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0))) hb (bondExtM0 ell k Lu U a t e q0 R H φ θ hφ hc) u
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hb]
  have e1 : ⟪u, NopM0 ell k Lu U a t e q0 R H φ θ hφ hc u⟫
      = ⟪u, ((ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Qb ∘L GiM0 ell k Lu U a
          ∘L ContinuousLinearMap.adjoint (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Qb) u⟫ := rfl
  rw [e1]; linarith

/-- **the M0 Schur-complement structure** -/
noncomputable def nM0 (hEG : 4 * EGM0 ell a (rhoM0 ell k e q0) θ hc ≤ 1 / KhatM0 ell a t (rhoM0 ell k e q0)) :
    NHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu))
      (PlaqFnL2 (scaleUp ell k Lu)) (FSp (GF ell k Lu)) where
  toGinvHyp := ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H
  Gi := GiM0 ell k Lu U a
  Ninv := Ring.inverse (NopM0 ell k Lu U a t e q0 R H φ θ hφ hc)
  cg := 1 / KhatM0 ell a t (rhoM0 ell k e q0)
  qb := qBS ell a (rhoM0 ell k e q0)
  bN := bNS a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0))
  hGi1 := GiM0_1 ell k Lu U a t e q0 R H φ θ hφ hc
  hGi2 := GiM0_2 ell k Lu U a t e q0 R H φ θ hφ hc
  hcg := by have := KhatM0_pos ell k Lu U a t e q0 R; positivity
  hcoerG := coerM0 ell k Lu U a t e q0 R H φ θ hφ hc
  hEG := by rw [ginvM0_EG]; exact hEG
  hqb := by unfold qBS; positivity
  hQb := m0_hQbN ell k Lu U a t e q0 R H φ θ hφ hc
  hbN := bNS_pos a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0)) hc.νS_nonneg
  extN := bondExtM0 ell k Lu U a t e q0 R H φ θ hφ hc
  hN1 := fun u => by
    have hb := bNS_pos a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0)) hc.νS_nonneg
    exact coercive_apply_inverse _ (by positivity) (NopM0_coer ell k Lu U a t e q0 R H φ θ hφ hc) u
  hN2 := fun u => by
    have hb := bNS_pos a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0)) hc.νS_nonneg
    have hu := coercive_isUnit _ (by positivity : (0 : ℝ) < 1 / bNS a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0)))
      (NopM0_coer ell k Lu U a t e q0 R H φ θ hφ hc)
    show Ring.inverse (NopM0 ell k Lu U a t e q0 R H φ θ hφ hc) (NopM0 ell k Lu U a t e q0 R H φ θ hφ hc u) = u
    rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hu, ContinuousLinearMap.one_apply]

theorem nM0_EN (hEG : 4 * EGM0 ell a (rhoM0 ell k e q0) θ hc ≤ 1 / KhatM0 ell a t (rhoM0 ell k e q0)) :
    (nM0 ell k Lu U a t e q0 R H φ θ hφ hc hEG).EN
      = ENfree ell a t (rhoM0 ell k e q0) θ hc (KhatM0_pos ell k Lu U a t e q0 R) hEG := rfl

/-- **`H_CT_M0`: the weighted bound of the scaled `H`, k- and volume-uniform** -/
theorem H_CT_M0 (hEG : 4 * EGM0 ell a (rhoM0 ell k e q0) θ hc ≤ 1 / KhatM0 ell a t (rhoM0 ell k e q0))
    (hN : ENfree ell a t (rhoM0 ell k e q0) θ hc (KhatM0_pos ell k Lu U a t e q0 R) hEG < 1 / bNS a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0)))
    (w : FSp (GF ell k Lu)) :
    ‖cjp (fspWP ell k Lu φ) (bondWP φ) (nM0 ell k Lu U a t e q0 R H φ θ hφ hc hEG).H w‖
      ≤ (2 * KhatM0 ell a t (rhoM0 ell k e q0)) * (qBS ell a (rhoM0 ell k e q0) + δBS ell a (rhoM0 ell k e q0) θ)
        / (1 / bNS a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0)) - ENfree ell a t (rhoM0 ell k e q0) θ hc (KhatM0_pos ell k Lu U a t e q0 R) hEG)
        * ‖w‖ := by
  have hK := KhatM0_pos ell k Lu U a t e q0 R
  have hcN : 0 < 1 / (nM0 ell k Lu U a t e q0 R H φ θ hφ hc hEG).bN - (nM0 ell k Lu U a t e q0 R H φ θ hφ hc hEG).EN := by
    rw [nM0_EN]; show 0 < 1 / bNS a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0)) - _; linarith
  have h := (nM0 ell k Lu U a t e q0 R H φ θ hφ hc hEG).H_cjp hcN w
  have e1 : (2 / (nM0 ell k Lu U a t e q0 R H φ θ hφ hc hEG).cg) = 2 * KhatM0 ell a t (rhoM0 ell k e q0) := by
    show 2 / (1 / KhatM0 ell a t (rhoM0 ell k e q0)) = _
    field_simp
  rw [e1, nM0_EN] at h
  exact h

end

#print axioms GinvHyp.Ginv_sym'
#print axioms GinvHyp.N_lower_of
#print axioms bNS_pos
#print axioms CondM0.modelN
#print axioms m0_qbM_le
#print axioms m0_hQbN
#print axioms GiM0_1
#print axioms GiM0_2
#print axioms coerM0
#print axioms NopM0_coer
#print axioms nM0
#print axioms ENfree
#print axioms nM0_EN
#print axioms H_CT_M0

end AdalyFormal.DLayer
