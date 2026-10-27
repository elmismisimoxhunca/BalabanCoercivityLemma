import DLR82

/-!
# DL83 -- the genuine `H₁` of (3.129) in fine-bond form, its scaling, and **`hH1col_M0`** (premise hH1col of DL5)

* `dataG1_eq` : `data.G1 G1inv = P ∘ G1Full⁻¹ ∘ ι`;  `N1f = Q G1Full⁻¹ Q*`;  `dataN1_eq`;  **`dataH1_eq`**;
* `N1opM0_eq` (`N1op = (s²/n²) N1f`, `s = √(a n³)`), `N1f_isUnit`, **`dataH1_scaled`** : `ι(data.H1 w) = s • H₁'(w)`;
* `tauAdj_single` : `τ*(δ_{e'} v) = δ_{p(e')} v` (or `0`);
* **`hH1col_M0`** : `Σ_b ‖(H₁in δ_{e'}^v)(b)‖ ≤ CH1free·n³·‖v‖`,
  `CH1free = √3·√a·(1/θ+2)^{3/2}·(2/cg1)(qBS + δBS)/(1/bN1 − EN1free)` — k- and volume-free.
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
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.AsmM0 (M0RegimeR rhoM0 Mc KhatM0 phiC ThetaM0)
open AdalyFormal.BondComposite (rr TowerClass thetaOf)
open AdalyFormal.M0Finish (PU)

section data
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))

theorem dataG1_eq (hu : IsUnit (G1Full ell k Lu U a (psiD (PU ell k Lu hell U a Lam)))) :
    (PU ell k Lu hell U a Lam).data.G1 (PU ell k Lu hell U a Lam).G1inv
      = pE (GF ell k Lu) ∘L Ring.inverse (G1Full ell k Lu U a (psiD (PU ell k Lu hell U a Lam))) ∘L iE (GF ell k Lu) := by
  unfold BaseDataS.G1
  rw [dataG1inv_eq]
  set F := G1Full ell k Lu U a (psiD (PU ell k Lu hell U a Lam))
  apply ring_inverse_eq_of
  · ext1 z
    show pE (GF ell k Lu) (F (iE (GF ell k Lu) (pE (GF ell k Lu) (Ring.inverse F (iE (GF ell k Lu) z))))) = z
    rw [iE_pE_full, ← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hu, ContinuousLinearMap.one_apply,
      pE_iE_full]
  · ext1 z
    show pE (GF ell k Lu) (Ring.inverse F (iE (GF ell k Lu) (pE (GF ell k Lu) (F (iE (GF ell k Lu) z))))) = z
    rw [iE_pE_full, ← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hu, ContinuousLinearMap.one_apply,
      pE_iE_full]

/-- the fine-bond Schur complement of `G₁` -/
noncomputable def N1f (ψ : FSp (GF ell k Lu)) : FSp (GF ell k Lu) →L[ℝ] FSp (GF ell k Lu) :=
  (bondSectorOf (GF ell k Lu) U).Qfull ∘L Ring.inverse (G1Full ell k Lu U a ψ)
    ∘L ContinuousLinearMap.adjoint (bondSectorOf (GF ell k Lu) U).Qfull

theorem dataN1_eq (hu : IsUnit (G1Full ell k Lu U a (psiD (PU ell k Lu hell U a Lam)))) :
    ((PU ell k Lu hell U a Lam).data.Q.comp ((PU ell k Lu hell U a Lam).data.G1 (PU ell k Lu hell U a Lam).G1inv)).comp
        (PU ell k Lu hell U a Lam).data.Qs
      = N1f ell k Lu U a (psiD (PU ell k Lu hell U a Lam)) := by
  rw [dataG1_eq ell k Lu hell U a Lam hu, dataQs_eq, dataQ_eq]
  ext1 w
  simp only [N1f, ContinuousLinearMap.comp_apply]
  rw [iE_pE_full, iE_pE_full]

/-- **the genuine `H₁` in fine-bond form** -/
theorem dataH1_eq (hu : IsUnit (G1Full ell k Lu U a (psiD (PU ell k Lu hell U a Lam)))) (w : FSp (GF ell k Lu)) :
    iE (GF ell k Lu) ((PU ell k Lu hell U a Lam).data.H1 (PU ell k Lu hell U a Lam).G1inv w)
      = Ring.inverse (G1Full ell k Lu U a (psiD (PU ell k Lu hell U a Lam)))
          (ContinuousLinearMap.adjoint (bondSectorOf (GF ell k Lu) U).Qfull
            (Ring.inverse (N1f ell k Lu U a (psiD (PU ell k Lu hell U a Lam))) w)) := by
  unfold BaseDataS.H1
  rw [dataN1_eq ell k Lu hell U a Lam hu, dataG1_eq ell k Lu hell U a Lam hu, dataQs_eq]
  simp only [ContinuousLinearMap.comp_apply]
  rw [iE_pE_full, iE_pE_full]

end data

/-! ## the adjoint of `τ` on a single unit bond -/

open Classical in
theorem tauAdj_single (P : IngrBParams) (e' : Bond P.Lu) (v : SuTwo) :
    ContinuousLinearMap.adjoint P.tau (WithLp.toLp 2 (Pi.single e' v) : BondFnL2 P.Lu)
      = if h : unitBondEmb P.ell P.k P.Lu P.hell e' ∈ bondsLam P.G P.k
        then (WithLp.toLp 2 (Pi.single (AdalyFormal.StatementLaneG.pe P e' h) v) : FSp P.G) else 0 := by
  classical
  refine ext_inner_right ℝ (fun f => ?_)
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hl : ⟪(WithLp.toLp 2 (Pi.single e' v) : BondFnL2 P.Lu), P.tau f⟫ = ⟪v, (WithLp.ofLp (P.tau f)) e'⟫ := by
    rw [PiLp.inner_apply, Finset.sum_eq_single e']
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  rw [hl]
  split_ifs with h
  · rw [AdalyFormal.StatementLaneG.tau_apply_mem P f e' h, PiLp.inner_apply,
      Finset.sum_eq_single (AdalyFormal.StatementLaneG.pe P e' h)]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [AdalyFormal.StatementLaneG.tau_apply_not_mem P f e' h, inner_zero_right, inner_zero_left]

/-! ## the scaling of `H₁` and the column bound at M0 -/

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
  (R : M0RegimeR ell k Lu U a t e q0) (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0))
  (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ)
  (hφ : WtLip (θ / (ell : ℝ) ^ k) φ) (hc : CondM0 ell a (rhoM0 ell k e q0) θ) (pd : PsiBd ell k Lu U θ)

theorem N1opM0_eq (u : FSp (GF ell k Lu)) :
    N1opM0 ell k Lu U a t e q0 R H φ θ hφ hc pd u
      = (Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) ^ 2 / ((ell : ℝ) ^ k) ^ 2) • N1f ell k Lu U a pd.ψ u := by
  show (Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) • (bondSectorOf (GF ell k Lu) U).Qfull)
      (GiM1 ell k Lu U a θ pd (ContinuousLinearMap.adjoint
        (Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) • (bondSectorOf (GF ell k Lu) U).Qfull) u)) = _
  rw [adjoint_smul_real]
  simp only [GiM1, N1f, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_smul]
  congr 1
  ring

include R H hφ in
theorem N1f_isUnit (hcg : 0 < cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ) : IsUnit (N1f ell k Lu U a pd.ψ) := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by have := R.hell; positivity
  have hs : 0 < Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) := Real.sqrt_pos.mpr (by have := R.ha; positivity)
  have hb := bN1_pos ell a t (rhoM0 ell k e q0) θ hc pd.νψ pd.νψ_nonneg (KhatM0_pos ell k Lu U a t e q0 R)
  set c := Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) ^ 2 / ((ell : ℝ) ^ k) ^ 2 with hcdef
  have hc0 : 0 < c := by positivity
  have hco : ∀ u, (c⁻¹ * (1 / bN1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ)) * ‖u‖ ^ 2 ≤ ⟪u, N1f ell k Lu U a pd.ψ u⟫ := by
    intro u
    have h := N1opM0_coer ell k Lu U a t e q0 R H φ θ hφ hc pd hcg u
    rw [N1opM0_eq, real_inner_smul_right] at h
    rw [mul_assoc, inv_mul_le_iff₀ hc0]; linarith
  exact coercive_isUnit _ (by positivity) hco

/-- **the genuine `H₁` is `√(a n³)` times the scaled one** -/
theorem dataH1_scaled (hcg : 0 < cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ)
    (hEG : 4 * EGM1 ell a (rhoM0 ell k e q0) θ hc pd.νψ pd.δψ pd.νψ_nonneg (pd.δψ_nonneg hc.hθ)
      ≤ cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ)
    (Lam : Set (PeriodicLatticeSite Lu)) (hpd : pd.ψ = psiD (PU ell k Lu (by have := R.hell; omega) U a Lam))
    (w : FSp (GF ell k Lu)) :
    iE (GF ell k Lu) ((PU ell k Lu (by have := R.hell; omega) U a Lam).data.H1
        (PU ell k Lu (by have := R.hell; omega) U a Lam).G1inv w)
      = Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) • (n1M0 ell k Lu U a t e q0 R H φ θ hφ hc pd hcg hEG).H w := by
  have hell0 : 0 < ell := by have := R.hell; omega
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  set s := Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr (by have := R.ha; positivity)
  have hu := G1Full_isUnit ell k Lu U a t e q0 R H φ θ hφ hc pd hcg
  have hNu := N1f_isUnit ell k Lu U a t e q0 R H φ θ hφ hc pd hcg
  set c := s ^ 2 / ((ell : ℝ) ^ k) ^ 2 with hcdef
  have hc0 : 0 < c := by positivity
  have hNop : N1opM0 ell k Lu U a t e q0 R H φ θ hφ hc pd = c • N1f ell k Lu U a pd.ψ := by
    ext1 u; rw [N1opM0_eq]; rfl
  have hinv : Ring.inverse (N1opM0 ell k Lu U a t e q0 R H φ θ hφ hc pd) = c⁻¹ • Ring.inverse (N1f ell k Lu U a pd.ψ) := by
    rw [hNop]
    apply ring_inverse_eq_of
    · ext1 u
      have h1 : N1f ell k Lu U a pd.ψ (Ring.inverse (N1f ell k Lu U a pd.ψ) u) = u := by
        rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hNu, ContinuousLinearMap.one_apply]
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul, h1,
        ContinuousLinearMap.one_apply]
      simp [hc0.ne']
    · ext1 u
      have h1 : Ring.inverse (N1f ell k Lu U a pd.ψ) (N1f ell k Lu U a pd.ψ u) = u := by
        rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hNu, ContinuousLinearMap.one_apply]
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul, h1,
        ContinuousLinearMap.one_apply]
      simp [hc0.ne']
  have hu' : IsUnit (G1Full ell k Lu U a (psiD (PU ell k Lu hell0 U a Lam))) := by rw [← hpd]; exact hu
  rw [dataH1_eq ell k Lu hell0 U a Lam hu' w, ← hpd]
  show _ = s • (GiM1 ell k Lu U a θ pd (ContinuousLinearMap.adjoint (s • (bondSectorOf (GF ell k Lu) U).Qfull)
      (Ring.inverse (N1opM0 ell k Lu U a t e q0 R H φ θ hφ hc pd) w)))
  rw [hinv, adjoint_smul_real]
  simp only [GiM1, ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  symm
  convert one_smul ℝ _ using 2
  rw [hcdef]; field_simp

end

/-- the k-free column constant of `H₁` -/
noncomputable def CH1free (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ δψ : ℝ) (hν : 0 ≤ νψ) (hδ : 0 ≤ δψ)
    (hK : 0 < KhatM0 ell a t ρ) (hcg : 0 < cg1 ell a t ρ θ hc νψ)
    (hEG : 4 * EGM1 ell a ρ θ hc νψ δψ hν hδ ≤ cg1 ell a t ρ θ hc νψ) : ℝ :=
  Real.sqrt 3 * Real.sqrt a * ((1 / θ + 2) * Real.sqrt (1 / θ + 2))
    * ((2 / cg1 ell a t ρ θ hc νψ) * (qBS ell a ρ + δBS ell a ρ θ)
      / (1 / bN1 ell a t ρ θ hc νψ - EN1free ell a t ρ θ hc νψ δψ hν hδ hK hcg hEG))

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
  (R : M0RegimeR ell k Lu U a t e q0) (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0))
include R H

/-- **`hH1col` at M0, with a k- and volume-free constant** -/
theorem hH1col_M0 (θ : ℝ) (hθ : 0 < θ) (hc : CondM0 ell a (rhoM0 ell k e q0) θ)
    (Lam : Set (PeriodicLatticeSite Lu))
    (pdOf : ∀ φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ, PsiBd ell k Lu U θ)
    (hpdψ : ∀ φ, (pdOf φ).ψ = psiD (PU ell k Lu (by have := R.hell; omega) U a Lam))
    (νψ δψ : ℝ) (hpdν : ∀ φ, (pdOf φ).νψ = νψ) (hpdδ : ∀ φ, (pdOf φ).δψ = δψ)
    (hν : 0 ≤ νψ) (hδ : 0 ≤ δψ)
    (hcg : 0 < cg1 ell a t (rhoM0 ell k e q0) θ hc νψ)
    (hEG : 4 * EGM1 ell a (rhoM0 ell k e q0) θ hc νψ δψ hν hδ ≤ cg1 ell a t (rhoM0 ell k e q0) θ hc νψ)
    (hN : EN1free ell a t (rhoM0 ell k e q0) θ hc νψ δψ hν hδ (KhatM0_pos ell k Lu U a t e q0 R) hcg hEG
      < 1 / bN1 ell a t (rhoM0 ell k e q0) θ hc νψ)
    (e' : Bond Lu) (v : SuTwo) :
    ∑ b, ‖((PU ell k Lu (by have := R.hell; omega) U a Lam).H1in (WithLp.toLp 2 (Pi.single e' v) : BondFnL2 Lu)) b‖
      ≤ CH1free ell a t (rhoM0 ell k e q0) θ hc νψ δψ hν hδ (KhatM0_pos ell k Lu U a t e q0 R) hcg hEG
          * ((ell : ℝ) ^ k) ^ 3 * ‖v‖ := by
  classical
  have hell0 : 0 < ell := by have := R.hell; omega
  have hn1 : (1 : ℝ) ≤ (ell : ℝ) ^ k := m0_n_ge_one ell k Lu U a t e q0 R
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by linarith
  set n := (ell : ℝ) ^ k with hndef
  set P := PU ell k Lu hell0 U a Lam with hP
  have hK := KhatM0_pos ell k Lu U a t e q0 R
  set CH := (2 / cg1 ell a t (rhoM0 ell k e q0) θ hc νψ) * (qBS ell a (rhoM0 ell k e q0) + δBS ell a (rhoM0 ell k e q0) θ)
    / (1 / bN1 ell a t (rhoM0 ell k e q0) θ hc νψ - EN1free ell a t (rhoM0 ell k e q0) θ hc νψ δψ hν hδ hK hcg hEG) with hCH
  have hCH0 : 0 ≤ CH := by
    rw [hCH]
    have : 0 ≤ qBS ell a (rhoM0 ell k e q0) := by unfold qBS; positivity
    have := hc.δBS_nonneg
    have : 0 < 1 / bN1 ell a t (rhoM0 ell k e q0) θ hc νψ
        - EN1free ell a t (rhoM0 ell k e q0) θ hc νψ δψ hν hδ hK hcg hEG := by linarith
    positivity
  have hCH1f : 0 ≤ CH1free ell a t (rhoM0 ell k e q0) θ hc νψ δψ hν hδ hK hcg hEG := by
    unfold CH1free; rw [← hCH]; positivity
  -- H₁in on a single unit bond
  have hcol : P.H1in (WithLp.toLp 2 (Pi.single e' v) : BondFnL2 Lu)
      = iE (GF ell k Lu) (P.data.H1 P.G1inv (ContinuousLinearMap.adjoint P.tau (WithLp.toLp 2 (Pi.single e' v)))) := rfl
  rw [hcol, tauAdj_single]
  split_ifs with hmem
  swap
  · simp only [map_zero, PiLp.zero_apply, norm_zero, Finset.sum_const_zero]
    have : 0 ≤ CH1free ell a t (rhoM0 ell k e q0) θ hc νψ δψ hν hδ hK hcg hEG * n ^ 3 * ‖v‖ := by positivity
    exact this
  set p := AdalyFormal.StatementLaneG.pe P e' hmem with hp
  set z := p.2.1.1 with hz
  set ψw := phiP (θ / n) z with hψw
  have hψl : WtLip (θ / n) ψw := phiP_lip (θ / n) (by positivity) z
  set pd := pdOf ψw with hpd
  have hpdν' : pd.νψ = νψ := hpdν ψw
  have hpdδ' : pd.δψ = δψ := hpdδ ψw
  -- transport the k-free hypotheses to `pd`
  have hcg' : 0 < cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ := by rw [hpdν']; exact hcg
  have hEG' : 4 * EGM1 ell a (rhoM0 ell k e q0) θ hc pd.νψ pd.δψ pd.νψ_nonneg (pd.δψ_nonneg hc.hθ)
      ≤ cg1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ := by
    have key : ∀ (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y), x = νψ → y = δψ →
        4 * EGM1 ell a (rhoM0 ell k e q0) θ hc x y hx hy ≤ cg1 ell a t (rhoM0 ell k e q0) θ hc x := by
      intro x y hx hy h1 h2; subst h1; subst h2; exact hEG
    exact key _ _ _ _ hpdν' hpdδ'
  have hN' : EN1free ell a t (rhoM0 ell k e q0) θ hc pd.νψ pd.δψ pd.νψ_nonneg (pd.δψ_nonneg hc.hθ) hK hcg' hEG'
      < 1 / bN1 ell a t (rhoM0 ell k e q0) θ hc pd.νψ := by
    have key : ∀ (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hcgx : 0 < cg1 ell a t (rhoM0 ell k e q0) θ hc x)
        (hEGx : 4 * EGM1 ell a (rhoM0 ell k e q0) θ hc x y hx hy ≤ cg1 ell a t (rhoM0 ell k e q0) θ hc x),
        x = νψ → y = δψ →
        EN1free ell a t (rhoM0 ell k e q0) θ hc x y hx hy hK hcgx hEGx < 1 / bN1 ell a t (rhoM0 ell k e q0) θ hc x := by
      intro x y hx hy hcgx hEGx h1 h2; subst h1; subst h2; exact hN
    exact key _ _ _ _ _ _ hpdν' hpdδ'
  set J := n1M0 ell k Lu U a t e q0 R H ψw θ hψl hc pd hcg' hEG' with hJ
  set δv : FSp (GF ell k Lu) := WithLp.toLp 2 (Pi.single p v) with hδv
  have hW := H1_CT_M0 ell k Lu U a t e q0 R H ψw θ hψl hc pd hcg' hEG' hN' δv
  have hδn : ‖δv‖ = ‖v‖ := by rw [hδv, PiLp.norm_toLp_single]
  have hfix : (fspWP ell k Lu ψw).wi δv = δv := by
    refine PiLp.ext (fun q => ?_)
    show Real.exp (-ψw q.2.1.1) • (δv q) = δv q
    by_cases hq : q = p
    · subst hq; rw [hψw, phiP_self]; simp
    · have : δv q = 0 := by rw [hδv]; simp [Pi.single_apply, hq]
      rw [this, smul_zero]
  have hcj : cjp (fspWP ell k Lu ψw) (bondWP ψw) J.H δv = bondWt ψw (J.H δv) := by
    rw [cjp_apply, hfix]; rfl
  rw [hcj, hδn] at hW
  -- the constant in `hW` is `CH` after rewriting `pd`'s fields
  have hWc : ‖bondWt ψw (J.H δv)‖ ≤ CH * ‖v‖ := by
    refine hW.trans (le_of_eq ?_)
    have key : ∀ (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hcgx : 0 < cg1 ell a t (rhoM0 ell k e q0) θ hc x)
        (hEGx : 4 * EGM1 ell a (rhoM0 ell k e q0) θ hc x y hx hy ≤ cg1 ell a t (rhoM0 ell k e q0) θ hc x),
        x = νψ → y = δψ →
        (2 / cg1 ell a t (rhoM0 ell k e q0) θ hc x) * (qBS ell a (rhoM0 ell k e q0) + δBS ell a (rhoM0 ell k e q0) θ)
          / (1 / bN1 ell a t (rhoM0 ell k e q0) θ hc x - EN1free ell a t (rhoM0 ell k e q0) θ hc x y hx hy hK hcgx hEGx)
          * ‖v‖ = CH * ‖v‖ := by
      intro x y hx hy hcgx hEGx h1 h2; subst h1; subst h2; rfl
    exact key _ _ _ _ _ _ hpdν' hpdδ'
  -- ℓ¹ from the weighted ℓ²
  set X := J.H δv with hX
  have hsum : ∑ b, ‖X b‖ ≤ Real.sqrt (∑ b : Bond (scaleUp ell k Lu), (Real.exp (ψw b.1))⁻¹ ^ 2)
      * Real.sqrt (∑ b : Bond (scaleUp ell k Lu), (Real.exp (ψw b.1) * ‖X b‖) ^ 2) :=
    sum_le_weighted Finset.univ (fun b => ‖X b‖) (fun b => Real.exp (ψw b.1)) (fun b _ => Real.exp_pos _)
  have hS2 : ∑ b : Bond (scaleUp ell k Lu), (Real.exp (ψw b.1) * ‖X b‖) ^ 2 = ‖bondWt ψw X‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    show (Real.exp (ψw b.1) * ‖X b‖) ^ 2 = ‖Real.exp (ψw b.1) • X b‖ ^ 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hS1 : ∑ b : Bond (scaleUp ell k Lu), (Real.exp (ψw b.1))⁻¹ ^ 2 ≤ 3 * (n * (1 / θ + 2)) ^ 3 := by
    have e1 : ∑ b : Bond (scaleUp ell k Lu), (Real.exp (ψw b.1))⁻¹ ^ 2
        = 3 * ∑ x : PeriodicLatticeSite (scaleUp ell k Lu), Real.exp (-(2 * ψw x)) := by
      rw [show (∑ b : Bond (scaleUp ell k Lu), (Real.exp (ψw b.1))⁻¹ ^ 2)
          = ∑ x : PeriodicLatticeSite (scaleUp ell k Lu), ∑ _μ : Fin 3, (Real.exp (ψw x))⁻¹ ^ 2 from
        Fintype.sum_prod_type _]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Real.exp_neg, ← Real.exp_nat_mul]
      push_cast; ring_nf
    rw [e1]
    have h2 := phiP_sum (θ / n) (by positivity) z
    have h3 := geom_le n θ hn1 hθ
    have h4 : (2 / (1 - Real.exp (-(2 * (θ / n))))) ^ 3 ≤ (n * (1 / θ + 2)) ^ 3 := by
      have h5 : 0 ≤ 2 / (1 - Real.exp (-(2 * (θ / n)))) := by
        have : Real.exp (-(2 * (θ / n))) < 1 := by
          have h0 : 0 < θ / n := by positivity
          have := Real.exp_lt_exp.mpr (show -(2 * (θ / n)) < 0 by linarith)
          rwa [Real.exp_zero] at this
        have : 0 < 1 - Real.exp (-(2 * (θ / n))) := by linarith
        positivity
      exact pow_le_pow_left₀ h5 h3 3
    linarith
  have hfinal : ∑ b, ‖X b‖ ≤ Real.sqrt (3 * (n * (1 / θ + 2)) ^ 3) * (CH * ‖v‖) := by
    refine hsum.trans ?_
    rw [hS2, Real.sqrt_sq (norm_nonneg _)]
    exact mul_le_mul (Real.sqrt_le_sqrt hS1) hWc (norm_nonneg _) (Real.sqrt_nonneg _)
  -- the genuine column
  have hgen : ∀ b, ‖(iE (GF ell k Lu) (P.data.H1 P.G1inv δv)) b‖ = Real.sqrt (a * n ^ 3) * ‖X b‖ := by
    intro b
    rw [dataH1_scaled ell k Lu U a t e q0 R H ψw θ hψl hc pd hcg' hEG' Lam (hpdψ ψw) δv]
    show ‖Real.sqrt (a * n ^ 3) • X b‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  simp only [hgen]
  rw [← Finset.mul_sum]
  have hsq : Real.sqrt (3 * (n * (1 / θ + 2)) ^ 3) = Real.sqrt 3 * (n * Real.sqrt n) * ((1 / θ + 2) * Real.sqrt (1 / θ + 2)) := by
    have hθ2 : 0 ≤ 1 / θ + 2 := by positivity
    rw [mul_pow, Real.sqrt_mul (by norm_num), Real.sqrt_mul (by positivity), sqrt_cube n hn.le, sqrt_cube _ hθ2]
    ring
  have hsa : Real.sqrt (a * n ^ 3) = Real.sqrt a * (n * Real.sqrt n) := by
    rw [Real.sqrt_mul (by have := R.ha; positivity), sqrt_cube n hn.le]
  have hsn2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  calc Real.sqrt (a * n ^ 3) * ∑ b, ‖X b‖
      ≤ Real.sqrt (a * n ^ 3) * (Real.sqrt (3 * (n * (1 / θ + 2)) ^ 3) * (CH * ‖v‖)) :=
        mul_le_mul_of_nonneg_left hfinal (Real.sqrt_nonneg _)
    _ = CH1free ell a t (rhoM0 ell k e q0) θ hc νψ δψ hν hδ hK hcg hEG * n ^ 3 * ‖v‖ := by
        rw [hsq, hsa]
        unfold CH1free
        rw [← hCH]
        have e : n * Real.sqrt n * (n * Real.sqrt n) = n ^ 3 := by nlinarith [hsn2]
        calc Real.sqrt a * (n * Real.sqrt n)
              * (Real.sqrt 3 * (n * Real.sqrt n) * ((1 / θ + 2) * Real.sqrt (1 / θ + 2)) * (CH * ‖v‖))
            = Real.sqrt 3 * Real.sqrt a * ((1 / θ + 2) * Real.sqrt (1 / θ + 2)) * CH
                * (n * Real.sqrt n * (n * Real.sqrt n)) * ‖v‖ := by ring
          _ = _ := by rw [e]

end

#print axioms dataG1_eq
#print axioms dataH1_eq
#print axioms tauAdj_single
#print axioms dataH1_scaled
#print axioms hH1col_M0

end AdalyFormal.DLayer
