import DLR99
import MC4

/-!
# DL100 -- the D-layer premises of MF7 / MF9 / MC4 AS TYPED (operator-norm `hD2` and `hJ`) on M0 ∩ PerCubeRegular2, k-free

* `Wop_norm_M0` : `‖Wop‖ ≤ GLv.nW ℓ a ρ θ` (k-free) — the CT `Γ` instance at M0 (weight `φ = 0`) has `W = Wop` (DL81 `gamM0_W`)
  and `‖W v‖ ≤ (1 + kDZ + dDZ)‖v‖` (DL15 `W_le`), whose constant IS the model's `nW` (definitional).
* `eps2op Num := 2·nW²·CHfree·JSfree(β)·K2free` (k-free).
* **`dlayer_M0_class`** (hypotheses = those of `instIneq_M0_class_unconditional`):
  `‖Δ2‖ ≤ eps2op/n²` (MF7's `hD2`, OPERATOR norm: `Δ2 = pE W* M_ψ W iE`, DL81) and, for every `B̃ ∈ Λ̃` on `Λ`,
  `|⟨H₁in(D2in(C Q₁ B̃)), Jf⟩| ≤ εJ ‖C Q₁ B̃‖²` with `εJ = epsJfree` (MF7's `hJ`).
* **`DLayer_M0_class`** : the same packaged as MC4's predicate `DLayer ℓ k Lu _ U a Λ ε2s εJ`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp OnLambdaTildeIn)
open AdalyFormal.StatementLane2 (OnLambdaT PerCubeRegular2)
open AdalyFormal.StatementLaneG (LamBlockSum InstIneq)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.AsmM0
open AdalyFormal.SliceCoerc
open AdalyFormal.RegBgKU (KUSmall kapHat)
open AdalyFormal.M0Finish (PU UnitSmall dCM0 cBM0)

theorem iE_opnorm_le {L : PeriodicLatticeExtent} (G : TowerGeom L) : ‖iE G‖ ≤ 1 := Submodule.norm_subtypeL_le _

theorem pE_opnorm_le {L : PeriodicLatticeExtent} (G : TowerGeom L) : ‖pE G‖ ≤ 1 := by
  unfold pE; rw [LinearIsometryEquiv.norm_map]; exact iE_opnorm_le G

theorem wtLip_zero (L : PeriodicLatticeExtent) (θ' : ℝ) (hθ : 0 ≤ θ') : WtLip θ' (fun _ : PeriodicLatticeSite L => (0 : ℝ)) :=
  fun _ _ => by simp [hθ]

/-- the genuine `W` at M0 has a k-free operator norm -/
theorem Wop_norm_M0 (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
    (R : M0RegimeR ell k Lu U a t e q0) (θ : ℝ) (hc : CondM0 ell a (rhoM0 ell k e q0) θ) :
    ‖Wop (GF ell k Lu) U a‖ ≤ GLv.nW ell a (rhoM0 ell k e q0) θ := by
  have hn : (0 : ℝ) ≤ θ / (ell : ℝ) ^ k := by have := hc.hθ; positivity
  have hφ := wtLip_zero (scaleUp ell k Lu) _ hn
  rw [← gamM0_W ell k Lu U a t e q0 R (fun _ => 0) θ hφ hc]
  have h0 : 0 ≤ GLv.nW ell a (rhoM0 ell k e q0) θ := nW_model_nonneg hc
  exact ContinuousLinearMap.opNorm_le_bound _ h0
    (fun v => (gamM0 ell k Lu U a t e q0 R (fun _ => 0) θ hφ hc).W_le v)

/-- the operator norm of the genuine `Δ2` from the three ingredient bounds -/
theorem Delta2_norm_le (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (S K nWb : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) (hnW : 0 ≤ nWb)
    (hψ : ∀ p, ‖psiD (PU ell k Lu hell U a Lam) p‖ ≤ S)
    (hC : ∀ z : BondFnL2 (scaleUp ell k Lu), ∑ p, ‖C2fullOf (GF ell k Lu) U z p‖ ≤ K * ‖z‖ ^ 2)
    (hW : ‖Wop (GF ell k Lu) U a‖ ≤ nWb) :
    ‖(PU ell k Lu hell U a Lam).data.Delta2 (PU ell k Lu hell U a Lam).data_laws‖ ≤ nWb * (2 * S * K) * nWb := by
  have hM := Mpsi_norm ell k Lu U (psiD (PU ell k Lu hell U a Lam)) S K hS hK hψ hC
  have hA : ‖ContinuousLinearMap.adjoint (Wop (GF ell k Lu) U a)‖ = ‖Wop (GF ell k Lu) U a‖ :=
    LinearIsometryEquiv.norm_map _ _
  have hMn0 : 0 ≤ ‖Mpsi ell k Lu U (psiD (PU ell k Lu hell U a Lam))‖ := ContinuousLinearMap.opNorm_nonneg _
  have hWn0 : 0 ≤ ‖Wop (GF ell k Lu) U a‖ := ContinuousLinearMap.opNorm_nonneg _
  have hAn0 : 0 ≤ ‖ContinuousLinearMap.adjoint (Wop (GF ell k Lu) U a)‖ := ContinuousLinearMap.opNorm_nonneg _
  have hpE0 : 0 ≤ ‖pE (GF ell k Lu)‖ := ContinuousLinearMap.opNorm_nonneg _
  have hiE0 : 0 ≤ ‖iE (GF ell k Lu)‖ := ContinuousLinearMap.opNorm_nonneg _
  have hSK : 0 ≤ 2 * S * K := by positivity
  rw [dataDelta2_eq]
  have step1 : ‖pE (GF ell k Lu) ∘L (ContinuousLinearMap.adjoint (Wop (GF ell k Lu) U a)
        ∘L Mpsi ell k Lu U (psiD (PU ell k Lu hell U a Lam)) ∘L Wop (GF ell k Lu) U a) ∘L iE (GF ell k Lu)‖
      ≤ ‖pE (GF ell k Lu)‖ * (‖ContinuousLinearMap.adjoint (Wop (GF ell k Lu) U a)‖
          * (‖Mpsi ell k Lu U (psiD (PU ell k Lu hell U a Lam))‖ * ‖Wop (GF ell k Lu) U a‖) * ‖iE (GF ell k Lu)‖) := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left ?_ hpE0)
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right ?_ hiE0)
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left ?_ hAn0)
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have step2 : ‖ContinuousLinearMap.adjoint (Wop (GF ell k Lu) U a)‖
        * (‖Mpsi ell k Lu U (psiD (PU ell k Lu hell U a Lam))‖ * ‖Wop (GF ell k Lu) U a‖)
      ≤ nWb * ((2 * S * K) * nWb) := by
    rw [hA]
    exact mul_le_mul hW (mul_le_mul hM hW hWn0 hSK) (mul_nonneg hMn0 hWn0) hnW
  have hin0 : 0 ≤ ‖ContinuousLinearMap.adjoint (Wop (GF ell k Lu) U a)‖
      * (‖Mpsi ell k Lu U (psiD (PU ell k Lu hell U a Lam))‖ * ‖Wop (GF ell k Lu) U a‖) :=
    mul_nonneg hAn0 (mul_nonneg hMn0 hWn0)
  have step3 := mul_le_mul (pE_opnorm_le (GF ell k Lu)) (mul_le_mul step2 (iE_opnorm_le (GF ell k Lu)) hiE0
    (by positivity)) (mul_nonneg hin0 hiE0) zero_le_one
  refine (step1.trans step3).trans (le_of_eq ?_)
  ring

/-- the operator-norm `Δ2` constant (k-free) -/
noncomputable def eps2op {ell : ℕ} {a t ρ β θ : ℝ} (h : M0ClassNum ell a t ρ β θ) : ℝ :=
  2 * GLv.nW ell a ρ θ ^ 2 * CHfree ell a t ρ θ h.hc h.hK h.hEG * JSfree β * K2free ell ρ

/-- **MF7's two D-layer premises, AS TYPED, on M0 ∩ PerCubeRegular2, with k- and volume-free constants** -/
theorem dlayer_M0_class (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0)
    (H : KUSmall ell (rhoM0 ell k e q0)) (HU : UnitSmall ell (rhoM0 ell k e q0))
    (hd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu))
    (M f : ℕ) (α₀ : ℝ) (hM : 0 < M) (hf : 4 ≤ f)
    (hP : PerCubeRegular2 ell M f k (fullTower ell k Lu) α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hsm : 4 * ((f : ℝ) * M * α₀) ≤ 1)
    (θ : ℝ) (Num : M0ClassNum ell a t (rhoM0 ell k e q0) ((f : ℝ) * M * α₀) θ) :
    ‖(PU ell k Lu hell U a Lam).data.Delta2 (PU ell k Lu hell U a Lam).data_laws‖ ≤ eps2op Num / ((ell : ℝ) ^ k) ^ 2 ∧
    ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      |⟪(PU ell k Lu hell U a Lam).H1in ((PU ell k Lu hell U a Lam).D2in
          (WithLp.toLp 2 (Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt))), (PU ell k Lu hell U a Lam).Jf⟫|
        ≤ epsJfree Num * ‖(WithLp.toLp 2 (Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt) : BondFnL2 Lu)‖ ^ 2 := by
  have hell2 : 2 ≤ ell := R.hell
  set ρ := rhoM0 ell k e q0 with hρdef
  set β := (f : ℝ) * M * α₀ with hβdef
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  set n := (ell : ℝ) ^ k with hndef
  have hρ0 : 0 ≤ ρ := m0_rho_nonneg ell k Lu U a t e q0 R
  set CHf := CHfree ell a t ρ θ Num.hc Num.hK Num.hEG with hCHf
  set JS := JSfree β with hJS
  set K2f := K2free ell ρ with hK2f
  have hCHf0 : 0 ≤ CHf := CHfree_nonneg ell a t ρ θ Num.hθ Num.hc Num.hK Num.hEG Num.hN
  have hJS0 : 0 ≤ JS := JSfree_nonneg β Num.hβ
  have hK2f0 : 0 ≤ K2f := K2free_nonneg ell ρ hell2 hρ0 Num.hK2c
  set P := PU ell k Lu hell U a Lam with hPdef
  have hJs : ∀ b, ‖P.Jf b‖ ≤ JS / n ^ 3 := fun b => hJs_class ell M f k Lu hell U a Lam α₀ hM hf hP hsm b
  have hHcol : ∀ (p : BIdx P.G) (v : SuTwo),
      ∑ b, ‖(iE P.G (P.data.H (WithLp.toLp 2 (Pi.single p v) : FSp P.G))) b‖ ≤ (CHf * n ^ 3) * ‖v‖ := by
    intro p v
    exact hHcol_M0 ell k Lu U a t e q0 R H θ Num.hθ Num.hc Num.hEG Num.hN Lam p v
  have hK2 : ∀ z : BondFnL2 (scaleUp ell k Lu), ∑ p, ‖C2fullOf P.G U z p‖ ≤ (K2f / n ^ 2) * ‖z‖ ^ 2 :=
    fun z => hK2_M0 ell k Lu hell U a t e q0 R H Lam Num.hK2c z
  have hψ : ∀ p, ‖psiD P p‖ ≤ CHf * JS := by
    intro p
    have h := psi_le_of_col P (CHf * n ^ 3) (JS / n ^ 3) (by positivity) (by positivity) hHcol hJs p
    have e : CHf * n ^ 3 * (JS / n ^ 3) = CHf * JS := by field_simp
    rwa [e] at h
  constructor
  · -- the operator norm of Δ2 = pE W* M_ψ W iE
    have hW := Wop_norm_M0 ell k Lu U a t e q0 R θ Num.hc
    have hW0 : 0 ≤ GLv.nW ell a ρ θ := nW_model_nonneg Num.hc
    have h := Delta2_norm_le ell k Lu hell U a Lam (CHf * JS) (K2f / n ^ 2) (GLv.nW ell a ρ θ) (by positivity)
      (by positivity) hW0 hψ hK2 hW
    refine h.trans (le_of_eq ?_)
    unfold eps2op; rw [← hCHf, ← hJS, ← hK2f]; field_simp
    rw [← hρdef]; ring
  · -- hJ
    have hH1col : ∀ (e' : Bond Lu) (v : SuTwo),
        ∑ b, ‖(P.H1in (WithLp.toLp 2 (Pi.single e' v) : BondFnL2 Lu)) b‖
          ≤ (CH1free ell a t ρ θ Num.hc (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
              (deltaPsi ell a t ρ β θ Num.hc Num.hK Num.hEG) Num.hν Num.hδ Num.hK Num.hcg1 Num.hEG1 * n ^ 3) * ‖v‖ := by
      have hθ0 : 0 ≤ θ := Num.hθ.le
      let pd0 : PsiBd ell k Lu U θ :=
        { ψ := psiD P
          S := CHf * JS
          K := K2f / n ^ 2
          νψ := nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG
          δψ := deltaPsi ell a t ρ β θ Num.hc Num.hK Num.hEG
          hS := by positivity
          hK := by positivity
          hψ := hψ
          hC := hK2
          hνψ := by
            apply le_of_eq
            unfold nuPsi
            rw [← hCHf, ← hJS, ← hK2f]
            simp only [hndef]
            field_simp
          hδψ := by
            apply le_of_eq
            unfold deltaPsi nuPsi
            rw [← hCHf, ← hJS, ← hK2f]
            simp only [hndef]
            field_simp }
      intro e' v
      exact hH1col_M0 ell k Lu U a t e q0 R H θ Num.hθ Num.hc Lam (fun _ => pd0) (fun _ => rfl)
        (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG) (deltaPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
        (fun _ => rfl) (fun _ => rfl) Num.hν Num.hδ Num.hcg1 Num.hEG1 Num.hN1 e' v
    have hKDb : ∀ B : BondFnL2 Lu, ∑ e', ‖(P.D2in B) e'‖ ≤ KDfree ell * ‖B‖ ^ 2 :=
      fun B => hKDb_M0 ell k Lu hell U a t e q0 R H HU hd Lam Num.hKDc B
    have hθ0 : 0 ≤ θ := Num.hθ.le
    set CH1 := CH1free ell a t ρ θ Num.hc (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
      (deltaPsi ell a t ρ β θ Num.hc Num.hK Num.hEG) Num.hν Num.hδ Num.hK Num.hcg1 Num.hEG1 with hCH1
    have hCH10 : 0 ≤ CH1 := by
      rw [hCH1]; unfold CH1free
      have : 0 ≤ qBS ell a ρ := by unfold qBS; positivity
      have := Num.hc.δBS_nonneg
      have : 0 < 1 / bN1 ell a t ρ θ Num.hc (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
          - EN1free ell a t ρ θ Num.hc (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
              (deltaPsi ell a t ρ β θ Num.hc Num.hK Num.hEG) Num.hν Num.hδ Num.hK Num.hcg1 Num.hEG1 := by
        linarith [Num.hN1]
      have := Num.hcg1
      have := Num.hc.ha
      positivity
    have hψ1 : ∀ e', ‖psi1u P e'‖ ≤ (CH1 * n ^ 3) * (JS / n ^ 3) :=
      psi1u_le_of_col P (CH1 * n ^ 3) (JS / n ^ 3) (by positivity) (by positivity) hH1col hJs
    intro Bt _ _
    have h1 := hJ_le P ((CH1 * n ^ 3) * (JS / n ^ 3)) hψ1 (WithLp.toLp 2 (Cop Lam P.Q1 Bt))
    have h2 := hKDb (WithLp.toLp 2 (Cop Lam P.Q1 Bt))
    have hS0 : 0 ≤ (CH1 * n ^ 3) * (JS / n ^ 3) := by positivity
    have e : (CH1 * n ^ 3) * (JS / n ^ 3) * KDfree ell = epsJfree Num := by
      unfold epsJfree; rw [← hCH1, ← hJS]; field_simp
    calc _ ≤ (CH1 * n ^ 3) * (JS / n ^ 3) * ∑ e', ‖(P.D2in (WithLp.toLp 2 (Cop Lam P.Q1 Bt))) e'‖ := h1
      _ ≤ (CH1 * n ^ 3) * (JS / n ^ 3) * (KDfree ell * ‖(WithLp.toLp 2 (Cop Lam P.Q1 Bt) : BondFnL2 Lu)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hS0
      _ = epsJfree Num * ‖(WithLp.toLp 2 (Cop Lam P.Q1 Bt) : BondFnL2 Lu)‖ ^ 2 := by rw [← e]; ring

/-- the same, as MC4's predicate `DLayer` -/
theorem DLayer_M0_class (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0)
    (H : KUSmall ell (rhoM0 ell k e q0)) (HU : UnitSmall ell (rhoM0 ell k e q0))
    (hd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu))
    (M f : ℕ) (α₀ : ℝ) (hM : 0 < M) (hf : 4 ≤ f)
    (hP : PerCubeRegular2 ell M f k (fullTower ell k Lu) α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hsm : 4 * ((f : ℝ) * M * α₀) ≤ 1)
    (θ : ℝ) (Num : M0ClassNum ell a t (rhoM0 ell k e q0) ((f : ℝ) * M * α₀) θ) :
    AdalyFormal.M0Corollary.DLayer ell k Lu hell U a Lam (eps2op Num) (epsJfree Num) :=
  dlayer_M0_class ell k Lu hell U a t e q0 R H HU hd Lam M f α₀ hM hf hP hsm θ Num

#print axioms Wop_norm_M0
#print axioms dlayer_M0_class
#print axioms DLayer_M0_class

end AdalyFormal.DLayer
