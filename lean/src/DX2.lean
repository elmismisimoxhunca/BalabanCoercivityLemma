import DX1

/-!
# DX2 -- the first D-layer clause at `V = U^g` and at `U` in the M1 regime, every structural input discharged
(M1 D-layer lane, 2026-10-14)

* **`clause1_Ug`** : at `V = U^g`, `|⟪A, Δ⁽²⁾ A⟫| ≤ eps2N … · wnormSq A`, from W4 at `V` and numeric conditions on DN0/DX1
  real functions only (no `k`, `S`, `Lu`, `U` in any numeric hypothesis).
* **`clause1_U`** : the same at `U` itself, from `M1Regular` at `U` and W4 at `U`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (RegData Estar rho1 rho1_nonneg SstarM delStar regData_M1 qs_injective_M1)
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.M1 (M1Regular M1Bounds strat bstrat wnormSq)
open AdalyFormal.M1DStrat.DQ
open AdalyFormal.M1GaugeW4 (rhoT rhoT_nonneg rhoT_smalls epsXnum holRegime_M1)
open AdalyFormal.W6 (CwE CgE CEp)

section m1
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ} {W : ℕ}
  (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hroom : 18 * ell ≤ R * M) (hM : 0 < M) (hR8 : 8 * ell ≤ R)
  (hLu5 : ∀ μ, 5 ≤ Lu μ + 1) (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
  (U : LinkCfg (scaleUp ell k Lu))
  (g : PeriodicLatticeSite (scaleUp ell k Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
  (A : Bond (scaleUp ell k Lu) → Matrix (Fin 2) (Fin 2) ℂ)
  (hU : ∀ e : Bond (scaleUp ell k Lu), ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp ((((((ell : ℝ) ^ k)⁻¹ : ℝ) : ℂ) * Complex.I) • A e))
  (hB : M1Bounds S ell M 12 k α₀ ((ell : ℝ) ^ k)⁻¹ A) (hα0 : 0 ≤ α₀)
  (ha1 : (12 : ℝ) * M * α₀ ≤ 1)
  (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M α₀ ≤ 1)
  (a : ℝ) (ha : 0 < a) (θ : ℝ) (hθ : 0 < θ)
  (hsm0 : 24 * ((Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2
          + 1 * (Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1)) ^ 2) ≤ csOf a (rhoT ell 12 M α₀))
  (hsmD0 : 4 * (Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2 ≤ csOf a (rhoT ell 12 M α₀))
  (hsmθ : 24 * ((Real.sqrt 3 * (Real.exp (ThN ell W θ) - 1)) ^ 2 + 1 * (Real.sqrt a * (Real.exp (DeN ell W θ) - 1)) ^ 2)
    ≤ csOf a (rhoT ell 12 M α₀))
  (hsmDθ : 4 * (Real.sqrt 3 * (Real.exp (ThN ell W θ) - 1)) ^ 2 ≤ csOf a (rhoT ell 12 M α₀))
  (hgs : Real.sqrt (max a 1) * ((1 + 12 * rhoT ell 12 M α₀) ^ 2 + (512 * rhoT ell 12 M α₀ ^ 2 + 4704) / a)
        * epsXnum ell W a (rhoT ell 12 M α₀) < (1 - 12 * rhoT ell 12 M α₀) ^ 2)
  (hsmA : (1 + 3 * Real.pi) * rho1 12 M α₀ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
  (hrr : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M α₀))
      < AdalyFormal.NonflatJet.r0)
  (hsQ : 3 * delStar ell (SstarM ell 12 M α₀) ^ 2 * CEp < 1)
  (hsW : 3 * (ell : ℝ) ^ 2 * delStar ell (SstarM ell 12 M α₀) ^ 2 * CwE ell ≤ 1 / 4)
  (ε1 : ℝ) (hε1 : 0 < ε1)
  (hLu : ∀ μ, ell < Lu μ + 1) (hsmJ : 4 * ((12 : ℝ) * M * α₀) ≤ 1) (hDQ : DQSmall ell (12 * M * α₀))
  (cw : ℝ) (hcw : 0 < cw)
  (hεγ : epsGN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) * gamN ell W a (rhoT ell 12 M α₀) ≤ 1)
  (hcG : 0 < cGN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀)))
  (hκ : kapN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))
      (3 * θ * (ell : ℝ) ^ 2) (3 * θ * ell) (rho1 12 M α₀) cw (SstarM ell 12 M α₀) < 1)
  (hcN : 0 < 1 / bNext ell W a (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1
      - ENF (kapN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))
          (3 * θ * (ell : ℝ) ^ 2) (3 * θ * ell) (rho1 12 M α₀) cw (SstarM ell 12 M α₀))
        (CQN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))
          (rho1 12 M α₀) cw)
        (d3c ell a (SstarM ell 12 M α₀) (3 * θ * ell)) cw)
  (CH : ℝ) (hCH0 : 0 ≤ CH)
  (hCH : CHwF (kapN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))
          (3 * θ * (ell : ℝ) ^ 2) (3 * θ * ell) (rho1 12 M α₀) cw (SstarM ell 12 M α₀))
        (CQN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))
          (rho1 12 M α₀) cw)
        (d3c ell a (SstarM ell 12 M α₀) (3 * θ * ell)) cw (bNext ell W a (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1)
      ≤ CH)
  (hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2)

include hell2 hS hroom hM hR8 hLu5 hW hWR hU hB hα0 ha1 hsm4 ha hθ hsm0 hsmD0 hsmθ hsmDθ hgs hsmA hrr hsQ hsW hε1
  hLu hsmJ hDQ hcw hεγ hcG hκ hcN hCH0 hCH hq in
/-- **the stratified `Δ⁽²⁾` bound at `V = U^g`** -/
theorem clause1_Ug (Lam : Set (PeriodicLatticeSite Lu))
    (hW4 : ∀ A' : ↥(bondSupp (geomOf ell k S)),
      cw * wnormSq S ell k (A' : BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A', (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).data.Ginv A'⟫)
    (A' : ↥(bondSupp (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).G)) :
    |⟪A', (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).data.Delta2
        (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).data_laws A'⟫|
      ≤ eps2N ell M W a θ α₀ CH (csOf a (rhoT ell 12 M α₀)) (gamN ell W a (rhoT ell 12 M α₀))
        * wnormSq S ell k (A' : BondFnL2 (scaleUp ell k Lu)) := by
  have hell0 : 0 < ell := by omega
  have hT3 : ∀ μ, 3 ≤ Lu μ + 1 := fun μ => by have := hLu5 μ; omega
  have hroom17 : 17 * ell ≤ R * M := by omega
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  have ha0 : 0 ≤ ((12 : ℕ) : ℝ) * M * α₀ := by positivity
  have hρ1 : 0 ≤ rho1 12 M α₀ := rho1_nonneg 12 M α₀ hα0
  have hreg := holRegime_M1 hell0 U g A hU hB hη ha0 (by exact_mod_cast ha1)
  have hlink := hlink_all S U g A hU hB hη (by omega) ha0
  have Dr := regData_M1 hell2 hS hroom17 hT3 U g A hU hB hη hα0 (by exact_mod_cast ha1) hsm4 hsmA hrr
  have hQs := qs_injective_M1 hell2 hS hroom17 hT3 U g A hU hB hη hα0 (by exact_mod_cast ha1) hsm4 hsmA hrr hM hR8 a Lam
    hsQ
  have hRi := bond_rightinv_M1 hell2 hS hroom17 hT3 U g A hU hB hη hα0 (by exact_mod_cast ha1) hsm4 hsmA hrr hM hR8 a
    Lam hsW
  have hp := hatPack_M1 hell2 hS hroom hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha hsm0 hsmD0
  have hext := hext_of_rightinv hS hell2 (by omega) (by omega) hW hWR hell0 (periodicGaugeTransform g U) a
    (csOf a (rhoT ell 12 M α₀)) hp (rho1 12 M α₀) hρ1 hreg ε1 hε1 (rho1 12 M α₀) hρ1 hlink Lam (4 * CwE ell)
    (4 * CgE ell) (by unfold CwE; have := AdalyFormal.W6.CE_pos; positivity)
    (by unfold CgE; have := AdalyFormal.W6.CE_pos; have := AdalyFormal.W6.GE_pos; positivity) hRi
  have hηS : 0 ≤ etaS ell W (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1 := by
    have hlg : 0 ≤ Real.log ell := Real.log_nonneg (by exact_mod_cast (show 1 ≤ ell by omega))
    have hq0 : 0 ≤ 2 * (ell : ℝ) ^ 2 * Real.log ell / W := by positivity
    exact etaS_nonneg ell W _ _ ε1 hp.hcs hρ1 hε1 (by linarith [Real.add_one_le_exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W)])
  have hbN : 0 < bNext ell W a (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1 := by
    unfold bNext CwE CgE
    have := AdalyFormal.W6.CE_pos; have := AdalyFormal.W6.GE_pos
    positivity
  have hεγ' : ∀ c, ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ
      hgs).toCT c).epsG * (ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ
      hsmDθ hgs).γ ≤ 1 := fun c => by rw [CTData.epsG_eqN]; exact hεγ
  have hcG' : ∀ c, 0 < ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ
      hsmDθ hgs).toCT c).cG := fun c => by rw [CTData.cG_eqN]; exact hcG
  have hκ1 : ∀ c, kapB (ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ
      hgs) hell0 Lam (rho1 12 M α₀) hρ1 hreg hεγ' hcG' cw hcw hW4 hR8 (SstarM ell 12 M α₀) Dr c < 1 := fun c => by
    unfold kapB; rw [CTData.kap_eqN]; exact hκ
  have hcN' : ∀ c, 0 < 1 / (wsB (ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0
      hsmθ hsmDθ hgs) hell0 Lam (rho1 12 M α₀) hρ1 hreg hεγ' hcG' cw hcw hW4 hR8 (SstarM ell 12 M α₀) Dr
      (bNext ell W a (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1) hbN hext hQs hκ1 c).bN
      - (wsB (ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0
      hsmθ hsmDθ hgs) hell0 Lam (rho1 12 M α₀) hρ1 hreg hεγ' hcG' cw hcw hW4 hR8 (SstarM ell 12 M α₀) Dr
      (bNext ell W a (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1) hbN hext hQs hκ1 c).EN := fun c => by
    unfold wsB; rw [CTData.EN_eqN, CTData.bN_eqN]; exact hcN
  have hCH' : ∀ c, (wsB (ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0
      hsmθ hsmDθ hgs) hell0 Lam (rho1 12 M α₀) hρ1 hreg hεγ' hcG' cw hcw hW4 hR8 (SstarM ell 12 M α₀) Dr
      (bNext ell W a (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1) hbN hext hQs hκ1 c).CHw ≤ CH := fun c => by
    unfold wsB; rw [CTData.CHw_eqN]; exact hCH
  have hcol := hcol_B (ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ
      hgs) hell0 Lam (rho1 12 M α₀) hρ1 hreg hεγ' hcG' cw hcw hW4 hR8 (SstarM ell 12 M α₀) Dr
      (bNext ell W a (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1) hbN hext hQs hκ1 hcN' CH hCH' hq
  have hUV : M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ (periodicGaugeTransform g U) := by
    refine ⟨fun _ => 1, A, fun e => ?_, hB⟩
    have e1 : periodicGaugeTransform (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) (periodicGaugeTransform g U) e
        = periodicGaugeTransform g U e := by simp [periodicGaugeTransform]
    rw [e1]; exact hU e
  have hCΨ0 : 0 ≤ Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH := mul_nonneg (Real.sqrt_nonneg _) hCH0
  exact dlayer_clause1 (ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ
      hsmDθ hgs) hell0 Lam _ hCΨ0 hcol α₀ hα0 hUV (by nlinarith) hsmJ hroom hLu hDQ A'

end m1

end AdalyFormal.M1DStrat
