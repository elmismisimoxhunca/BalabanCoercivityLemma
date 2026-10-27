import DX2
import DY5b
import DN3

/-!
# DX4 -- the SECOND clause of `DLayerStrat` (`hJ`) at `V = U^g` in the M1 regime (M1 D-layer lane, 2026-10-14)

From the data of DX2 (`ctM1`, W4 at `V`, the clause-1 numerics) and the clause-2 numerics (`δ₀ < cw`, the twins of the
`H₁` Schur constants), every structural input of DY5b is produced at `V`:
* `δ₀`, `δ₁` : DY3 `delta2_conj` with `ξ = 0` and `ξ = phiC θ c` (DY5a `ball_osc`, `Ω = 32θℓ`), `kW = kWc`
  (DC8 `WC_bound`), `Sψ = CΨ·SJ` (DS1 `psi_le_of_wcol` with the clause-1 columns), `K2 = K2strat` (DQ5);
* **`clause2_Ug`** : `|⟪H₁in(D̃⁽²⁾B), J⟫| ≤ (√(3ℓ⁷ a Cg) CH1 · SJ) · KD · ‖B‖²` for every unit-bond field `B`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
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

/-- the bilinear bound of `Δ⁽²⁾` from DY3 -/
noncomputable def delN (ell : ℕ) (a θ CH t K2 kW Ω : ℝ) : ℝ :=
  2 * ((Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH) * (400 * (ell : ℝ) ^ 3 * t)) * K2 * Real.exp (2 * Ω)
    * 44217 * ((ell : ℝ) * kW) ^ 2

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

  (KD : ℝ) (hKD0 : 0 ≤ KD) (CH1 : ℝ) (hCH10 : 0 ≤ CH1)
  (hlt2 : (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0) < cw)
  (hκ1N : (kap1N ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀)) (3 * θ * (ell : ℝ) ^ 2) (3 * θ * ell) (rho1 12 M α₀) cw (SstarM ell 12 M α₀) (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0) (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) (32 * θ * ell))) < 1)
  (hcN1N : 0 < 1 / ((1 + (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0) / cw) * (bNext ell W a (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1))
      - ENF (kap1N ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀)) (3 * θ * (ell : ℝ) ^ 2) (3 * θ * ell) (rho1 12 M α₀) cw (SstarM ell 12 M α₀) (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0) (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) (32 * θ * ell)))
        (CQ1N ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀)) (rho1 12 M α₀) cw (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0))
        (d3c ell a (SstarM ell 12 M α₀) (3 * θ * ell)) (cw - (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0)))
  (hCH1N : CHwF (kap1N ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀)) (3 * θ * (ell : ℝ) ^ 2) (3 * θ * ell) (rho1 12 M α₀) cw (SstarM ell 12 M α₀) (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0) (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) (32 * θ * ell)))
        (CQ1N ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀)) (rho1 12 M α₀) cw (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0))
        (d3c ell a (SstarM ell 12 M α₀) (3 * θ * ell)) (cw - (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0)) ((1 + (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0) / cw) * (bNext ell W a (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1)) ≤ CH1)

include hell2 hS hroom hM hR8 hLu5 hW hWR hU hB hα0 ha1 hsm4 ha hθ hsm0 hsmD0 hsmθ hsmDθ hgs hsmA hrr hsQ hsW hε1
  hLu hsmJ hDQ hcw hεγ hcG hκ hcN hCH0 hCH hq hKD0 hCH10 hlt2 hκ1N hcN1N hCH1N in
/-- **the second D-layer clause at `V = U^g`** -/
theorem clause2_Ug (Lam : Set (PeriodicLatticeSite Lu))
    (hW4 : ∀ A' : ↥(bondSupp (geomOf ell k S)),
      cw * wnormSq S ell k (A' : BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A', (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).data.Ginv A'⟫)
    (hKD : ∀ Bt : BondFnL2 Lu,
      ∑ e, ‖((gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).D2in Bt) e‖ ≤ KD * ‖Bt‖ ^ 2)
    (Bt : BondFnL2 Lu) :
    |⟪(gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).H1in
        ((gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).D2in Bt),
      (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).Jf⟫|
      ≤ ((Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH1) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * KD
        * ‖Bt‖ ^ 2 := by
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
  -- the source and the second jet at `V`
  have hSJ0 : 0 ≤ 400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀) := by positivity
  have hJ : ∀ b, ‖(gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam).Jf b‖ ≤ (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀)) * omJ S ell k b := fun b =>
    Jf_strat ell M R k Lu hell0 S (periodicGaugeTransform g U) a Lam α₀ hS (by nlinarith) hUV hsmJ b
  have hψ := psi_le_of_wcol (gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam) (omJ S ell k) _ _ hCΨ0 hSJ0 hcol hJ
  have hK20 : 0 ≤ (K2strat ell (12 * M * α₀)) := by
    unfold K2strat
    have := K2free_nonneg ell ((1 + 3 * Real.pi) * alphaQ ell (12 * M * α₀)) (thetaK2_lt_of ell _ hDQ.hK2c)
    positivity
  have hC : ∀ z, ∑ q, ‖C2fullOf (geomOf ell k S) (periodicGaugeTransform g U) z q‖ ≤ (K2strat ell (12 * M * α₀)) * ‖wq S ell k z‖ ^ 2 := by
    intro z
    rw [wq_normSq]
    exact C2full_strat ell M R k Lu S (periodicGaugeTransform g U) α₀ hS hell2 hroom hLu hα0 hUV hDQ z
  have hR1 : 1 ≤ R := by omega
  have hM1 : 1 ≤ M := by omega
  -- the conjugated `W` bounds at the D2 weight, uniform in the centre
  set c0 : PeriodicLatticeSite (scaleUp ell k Lu) := fun _ => 0 with hc0
  have hkW : ∀ c, ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).kWc = (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) := fun c => rfl
  have hkW0 : 0 ≤ (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) := by rw [← hkW c0]; exact ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c0).kWc_nonneg (hcG' c0)
  have eW0 : ∀ x : ↥(bondSupp (geomOf ell k S)), eW (geomOf ell k S) (fun _ => (0 : ℝ)) x = x := fun x => by
    apply Subtype.ext
    show iE (geomOf ell k S) (eW (geomOf ell k S) (fun _ => (0 : ℝ)) x) = iE (geomOf ell k S) x
    rw [iE_eW, bondWt_zero_fn]
  have eW0' : ∀ x : ↥(bondSupp (geomOf ell k S)), eW (geomOf ell k S) (-(fun _ => (0 : ℝ))) x = x := fun x => by
    rw [show (-(fun _ : PeriodicLatticeSite (scaleUp ell k Lu) => (0 : ℝ))) = fun _ => (0 : ℝ) from by funext; simp]
    exact eW0 x
  have hD0 : ∀ x y : ↥(bondSupp (geomOf ell k S)), |⟪x, (gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam).data.Delta2 (gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam).data_laws y⟫|
      ≤ (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0) * (nq S ell k (geomOf ell k S) x * nq S ell k (geomOf ell k S) y) := by
    intro x y
    have hWp : ∀ z, ‖bondWt (-sigG (geomOf ell k S)) (bondWt (-(fun _ => (0 : ℝ))) (Wop (geomOf ell k S) (periodicGaugeTransform g U) a
        (bondWt (fun _ => (0 : ℝ)) z)))‖ ≤ (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) * ‖bondWt (-sigG (geomOf ell k S)) z‖ := by
      intro z
      rw [show (-(fun _ : PeriodicLatticeSite (scaleUp ell k Lu) => (0 : ℝ))) = fun _ => (0 : ℝ) from by funext; simp,
        bondWt_zero_fn, bondWt_zero_fn]
      have h := ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c0).WC_bound (fun _ => (0 : ℝ)) ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c0).ok0P ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c0).ok0M
        ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c0).ok0N (hεγ' c0) (hcG' c0) z
      rw [((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c0).WC_zero] at h
      rw [← hkW c0]; exact h
    have hWm : ∀ z, ‖bondWt (-sigG (geomOf ell k S)) (bondWt (fun _ => (0 : ℝ)) (Wop (geomOf ell k S) (periodicGaugeTransform g U) a
        (bondWt (-(fun _ => (0 : ℝ))) z)))‖ ≤ (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) * ‖bondWt (-sigG (geomOf ell k S)) z‖ := by
      intro z
      rw [show (-(fun _ : PeriodicLatticeSite (scaleUp ell k Lu) => (0 : ℝ))) = fun _ => (0 : ℝ) from by funext; simp,
        bondWt_zero_fn, bondWt_zero_fn]
      have h := ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c0).WC_bound (fun _ => (0 : ℝ)) ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c0).ok0P ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c0).ok0M
        ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c0).ok0N (hεγ' c0) (hcG' c0) z
      rw [((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c0).WC_zero] at h
      rw [← hkW c0]; exact h
    have h := delta2_conj hS hell2 hroom hell0 (periodicGaugeTransform g U) a Lam (fun _ => (0 : ℝ)) _ hkW0 hWp hWm
      0 le_rfl (fun p _ e _ => by simp) _ (mul_nonneg hCΨ0 hSJ0) hψ _ hK20 hC hR1 hM1 x y
    rw [eW0, eW0'] at h
    refine h.trans (le_of_eq ?_)
    unfold delN nq; ring
  have hosc : ∀ (c : PeriodicLatticeSite (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)), 1 ≤ (p.1 : ℕ) →
      ∀ e : Bond (scaleUp ell k Lu), e.1 ∈ AdalyFormal.StatementLaneR8.Ball p.2.1.1 (AdalyFormal.StatementLaneR8.rhoT ell p.1) →
      |((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).χ e.1 - ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).χ p.2.1.1| ≤ 32 * θ * ell :=
    fun c p hp e he => ball_osc hS hell2 hroom hR1 hM1 hθ.le c p hp e he
  have hD1 : ∀ (c : PeriodicLatticeSite (scaleUp ell k Lu)) (x y : ↥(bondSupp (geomOf ell k S))),
      |⟪(EWP (geomOf ell k S) ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).χ).w x, (gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam).data.Delta2 (gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam).data_laws
        ((EWP (geomOf ell k S) ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).χ).wi y)⟫|
      ≤ (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) (32 * θ * ell)) * (nq S ell k (geomOf ell k S) x * nq S ell k (geomOf ell k S) y) := by
    intro c x y
    have hWp : ∀ z, ‖bondWt (-sigG (geomOf ell k S)) (bondWt (-((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).χ) (Wop (geomOf ell k S) (periodicGaugeTransform g U) a
        (bondWt ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).χ z)))‖ ≤ (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) * ‖bondWt (-sigG (geomOf ell k S)) z‖ := by
      intro z
      have h := ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).WC_bound (-((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).χ) ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).okM ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).okMM
        ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).okN2 (hεγ' c) (hcG' c) z
      rw [← hkW c]
      unfold CTData.WC at h
      rw [neg_neg] at h
      exact h
    have hWm : ∀ z, ‖bondWt (-sigG (geomOf ell k S)) (bondWt ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).χ (Wop (geomOf ell k S) (periodicGaugeTransform g U) a
        (bondWt (-((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).χ) z)))‖ ≤ (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) * ‖bondWt (-sigG (geomOf ell k S)) z‖ := by
      intro z
      have h := ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).WC_bound ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).χ ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).okP ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).okM
        ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).okN1 (hεγ' c) (hcG' c) z
      rw [← hkW c]
      exact h
    have h := delta2_conj hS hell2 hroom hell0 (periodicGaugeTransform g U) a Lam ((ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs).toCT c).χ _ hkW0 hWp hWm
      (32 * θ * ell) (by positivity) (hosc c) _ (mul_nonneg hCΨ0 hSJ0) hψ _ hK20 hC hR1 hM1 x y
    refine h.trans (le_of_eq ?_)
    unfold delN nq; ring
  have hδ0 : 0 ≤ (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0) := by unfold delN; positivity
  have hδ1 : 0 ≤ (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) (32 * θ * ell)) := by unfold delN; positivity
  have hκ1 : ∀ c, kapB1 (ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs) hell0 Lam (rho1 12 M α₀) hρ1 hreg hεγ' hcG' cw hcw hW4 hR8 (SstarM ell 12 M α₀) Dr
      (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0) (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) (32 * θ * ell)) hδ0 hδ1 hlt2 hD0 hD1 c < 1 := fun c => by
    unfold kapB1; rw [CTData.kap1_eqN]; exact hκ1N
  have hcN1 : ∀ c, 0 < 1 / (wsB1 (ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs) hell0 Lam (rho1 12 M α₀) hρ1 hreg hεγ' hcG' cw hcw hW4 hR8 (SstarM ell 12 M α₀)
      Dr (bNext ell W a (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1) hbN hext hQs (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0) (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) (32 * θ * ell)) hδ0 hδ1 hlt2 hD0 hD1 hκ1 c).bN
      - (wsB1 (ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs) hell0 Lam (rho1 12 M α₀) hρ1 hreg hεγ' hcG' cw hcw hW4 hR8 (SstarM ell 12 M α₀)
      Dr (bNext ell W a (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1) hbN hext hQs (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0) (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) (32 * θ * ell)) hδ0 hδ1 hlt2 hD0 hD1 hκ1 c).EN := fun c => by
    unfold wsB1; rw [CTData.EN1_eqN, CTData.bN1_eqN]; exact hcN1N
  have hCH1 : ∀ c, (wsB1 (ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs) hell0 Lam (rho1 12 M α₀) hρ1 hreg hεγ' hcG' cw hcw hW4 hR8 (SstarM ell 12 M α₀)
      Dr (bNext ell W a (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1) hbN hext hQs (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0) (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) (32 * θ * ell)) hδ0 hδ1 hlt2 hD0 hD1 hκ1 c).CHw ≤ CH1 := fun c => by
    unfold wsB1; rw [CTData.CHw1_eqN]; exact hCH1N
  have hH1col := hH1col_B (ctM1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha θ hθ hsm0 hsmD0 hsmθ hsmDθ hgs) hell0 Lam (rho1 12 M α₀) hρ1 hreg hεγ' hcG' cw hcw hW4 hR8 (SstarM ell 12 M α₀) Dr
    (bNext ell W a (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1) hbN hext hQs (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) 0) (delN ell a θ CH ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell W θ) (DeN ell W θ) (gamN ell W a (rhoT ell 12 M α₀))) (32 * θ * ell)) hδ0 hδ1 hlt2 hD0 hD1 hκ1 hcN1 CH1 hCH10 hCH1 hq
  have hCH1' : 0 ≤ Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH1 := mul_nonneg (Real.sqrt_nonneg _) hCH10
  exact hJ_strat (gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam) (omJ S ell k) _ _ _ hCH1' hSJ0 hH1col hJ Bt (hKD Bt)

end m1

#print axioms delN
#print axioms clause2_Ug

end AdalyFormal.M1DStrat
