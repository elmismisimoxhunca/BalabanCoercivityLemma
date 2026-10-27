import MA10
import MA13
import DX6

/-!
# MA14 -- `chart_config` (lane m1_assembly_20261014)

At ONE configuration `(S, Lam, U)` with an `M1Regular` witness `(g, A0)`, the chart `V = U^g`: every hypothesis of `chart_core` (MA8)
is produced from the M1 regime (`hatPack_of`, `holRegime_M1`, `drift_F_M1`, `hlink_M1`, `cop_M1`, `W4Num.hη`), so that what remains are the
W4 / D-layer / WellDef inputs at `V` and the numeric inequality `hEt`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.M1Assembly

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp OnLambdaTildeIn TorusOK)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneG (gparams LambdaOK2 GenP.genForm GenP.genC GenP.WellDef)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.M1GaugeW4 (W4Num rhoT rhoT_smalls hbig_of site_hU_M1 site_hT_M1 holRegime_M1 hlink_M1)
open AdalyFormal.TowerLoc (rho1 SstarM delStar drift_F_M1)
open AdalyFormal.M1DK (KDsmall kapM1)
open AdalyFormal.M1IMS (csOf etaC nuC)

theorem chart_config {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hroom : 17 * ell ≤ R * M) (hM : 0 < M)
    (hR8 : 8 * ell ≤ R) (hT : TorusOK ell M Lu) (hLu5 : ∀ μ, 5 ≤ Lu μ + 1)
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK2 ell M R k S Lam)
    (U : LinkCfg (scaleUp ell k Lu))
    (g : PeriodicLatticeSite (scaleUp ell k Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (A0 : Bond (scaleUp ell k Lu) → Matrix (Fin 2) (Fin 2) ℂ) {α₀ : ℝ} (hα0 : 0 < α₀)
    (hUg : ∀ e : Bond (scaleUp ell k Lu), ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp (((((ell : ℝ) ^ k)⁻¹ : ℝ) * Complex.I) • A0 e))
    (hB : AdalyFormal.M1.M1Bounds S ell M 12 k α₀ ((ell : ℝ) ^ k)⁻¹ A0)
    (ha1 : ((12 : ℕ) : ℝ) * M * α₀ ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M α₀ ≤ 1)
    (hsmA : (1 + 3 * Real.pi) * rho1 12 M α₀ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
    (hrr : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M α₀))
        < AdalyFormal.NonflatJet.r0)
    (hKD : KDsmall ell (12 * M * α₀))
    (a : ℝ) (ha : 0 < a) (ε1 : ℝ) (hε1 : 0 < ε1) (hε1' : ε1 < 1)
    (hN : W4Num ell M 12 (R * M * ell) a α₀ ε1)
    (hWD : GenP.WellDef (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam))
    (cw ε2s εJ : ℝ) (hcw : 0 < cw) (hε2 : 0 ≤ ε2s) (hεJ : 0 ≤ εJ) (hε2cw : ε2s ≤ cw)
    (hcoer : ∀ A : ↥(bondSupp (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).G),
      cw * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A, (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).data.Ginv A⟫)
    (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).G),
      |⟪A, (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).data.Delta2
          (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).data_laws A⟫|
        ≤ ε2s * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
    (hJ : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      |⟪(gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).H1in
          ((gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).D2in
            (WithLp.toLp 2 (Cop Lam (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).Q1 Bt))),
          (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).Jf⟫|
        ≤ εJ * ‖(WithLp.toLp 2 (Cop Lam (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).Q1 Bt) :
            BondFnL2 Lu)‖ ^ 2)
    (Et : ℝ) (hEt : (8 * ((17 / Real.sqrt 2) * 12 * (rho1 12 M α₀ * (ell : ℝ) ^ 4)) / (1 - ε1)
        + 4 * (32 * rho1 12 M α₀ ^ 2) + 128 * (3 * delStar ell (SstarM ell 12 M α₀) ^ 2)) / cw ≤ Et) :
    ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      gam1 (1 / 54 * (1 / (ell : ℝ) ^ 5)) a (ε2s / cw) εJ ε1 Et (dCof ell (kapM1 (12 * M * α₀)))
          ((1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) / (1 - dCof ell (kapM1 (12 * M * α₀)))) * bondEnergy Bt
        ≤ GenP.genForm (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam) Bt)) := by
  have hell0 : 0 < ell := by omega
  have hη0 : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  have hα0' : 0 ≤ α₀ := hα0.le
  obtain ⟨h216, h12⟩ := rhoT_smalls ell 12 M α₀ hα0' (by omega) hsm4
  have hρ := AdalyFormal.M1GaugeW4.rhoT_nonneg ell 12 M α₀ hα0'
  have hU' := site_hU_M1 hell2 hS U g A0 hUg hB hη0 hα0'
  have hT' := site_hT_M1 hell2 hS (by nlinarith) (hbig_of ell k Lu hLu5) U g A0 hUg hB hη0 hα0' ha1 hsm4
  have ha0 : 0 ≤ ((12 : ℕ) : ℝ) * M * α₀ := by positivity
  have hreg := holRegime_M1 hell0 U g A0 hUg hB hη0 ha0 ha1
  have hp := AdalyFormal.M1IMS.hatPack_of (W := R * M * ell) hS hell2 (periodicGaugeTransform g U) a ha
    (rhoT ell 12 M α₀) hρ h216 hU' hT' hN.hsm hN.hsmD
  have hρ1 : 0 ≤ rho1 12 M α₀ := AdalyFormal.TowerLoc.rho1_nonneg 12 M α₀ hα0'
  have hTT : (1 + 1 / ε1) * (12 * rho1 12 M α₀ ^ 2 * (ell : ℝ) ^ 8 * (4 * ell / csOf a (rhoT ell 12 M α₀)) ^ 2)
        + 2 * ((17 / Real.sqrt 2) * 12 * (rho1 12 M α₀ * (ell : ℝ) ^ 4)) *
          ((ell : ℝ) * (Real.sqrt (12 / csOf a (rhoT ell 12 M α₀)) + Real.sqrt 3 *
            (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / ((R * M * ell : ℕ) : ℝ)) - 1)
            * (4 / csOf a (rhoT ell 12 M α₀)))) ^ 2 ≤ 1 := by
    have h := hN.hη
    unfold etaC nuC at h
    linarith
  have hδ := drift_F_M1 hell2 hS hroom (fun μ => by have := hLu5 μ; omega) U g A0 hUg hB hη0 hα0' ha1 hsm4 hsmA hrr hM hR8
  have hα : ∀ e : Bond (scaleUp ell k Lu), e.1 ∈ S.Om k → periodicLatticeShift e.1 e.2 ∈ S.Om k →
      frobNorm (((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ rho1 12 M α₀ / (ell : ℝ) ^ k := by
    intro e h1 h2
    have := hlink_M1 S U g A0 hUg hB hη0 (by omega) ha0 k le_rfl e h1 h2
    exact this
  have hdC := dCof_lt_one ell hell0 (kapM1 (12 * M * α₀)) (AdalyFormal.M1DK.kapM1_nonneg (by positivity)) hKD.kd
  have hdC0 : 0 ≤ dCof ell (kapM1 (12 * M * α₀)) := by unfold dCof; positivity
  have hcB0 : 0 ≤ (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) / (1 - dCof ell (kapM1 (12 * M * α₀))) := by
    apply div_nonneg (by positivity); linarith
  have hcop : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      ∑ b, ‖Cop Lam (gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam).Q1 Bt b
          - Cop Lam (AdalyFormal.IngredientFamily.q1SU2 ell) Bt b‖ ^ 2
        ≤ dCof ell (kapM1 (12 * M * α₀)) ^ 2 *
          ∑ b, ‖Cop Lam (gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam).Q1 Bt b‖ ^ 2 ∧
      ∑ b, ‖Cop Lam (gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam).Q1 Bt b‖ ^ 2
        ≤ ((1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) / (1 - dCof ell (kapM1 (12 * M * α₀)))) ^ 2
          * bondEnergy Bt := fun Bt _ _ =>
    cop_M1 ell M R k Lu hell0 S U a Lam α₀ hS hell2 hroom hT hL g A0 hUg hB hα0' hKD Bt
  have hRM3 : 3 ≤ R * M := by omega
  have hWR : 1 ≤ R * M * ell := by
    have : 1 ≤ R * M := by omega
    exact Nat.mul_pos (by omega) hell0
  exact chart_core hell0 hell2 hS hRM3 hT hL (periodicGaugeTransform g U) a ha hWD cw ε2s εJ hcw hε2 hεJ hε2cw hcoer hD2 hJ
    (W := R * M * ell) hWR le_rfl (by omega) (by omega) (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1 hp hρ1 hreg hε1 hε1'
    hTT (delStar ell (SstarM ell 12 M α₀)) hδ (rho1 12 M α₀) hρ1 hα (dCof ell (kapM1 (12 * M * α₀)))
    ((1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) / (1 - dCof ell (kapM1 (12 * M * α₀)))) hdC0 hcB0 hcop Et hEt

end AdalyFormal.M1Assembly

#print axioms AdalyFormal.M1Assembly.chart_config
