import MA16

/-!
# MA17 -- `config_inst`: the printed inequality `InstIneq` at ONE configuration, from the chart inputs and the real-number windows
(lane m1_assembly_20261014).  `Gamma/(4(T+1))` with `T = 4/(1-eps1)` is the resulting constant.
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
open AdalyFormal.StatementLaneG (gparams LambdaOK2 GenP.genForm GenP.genC GenP.WellDef InstIneq)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.M1IMS AdalyFormal.M1GaugeW4 AdalyFormal.TowerLoc
open AdalyFormal.M1DK (KDsmall kapM1)
open AdalyFormal.M1Num (rhoH Ssr)

theorem Etf_eq (ell M : ℕ) (α₀ ε1 cw : ℝ) :
    Etf ell ε1 cw ((12 : ℝ) * M * α₀)
      = (8 * ((17 / Real.sqrt 2) * 12 * (rho1 12 M α₀ * (ell : ℝ) ^ 4)) / (1 - ε1)
        + 4 * (32 * rho1 12 M α₀ ^ 2) + 128 * (3 * delStar ell (SstarM ell 12 M α₀) ^ 2)) / cw := by
  unfold Etf AdalyFormal.M1Num.rhoH AdalyFormal.M1Num.Ssr rho1 SstarM
  push_cast
  rfl

theorem config_inst {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell)
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
    (Γ : ℝ) (hΓ : Γ = 1 / 54 * (1 / (ell : ℝ) ^ 5)) (cBm : ℝ)
    (hcBm : cBm = 2 * (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)))
    (hw1 : Etf ell ε1 cw ((12 : ℝ) * M * α₀) ≤ 1)
    (hw2 : dCof ell (kapM1 ((12 : ℝ) * M * α₀)) ≤ 1 / 2)
    (hw3 : (Etf ell ε1 cw ((12 : ℝ) * M * α₀) * a + 128 * dCof ell (kapM1 ((12 : ℝ) * M * α₀)) ^ 2) * cBm ^ 2 ≤ Γ / 4)
    (he1 : ε2s / cw ≤ 1 / 2)
    (he2 : (ε2s / cw * a + 2 * εJ) * cBm ^ 2 ≤ Γ / (8 * (4 / (1 - ε1) + 1))) :
    InstIneq ell k (by omega) a Lu (Γ / (4 * (4 / (1 - ε1) + 1))) S Lam U := by
  have hell0 : 0 < ell := by omega
  have hΓ0 : 0 < Γ := by rw [hΓ]; positivity
  rw [← AdalyFormal.GaugeCov.instIneq_gauge_iff (γ := g)]
  intro Bt hBt hBT
  have hch := chart_config hell2 hS hroom hM hR8 hT hLu5 hL U g A0 hα0 hUg hB ha1 hsm4 hsmA hrr hKD a ha ε1 hε1 hε1' hN hWD
    cw ε2s εJ hcw hε2 hεJ hε2cw hcoer hD2 hJ (Etf ell ε1 cw ((12 : ℝ) * M * α₀)) (le_of_eq (Etf_eq ell M α₀ ε1 cw).symm)
    Bt hBt hBT
  have hs0 : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
  have hdC := dCof_lt_one ell hell0 (kapM1 (12 * M * α₀)) (AdalyFormal.M1DK.kapM1_nonneg hs0) hKD.kd
  have hdC0 : 0 ≤ dCof ell (kapM1 (12 * M * α₀)) := by unfold dCof; positivity
  have hcB0 : 0 ≤ (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) / (1 - dCof ell (kapM1 (12 * M * α₀))) := by
    apply div_nonneg (by positivity); linarith
  have hcB : (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) / (1 - dCof ell (kapM1 (12 * M * α₀))) ≤ cBm := by
    rw [hcBm, div_le_iff₀ (by linarith)]
    have h1 : 0 ≤ 1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3) := by positivity
    nlinarith
  have hEt0 := Etf_nonneg ell ε1 cw ((12 : ℝ) * M * α₀) hε1' hcw hs0
  have hge := gam1_ge Γ a (ε2s / cw) εJ ε1 (Etf ell ε1 cw ((12 : ℝ) * M * α₀)) (dCof ell (kapM1 (12 * M * α₀)))
    ((1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) / (1 - dCof ell (kapM1 (12 * M * α₀)))) cBm hΓ0 ha.le hε1 hε1'
    (div_nonneg hε2 hcw.le) he1 hεJ hEt0 hw1 hdC0 hcB0 hcB hw3 he2
  have hbe : 0 ≤ bondEnergy Bt := Finset.sum_nonneg (fun b _ => sq_nonneg _)
  rw [hΓ] at hge
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hbe) hch
  rw [hΓ]
  exact hge

end AdalyFormal.M1Assembly

#print axioms AdalyFormal.M1Assembly.Etf_eq
#print axioms AdalyFormal.M1Assembly.config_inst
