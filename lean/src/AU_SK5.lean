import SK5
import AU_UD7

/-! AU copy of SK5 (c-free): `config_inst_classU` takes a `BallChartsAt` instance (at parameter `αb`, `C αb ≤ α₀`) instead of the class and top-level cube. -/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 32000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false
namespace AdalyFormal.M2Skel


open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp OnLambdaTildeIn TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled OnLambdaT)
open AdalyFormal.StatementLaneG (gparams LambdaOK2 GenP.genForm GenP.genC GenP.WellDef InstIneq)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.M1IMS AdalyFormal.M1GaugeW4 AdalyFormal.TowerLoc
open AdalyFormal.M1DK (KDsmall kapM1)
open AdalyFormal.M1Assembly (gam1 gam1_ge)
open AdalyFormal.M1Num (rhoH Ssr)

open Classical in
theorem config_inst_classU {ell M R k Mc : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hroom : 17 * ell ≤ R * M) (hM : 0 < M)
    (hT : TorusOK ell M Lu)
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK2 ell M R k S Lam)
    (U : LinkCfg (scaleUp ell k Lu)) {α₀ : ℝ} (hα0 : 0 < α₀)
    {αb : ℝ} (hαb : 0 < αb) {C : ℝ} (hC : 1 ≤ C) (hCb : C * αb ≤ α₀)
    (hBall : AdalyFormal.OneGap.BallChartsAt ell M k S U C αb ((ell : ℝ) ^ k)⁻¹) (a : ℝ) (ha : 0 < a)
    (hMc : M = ell * Mc) (hMc0 : 0 < Mc) (hMbig : 6 * Mc + 4 * ell + 165 ≤ 4 * M) (hRM : 6 * Mc + 4 * ell + 25 ≤ R * M) (hR6 : 6 * ell ≤ R) (hk1 : 1 ≤ k)
    (hthick : ∀ σ : Fin 3, 12 * (M * ell ^ k) ≤ scaleUp ell k Lu σ + 1)
    (ha1 : ((12 : ℕ) : ℝ) * M * alpha1 ell α₀ ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M (alpha1 ell α₀) ≤ 1)
    (hsmA : (1 + 3 * Real.pi) * rho1 12 M (alpha1 ell α₀) ≤ 1 / (1000 * (ell : ℝ) ^ 4))
    (hrr : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M (alpha1 ell α₀)))
        < AdalyFormal.NonflatJet.r0)
    (hKD : KDsmall ell (12 * M * alpha1 ell α₀))
    (hrho : AdalyFormal.NonflatJet.rhoOf ell (kapM1 (12 * M * alpha1 ell α₀)) < Real.pi / 2)
    (hcU : (1 / 108) * (1 / (ell : ℝ) ^ 5) ≤ AdalyFormal.M2Unit.cU ell Mc (kapM1 (12 * M * alpha1 ell α₀)) 1 1)
    (hb : Function.Bijective (H0 Lam (gparams ell k Lu (by omega) S U a Lam).Q1))
    (ε1 : ℝ) (hε1 : 0 < ε1) (hε1' : ε1 < 1)
    (hN : W4Num ell M 12 (R * M * ell) a (alpha1 ell α₀) ε1)
    (hWD : GenP.WellDef (gparams ell k Lu (by omega) S U a Lam))
    (cw ε2s εJ : ℝ) (hcw : 0 < cw) (hε2 : 0 ≤ ε2s) (hεJ : 0 ≤ εJ) (hε2cw : ε2s ≤ cw)
    (hcoer : ∀ A : ↥(bondSupp (gparams ell k Lu (by omega) S U a Lam).G),
      cw * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A, (gparams ell k Lu (by omega) S U a Lam).data.Ginv A⟫)
    (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu (by omega) S U a Lam).G),
      |⟪A, (gparams ell k Lu (by omega) S U a Lam).data.Delta2 (gparams ell k Lu (by omega) S U a Lam).data_laws A⟫|
        ≤ ε2s * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
    (hJ : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      |⟪(gparams ell k Lu (by omega) S U a Lam).H1in
          ((gparams ell k Lu (by omega) S U a Lam).D2in
            (WithLp.toLp 2 (Cop Lam (gparams ell k Lu (by omega) S U a Lam).Q1 Bt))),
          (gparams ell k Lu (by omega) S U a Lam).Jf⟫|
        ≤ εJ * ‖(WithLp.toLp 2 (Cop Lam (gparams ell k Lu (by omega) S U a Lam).Q1 Bt) : BondFnL2 Lu)‖ ^ 2)
    (h216 : 216 * rhoT ell 12 M (alpha1 ell α₀) ^ 2 < 1)
    (hat : SiteS1 ell k S U a (csOf a (rhoT ell 12 M (alpha1 ell α₀))))
    (hreg : HolRegime S ell k U (rho1 12 M (alpha1 ell α₀)))
    (hw1 : Etc ell ε1 cw ((12 : ℝ) * M * alpha1 ell α₀) ≤ 1)
    (hw3 : Etc ell ε1 cw ((12 : ℝ) * M * alpha1 ell α₀) * a ≤ Gam0 ell / 4)
    (he1 : ε2s / cw ≤ 1 / 2)
    (he2 : (ε2s / cw * a + 2 * εJ) ≤ Gam0 ell / (8 * (4 / (1 - ε1) + 1))) :
    InstIneq ell k (by omega) a Lu (Gam0 ell / (4 * (4 / (1 - ε1) + 1))) S Lam U := by
  have hell0 : 0 < ell := by omega
  have hMpos : 1 ≤ M := hM
  have hRM3 : 3 ≤ R * M := by omega
  have hα1p : 0 ≤ alpha1 ell α₀ := alpha1_nonneg ell hα0.le
  have hρ1 : 0 ≤ rho1 12 M (alpha1 ell α₀) := AdalyFormal.TowerLoc.rho1_nonneg 12 M _ hα1p
  have hρ := AdalyFormal.M1GaugeW4.rhoT_nonneg ell 12 M _ hα1p
  have hWR : 1 ≤ R * M * ell := by
    have : 1 ≤ R * M := by omega
    exact Nat.mul_pos (by omega) hell0
  have hR1 : 1 ≤ R := by
    by_contra h
    have : R = 0 := by omega
    subst this; simp at hRM
  have hp := hatPack_of_S1 (show 1 ≤ ell by omega) ha hN h216 hat
  have hTT : (1 + 1 / ε1) * (12 * rho1 12 M (alpha1 ell α₀) ^ 2 * (ell : ℝ) ^ 8
        * (4 * ell / csOf a (rhoT ell 12 M (alpha1 ell α₀))) ^ 2)
        + 2 * ((17 / Real.sqrt 2) * 12 * (rho1 12 M (alpha1 ell α₀) * (ell : ℝ) ^ 4)) *
          ((ell : ℝ) * (Real.sqrt (12 / csOf a (rhoT ell 12 M (alpha1 ell α₀))) + Real.sqrt 3 *
            (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / ((R * M * ell : ℕ) : ℝ)) - 1)
            * (4 / csOf a (rhoT ell 12 M (alpha1 ell α₀))))) ^ 2 ≤ 1 := by
    have h := hN.hη
    unfold etaC nuC at h
    linarith
  have hfloor : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      ∀ y : BondFnL2 (scaleUp ell k Lu),
      (bondSectorOf (geomOf ell k S) U).Qfull y = ContinuousLinearMap.adjoint (gparams ell k Lu hell0 S U a Lam).tau
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S U a Lam) Bt)) →
      ((1 / 108) * (1 / (ell : ℝ) ^ 5) * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu hell0 S U a Lam) Bt b‖ ^ 2
        ≤ (2 * (1 + 1) * (1 + 1)) / (ell : ℝ) ^ k *
            ∑ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette (scaleUp ell k Lu))).filter
                (fun p => p ∈ plaqIn (S.Om k)), ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2
          + ((1 + 1) * ((1 + 1) * 64 * rho1 12 M (alpha1 ell α₀) ^ 2
              + (1 + 1 / (1 : ℝ)) * 62208 * delStar ell (SstarM ell 12 M (alpha1 ell α₀)) ^ 2)) / (ell : ℝ) ^ k
            * AdalyFormal.M1.wnormSq S ell k y)
      ∧ bondEnergy Bt ≤ ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu hell0 S U a Lam) Bt b‖ ^ 2 := by
    intro Bt hBt hBT y hQ
    obtain ⟨-, h2, h3⟩ := AdalyFormal.M2UnitCharts.unit_floor_classU hell2 hT hMc hMc0 hMbig hRM hroom hR6 hk1 hthick S hS Lam hL U a αb hαb hC hBall hb
      Bt hBt hBT (alpha1 ell α₀) (by unfold alpha1; have := pow_pos (show (0:ℝ) < ell by exact_mod_cast hell0) 3; nlinarith) (by simpa using ha1) hsm4 hKD.hcb hsmA hrr hrho hKD.u2 1 1 one_pos one_pos
      (le_trans (by positivity : (0:ℝ) ≤ (1 / 108) * (1 / (ell : ℝ) ^ 5)) hcU) y hQ
    refine ⟨?_, h3⟩
    have hSum : 0 ≤ ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu hell0 S U a Lam) Bt b‖ ^ 2 :=
      Finset.sum_nonneg (fun b _ => sq_nonneg _)
    calc (1 / 108) * (1 / (ell : ℝ) ^ 5) * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu hell0 S U a Lam) Bt b‖ ^ 2
        ≤ AdalyFormal.M2Unit.cU ell Mc (kapM1 (12 * M * alpha1 ell α₀)) 1 1
          * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu hell0 S U a Lam) Bt b‖ ^ 2 := mul_le_mul_of_nonneg_right hcU hSum
      _ ≤ _ := h2
      _ = _ := by ring
  have hc1 : (0 : ℝ) < 2 * (1 + 1) * (1 + 1) := by norm_num
  have hcUc : (0 : ℝ) < (1 / 108) * (1 / (ell : ℝ) ^ 5) := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  have hc2 : (0 : ℝ) ≤ (1 + 1) * ((1 + 1) * 64 * rho1 12 M (alpha1 ell α₀) ^ 2
              + (1 + 1 / (1 : ℝ)) * 62208 * delStar ell (SstarM ell 12 M (alpha1 ell α₀)) ^ 2) := by positivity
  have hEtn : (8 * ((17 / Real.sqrt 2) * 12 * (rho1 12 M (alpha1 ell α₀) * (ell : ℝ) ^ 4)) / (1 - ε1)
        + 4 * (((1 + 1) * ((1 + 1) * 64 * rho1 12 M (alpha1 ell α₀) ^ 2
              + (1 + 1 / (1 : ℝ)) * 62208 * delStar ell (SstarM ell 12 M (alpha1 ell α₀)) ^ 2))
          / (2 * (1 + 1) * (1 + 1)))) / cw ≤ Etc ell ε1 cw ((12 : ℝ) * M * alpha1 ell α₀) :=
    le_of_eq (Etc_eq ell M _ ε1 cw).symm
  have hG0 : 4 * ((1 / 108) * (1 / (ell : ℝ) ^ 5)) / (2 * (1 + 1) * (1 + 1)) = Gam0 ell := rfl
  have hs0 : 0 ≤ (12 : ℝ) * M * alpha1 ell α₀ := by positivity
  have hEt0 := Etc_nonneg ell ε1 cw ((12 : ℝ) * M * alpha1 ell α₀) hε1' hcw hs0
  have hT1 : 0 < 4 / (1 - ε1) + 1 := by
    have : 0 < 4 / (1 - ε1) := div_pos (by norm_num) (by linarith)
    linarith
  have hge := gam1_ge (Gam0 ell) a (ε2s / cw) εJ ε1 (Etc ell ε1 cw ((12 : ℝ) * M * alpha1 ell α₀)) 0 1 1
    (Gam0_pos hell0) ha.le hε1 hε1' (div_nonneg hε2 hcw.le) he1 hεJ hEt0 hw1 le_rfl zero_le_one le_rfl
    (by simpa using hw3) (by simpa using he2)
  have hg0 : 0 ≤ gam1 (4 * ((1 / 108) * (1 / (ell : ℝ) ^ 5)) / (2 * (1 + 1) * (1 + 1))) a (ε2s / cw) εJ ε1
      (Etc ell ε1 cw ((12 : ℝ) * M * alpha1 ell α₀)) 0 1 := by
    rw [hG0]
    exact le_trans (by have := Gam0_pos hell0; positivity) hge
  intro Bt hBt hBT
  have hch := chart_core_class hell0 hell2 hS hRM3 hT hL U a ha hWD cw ε2s εJ hcw hε2 hεJ hε2cw hcoer hD2 hJ
    (W := R * M * ell) hWR le_rfl hR1 hMpos (csOf a (rhoT ell 12 M (alpha1 ell α₀))) (rho1 12 M (alpha1 ell α₀)) ε1 hp hρ1 hreg
    hε1 hε1' hTT ((1 / 108) * (1 / (ell : ℝ) ^ 5)) (2 * (1 + 1) * (1 + 1))
    ((1 + 1) * ((1 + 1) * 64 * rho1 12 M (alpha1 ell α₀) ^ 2
              + (1 + 1 / (1 : ℝ)) * 62208 * delStar ell (SstarM ell 12 M (alpha1 ell α₀)) ^ 2))
    hcUc hc1 hc2 hfloor (Etc ell ε1 cw ((12 : ℝ) * M * alpha1 ell α₀)) hEtn hg0 Bt hBt hBT
  have hbe : 0 ≤ bondEnergy Bt := Finset.sum_nonneg (fun b _ => sq_nonneg _)
  rw [hG0] at hch
  exact le_trans (mul_le_mul_of_nonneg_right hge hbe) hch

end AdalyFormal.M2Skel

