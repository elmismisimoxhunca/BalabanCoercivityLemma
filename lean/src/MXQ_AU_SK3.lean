import SK3
import AC_MR4
import MXQ_AC_MR5
import MXQ_AC_SK3
import MXQ_Base
import AU_SK3

/-! AU copy of `w4_classACΦ` with `fc` moved INSIDE the quantifier prefix (the witnesses `cW, a0, D` come from `patchCoercive_class_existsAC`, which does not mention `fc`). -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false
namespace MXQ.M2Skel
open MXQ.AllC (CF CubeFamOK)
open AdalyFormal.M2Skel

open AdalyFormal.AllC MXQ.AllC

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp OnLambdaTildeIn TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled OnLambdaT PerCubeRegular2 CoversPlaqOm0c)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.M1Site AdalyFormal.M1IMS
open AdalyFormal.M1GaugeW4
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar)
open AdalyFormal.M1NonFlat (epsNF PkA thetaN)

theorem w4_classUΦ {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ D : ℕ, 12 * ell + 10 ≤ D ∧
    (∀ d, D ≤ d → epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2) ∧
    ∀ {Fm : CF} [CubeFamOK Fm] {M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
      {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hM : 0 < M) (hR1 : 1 ≤ R)
      (hR24 : 24 ≤ R) (hR4 : (5 + 4) * 1 * ell ≤ R) (hroom : 17 * ell ≤ R * M)
      {d : ℕ} (hdD : D ≤ d) (hdM : d + 64 * ell ^ 2 + 2 ≤ M)
      {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
      (U : LinkCfg (scaleUp ell k Lu)) {α₀ : ℝ} (hα0 : 0 < α₀) (hαa : (12 : ℝ) * M * α₀ ≤ a₀)
      (hU : ClassCoupledHQ ell M Fm 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
      (ha1 : ((12 : ℕ) : ℝ) * M * α₀ ≤ 1)
      (Lam : Set (PeriodicLatticeSite Lu)) (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2)
      (hN : W4Num ell M 12 W a (alpha1 ell α₀) ε1)
      (h216 : 216 * rhoT ell 12 M (alpha1 ell α₀) ^ 2 < 1)
      (hat : SiteS1 ell k S U a (csOf a (rhoT ell 12 M (alpha1 ell α₀))))
      (gd : RowBound ell k S U a (gamC ell a (rhoT ell 12 M (alpha1 ell α₀))
        (epsXnum ell W a (rhoT ell 12 M (alpha1 ell α₀)))))
      (mc : MassComm ell M k 1 5 S U a (CMcStar ell M 1 5 a (SstarM ell 12 M (alpha1 ell α₀))))
      (hI : AdalyFormal.M2Route.PatchCharts ell M k 1 5 d S U ((ell : ℝ) ^ k)⁻¹ ((12 : ℕ) * M * α₀))
      (A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G)),
      cwW4 ell M 1 5 W a (rhoT ell 12 M (alpha1 ell α₀)) (rho1 12 M (alpha1 ell α₀)) ε1 ε2
          (cPnf ell W d a cW (alpha1 ell α₀) ε1 12 M)
          (epsXnum ell W a (rhoT ell 12 M (alpha1 ell α₀))) (CMcStar ell M 1 5 a (SstarM ell 12 M (alpha1 ell α₀)))
        * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ := by
  obtain ⟨cW, hcW, a₀, ha₀, D, hD, hDle, hmain⟩ := AdalyFormal.M2Route.patchCoercive_class_existsAC hell ha
  refine ⟨cW, hcW, a₀, ha₀, D, hD, hDle, ?_⟩
  intro Fm _ M R k Lu hell0 S hS hM hR1 hR24 hR4 hroom d hdD hdM W hW hWR U α₀ hα0 hαa hU ha1 Lam ε1 ε2 hε1 hε2 hN h216 hat gd mc hI A
  have hηk : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  set α₁ := alpha1 ell α₀ with hα1
  have hα1p : 0 ≤ α₁ := alpha1_nonneg ell hα0.le
  have hρ := AdalyFormal.M1GaugeW4.rhoT_nonneg ell 12 M α₁ hα1p
  have hρh : 0 ≤ rho1 12 M α₁ := AdalyFormal.TowerLoc.rho1_nonneg 12 M α₁ hα1p
  have hp := hatPack_of_S1 (show 1 ≤ ell by omega) ha hN h216 hat
  have hreg := holRegime_rho1ACΦ (show 1 ≤ ell by omega) hS hηk hα0.le ha1 hU
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hP := hmain hell0 hS hM hR1 hR24 hR4 hroom hdD hdM hW hWR U (csOf a (rhoT ell 12 M α₁)) Lam hp
    (rho1 12 M α₁) hρh hreg ε1 hε1 hN.hη ((ell : ℝ) ^ k)⁻¹ hηk ((12 : ℕ) * M * α₀) (by positivity)
    (by simpa using hαa) hI
  obtain ⟨Gi, hG1, hG2⟩ := gi_of_rowBound (geomOf ell k S) (show 1 ≤ ell by omega) U a _ gd
  have hγ := gd
  have hD' : 0 < (1 - 12 * rhoT ell 12 M α₁) ^ 2 - Real.sqrt (max a 1) * ((1 + 12 * rhoT ell 12 M α₁) ^ 2
      + (512 * rhoT ell 12 M α₁ ^ 2 + 4704) / a) * epsXnum ell W a (rhoT ell 12 M α₁) := by
    have := hN.hgs; linarith
  have hγ0 : 0 ≤ gamC ell a (rhoT ell 12 M α₁) (epsXnum ell W a (rhoT ell 12 M α₁)) := by
    unfold gamC
    apply div_nonneg _ hD'.le
    have : 0 ≤ Real.sqrt (max a 1) := Real.sqrt_nonneg _
    have hr1 : 0 ≤ (512 * rhoT ell 12 M α₁ ^ 2 + 4704) / a := by positivity
    positivity
  have hCM : 0 ≤ CMcStar ell M 1 5 a (SstarM ell 12 M α₁) := by
    unfold AdalyFormal.TowerLoc.CMcStar AdalyFormal.TowerLoc.Estar
    have := AdalyFormal.M1IMS.KG_nonneg ell M 1 5
    positivity
  have hR : (5 + 3) * 1 * ell ≤ R := by omega
  exact ginv_weighted_coercive hell0 hS one_pos hM hell hR1 hR (le_refl 5) hW hWR U a (csOf a (rhoT ell 12 M α₁)) Lam hp
    Gi hG1 hG2 _ hγ0 hγ (rho1 12 M α₁) hρh hreg _ hCM mc ε1 ε2 hε1 hε2 hN.hη _ hP A

end MXQ.M2Skel

#print axioms MXQ.M2Skel.w4_classUΦ
