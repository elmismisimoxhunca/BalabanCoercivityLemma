import UD10
import AU_UD4
import AU_DK2
import AU_CUT

/-! AU copy of UD10 (c-free): `hb_classU` takes a `BallChartsAt` instance. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2UnitCharts


open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist TorusOK CRowIn)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt rhoT pdist_comm pdist_triangle pdist_coarseShift_le lamPrime_sub Ball_sub)
open AdalyFormal.IngredientFamilyR2 (embY embY_val H0)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.M1DK (kapM1 qM1 KDsmall)
open AdalyFormal.M2Unit (agree_gauge unitBgU_chart_small)

theorem hb_classU {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell)
    (hT : TorusOK ell M Lu) (hMb : 4 * ell + 141 ≤ 4 * M) (hRM : 5 * ell + 17 ≤ R * M) (hR6 : 6 * ell ≤ R) (hk1 : 1 ≤ k)
    (hthick : ∀ σ : Fin 3, 12 * (M * ell ^ k) ≤ scaleUp ell k Lu σ + 1)
    (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S)
    (Lam : Set (PeriodicLatticeSite Lu)) (hL : LambdaOK2 ell M R k S Lam)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (αb : ℝ) (hα : 0 < αb) {C : ℝ} (hC : 1 ≤ C)
    (hBall : AdalyFormal.OneGap.BallChartsAt ell M k S U C αb ((ell : ℝ) ^ k)⁻¹)
    (α₁ : ℝ) (hα1 : (ell : ℝ) ^ 3 * (2 * (C * αb)) ≤ α₁) (hsm : KDsmall ell (12 * M * α₁)) :
    Function.Bijective (H0 Lam (gparams ell k Lu (by omega) S U a Lam).Q1) := by
  have hell : 0 < ell := by omega
  have hn : 0 < ell ^ k := pow_pos hell k
  have hLu : ∀ σ : Fin 3, 1 ≤ scaleUp ell k Lu σ := by
    intro σ
    have h1 := scaleUp_succ ell k Lu hell σ
    have h2 := hT.2.1 σ
    have : 3 ≤ Lu σ + 1 := by omega
    have h3 : (Lu σ + 1) * 1 ≤ (Lu σ + 1) * ell ^ k := Nat.mul_le_mul_left _ hn
    omega
  have hT3 : ∀ μ, 3 ≤ Lu μ + 1 := fun μ => by have := hT.2.1 μ; omega
  have hα1pos : 0 < α₁ := lt_of_lt_of_le (by have := lt_of_lt_of_le one_pos hC; positivity) hα1
  have hβ0 : 0 ≤ 12 * (M : ℝ) * α₁ := by positivity
  have hL1 := hL.1
  set P := gparams ell k Lu hell S U a Lam with hP
  have hrho := AdalyFormal.StatementLaneR8.rhoT_le ell hell2 k
  refine hb_of_row_gauges hell hell2 hT.1 Lam P.unitBgU (kapM1 (12 * M * α₁)) (AdalyFormal.M1DK.kapM1_nonneg hβ0)
    hsm.u1 hsm.u2 hsm.kd (fun c hc => ?_)
  -- a point of Λ within ℓ of c₋
  obtain ⟨y0, hy0, hyc⟩ : ∃ y ∈ Lam, pdist y c.1.1 ≤ ell := by
    rcases hc with h | h
    · exact ⟨c.1.1, lamPrime_sub hell h, by rw [AdalyFormal.StatementLane.pdist_self]; exact Nat.zero_le _⟩
    · refine ⟨coarseShift c.1.1 ell c.2, lamPrime_sub hell h, ?_⟩
      rw [pdist_comm]; exact pdist_coarseShift_le _ _ _
  have hrad : (ell ^ k * (4 * ell) + 8 * ell ^ k) + 64 * ell ^ k + 5 ≤ 6 * (M * ell ^ k) - 1 := by
    have h1 : ell ^ k * (4 * ell + 141) ≤ ell ^ k * (4 * M) := Nat.mul_le_mul_left _ hMb
    have e1 : ell ^ k * (4 * ell + 141) = ell ^ k * (4 * ell) + 141 * ell ^ k := by ring
    have e2 : ell ^ k * (4 * M) = 4 * (M * ell ^ k) := by ring
    omega
  obtain ⟨γ, V, hV, hag⟩ := chart_of_ballU hell (by omega : 0 < M) hk1 hS hL1 hthick hR6 hy0 c.1.1 (by omega)
    (ell ^ k * (4 * ell) + 8 * ell ^ k) hrad hC hα hBall
  replace hV := AdalyFormal.AllU.M1RegularU.mono (by positivity) hα1 hV
  obtain ⟨g, A, hgA, hB⟩ := hV
  obtain ⟨hlk, hpl⟩ := AdalyFormal.M1DK.chart_boundsU ell M k hell S α₁ V g A _ rfl hgA hB hα1pos.le hsm.h1
  refine ⟨fun w => (g (embY ell k Lu hell w)) * (γ (embY ell k Lu hell w)), fun z hz μ => ?_⟩
  set γ' : GaugeFn (scaleUp ell k Lu) := fun x => g x * γ x with hγ'
  have hcomp : periodicGaugeTransform γ' U = periodicGaugeTransform g (periodicGaugeTransform γ U) :=
    (AdalyFormal.Lattice.Witness.periodicGaugeTransform_comp g γ U).symm
  have hag' : AgreeAt (Ball (embY ell k Lu hell c.1.1) (ell ^ k * (4 * ell) + 8 * ell ^ k)) (periodicGaugeTransform γ' U)
      (periodicGaugeTransform g V) := by
    rw [hcomp]; exact agree_gauge hag g
  have hz' : pdist c.1.1 z ≤ 4 * (1 * ell) := hz
  have hsub : AgreeAt (Ball (embY ell k Lu hell z) (rhoT ell k)) (periodicGaugeTransform γ' U) (periodicGaugeTransform g V) := by
    refine hag'.mono (Ball_sub (d := ell ^ k * (4 * ell)) ?_ (by omega))
    rw [pdist_embY hell]
    exact Nat.mul_le_mul_left _ (by omega)
  have hnear : pdist y0 z + 17 ≤ R * M := by
    have := pdist_triangle y0 c.1.1 z
    omega
  have := unitBgU_chart_small hell hell2 S hS Lam hL hT3 U a γ' (periodicGaugeTransform g V) (12 * M * α₁)
    (qM1 (12 * M * α₁)) (AdalyFormal.M1DK.qM1_nonneg hβ0) hlk hpl hsm.hcb z hsub hy0 hnear μ
  unfold kapM1; exact this

end AdalyFormal.M2UnitCharts

