import UA8
import HB1

/-!
# UA9 -- U3 at the statement's objects, from fine charts (lane m2_unit_20261014)

* `unitBgU_chart_small` : if a fine gauge `γ` makes `U^γ` agree, on the fine ball `Ball(embY z, rhoT ℓ k)`, with a fine
  configuration `V` carrying the DK2 `tower_near` bounds on `Ω_k` (links `e₁/ℓ^k`, plaquettes `q₁/ℓ^{2k}`), and `z` is within
  `RM − 17` of `Λ`, then the statement's unit background in the induced unit gauge `u = γ ∘ embY` is small at `z`:
  `‖(Ū^k)^u(z,μ) − 1‖_F ≤ e₁ + 3π q₁`.   (GCa6 `unitBgU_gauge` + ZR8Read `bgTower_congr` + DK2 `tower_near`; ONE chart, no
  global gauge.)
* `lemma24_cov_gparams` : UA8 `lemma24_cov_C` at `P = gparams ℓ k Lu hell S U a Λ` (`W = P.unitBgU`, `C = genC P`), the per-cell
  smallness discharged by `unitBgU_chart_small` from per-cell fine charts `(γ_m, V_m)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2Unit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist OnLambdaTildeIn)
open AdalyFormal.StatementLaneG (LambdaOK2 gparams GenP.genC)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.IngredientFamilyR2 (Q1jet H0 Cop embY)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo curlValueCovariant)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt rhoT)
open AdalyFormal.CurvBlock (dv pw PlaqT plaqIn)
open AdalyFormal.M1DK (BK)
open AdalyFormal.NonflatJet (rhoOf r0)
open SmallnessBridge.Assemble (loopFactorBound)

theorem unitBgU_chart_small {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (hell2 : 2 ≤ ell)
    (S : Tower (scaleUp ell k Lu)) (hA : Admissible ell M R k S) (Lam : Set (PeriodicLatticeSite Lu))
    (hL : LambdaOK2 ell M R k S Lam) (hT3 : ∀ μ, 3 ≤ Lu μ + 1)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (γ : GaugeFn (scaleUp ell k Lu))
    (V : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)) (e1 q1 : ℝ) (hq1 : 0 ≤ q1)
    (hlink : ∀ e : PeriodicLatticeEdge (scaleUp ell k Lu), BK S k e → dv (V e) ≤ e1 / (ell : ℝ) ^ k)
    (hplaq : ∀ t : PlaqT (scaleUp ell k Lu), plaqIn (BK S k) t → dv (pw 1 V t.1 t.2.1 t.2.2) ≤ q1 / ((ell : ℝ) ^ k) ^ 2)
    (hsm : 4000000 * (ell : ℝ) ^ 2 * q1 ≤ 1)
    (z : PeriodicLatticeSite Lu) (hag : AgreeAt (Ball (embY ell k Lu hell z) (rhoT ell k)) (periodicGaugeTransform γ U) V)
    {y : PeriodicLatticeSite Lu} (hy : y ∈ Lam) (hz : pdist y z + 17 ≤ R * M) (μ : Fin 3) :
    frobNorm (((periodicGaugeTransform (fun w => γ (embY ell k Lu hell w))
        (gparams ell k Lu hell S U a Lam).unitBgU (z, μ) : SU2) : M2) - 1) ≤ e1 + 3 * Real.pi * q1 := by
  set P := gparams ell k Lu hell S U a Lam with hP
  have h1 := AdalyFormal.GaugeCov.unitBgU_gauge P γ
  rw [← h1]
  have h2 := AdalyFormal.StatementLaneR8.bgTower_congr P.G hell k (embY ell k Lu hell z) hag μ
  have h3 := AdalyFormal.M1DK.tower_near ell M R k Lu hell2 hell S hA Lam hL hT3 V e1 q1 hq1 hlink hplaq hsm hy hz μ
  simp only [dv] at h3
  convert h3 using 4
  exact h2

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.unitBgU_chart_small
