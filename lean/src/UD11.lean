import UD10

/-!
# UD11 -- `unit_floor_class_nohb` (UD7 with `hb` replaced by `KDsmall`, via `hb_class`): the unit-level floor (`unit_floor_kfree`) at a configuration of the PRINTED class, no global gauge (lane m2_unitcharts_20261014)

The unit charts `Vq q`, `Vc m` of `unit_floor_kfree` are produced from `ClassCoupled ell M 12 k S α₀ ℓ^{-k} U` by `chart_of_class` (one index-`k` class cube
per chart, UD3/UD4).  `Qs` is the set of plaquettes within `2ℓ+1` of `Λ` and `I` the set of cells containing a point within `1` of `Λ`; their support
properties are proved (`genC_support`, `hpart_pdist`), not assumed.  All smallness hypotheses are at `α₁ = ℓ³ · 2 α₀`.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2UnitCharts

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist OnLambdaTildeIn TorusOK)
open AdalyFormal.StatementLaneG (gparams LambdaOK2 GenP.genC)
open AdalyFormal.StatementLane2 (OnLambdaT ClassCoupled)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt rhoT pdist_comm pdist_triangle pdist_shift_le)
open AdalyFormal.FlatEllGeneral (InBox)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.TowerLoc (rho1 epsM delLoc delStar SstarM)
open AdalyFormal.BondComposite (rr thetaOf thetaOf_nonneg)
open AdalyFormal.M1DK (kapM1 qM1)
open AdalyFormal.M2Unit

open Classical in
theorem unit_floor_class_nohb {ell M R k Mc : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell)
    (hT : TorusOK ell M Lu) (hMc : M = ell * Mc) (hMc0 : 0 < Mc)
    (hMbig : 6 * Mc + 4 * ell + 165 ≤ 5 * M) (hRM : 21 * M + 2 * ell + 12 ≤ R * M)
    (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S)
    (Lam : Set (PeriodicLatticeSite Lu)) (hL : LambdaOK2 ell M R k S Lam)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (α₀ : ℝ) (hα : 0 < α₀)
    (hU : ClassCoupled ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (Bt : Bond Lu → SuTwo) (hBt : OnLambdaTildeIn Lam ell Bt) (hBT : OnLambdaT Lam Bt)
    (α₁ : ℝ) (hα1 : α₁ = (ell : ℝ) ^ 3 * (2 * α₀))
    (ha1 : (12 : ℝ) * M * α₁ ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M α₁ ≤ 1)
    (hsmq : 4000000 * (ell : ℝ) ^ 2 * qM1 (12 * M * α₁) ≤ 1)
    (hsmA : (1 + 3 * Real.pi) * rho1 12 M α₁ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
    (hrr : Real.pi / 2 * ((loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M α₁)) < r0)
    (hsm : AdalyFormal.M1DK.KDsmall ell (12 * M * α₁))
    (hρ : rhoOf ell (kapM1 (12 * M * α₁)) < Real.pi / 2)
    (hrg : Real.pi / 2 * ((loopFactorBound ell : ℝ) * kapM1 (12 * M * α₁)) < r0)
    (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε')
    (hcoef : 0 ≤ cU ell Mc (kapM1 (12 * M * α₁)) ε ε')
    (y : BondFnL2 (scaleUp ell k Lu))
    (hQ : (bondSectorOf (geomOf ell k S) U).Qfull y = ContinuousLinearMap.adjoint (gparams ell k Lu (by omega) S U a Lam).tau
      (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt))) :
    (cU ell Mc (kapM1 (12 * M * α₁)) ε ε' * bondEnergy Bt
      ≤ 2 * (1 + ε) * (1 + ε') / (ell : ℝ) ^ k *
          ∑ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette (scaleUp ell k Lu))).filter
              (fun p => p ∈ plaqIn (S.Om k)), ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2
        + (1 + ε) / (ell : ℝ) ^ k * ((1 + ε') * 64 * rho1 12 M α₁ ^ 2
            + (1 + 1 / ε') * 62208 * delStar ell (SstarM ell 12 M α₁) ^ 2)
          * AdalyFormal.M1.wnormSq S ell k y)
    ∧ (cU ell Mc (kapM1 (12 * M * α₁)) ε ε'
          * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt b‖ ^ 2
      ≤ 2 * (1 + ε) * (1 + ε') / (ell : ℝ) ^ k *
          ∑ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette (scaleUp ell k Lu))).filter
              (fun p => p ∈ plaqIn (S.Om k)), ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2
        + (1 + ε) / (ell : ℝ) ^ k * ((1 + ε') * 64 * rho1 12 M α₁ ^ 2
            + (1 + 1 / ε') * 62208 * delStar ell (SstarM ell 12 M α₁) ^ 2)
          * AdalyFormal.M1.wnormSq S ell k y)
    ∧ bondEnergy Bt ≤ ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt b‖ ^ 2 := by
  have hb := hb_class (R := R) hell2 hT (by omega) hRM S hS Lam hL U a α₀ hα hU α₁ hα1 hsm
  exact unit_floor_class hell2 hT hMc hMc0 hMbig hRM S hS Lam hL U a α₀ hα hU hb Bt hBt hBT α₁ hα1 ha1 hsm4 hsmq hsmA hrr hρ hrg
    ε ε' hε hε' hcoef y hQ

end AdalyFormal.M2UnitCharts

#print axioms AdalyFormal.M2UnitCharts.unit_floor_class_nohb
