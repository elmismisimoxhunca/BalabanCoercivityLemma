import AU_CUT
import UC4
import AU_UC2

open AdalyFormal.AllU (M1BoundsU M1RegularU)

/-! AU copy of UC4: M1Regular -> M1RegularU, affected declarations only (lane allc_20261016, uniform-in-c route). -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.M2Unit

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
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist OnLambdaTildeIn)
open AdalyFormal.StatementLaneG (gparams LambdaOK2 GenP.genC)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt rhoT)
open AdalyFormal.FlatEllGeneral (InBox)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.TowerLoc (rho1 epsM delLoc)
open AdalyFormal.M1DK (kapM1 qM1)

open Classical in
theorem unit_floor_M1chartsU {ell M R k Mc : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell)
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hdvd : ∀ μ : Fin 3, ell ∣ (Lu μ + 1)) (hP : PartOK Lu Mc)
    (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S) (hroom : 17 * ell ≤ R * M)
    (Lam : Set (PeriodicLatticeSite Lu)) (hL : LambdaOK2 ell M R k S Lam)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (hb : Function.Bijective (H0 Lam (gparams ell k Lu (by omega) S U a Lam).Q1))
    (Bt : Bond Lu → SuTwo) (hBt : OnLambdaTildeIn Lam ell Bt) (hBT : OnLambdaT Lam Bt)
    (α₀ : ℝ) (hα0 : 0 ≤ α₀) (ha1 : (12 : ℝ) * M * α₀ ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M α₀ ≤ 1)
    (hsmq : 4000000 * (ell : ℝ) ^ 2 * qM1 (12 * M * α₀) ≤ 1)
    (hsmA : (1 + 3 * Real.pi) * rho1 12 M α₀ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
    (hrr : Real.pi / 2 * ((loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M α₀)) < r0)
    (hρ : rhoOf ell (kapM1 (12 * M * α₀)) < Real.pi / 2)
    (hrg : Real.pi / 2 * ((loopFactorBound ell : ℝ) * kapM1 (12 * M * α₀)) < r0)
    (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε')
    (hcoef : 0 ≤ cU ell Mc (kapM1 (12 * M * α₀)) ε ε')
    (I : Set ((μ : Fin 3) → Fin (Kc Lu Mc μ)))
    (hI : ∀ m (b : Bond Lu), (b.1 ∈ Lam ∨ periodicLatticeShift b.1 b.2 ∈ Lam) → hpart Mc m b.1 ≠ 0 → m ∈ I)
    (γc : ((μ : Fin 3) → Fin (Kc Lu Mc μ)) → GaugeFn (scaleUp ell k Lu))
    (Vc : ((μ : Fin 3) → Fin (Kc Lu Mc μ)) → LinkCfg (scaleUp ell k Lu))
    (hVc : ∀ m ∈ I, AdalyFormal.AllU.M1RegularU ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ (Vc m))
    (hagc : ∀ m ∈ I, ∀ x, hpart Mc m x ≠ 0 → ∀ z ∈ Ball x (4 * (1 * ell)),
      AgreeAt (Ball (embY ell k Lu (by omega) z) (rhoT ell k)) (periodicGaugeTransform (γc m) U) (Vc m) ∧
      ∃ y0 ∈ Lam, pdist y0 z + 17 ≤ R * M)
    (y : BondFnL2 (scaleUp ell k Lu))
    (hQ : (bondSectorOf (geomOf ell k S) U).Qfull y = ContinuousLinearMap.adjoint (gparams ell k Lu (by omega) S U a Lam).tau
      (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)))
    (Qs : Finset (PeriodicLatticePlaquette Lu))
    (hQs : ∀ q, (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt (qb1 q) ≠ 0
        ∨ GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt (qb2 q) ≠ 0
        ∨ GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt (qb3 q) ≠ 0
        ∨ GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt (qb4 q) ≠ 0) → q ∈ Qs)
    (hgood : ∀ q ∈ Qs, ∀ c, InBox q.1 c → embY ell k Lu (by omega) c ∈ S.Om k)
    (hnear : ∀ q ∈ Qs, ∃ y0 ∈ Lam, pdist y0 q.1 + 17 ≤ R * M)
    (γq : PeriodicLatticePlaquette Lu → GaugeFn (scaleUp ell k Lu))
    (Vq : PeriodicLatticePlaquette Lu → LinkCfg (scaleUp ell k Lu))
    (hVq : ∀ q ∈ Qs, AdalyFormal.AllU.M1RegularU ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ (Vq q))
    (hagq : ∀ q ∈ Qs, AgreeAt (Ball (embY ell k Lu (by omega) q.1) (32 * ell ^ k)) (periodicGaugeTransform (γq q) U) (Vq q)) :
    (cU ell Mc (kapM1 (12 * M * α₀)) ε ε' * bondEnergy Bt
      ≤ 2 * (1 + ε) * (1 + ε') / (ell : ℝ) ^ k *
          ∑ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette (scaleUp ell k Lu))).filter
              (fun p => p ∈ plaqIn (S.Om k)), ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2
        + (1 + ε) / (ell : ℝ) ^ k * ((1 + ε') * 64 * rho1 12 M α₀ ^ 2
            + (1 + 1 / ε') * 62208 * delLoc ell (fun l => epsM ell 12 M α₀ k l) (Fin.last k) ^ 2)
          * AdalyFormal.M1.wnormSq S ell k y)
    ∧ (cU ell Mc (kapM1 (12 * M * α₀)) ε ε'
          * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt b‖ ^ 2
      ≤ 2 * (1 + ε) * (1 + ε') / (ell : ℝ) ^ k *
          ∑ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette (scaleUp ell k Lu))).filter
              (fun p => p ∈ plaqIn (S.Om k)), ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2
        + (1 + ε) / (ell : ℝ) ^ k * ((1 + ε') * 64 * rho1 12 M α₀ ^ 2
            + (1 + 1 / ε') * 62208 * delLoc ell (fun l => epsM ell 12 M α₀ k l) (Fin.last k) ^ 2)
          * AdalyFormal.M1.wnormSq S ell k y)
    ∧ bondEnergy Bt ≤ ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt b‖ ^ 2 := by
  have hell : 0 < ell := by omega
  obtain ⟨hch, hen⟩ := unit_chain_M1chartsU hell2 hstrict hdvd hP S hS hroom Lam hL U a hb Bt hBt hBT α₀ hα0 ha1 hsm4
    hsmq hsmA hrr hρ hrg ε ε' hε hε' I hI γc Vc hVc hagc y hQ Qs hQs hgood hnear γq Vq hVq hagq
  have hnR0 : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  have hY := AdalyFormal.M1Assembly.normSq_le_wnorm (k := k) (by omega : 1 ≤ ell) S y
  have hxx : 0 ≤ AdalyFormal.M1.wnormSq S ell k y := by
    unfold AdalyFormal.M1.wnormSq; exact Finset.sum_nonneg (fun b _ => by positivity)
  have hδ : 0 ≤ delLoc ell (fun l => epsM ell 12 M α₀ k l) (Fin.last k) ^ 2 := sq_nonneg _
  unfold cU at hcoef ⊢
  have hch' : (1 / 54 * (1 / (ell : ℝ) ^ 5)) * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu hell S U a Lam) Bt b‖ ^ 2
      ≤ (1 + ε) * (1 / (ell : ℝ) ^ k) *
          ((1 + ε') * (2 * ∑ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette (scaleUp ell k Lu))).filter
              (fun p => p ∈ plaqIn (S.Om k)), ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2
            + 64 * (rho1 12 M α₀ / (ell : ℝ) ^ k) ^ 2 * ‖y‖ ^ 2)
          + (1 + 1 / ε') * (64 * kapM1 (12 * M * α₀) ^ 2 * (ell : ℝ) ^ k
              * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu hell S U a Lam) Bt b‖ ^ 2
            + 8 * 7776 * (1 / ((ell : ℝ) ^ k) ^ 2) * delLoc ell (fun l => epsM ell 12 M α₀ k l) (Fin.last k) ^ 2
              * ‖y‖ ^ 2))
        + Eims ell (Real.pi / (2 * Mc)) ((4 * ell : ℕ) * (Real.pi / (2 * Mc))) (kapM1 (12 * M * α₀)) ε
          * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu hell S U a Lam) Bt b‖ ^ 2 := by
    have e : (1 / 54 : ℝ) * (1 / (ell : ℝ) ^ 5) * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu hell S U a Lam) Bt b‖ ^ 2
        = (1 / 54 * (1 / (ell : ℝ) ^ 5)) * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu hell S U a Lam) Bt b‖ ^ 2 := rfl
    linarith
  exact ⟨unit_chain_closed hnR0 hε hε' hY hxx hen hcoef hch',
    unit_chain_closed hnR0 hε hε' hY hxx le_rfl hcoef hch', hen⟩

end AdalyFormal.M2Unit

