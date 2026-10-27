import UB9

/-!
# UC2 -- the Layer-U chain from LOCAL M1 charts only (lane m2_unit_20261014)

* `hS3_of_M1` : the U3 per-cell smallness `‖(Ū^k)^{u_m} − 1‖ ≤ kapM1(12Mα₀)` on the 4ℓ-balls of cell `m`'s support, from a fine
  gauge `γ_m` and an `M1Regular` configuration `V_m` agreeing with `U^{γ_m}` on the fine balls `Ball(embY z, rhoT ℓ k)`.
* `unit_chain_M1charts` : UC1 `unit_chain` with every chart hypothesis supplied by local M1 charts (per unit plaquette `q ∈ Qs`
  and per cell `m ∈ I`).  The remaining hypotheses are geometry (good boxes, distance to `Λ`, agreement balls), the k-free
  smallness of `α₀`, `hb`, and `Q_U y = τ* C B̃`.  No global gauge.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.M2Unit

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice blockOf)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist OnLambdaTildeIn)
open AdalyFormal.StatementLaneG (gparams LambdaOK2 LamBlockSum GenP.genC)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt rhoT)
open AdalyFormal.FlatEllGeneral (InBox)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.TowerLoc (rho1 epsM delLoc)
open AdalyFormal.M1DK (kapM1 qM1)

theorem hS3_of_M1 {ell M R k Mc : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell) (hT3 : ∀ μ, 3 ≤ Lu μ + 1)
    (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S) (Lam : Set (PeriodicLatticeSite Lu))
    (hL : LambdaOK2 ell M R k S Lam) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (α₀ : ℝ) (hα0 : 0 ≤ α₀)
    (ha1 : (12 : ℝ) * M * α₀ ≤ 1) (hsmq : 4000000 * (ell : ℝ) ^ 2 * qM1 (12 * M * α₀) ≤ 1)
    (I : Set ((μ : Fin 3) → Fin (Kc Lu Mc μ)))
    (γ : ((μ : Fin 3) → Fin (Kc Lu Mc μ)) → GaugeFn (scaleUp ell k Lu))
    (V : ((μ : Fin 3) → Fin (Kc Lu Mc μ)) → LinkCfg (scaleUp ell k Lu))
    (hV : ∀ m ∈ I, AdalyFormal.M1.M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ (V m))
    (hag : ∀ m ∈ I, ∀ x, hpart Mc m x ≠ 0 → ∀ z ∈ Ball x (4 * (1 * ell)),
      AgreeAt (Ball (embY ell k Lu (by omega) z) (rhoT ell k)) (periodicGaugeTransform (γ m) U) (V m) ∧
      ∃ y0 ∈ Lam, pdist y0 z + 17 ≤ R * M) :
    ∃ u : ((μ : Fin 3) → Fin (Kc Lu Mc μ)) → GaugeFn Lu,
      ∀ m ∈ I, ∀ x, hpart Mc m x ≠ 0 → ∀ z ∈ Ball x (4 * (1 * ell)), ∀ μ : Fin 3,
        frobNorm (((periodicGaugeTransform (u m) (gparams ell k Lu (by omega) S U a Lam).unitBgU (z, μ) : SU2) : M2) - 1)
          ≤ kapM1 (12 * M * α₀) := by
  classical
  have hell : 0 < ell := by omega
  -- the gauge of each chart
  have hex : ∀ m, ∃ g : GaugeFn (scaleUp ell k Lu), m ∈ I → ∃ A : Bond (scaleUp ell k Lu) → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ e : Bond (scaleUp ell k Lu), ((periodicGaugeTransform g (V m) e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp ((((((ell : ℝ) ^ k)⁻¹ : ℝ) : ℂ) * Complex.I) • A e)) ∧
      AdalyFormal.M1.M1Bounds S ell M 12 k α₀ ((ell : ℝ) ^ k)⁻¹ A := by
    intro m
    by_cases hm : m ∈ I
    · obtain ⟨g, A, h1, h2⟩ := hV m hm
      exact ⟨g, fun _ => ⟨A, h1, h2⟩⟩
    · exact ⟨fun _ => 1, fun h => absurd h hm⟩
  choose g hg using hex
  refine ⟨fun m w => g m (embY ell k Lu hell w) * γ m (embY ell k Lu hell w), ?_⟩
  intro m hm x hx z hz μ
  obtain ⟨A, hgA, hB⟩ := hg m hm
  obtain ⟨hagz, y0, hy0, hnear⟩ := hag m hm x hx z hz
  obtain ⟨hlk, hpl⟩ := AdalyFormal.M1DK.chart_bounds ell M k hell S α₀ (V m) (g m) A _ rfl hgA hB hα0 ha1
  have hcomp : periodicGaugeTransform (fun x => g m x * γ m x) U
      = periodicGaugeTransform (g m) (periodicGaugeTransform (γ m) U) :=
    (AdalyFormal.Lattice.Witness.periodicGaugeTransform_comp (g m) (γ m) U).symm
  have hag' : AgreeAt (Ball (embY ell k Lu hell z) (rhoT ell k))
      (periodicGaugeTransform (fun x => g m x * γ m x) U) (periodicGaugeTransform (g m) (V m)) := by
    rw [hcomp]; exact agree_gauge hagz (g m)
  have := unitBgU_chart_small hell hell2 S hS Lam hL hT3 U a (fun x => g m x * γ m x) (periodicGaugeTransform (g m) (V m))
    (12 * M * α₀) (qM1 (12 * M * α₀)) (AdalyFormal.M1DK.qM1_nonneg (by positivity)) hlk hpl hsmq z hag' hy0 hnear μ
  unfold kapM1
  exact this

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.hS3_of_M1

namespace AdalyFormal.M2Unit

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice blockOf)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist OnLambdaTildeIn)
open AdalyFormal.StatementLaneG (gparams LambdaOK2 LamBlockSum GenP.genC)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt rhoT)
open AdalyFormal.FlatEllGeneral (InBox)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.TowerLoc (rho1 epsM delLoc)
open AdalyFormal.M1DK (kapM1 qM1)

open Classical in
/-- **Layer U from local M1 charts** (`unit_chain_M1charts`). -/
theorem unit_chain_M1charts {ell M R k Mc : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell)
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
    -- U3 cell charts
    (I : Set ((μ : Fin 3) → Fin (Kc Lu Mc μ)))
    (hI : ∀ m (b : Bond Lu), (b.1 ∈ Lam ∨ periodicLatticeShift b.1 b.2 ∈ Lam) → hpart Mc m b.1 ≠ 0 → m ∈ I)
    (γc : ((μ : Fin 3) → Fin (Kc Lu Mc μ)) → GaugeFn (scaleUp ell k Lu))
    (Vc : ((μ : Fin 3) → Fin (Kc Lu Mc μ)) → LinkCfg (scaleUp ell k Lu))
    (hVc : ∀ m ∈ I, AdalyFormal.M1.M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ (Vc m))
    (hagc : ∀ m ∈ I, ∀ x, hpart Mc m x ≠ 0 → ∀ z ∈ Ball x (4 * (1 * ell)),
      AgreeAt (Ball (embY ell k Lu (by omega) z) (rhoT ell k)) (periodicGaugeTransform (γc m) U) (Vc m) ∧
      ∃ y0 ∈ Lam, pdist y0 z + 17 ≤ R * M)
    -- U1 plaquette charts
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
    (hVq : ∀ q ∈ Qs, AdalyFormal.M1.M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ (Vq q))
    (hagq : ∀ q ∈ Qs, AgreeAt (Ball (embY ell k Lu (by omega) q.1) (32 * ell ^ k)) (periodicGaugeTransform (γq q) U) (Vq q)) :
    (1 / 54 : ℝ) * (1 / (ell : ℝ) ^ 5) * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt b‖ ^ 2
      ≤ (1 + ε) * (1 / (ell : ℝ) ^ k) *
          ((1 + ε') * (2 * ∑ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette (scaleUp ell k Lu))).filter
              (fun p => p ∈ plaqIn (S.Om k)), ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2
            + 64 * (rho1 12 M α₀ / (ell : ℝ) ^ k) ^ 2 * ‖y‖ ^ 2)
          + (1 + 1 / ε') * (64 * kapM1 (12 * M * α₀) ^ 2 * (ell : ℝ) ^ k
              * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt b‖ ^ 2
            + 8 * 7776 * (1 / ((ell : ℝ) ^ k) ^ 2) * delLoc ell (fun l => epsM ell 12 M α₀ k l) (Fin.last k) ^ 2
              * ‖y‖ ^ 2))
        + Eims ell (Real.pi / (2 * Mc)) ((4 * ell : ℕ) * (Real.pi / (2 * Mc))) (kapM1 (12 * M * α₀)) ε
          * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt b‖ ^ 2
    ∧ bondEnergy Bt ≤ ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt b‖ ^ 2 := by
  have hell : 0 < ell := by omega
  have hu : ∀ μ, 1 ≤ Lu μ := fun μ => by have := hstrict μ; omega
  have hT3 : ∀ μ, 3 ≤ Lu μ + 1 := fun μ => by have := hstrict μ; omega
  have hβ : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
  have hκ : 0 ≤ kapM1 (12 * M * α₀) := AdalyFormal.M1DK.kapM1_nonneg hβ
  have hs : 0 ≤ rho1 12 M α₀ := AdalyFormal.TowerLoc.rho1_nonneg 12 M α₀ hα0
  obtain ⟨hε0, hsm, hr⟩ := epsM_conds hell α₀ hα0 k hsmA hrr
  -- cell gauges
  obtain ⟨u, hS3⟩ := hS3_of_M1 hell2 hT3 S hS Lam hL U a α₀ hα0 ha1 hsmq I γc Vc hVc hagc
  -- plaquette charts
  have hch : ∀ q, ∃ γ' : GaugeFn (scaleUp ell k Lu), ∃ Wr : ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)),
      q ∈ Qs → ChartOK hell S U (gparams ell k Lu hell S U a Lam).unitBgU q γ' (rho1 12 M α₀) (kapM1 (12 * M * α₀))
        (fun l => epsM ell 12 M α₀ k l) Wr := by
    intro q
    by_cases hq : q ∈ Qs
    · obtain ⟨y0, hy0, hn⟩ := hnear q hq
      obtain ⟨γ', Wr, h⟩ := chartOK_of_M1 hell2 hu hT3 S hS hroom Lam hL U a α₀ hα0 ha1 hsm4 hsmq q (hgood q hq) hy0 hn
        (γq q) (Vq q) (hVq q hq) (hagq q hq)
      exact ⟨γ', Wr, fun _ => h⟩
    · exact ⟨fun _ => 1, fun _ => ∅, fun h => absurd h hq⟩
  choose γ' Wr hC using hch
  exact unit_chain hell2 hstrict hdvd hP S hS U a Lam hL.2 hb Bt hBt hBT I hI u (kapM1 (12 * M * α₀)) ε hκ hε hρ hrg
    hS3 y hQ Qs hQs γ' Wr (rho1 12 M α₀) (kapM1 (12 * M * α₀)) ε' (fun l => epsM ell 12 M α₀ k l) hs hκ hε'
    (fun j _ => hε0 j) (fun j _ => hsm j) (fun j _ => hr j) (fun q hq => hC q hq) hgood

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.unit_chain_M1charts
