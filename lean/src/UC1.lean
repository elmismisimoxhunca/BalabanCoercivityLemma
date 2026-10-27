import UB7

/-!
# UC1 -- the Layer-U chain at the statement's objects (lane m2_unit_20261014)

At `P = gparams ℓ k Lu hell S U a Λ` (unit background `Ū = P.unitBgU`, `Q₁ = P.Q1 = Q1jet ℓ Ū`, `C = genC P`), for `B̃ ∈ Λ̃`
with `H₀(Q₁)` bijective, `B = C B̃`, a fine field `y` with `Q_U y = τ* B`:
  `(1/54)ℓ⁻⁵ ‖B‖² ≤ (1+ε) Σ_q ‖curl_Ū B q‖² + Eims ‖B‖²`                              (U3, per-cell gauges)
  `n Σ_q ‖curl_Ū B q‖² ≤ (1+ε')(2 Xbox + 64 (s/n)² ‖y‖²) + (1+1/ε')(64 κ₁² n ‖B‖² + 62208 n⁻² δ² ‖y‖²)` (U1, per-plaquette gauges)
combined in `unit_chain`.  `‖B̃‖² ≤ ‖B‖²` is returned too.  No global gauge anywhere.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.M2Unit

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp OnLambdaTildeIn)
open AdalyFormal.StatementLaneG (gparams LamBlockSum GenP.genC)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.FlatEllGeneral (InBox)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.TowerLoc (delLoc)

/-- the covariant curl vanishes on a plaquette all of whose bonds carry `0`. -/
theorem curl_zero_of_bonds {L : PeriodicLatticeExtent} (W : PeriodicLinkConfiguration SU2 L) (B : Bond L → SuTwo)
    (q : PeriodicLatticePlaquette L) (h1 : B (qb1 q) = 0) (h2 : B (qb2 q) = 0) (h3 : B (qb3 q) = 0) (h4 : B (qb4 q) = 0) :
    curlValueCovariant W B q = 0 := by
  unfold curlValueCovariant
  simp only [qb1, qb2, qb3, qb4] at h1 h2 h3 h4
  rw [h1, h2, h3, h4]; simp

open Classical in
theorem sum_curl_support {L : PeriodicLatticeExtent} (W : PeriodicLinkConfiguration SU2 L) (B : Bond L → SuTwo)
    (Qs : Finset (PeriodicLatticePlaquette L))
    (hQs : ∀ q, (B (qb1 q) ≠ 0 ∨ B (qb2 q) ≠ 0 ∨ B (qb3 q) ≠ 0 ∨ B (qb4 q) ≠ 0) → q ∈ Qs) :
    ∑ q : PeriodicLatticePlaquette L, ‖curlValueCovariant W B q‖ ^ 2 = ∑ q ∈ Qs, ‖curlValueCovariant W B q‖ ^ 2 := by
  symm
  refine Finset.sum_subset (Finset.subset_univ _) (fun q _ hq => ?_)
  have hz : B (qb1 q) = 0 ∧ B (qb2 q) = 0 ∧ B (qb3 q) = 0 ∧ B (qb4 q) = 0 := by
    by_contra h
    apply hq
    apply hQs
    tauto
  rw [curl_zero_of_bonds W B q hz.1 hz.2.1 hz.2.2.1 hz.2.2.2]; simp

open Classical in
/-- **the Layer-U chain** (`unit_chain`). -/
theorem unit_chain {ell M R k Mc : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell)
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hdvd : ∀ μ : Fin 3, ell ∣ (Lu μ + 1)) (hP : PartOK Lu Mc)
    (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam)
    (hb : Function.Bijective (H0 Lam (gparams ell k Lu (by omega) S U a Lam).Q1))
    (Bt : Bond Lu → SuTwo) (hBt : OnLambdaTildeIn Lam ell Bt) (hBT : OnLambdaT Lam Bt)
    -- U3 charts (unit cells)
    (I : Set ((μ : Fin 3) → Fin (Kc Lu Mc μ)))
    (hI : ∀ m (b : Bond Lu), (b.1 ∈ Lam ∨ periodicLatticeShift b.1 b.2 ∈ Lam) → hpart Mc m b.1 ≠ 0 → m ∈ I)
    (u : ((μ : Fin 3) → Fin (Kc Lu Mc μ)) → GaugeFn Lu) (κ ε : ℝ) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hρ : rhoOf ell κ < Real.pi / 2) (hrg : Real.pi / 2 * ((loopFactorBound ell : ℝ) * κ) < r0)
    (hS3 : ∀ m ∈ I, ∀ x, hpart Mc m x ≠ 0 → ∀ z ∈ Ball x (4 * (1 * ell)), ∀ μ : Fin 3,
      frobNorm (((periodicGaugeTransform (u m) (gparams ell k Lu (by omega) S U a Lam).unitBgU (z, μ) : SU2) : M2) - 1) ≤ κ)
    -- U1 charts (unit plaquettes)
    (y : BondFnL2 (scaleUp ell k Lu))
    (hQ : (bondSectorOf (geomOf ell k S) U).Qfull y = ContinuousLinearMap.adjoint (gparams ell k Lu (by omega) S U a Lam).tau
      (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)))
    (Qs : Finset (PeriodicLatticePlaquette Lu))
    (hQs : ∀ q, (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt (qb1 q) ≠ 0
        ∨ GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt (qb2 q) ≠ 0
        ∨ GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt (qb3 q) ≠ 0
        ∨ GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt (qb4 q) ≠ 0) → q ∈ Qs)
    (γ : PeriodicLatticePlaquette Lu → GaugeFn (scaleUp ell k Lu))
    (Wr : PeriodicLatticePlaquette Lu → ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (s κ₁ ε' : ℝ) (εr : ℕ → ℝ) (hs : 0 ≤ s) (hκ₁ : 0 ≤ κ₁) (hε' : 0 < ε')
    (hε0 : ∀ j, j < k → 0 ≤ εr j) (hsm : ∀ j, j < k → rhoOf ell (εr j) < Real.pi / 2)
    (hr : ∀ j, j < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * εr j) < r0)
    (hC : ∀ q ∈ Qs, ChartOK (by omega) S U (gparams ell k Lu (by omega) S U a Lam).unitBgU q (γ q) s κ₁ εr (Wr q))
    (hgood : ∀ q ∈ Qs, ∀ c, InBox q.1 c → embY ell k Lu (by omega) c ∈ S.Om k) :
    (1 / 54 : ℝ) * (1 / (ell : ℝ) ^ 5) * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt b‖ ^ 2
      ≤ (1 + ε) * (1 / (ell : ℝ) ^ k) *
          ((1 + ε') * (2 * ∑ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette (scaleUp ell k Lu))).filter
              (fun p => p ∈ plaqIn (S.Om k)), ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2
            + 64 * (s / (ell : ℝ) ^ k) ^ 2 * ‖y‖ ^ 2)
          + (1 + 1 / ε') * (64 * κ₁ ^ 2 * (ell : ℝ) ^ k
              * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt b‖ ^ 2
            + 8 * 7776 * (1 / ((ell : ℝ) ^ k) ^ 2) * delLoc ell εr (Fin.last k) ^ 2 * ‖y‖ ^ 2))
        + Eims ell (Real.pi / (2 * Mc)) ((4 * ell : ℕ) * (Real.pi / (2 * Mc))) κ ε
          * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt b‖ ^ 2
    ∧ bondEnergy Bt ≤ ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt b‖ ^ 2 := by
  have hell : 0 < ell := by omega
  have hu : ∀ μ, 1 ≤ Lu μ := fun μ => by have := hstrict μ; omega
  set P := gparams ell k Lu hell S U a Lam with hPdef
  set Bc := GenP.genC P Bt with hBc
  have hgenC : Bc = Cop Lam (Q1jet ell P.unitBgU) Bt := rfl
  obtain ⟨h3, hen⟩ := lemma24_cov_C hell2 hstrict hdvd hP hLB P.unitBgU hb Bt hBt hBT I hI u κ ε hκ hε hρ hrg hS3
  refine ⟨?_, hen⟩
  rw [← hgenC] at h3
  have hsupp := sum_curl_support P.unitBgU Bc Qs hQs
  have hU1 := stokes_U1 hell2 hu S hS U a Lam P.unitBgU y (WithLp.toLp 2 Bc) hQ Qs γ Wr s κ₁ ε' εr hs hκ₁ hε' hε0 hsm hr hC hgood
  have hBn : ‖(WithLp.toLp 2 Bc : BondFnL2 Lu)‖ ^ 2 = ∑ b : Bond Lu, ‖Bc b‖ ^ 2 := by rw [PiLp.norm_sq_eq_of_L2]
  have hofLp : (WithLp.ofLp (WithLp.toLp 2 Bc : BondFnL2 Lu)) = Bc := rfl
  rw [hofLp, hBn] at hU1
  rw [hsupp] at h3
  have hnR0 : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  have hdiv : ∑ q ∈ Qs, ‖curlValueCovariant P.unitBgU Bc q‖ ^ 2
      ≤ (1 / (ell : ℝ) ^ k) * ((ell : ℝ) ^ k * ∑ q ∈ Qs, ‖curlValueCovariant P.unitBgU Bc q‖ ^ 2) := by
    rw [← mul_assoc, one_div_mul_cancel hnR0.ne', one_mul]
  have hU1' := mul_le_mul_of_nonneg_left hU1 (by positivity : (0 : ℝ) ≤ 1 / (ell : ℝ) ^ k)
  have hε0' : (0 : ℝ) ≤ 1 + ε := by linarith
  have := mul_le_mul_of_nonneg_left (hdiv.trans hU1') hε0'
  nlinarith

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.curl_zero_of_bonds
#print axioms AdalyFormal.M2Unit.sum_curl_support
#print axioms AdalyFormal.M2Unit.unit_chain
