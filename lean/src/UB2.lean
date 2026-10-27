import UB1

/-!
# UB2 -- U1 core: covariant Stokes at ONE unit plaquette, in that plaquette's own chart (lane m2_unit_20261014)

Fine torus `Lf = scaleUp ℓ k Lu`, `n = ℓ^k`.  For a unit plaquette `q`, a FINE gauge `γ` (the chart of `q`), its unit trace
`u = γ ∘ embY`, a fine configuration `U`, a unit configuration `W`, a fine field `y`, a unit field `B`:
  `n ‖curl_W B q‖² ≤ (1+ε) n⁻² winSum n G (q) + (1+1/ε) n (16 κ² (‖B b₂‖² + ‖B b₃‖²) + 8 D_q)`
  `G(z) = 2‖curl_U y z‖² + 16 (s/n)² (‖y(z₀+μ,ν)‖² + ‖y(z₀+ν,μ)‖²)`   (no chart in `G`),
  `D_q = Σ_{b ∈ ∂q} ‖q₁ⁿ(γ·y)(b) − (u·B)(b)‖²`   (the bond defect IN THE CHART),
provided `U^γ` has its window base links `≤ s/n` and `W^u` has the two base links of `q` `≤ κ`.
Only `D_q` and the two smallness hypotheses depend on the chart; everything else is gauge invariant.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2Unit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap curlValueCovariant)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply)
open AdalyFormal.Balaban.RegularUPerturbation (curlDrift)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.IngredientFamilyR2 (embY)
open AdalyFormal.GenuineU1 (unitField plaqE bondsE curl_reindex)

/-- `‖a + b − c − d‖² ≤ 4(‖a‖² + ‖b‖² + ‖c‖² + ‖d‖²)`. -/
theorem sq_four_le {E : Type*} [SeminormedAddCommGroup E] (a b c d : E) :
    ‖a + b - c - d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h1 : ‖a + b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    calc ‖a + b - c - d‖ ≤ ‖a + b - c‖ + ‖d‖ := norm_sub_le _ _
      _ ≤ ‖a + b‖ + ‖c‖ + ‖d‖ := by linarith [norm_sub_le (a + b) c]
      _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by linarith [norm_add_le a b]
  have h0 : 0 ≤ ‖a + b - c - d‖ := norm_nonneg _
  have h2 := pow_le_pow_left₀ h0 h1 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖a‖ - ‖d‖), sq_nonneg (‖b‖ - ‖c‖),
    sq_nonneg (‖b‖ - ‖d‖), sq_nonneg (‖c‖ - ‖d‖)]

/-- the chart-free window integrand. -/
noncomputable def Gwin {L : PeriodicLatticeExtent} (U : PeriodicLinkConfiguration SU2 L) (y : Bond L → SuTwo) (σ : ℝ)
    (z : PeriodicLatticePlaquette L) : ℝ :=
  2 * ‖curlValueCovariant U y z‖ ^ 2
    + 16 * σ ^ 2 * (‖y (periodicLatticeShift z.1 z.2.1.1, z.2.1.2)‖ ^ 2 + ‖y (periodicLatticeShift z.1 z.2.1.2, z.2.1.1)‖ ^ 2)

theorem Gwin_nonneg {L : PeriodicLatticeExtent} (U : PeriodicLinkConfiguration SU2 L) (y : Bond L → SuTwo) (σ : ℝ)
    (z : PeriodicLatticePlaquette L) : 0 ≤ Gwin U y σ z := by
  unfold Gwin; positivity

/-- the chart bond defect of `q`. -/
noncomputable def Dq {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (γ : GaugeFn (scaleUp ell k Lu))
    (y : Bond (scaleUp ell k Lu) → SuTwo) (B : Bond Lu → SuTwo) (q : PeriodicLatticePlaquette Lu) : ℝ :=
  let X : Bond Lu → SuTwo := fun b =>
    unitField ell k Lu hell (lineCoarseRestrictSuTwo (ell ^ k) (gaugeActA γ y)) b
      - gaugeActA (fun w => γ (embY ell k Lu hell w)) B b
  ‖X (q.1, q.2.1.1)‖ ^ 2 + ‖X (periodicLatticeShift q.1 q.2.1.1, q.2.1.2)‖ ^ 2
    + ‖X (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)‖ ^ 2 + ‖X (q.1, q.2.1.2)‖ ^ 2

theorem norm_gaugeActA' {L : PeriodicLatticeExtent} (γ : GaugeFn L) (B : Bond L → SuTwo) (b : Bond L) :
    ‖gaugeActA γ B b‖ = ‖B b‖ := by
  rw [gaugeActA_apply]; exact AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap _ _

theorem norm_curl_gauge {L : PeriodicLatticeExtent} (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2 L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    ‖curlValueCovariant (periodicGaugeTransform γ U) (gaugeActA γ A) p‖ = ‖curlValueCovariant U A p‖ := by
  rw [AdalyFormal.Balaban.AlphaAnalyticity.curlValueCovariant_gauge, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]

/-- **U1 core at one unit plaquette, in its own chart.** -/
theorem stokes_chart {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (hu : ∀ μ, 1 ≤ Lu μ)
    (U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)) (W : PeriodicLinkConfiguration SU2 Lu)
    (y : Bond (scaleUp ell k Lu) → SuTwo) (B : Bond Lu → SuTwo) (q : PeriodicLatticePlaquette Lu)
    (γ : GaugeFn (scaleUp ell k Lu)) (s κ ε : ℝ) (hs : 0 ≤ s) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hwin : ∀ x ∈ blockOf (embY ell k Lu hell q.1) (ell ^ k), ∀ i ∈ Finset.range (ell ^ k), ∀ j ∈ Finset.range (ell ^ k),
      frobNorm (((periodicGaugeTransform γ U ((winPl q.2 x i j).1, q.2.1.1) : SU2) : M2) - 1) ≤ s / (ell : ℝ) ^ k ∧
      frobNorm (((periodicGaugeTransform γ U ((winPl q.2 x i j).1, q.2.1.2) : SU2) : M2) - 1) ≤ s / (ell : ℝ) ^ k)
    (hW1 : frobNorm (((periodicGaugeTransform (fun w => γ (embY ell k Lu hell w)) W (q.1, q.2.1.1) : SU2) : M2) - 1) ≤ κ)
    (hW2 : frobNorm (((periodicGaugeTransform (fun w => γ (embY ell k Lu hell w)) W (q.1, q.2.1.2) : SU2) : M2) - 1) ≤ κ) :
    (ell : ℝ) ^ k * ‖curlValueCovariant W B q‖ ^ 2
      ≤ (1 + ε) * ((1 / ((ell : ℝ) ^ k) ^ 2) *
            winSum (ell ^ k) (Gwin U y (s / (ell : ℝ) ^ k)) (plaqE ell k Lu hell q))
        + (1 + 1 / ε) * ((ell : ℝ) ^ k * (16 * κ ^ 2 * (‖B (periodicLatticeShift q.1 q.2.1.1, q.2.1.2)‖ ^ 2
            + ‖B (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)‖ ^ 2) + 8 * Dq hell γ y B q)) := by
  set n : ℕ := ell ^ k with hn
  have hnpos : 0 < n := pow_pos hell k
  have hnR : ((n : ℕ) : ℝ) = (ell : ℝ) ^ k := by rw [hn]; push_cast; ring
  have hnR0 : (0 : ℝ) < (ell : ℝ) ^ k := by rw [← hnR]; exact_mod_cast hnpos
  set u : GaugeFn Lu := fun w => γ (embY ell k Lu hell w) with hu_def
  set B' := gaugeActA u B with hB'
  set W' := periodicGaugeTransform u W with hW'
  set y' := gaugeActA γ y with hy'
  set V := periodicGaugeTransform γ U with hV
  set Bf : Bond Lu → SuTwo := unitField ell k Lu hell (lineCoarseRestrictSuTwo n y') with hBf
  set X : Bond Lu → SuTwo := fun b => Bf b - B' b with hX
  -- the unit-level decomposition
  have hcurl : ‖curlValueCovariant W B q‖ = ‖curlValueCovariant W' B' q‖ := (norm_curl_gauge u W B q).symm
  set E := curlDrift W' B' q - flatCurlValue X q with hE
  have hsplit : curlValueCovariant W' B' q = flatCurlValue Bf q + E := by
    have h1 := flat_eq_cov_sub_drift W' B' q
    have h2 : flatCurlValue X q = flatCurlValue Bf q - flatCurlValue B' q := by
      simp only [hX, flatCurlValue]; abel
    rw [hE, h2]
    have : curlValueCovariant W' B' q = flatCurlValue B' q + curlDrift W' B' q := by rw [h1]; abel
    rw [this]; abel
  have hY := sq_add_young (flatCurlValue Bf q) E hε
  rw [← hsplit] at hY
  -- the error term
  have hE2 : ‖E‖ ^ 2 ≤ 16 * κ ^ 2 * (‖B (periodicLatticeShift q.1 q.2.1.1, q.2.1.2)‖ ^ 2
        + ‖B (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)‖ ^ 2) + 8 * Dq hell γ y B q := by
    have h1 := sq_add_two (curlDrift W' B' q) (-(flatCurlValue X q))
    rw [← sub_eq_add_neg, norm_neg] at h1
    have h2 := curlDrift_sq_loc W' B' q κ hκ hW1 hW2
    rw [norm_gaugeActA', norm_gaugeActA'] at h2
    have h3 : ‖flatCurlValue X q‖ ^ 2 ≤ 4 * Dq hell γ y B q := by
      unfold flatCurlValue Dq
      exact sq_four_le _ _ _ _
    rw [hE]; nlinarith
  -- Stokes in the chart
  have hst := stokes_pt hnpos (AdalyFormal.GenuineU1.scaleUp_tiling ell k Lu hell) y' (plaqE ell k Lu hell q)
  have hre : flatCurlValue Bf q = AdalyFormal.Balaban.ThirdLevelStokes.coarseCurlSuTwo
      (AdalyFormal.GenuineU1.scaleUp_tiling ell k Lu hell) (lineCoarseRestrictSuTwo n y') (plaqE ell k Lu hell q) :=
    curl_reindex ell k Lu hell hu _ q
  rw [← hre] at hst
  -- the window integrand, chart-free
  have hwinG : winSum n (fun z => ‖flatCurlValue y' z‖ ^ 2) (plaqE ell k Lu hell q)
      ≤ winSum n (Gwin U y (s / (ell : ℝ) ^ k)) (plaqE ell k Lu hell q) := by
    unfold winSum
    refine Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_)))
    have hx' : x ∈ blockOf (embY ell k Lu hell q.1) (ell ^ k) := hx
    obtain ⟨h1, h2⟩ := hwin x hx' i hi j hj
    set z := winPl (plaqE ell k Lu hell q).2 x i j with hz
    have hz2 : z.2 = q.2 := rfl
    have hfl := flat_eq_cov_sub_drift V y' z
    have hsq := sq_add_two (curlValueCovariant V y' z) (-(curlDrift V y' z))
    rw [← sub_eq_add_neg, norm_neg, ← hfl] at hsq
    have hcov : ‖curlValueCovariant V y' z‖ = ‖curlValueCovariant U y z‖ := norm_curl_gauge γ U y z
    have hdr := curlDrift_sq_loc V y' z (s / (ell : ℝ) ^ k) (by positivity) (by rw [hz2]; exact h1) (by rw [hz2]; exact h2)
    rw [norm_gaugeActA', norm_gaugeActA'] at hdr
    unfold Gwin
    rw [hcov] at hsq
    nlinarith
  have hn1 : (n : ℝ) * ‖flatCurlValue Bf q‖ ^ 2
      ≤ (1 / ((ell : ℝ) ^ k) ^ 2) * winSum n (Gwin U y (s / (ell : ℝ) ^ k)) (plaqE ell k Lu hell q) := by
    refine hst.trans ?_
    rw [hnR]
    exact mul_le_mul_of_nonneg_left hwinG (by positivity)
  rw [hnR] at hn1
  rw [hcurl]
  have hε1 : 0 ≤ 1 + 1 / ε := by positivity
  have hε0 : 0 ≤ 1 + ε := by linarith
  have t1 := mul_le_mul_of_nonneg_left hY hnR0.le
  have t2 := mul_le_mul_of_nonneg_left hn1 hε0
  have t3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE2 hnR0.le) hε1
  nlinarith

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.sq_four_le
#print axioms AdalyFormal.M2Unit.stokes_chart
