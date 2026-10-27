import UA3
import GCa5

/-!
# UA4 -- U3 core: the COVARIANT Lemma 2.4 floor under LOCAL (per-chart) smallness, by unit-scale IMS (lane m2_unit_20261014)

Setting: unit torus `L`, unit background `W` (any `SU(2)` link configuration), a field `B` with the axial (staircase) zeros and,
on every coarse bond `c`, EITHER `Q1jet ℓ W B c = 0` OR `B` vanishes on every bond the flat row `q₁(c)` reads.  A finite family of charts `i : ι`: a site function `h i` and a gauge `u i`, with
* `Σ_i h_i(x)² ≤ 1` everywhere and `= 1` at the base point of every bond where `B ≠ 0`;
* `Σ_i (h_i(x+μ) − h_i(x))² ≤ Dp²`, and `Σ_i (h_i(x+jμ) − h_i(c₀))² ≤ Dq²` for `x` in the block of `c`, `j < ℓ`;
* `‖(W^{u_i})(z,μ) − 1‖_F ≤ κ` for `z ∈ Ball(x, 4ℓ)` whenever `h_i(x) ≠ 0`   (ONE gauge per chart; no global gauge).
Conclusion (`cov_floor_ims`):
  `(1/54) ℓ⁻⁵ ‖B‖² ≤ (1+ε) Σ_p ‖curl_W B p‖² + Eims ‖B‖²`,
  `Eims = ℓ (384 κ'² + 2 Dq²/ℓ³) + 4 (1 + 1/ε)(4 Dp² + 16 κ²)`,  `κ' = kapQ ℓ κ`.
Proof: per chart, flat Lemma 2.4 with Q-term (UA1) on `Y_i = h_i · Ad_{u_i} B`; the covariant curl and `Q1jet` are gauge covariant
(`curlValueCovariant_gauge`, GCa5 `Q1jet_gauge`), the flat ones differ from them by local drifts (curl: two base links; `Q₁`: UA3),
and `[·, h_i]` are the IMS commutators; `Σ_i h_i² = 1` removes every multiplicity factor from the drift terms.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2Unit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap curlValueCovariant)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply)
open AdalyFormal.Balaban.RegularUPerturbation (curlDrift bondEnergy)
open AdalyFormal.StatementLaneR8 (Ball mem_Ball_self)
open AdalyFormal.IngredientFamilyR2 (Q1jet)
open AdalyFormal.NonflatJet (rhoOf r0)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.DLayer (VisStep)

variable {L : PeriodicLatticeExtent}

theorem norm_gaugeActA (γ : GaugeFn L) (B : Bond L → SuTwo) (b : Bond L) : ‖gaugeActA γ B b‖ = ‖B b‖ := by
  rw [gaugeActA_apply]; exact AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap _ _

/-- local form of the curl drift bound (as MA5 `norm_curlDrift_sq_loc`). -/
theorem curlDrift_sq_loc (U : PeriodicLinkConfiguration SU2 L) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L)
    (α : ℝ) (hα0 : 0 ≤ α)
    (h1 : frobNorm (((U (p.1, p.2.1.1) : SU2) : M2) - 1) ≤ α)
    (h2 : frobNorm (((U (p.1, p.2.1.2) : SU2) : M2) - 1) ≤ α) :
    ‖curlDrift U A p‖ ^ 2 ≤
      8 * α ^ 2 * (‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
        + ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) := by
  have hb := AdalyFormal.Balaban.RegularUPerturbation.norm_curlDrift_le U A p
  set a1 := ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖
  set a2 := ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖
  have ha1 : 0 ≤ a1 := norm_nonneg _
  have ha2 : 0 ≤ a2 := norm_nonneg _
  have hle : ‖curlDrift U A p‖ ≤ 2 * α * a1 + 2 * α * a2 := by
    refine hb.trans ?_
    have e1 := mul_le_mul_of_nonneg_right h1 ha1
    have e2 := mul_le_mul_of_nonneg_right h2 ha2
    nlinarith
  have h0 := norm_nonneg (curlDrift U A p)
  have hsq := pow_le_pow_left₀ h0 hle 2
  nlinarith [sq_nonneg (a1 - a2), sq_nonneg α, mul_nonneg hα0 hα0]

/-- `flatCurl Z = curl_V Z − curlDrift V Z` pointwise. -/
theorem flat_eq_cov_sub_drift (V : PeriodicLinkConfiguration SU2 L) (Z : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    flatCurlValue Z p = curlValueCovariant V Z p - curlDrift V Z p := by
  have : curlDrift V Z p = curlValueCovariant V Z p
      - curlValueCovariant (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L) Z p := rfl
  rw [this, AdalyFormal.Balaban.CovU1Reduction.curlValueCovariant_trivialU_local]; abel

/-- the Eims constant. -/
noncomputable def Eims (ell : ℕ) (Dp Dq κ ε : ℝ) : ℝ :=
  (ell : ℝ) * (384 * kapQ ell κ ^ 2 + 2 * Dq ^ 2 / (ell : ℝ) ^ 3) + 4 * (1 + 1 / ε) * (4 * Dp ^ 2 + 16 * κ ^ 2)

/-! ## the curl part, one plaquette -/

theorem curl_part_pt {ι : Type*} [Fintype ι] (W : PeriodicLinkConfiguration SU2 L) (B : Bond L → SuTwo)
    (h : ι → PeriodicLatticeSite L → ℝ) (u : ι → GaugeFn L) (Dp κ ε : ℝ) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hP1' : ∀ x, ∑ i, h i x ^ 2 ≤ 1)
    (hDp : ∀ x (μ : Fin 3), ∑ i, (h i (periodicLatticeShift x μ) - h i x) ^ 2 ≤ Dp ^ 2)
    (hS : ∀ i x, h i x ≠ 0 → ∀ μ : Fin 3,
      frobNorm (((periodicGaugeTransform (u i) W (x, μ) : SU2) : M2) - 1) ≤ κ)
    (p : PeriodicLatticePlaquette L) :
    ∑ i, ‖flatCurlValue (hmul (h i) (gaugeActA (u i) B)) p‖ ^ 2
      ≤ (1 + ε) * ‖curlValueCovariant W B p‖ ^ 2
        + (1 + 1 / ε) * (4 * Dp ^ 2 + 16 * κ ^ 2) *
          (‖B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2 + ‖B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) := by
  set b2 : Bond L := (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) with hb2
  set b3 : Bond L := (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) with hb3
  set n2 := ‖B b2‖ ^ 2 with hn2
  set n3 := ‖B b3‖ ^ 2 with hn3
  have hn20 : 0 ≤ n2 := sq_nonneg _
  have hn30 : 0 ≤ n3 := sq_nonneg _
  set cw := ‖curlValueCovariant W B p‖ ^ 2 with hcw
  have hcw0 : 0 ≤ cw := sq_nonneg _
  -- per chart decomposition
  have hdec : ∀ i, ‖flatCurlValue (hmul (h i) (gaugeActA (u i) B)) p‖ ^ 2
      ≤ (1 + ε) * (h i p.1 ^ 2 * cw)
        + (1 + 1 / ε) * (4 * ((h i (periodicLatticeShift p.1 p.2.1.1) - h i p.1) ^ 2 * n2
            + (h i (periodicLatticeShift p.1 p.2.1.2) - h i p.1) ^ 2 * n3)
          + 16 * κ ^ 2 * (h i p.1 ^ 2 * (n2 + n3))) := by
    intro i
    set Z := gaugeActA (u i) B with hZ
    set V := periodicGaugeTransform (u i) W with hV
    set K := (h i (periodicLatticeShift p.1 p.2.1.1) - h i p.1) • Z b2
        - (h i (periodicLatticeShift p.1 p.2.1.2) - h i p.1) • Z b3 with hK
    have e1 := flatCurl_hmul (h i) Z p
    have e2 := flat_eq_cov_sub_drift V Z p
    have e3 : curlValueCovariant V Z p = RMap (u i p.1) (curlValueCovariant W B p) :=
      AdalyFormal.Balaban.AlphaAnalyticity.curlValueCovariant_gauge (u i) W B p
    set a := h i p.1 • RMap (u i p.1) (curlValueCovariant W B p) with ha
    set e := K - h i p.1 • curlDrift V Z p with he
    have hsplit : flatCurlValue (hmul (h i) Z) p = a + e := by
      rw [e1, e2, e3, ha, he, hK]; simp only [smul_sub]; abel
    rw [hsplit]
    have hy := sq_add_young a e hε
    have hna : ‖a‖ ^ 2 = h i p.1 ^ 2 * cw := by
      rw [ha, norm_smul, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap, mul_pow, Real.norm_eq_abs, sq_abs]
    have hne : ‖e‖ ^ 2 ≤ 2 * ‖K‖ ^ 2 + 2 * (h i p.1 ^ 2 * ‖curlDrift V Z p‖ ^ 2) := by
      have := sq_add_two K (-(h i p.1 • curlDrift V Z p))
      rw [← sub_eq_add_neg, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at this
      rw [he]; linarith
    have hnK : ‖K‖ ^ 2 ≤ 2 * (h i (periodicLatticeShift p.1 p.2.1.1) - h i p.1) ^ 2 * n2
        + 2 * (h i (periodicLatticeShift p.1 p.2.1.2) - h i p.1) ^ 2 * n3 := by
      have := sq_smul_sub_le (h i (periodicLatticeShift p.1 p.2.1.1) - h i p.1)
        (h i (periodicLatticeShift p.1 p.2.1.2) - h i p.1) (Z b2) (Z b3)
      rw [hZ, norm_gaugeActA, norm_gaugeActA] at this
      rw [hK, hZ]; linarith
    have hdr : h i p.1 ^ 2 * ‖curlDrift V Z p‖ ^ 2 ≤ h i p.1 ^ 2 * (8 * κ ^ 2 * (n2 + n3)) := by
      by_cases h0 : h i p.1 = 0
      · rw [h0]; simp
      · have hd := curlDrift_sq_loc V Z p κ hκ (hS i p.1 h0 _) (hS i p.1 h0 _)
        rw [hZ, norm_gaugeActA, norm_gaugeActA] at hd
        exact mul_le_mul_of_nonneg_left hd (sq_nonneg _)
    have hε1 : 0 ≤ 1 + 1 / ε := by positivity
    have hfin : ‖e‖ ^ 2 ≤ 4 * ((h i (periodicLatticeShift p.1 p.2.1.1) - h i p.1) ^ 2 * n2
            + (h i (periodicLatticeShift p.1 p.2.1.2) - h i p.1) ^ 2 * n3)
          + 16 * κ ^ 2 * (h i p.1 ^ 2 * (n2 + n3)) := by nlinarith
    calc ‖a + e‖ ^ 2 ≤ (1 + ε) * ‖a‖ ^ 2 + (1 + 1 / ε) * ‖e‖ ^ 2 := hy
      _ ≤ _ := by rw [hna]; nlinarith [mul_le_mul_of_nonneg_left hfin hε1]
  set dμ : ι → ℝ := fun i => h i (periodicLatticeShift p.1 p.2.1.1) - h i p.1 with hdμ
  set dν : ι → ℝ := fun i => h i (periodicLatticeShift p.1 p.2.1.2) - h i p.1 with hdν
  set x : ι → ℝ := fun i => h i p.1 ^ 2 with hx
  set c1 : ℝ := (1 + ε) * cw with hc1
  set c2 : ℝ := (1 + 1 / ε) * 4 * n2 with hc2
  set c3 : ℝ := (1 + 1 / ε) * 4 * n3 with hc3
  set c4 : ℝ := (1 + 1 / ε) * 16 * κ ^ 2 * (n2 + n3) with hc4
  have hdec' : ∀ i, ‖flatCurlValue (hmul (h i) (gaugeActA (u i) B)) p‖ ^ 2
      ≤ c1 * x i + c2 * dμ i ^ 2 + c3 * dν i ^ 2 + c4 * x i := by
    intro i
    have := hdec i
    simp only [hx, hdμ, hdν, hc1, hc2, hc3, hc4]
    linarith
  have hsum : ∑ i, (c1 * x i + c2 * dμ i ^ 2 + c3 * dν i ^ 2 + c4 * x i)
      = c1 * ∑ i, x i + c2 * ∑ i, dμ i ^ 2 + c3 * ∑ i, dν i ^ 2 + c4 * ∑ i, x i := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  refine (Finset.sum_le_sum (fun i _ => hdec' i)).trans ?_
  rw [hsum]
  have sx : ∑ i, x i ≤ 1 := hP1' p.1
  have sμ : ∑ i, dμ i ^ 2 ≤ Dp ^ 2 := hDp p.1 _
  have sν : ∑ i, dν i ^ 2 ≤ Dp ^ 2 := hDp p.1 _
  have hε1 : 0 ≤ 1 + 1 / ε := by positivity
  have hε0 : 0 ≤ 1 + ε := by linarith
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have hc30 : 0 ≤ c3 := by positivity
  have hc40 : 0 ≤ c4 := by positivity
  have t1 := mul_le_mul_of_nonneg_left sx hc10
  have t2 := mul_le_mul_of_nonneg_left sμ hc20
  have t3 := mul_le_mul_of_nonneg_left sν hc30
  have t4 := mul_le_mul_of_nonneg_left sx hc40
  have e : c1 * 1 + c2 * Dp ^ 2 + c3 * Dp ^ 2 + c4 * 1
      = (1 + ε) * cw + (1 + 1 / ε) * (4 * Dp ^ 2 + 16 * κ ^ 2) * (n2 + n3) := by
    simp only [hc1, hc2, hc3, hc4]; ring
  linarith

/-! ## the Q part, one coarse bond -/

open Classical in
theorem q_part_pt {ι : Type*} [Fintype ι] {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (W : PeriodicLinkConfiguration SU2 L) (B : Bond L → SuTwo)
    (h : ι → PeriodicLatticeSite L → ℝ) (u : ι → GaugeFn L) (Dq κ : ℝ) (hκ : 0 ≤ κ)
    (hρ : rhoOf ell κ < Real.pi / 2) (hrg : Real.pi / 2 * ((loopFactorBound ell : ℝ) * κ) < r0)
    (hP1' : ∀ x, ∑ i, h i x ^ 2 ≤ 1)
    (hDq : ∀ c : CoarseBond L ell, ∀ x ∈ blockOf c.1.1 ell, ∀ j ∈ Finset.range ell,
      ∑ i, (h i (pathSite x c.2 j) - h i c.1.1) ^ 2 ≤ Dq ^ 2)
    (hS : ∀ i x, h i x ≠ 0 → ∀ z ∈ Ball x (4 * (1 * ell)), ∀ μ : Fin 3,
      frobNorm (((periodicGaugeTransform (u i) W (z, μ) : SU2) : M2) - 1) ≤ κ)
    (c : CoarseBond L ell)
    (hQ0 : Q1jet ell W B c = 0 ∨ ∀ x ∈ blockOf c.1.1 ell, ∀ j ∈ Finset.range ell, B (pathSite x c.2 j, c.2) = 0) :
    ∑ i, ‖lineCoarseRestrictSuTwo ell (hmul (h i) (gaugeActA (u i) B)) c‖ ^ 2
      ≤ 2 * kapQ ell κ ^ 2 * ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (c.1.1, c.2) e), ‖B e‖ ^ 2
        + 2 * (1 / (ell : ℝ) ^ 4) * Dq ^ 2 *
          ∑ x ∈ blockOf c.1.1 ell, ∑ j ∈ Finset.range ell, ‖B (pathSite x c.2 j, c.2)‖ ^ 2 := by
  set SV := ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (c.1.1, c.2) e), ‖B e‖ ^ 2 with hSV
  have hSV0 : 0 ≤ SV := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hRHS0 : 0 ≤ 2 * kapQ ell κ ^ 2 * SV + 2 * (1 / (ell : ℝ) ^ 4) * Dq ^ 2 *
      ∑ x ∈ blockOf c.1.1 ell, ∑ j ∈ Finset.range ell, ‖B (pathSite x c.2 j, c.2)‖ ^ 2 := by
    have : 0 ≤ ∑ x ∈ blockOf c.1.1 ell, ∑ j ∈ Finset.range ell, ‖B (pathSite x c.2 j, c.2)‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    positivity
  rcases hQ0 with hQ0 | hz
  swap
  · -- the row reads only zeros of `B`
    have hzero : ∀ i, lineCoarseRestrictSuTwo ell (hmul (h i) (gaugeActA (u i) B)) c = 0 := by
      intro i
      simp only [lineCoarseRestrictSuTwo]
      rw [Finset.sum_eq_zero (fun x hx => Finset.sum_eq_zero (fun j hj => by
        rw [hmul_apply, gaugeActA_apply, hz x hx j hj, map_zero, smul_zero])), smul_zero]
    simp only [hzero, norm_zero]
    simpa using hRHS0
  set T := blockOf c.1.1 ell with hT
  have hTc : (T.card : ℝ) = (ell : ℝ) ^ 3 := by
    rw [hT, card_blockOf_of_coarse hdvd c.1.2]; push_cast; ring
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hdec : ∀ i, ‖lineCoarseRestrictSuTwo ell (hmul (h i) (gaugeActA (u i) B)) c‖ ^ 2
      ≤ 2 * (h i c.1.1 ^ 2 * (kapQ ell κ ^ 2 * SV))
        + 2 * ((1 / (ell : ℝ) ^ 4) * ∑ x ∈ T, ∑ j ∈ Finset.range ell,
            (h i (pathSite x c.2 j) - h i c.1.1) ^ 2 * ‖B (pathSite x c.2 j, c.2)‖ ^ 2) := by
    intro i
    set Z := gaugeActA (u i) B with hZ
    set V := periodicGaugeTransform (u i) W with hV
    have e1 := q1_hmul ell (h i) Z c
    have e2 : lineCoarseRestrictSuTwo ell Z c = AdalyFormal.IngredientFamily.q1SU2 ell Z c := by
      rw [AdalyFormal.IngredientFamily.q1SU2_apply]; rfl
    have e3 : Q1jet ell V Z c = 0 := by
      have := congrFun (AdalyFormal.GaugeCov.Q1jet_gauge ell (u i) W B) c
      rw [this]
      show RMap (u i c.1.1) (Q1jet ell W B c) = 0
      rw [hQ0, map_zero]
    set dQ := Q1jet ell V Z c - AdalyFormal.IngredientFamily.q1SU2 ell Z c with hdQ
    set KQ := (1 / (ell : ℝ) ^ 4) • ∑ x ∈ T, ∑ j ∈ Finset.range ell,
        (h i (pathSite x c.2 j) - h i c.1.1) • Z (pathSite x c.2 j, c.2) with hKQ
    have hsplit : lineCoarseRestrictSuTwo ell (hmul (h i) Z) c = -(h i c.1.1 • dQ) + KQ := by
      rw [e1, e2, hdQ, e3, hKQ, hT]; simp only [zero_sub, smul_neg, neg_neg]
    rw [hsplit]
    have h2 := sq_add_two (-(h i c.1.1 • dQ)) KQ
    rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h2
    have hd : h i c.1.1 ^ 2 * ‖dQ‖ ^ 2 ≤ h i c.1.1 ^ 2 * (kapQ ell κ ^ 2 * SV) := by
      by_cases h0 : h i c.1.1 = 0
      · rw [h0]; simp
      · have hq := q1_drift_row hell hdvd V κ hκ hρ hrg c (hS i c.1.1 h0) Z
        have hsv : ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (c.1.1, c.2) e), ‖Z e‖ ^ 2 = SV := by
          rw [hSV]; refine Finset.sum_congr rfl (fun e _ => ?_); rw [hZ, norm_gaugeActA]
        rw [hsv] at hq
        exact mul_le_mul_of_nonneg_left hq (sq_nonneg _)
    -- the commutator
    have hk : ‖KQ‖ ^ 2 ≤ (1 / (ell : ℝ) ^ 4) * ∑ x ∈ T, ∑ j ∈ Finset.range ell,
        (h i (pathSite x c.2 j) - h i c.1.1) ^ 2 * ‖B (pathSite x c.2 j, c.2)‖ ^ 2 := by
      set v : PeriodicLatticeSite L → ℕ → SuTwo := fun x j =>
        (h i (pathSite x c.2 j) - h i c.1.1) • Z (pathSite x c.2 j, c.2) with hv
      have hnv : ∀ x j, ‖v x j‖ ^ 2 = (h i (pathSite x c.2 j) - h i c.1.1) ^ 2 * ‖B (pathSite x c.2 j, c.2)‖ ^ 2 := by
        intro x j
        rw [hv]; dsimp only
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hZ, norm_gaugeActA]
      have c1 := sq_sum_le_card T (fun x => ∑ j ∈ Finset.range ell, v x j)
      have c2 : ∀ x ∈ T, ‖∑ j ∈ Finset.range ell, v x j‖ ^ 2 ≤ (ell : ℝ) * ∑ j ∈ Finset.range ell, ‖v x j‖ ^ 2 := by
        intro x _
        have := sq_sum_le_card (Finset.range ell) (v x)
        rwa [Finset.card_range] at this
      have c3 : ∑ x ∈ T, ‖∑ j ∈ Finset.range ell, v x j‖ ^ 2
          ≤ (ell : ℝ) * ∑ x ∈ T, ∑ j ∈ Finset.range ell, ‖v x j‖ ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum c2
      have hKn : ‖KQ‖ ^ 2 = (1 / (ell : ℝ) ^ 4) ^ 2 * ‖∑ x ∈ T, ∑ j ∈ Finset.range ell, v x j‖ ^ 2 := by
        rw [hKQ, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have hsum : ∑ x ∈ T, ∑ j ∈ Finset.range ell, ‖v x j‖ ^ 2 = ∑ x ∈ T, ∑ j ∈ Finset.range ell,
          (h i (pathSite x c.2 j) - h i c.1.1) ^ 2 * ‖B (pathSite x c.2 j, c.2)‖ ^ 2 :=
        Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun j _ => hnv x j))
      rw [hsum] at c3
      set R := ∑ x ∈ T, ∑ j ∈ Finset.range ell,
          (h i (pathSite x c.2 j) - h i c.1.1) ^ 2 * ‖B (pathSite x c.2 j, c.2)‖ ^ 2 with hR
      have hR0 : 0 ≤ R := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
      have hfin : ‖∑ x ∈ T, ∑ j ∈ Finset.range ell, v x j‖ ^ 2 ≤ (ell : ℝ) ^ 4 * R := by
        rw [hTc] at c1
        have := mul_le_mul_of_nonneg_left c3 (by positivity : (0 : ℝ) ≤ (ell : ℝ) ^ 3)
        calc _ ≤ (ell : ℝ) ^ 3 * ∑ x ∈ T, ‖∑ j ∈ Finset.range ell, v x j‖ ^ 2 := c1
          _ ≤ (ell : ℝ) ^ 3 * ((ell : ℝ) * R) := this
          _ = (ell : ℝ) ^ 4 * R := by ring
      rw [hKn]
      have hp4 : (0 : ℝ) < (ell : ℝ) ^ 4 := by positivity
      have e : (1 / (ell : ℝ) ^ 4) ^ 2 * ((ell : ℝ) ^ 4 * R) = (1 / (ell : ℝ) ^ 4) * R := by
        field_simp
      calc (1 / (ell : ℝ) ^ 4) ^ 2 * ‖∑ x ∈ T, ∑ j ∈ Finset.range ell, v x j‖ ^ 2
          ≤ (1 / (ell : ℝ) ^ 4) ^ 2 * ((ell : ℝ) ^ 4 * R) := mul_le_mul_of_nonneg_left hfin (by positivity)
        _ = (1 / (ell : ℝ) ^ 4) * R := e
    linarith
  refine (Finset.sum_le_sum (fun i _ => hdec i)).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have s1 : ∑ i, h i c.1.1 ^ 2 * (kapQ ell κ ^ 2 * SV) ≤ kapQ ell κ ^ 2 * SV := by
    rw [← Finset.sum_mul]
    have := hP1' c.1.1
    have h0 : 0 ≤ kapQ ell κ ^ 2 * SV := by positivity
    nlinarith
  have s2 : ∑ i, (1 / (ell : ℝ) ^ 4) * ∑ x ∈ T, ∑ j ∈ Finset.range ell,
        (h i (pathSite x c.2 j) - h i c.1.1) ^ 2 * ‖B (pathSite x c.2 j, c.2)‖ ^ 2
      ≤ (1 / (ell : ℝ) ^ 4) * Dq ^ 2 * ∑ x ∈ T, ∑ j ∈ Finset.range ell, ‖B (pathSite x c.2 j, c.2)‖ ^ 2 := by
    rw [← Finset.mul_sum, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum (fun x hx => ?_)
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hDq c x hx j hj) (sq_nonneg _)
  nlinarith

/-! ## the norm identity -/

theorem norm_part {ι : Type*} [Fintype ι] (B : Bond L → SuTwo) (h : ι → PeriodicLatticeSite L → ℝ) (u : ι → GaugeFn L)
    (hP1 : ∀ b : Bond L, B b ≠ 0 → ∑ i, h i b.1 ^ 2 = 1) :
    ∑ i, ∑ b : Bond L, ‖hmul (h i) (gaugeActA (u i) B) b‖ ^ 2 = ∑ b : Bond L, ‖B b‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have e : ∀ i, ‖hmul (h i) (gaugeActA (u i) B) b‖ ^ 2 = h i b.1 ^ 2 * ‖B b‖ ^ 2 := by
    intro i
    rw [hmul_apply, norm_smul, norm_gaugeActA, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.sum_mul]
  by_cases hb : B b = 0
  · rw [hb]; simp
  · rw [hP1 b hb, one_mul]

/-! ## U3 core -/

open Classical in
/-- **U3 core (`cov_floor_ims`)**: the covariant Lemma 2.4 floor under per-chart smallness. -/
theorem cov_floor_ims {ι : Type*} [Fintype ι] {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ μ : Fin 3, ell < L μ + 1) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (W : PeriodicLinkConfiguration SU2 L) (B : Bond L → SuTwo)
    (hax : ∀ y ∈ CoarseLattice L ell, ∀ x ∈ blockOf y ell, ∀ b ∈ staircasePath y x, B b = 0)
    (hQ0 : ∀ c : CoarseBond L ell, Q1jet ell W B c = 0 ∨
      ∀ x ∈ blockOf c.1.1 ell, ∀ j ∈ Finset.range ell, B (pathSite x c.2 j, c.2) = 0)
    (h : ι → PeriodicLatticeSite L → ℝ) (u : ι → GaugeFn L) (Dp Dq κ ε : ℝ) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hρ : rhoOf ell κ < Real.pi / 2) (hrg : Real.pi / 2 * ((loopFactorBound ell : ℝ) * κ) < r0)
    (hP1 : ∀ b : Bond L, B b ≠ 0 → ∑ i, h i b.1 ^ 2 = 1)
    (hP1' : ∀ x, ∑ i, h i x ^ 2 ≤ 1)
    (hDp : ∀ x (μ : Fin 3), ∑ i, (h i (periodicLatticeShift x μ) - h i x) ^ 2 ≤ Dp ^ 2)
    (hDq : ∀ c : CoarseBond L ell, ∀ x ∈ blockOf c.1.1 ell, ∀ j ∈ Finset.range ell,
      ∑ i, (h i (pathSite x c.2 j) - h i c.1.1) ^ 2 ≤ Dq ^ 2)
    (hS : ∀ i x, h i x ≠ 0 → ∀ z ∈ Ball x (4 * (1 * ell)), ∀ μ : Fin 3,
      frobNorm (((periodicGaugeTransform (u i) W (z, μ) : SU2) : M2) - 1) ≤ κ) :
    (1 / 54 : ℝ) * (1 / (ell : ℝ) ^ 5) * ∑ b : Bond L, ‖B b‖ ^ 2
      ≤ (1 + ε) * ∑ p : PeriodicLatticePlaquette L, ‖curlValueCovariant W B p‖ ^ 2
        + Eims ell Dp Dq κ ε * ∑ b : Bond L, ‖B b‖ ^ 2 := by
  have hell : 0 < ell := by omega
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set N := ∑ b : Bond L, ‖B b‖ ^ 2 with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- per chart: flat Lemma 2.4 with Q-term
  have hper : ∀ i, (1 / 54 : ℝ) * (1 / (ell : ℝ) ^ 5) * ∑ b : Bond L, ‖hmul (h i) (gaugeActA (u i) B) b‖ ^ 2
      ≤ (ell : ℝ) * ∑ c : CoarseBond L ell, ‖lineCoarseRestrictSuTwo ell (hmul (h i) (gaugeActA (u i) B)) c‖ ^ 2
        + ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue (hmul (h i) (gaugeActA (u i) B)) p‖ ^ 2 := by
    intro i
    refine lemma24Q_su2 hell2 hstrict hdvd _ ?_
    intro y hy x hx b hb
    rw [hmul_apply, gaugeActA_apply, hax y hy x hx b hb, map_zero, smul_zero]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hper i)
  rw [← Finset.mul_sum, norm_part B h u hP1, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  -- the curl part
  have hS0 : ∀ i x, h i x ≠ 0 → ∀ μ : Fin 3,
      frobNorm (((periodicGaugeTransform (u i) W (x, μ) : SU2) : M2) - 1) ≤ κ :=
    fun i x hx μ => hS i x hx x (mem_Ball_self x _) μ
  have hC : ∑ i, ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue (hmul (h i) (gaugeActA (u i) B)) p‖ ^ 2
      ≤ (1 + ε) * ∑ p : PeriodicLatticePlaquette L, ‖curlValueCovariant W B p‖ ^ 2
        + 4 * (1 + 1 / ε) * (4 * Dp ^ 2 + 16 * κ ^ 2) * N := by
    rw [Finset.sum_comm]
    refine (Finset.sum_le_sum (fun p _ => curl_part_pt W B h u Dp κ ε hκ hε hP1' hDp hS0 p)).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
    have n1 := AdalyFormal.Balaban.RegularUPerturbation.sum_nbr1_sq_le B
    have n2 := AdalyFormal.Balaban.RegularUPerturbation.sum_nbr2_sq_le B
    have hbE : bondEnergy B = N := rfl
    rw [hbE] at n1 n2
    have hk : 0 ≤ (1 + 1 / ε) * (4 * Dp ^ 2 + 16 * κ ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_left (add_le_add n1 n2) hk
    nlinarith
  -- the Q part
  have hQ : ∑ i, ∑ c : CoarseBond L ell, ‖lineCoarseRestrictSuTwo ell (hmul (h i) (gaugeActA (u i) B)) c‖ ^ 2
      ≤ (384 * kapQ ell κ ^ 2 + 2 * Dq ^ 2 / (ell : ℝ) ^ 3) * N := by
    rw [Finset.sum_comm]
    refine (Finset.sum_le_sum (fun c _ => q_part_pt hell hdvd W B h u Dq κ hκ hρ hrg hP1' hDq hS c (hQ0 c))).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have v1 := sum_vis_sq_le hell hdvd B
    have v2 := sum_path_bonds hell hdvd (fun b => ‖B b‖ ^ 2)
    rw [v2]
    have hk : 0 ≤ 2 * kapQ ell κ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left v1 hk
    have e : 2 * (1 / (ell : ℝ) ^ 4) * Dq ^ 2 * ((ell : ℝ) * N) = 2 * Dq ^ 2 / (ell : ℝ) ^ 3 * N := by
      field_simp
    rw [e]
    nlinarith
  have hQl := mul_le_mul_of_nonneg_left hQ hellR.le
  unfold Eims
  nlinarith

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.curlDrift_sq_loc
#print axioms AdalyFormal.M2Unit.curl_part_pt
#print axioms AdalyFormal.M2Unit.q_part_pt
#print axioms AdalyFormal.M2Unit.norm_part
#print axioms AdalyFormal.M2Unit.cov_floor_ims
