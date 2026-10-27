import UD7
import AU_UD4
import AU_UC6
import AU_CUT

/-! AU copy of UD7 (c-free): `unit_floor_classU` takes a `BallChartsAt` instance instead of the class and top-level cube. -/
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
theorem unit_floor_classU {ell M R k Mc : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell)
    (hT : TorusOK ell M Lu) (hMc : M = ell * Mc) (hMc0 : 0 < Mc)
    (hMbig : 6 * Mc + 4 * ell + 165 ≤ 4 * M) (hRM : 6 * Mc + 4 * ell + 25 ≤ R * M) (hroom : 17 * ell ≤ R * M) (hR6 : 6 * ell ≤ R) (hk1 : 1 ≤ k)
    (hthick : ∀ σ : Fin 3, 12 * (M * ell ^ k) ≤ scaleUp ell k Lu σ + 1)
    (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S)
    (Lam : Set (PeriodicLatticeSite Lu)) (hL : LambdaOK2 ell M R k S Lam)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (αb : ℝ) (hα : 0 < αb) {C : ℝ} (hC : 1 ≤ C)
    (hBall : AdalyFormal.OneGap.BallChartsAt ell M k S U C αb ((ell : ℝ) ^ k)⁻¹)
    (hb : Function.Bijective (IngredientFamilyR2.H0 Lam (gparams ell k Lu (by omega) S U a Lam).Q1))
    (Bt : Bond Lu → SuTwo) (hBt : OnLambdaTildeIn Lam ell Bt) (hBT : OnLambdaT Lam Bt)
    (α₁ : ℝ) (hα1 : (ell : ℝ) ^ 3 * (2 * (C * αb)) ≤ α₁)
    (ha1 : (12 : ℝ) * M * α₁ ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M α₁ ≤ 1)
    (hsmq : 4000000 * (ell : ℝ) ^ 2 * qM1 (12 * M * α₁) ≤ 1)
    (hsmA : (1 + 3 * Real.pi) * rho1 12 M α₁ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
    (hrr : Real.pi / 2 * ((loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M α₁)) < r0)
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
  have hell : 0 < ell := by omega
  have hn : 0 < ell ^ k := pow_pos hell k
  have hPO : PartOK Lu Mc := by
    refine ⟨hMc0, fun μ => ?_, fun μ => ?_⟩
    · exact dvd_trans (Dvd.intro_left ell hMc.symm) (hT.2.2 μ)
    · obtain ⟨c, hc⟩ := hT.2.2 μ
      have hc0 : c ≠ 0 := by rintro rfl; simp at hc
      have : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc0
      rw [hc, hMc]
      calc 2 * Mc ≤ ell * Mc := Nat.mul_le_mul_right _ hell2
        _ ≤ ell * Mc * c := Nat.le_mul_of_pos_right _ this
  have hLu : ∀ σ : Fin 3, 1 ≤ scaleUp ell k Lu σ := by
    intro σ
    have h1 := scaleUp_succ ell k Lu hell σ
    have h2 := hT.2.1 σ
    have : 3 ≤ Lu σ + 1 := by omega
    have h3 : (Lu σ + 1) * 1 ≤ (Lu σ + 1) * ell ^ k := Nat.mul_le_mul_left _ hn
    omega
  have hα1pos : 0 < α₁ := lt_of_lt_of_le (by have := lt_of_lt_of_le one_pos hC; positivity) hα1
  have hL1 := hL.1
  -- plaquette charts
  let Qs : Finset (PeriodicLatticePlaquette Lu) :=
    Finset.univ.filter (fun q => ∃ y0 ∈ Lam, pdist y0 q.1 ≤ 2 * ell + 1)
  have hQsmem : ∀ q ∈ Qs, ∃ y0 ∈ Lam, pdist y0 q.1 ≤ 2 * ell + 1 := by
    intro q hq; simpa [Qs] using hq
  have hch : ∀ q : PeriodicLatticePlaquette Lu, ∃ (γ : GaugeFn (scaleUp ell k Lu)) (V : LinkCfg (scaleUp ell k Lu)),
      q ∈ Qs → (AdalyFormal.AllU.M1RegularU ell M 12 k S α₁ ((ell : ℝ) ^ k)⁻¹ V ∧
        AgreeAt (Ball (embY ell k Lu hell q.1) (32 * ell ^ k)) (periodicGaugeTransform γ U) V) := by
    intro q
    by_cases hq : q ∈ Qs
    · obtain ⟨y0, hy0, hd⟩ := hQsmem q hq
      have hrp : 32 * ell ^ k + 64 * ell ^ k + 5 ≤ 6 * (M * ell ^ k) - 1 := by
        have h1 : ell ^ k * 165 ≤ ell ^ k * (4 * M) := Nat.mul_le_mul_left _ (by omega)
        have e2 : ell ^ k * (4 * M) = 4 * (M * ell ^ k) := by ring
        omega
      obtain ⟨g, V, h1, h2⟩ := chart_of_ballU hell (by omega : 0 < M) hk1 hS hL1 hthick hR6 hy0 q.1 (by omega) (32 * ell ^ k)
        hrp hC hα hBall
      exact ⟨g, V, fun _ => ⟨AdalyFormal.AllU.M1RegularU.mono (by positivity) hα1 h1, h2⟩⟩
    · exact ⟨fun _ => 1, U, fun h => absurd h hq⟩
  choose γq Vq hq using hch
  -- cell charts
  let I : Set ((μ : Fin 3) → Fin (Kc Lu Mc μ)) :=
    {m | ∃ x0, hpart Mc m x0 ≠ 0 ∧ ∃ y0 ∈ Lam, pdist y0 x0 ≤ 1}
  have hrho := AdalyFormal.StatementLaneR8.rhoT_le ell hell2 k
  have hchc : ∀ m : (μ : Fin 3) → Fin (Kc Lu Mc μ), ∃ (γ : GaugeFn (scaleUp ell k Lu)) (V : LinkCfg (scaleUp ell k Lu)),
      m ∈ I → (AdalyFormal.AllU.M1RegularU ell M 12 k S α₁ ((ell : ℝ) ^ k)⁻¹ V ∧
        ∀ x, hpart Mc m x ≠ 0 → ∀ z ∈ Ball x (4 * (1 * ell)),
          AgreeAt (Ball (embY ell k Lu hell z) (rhoT ell k)) (periodicGaugeTransform γ U) V ∧
          ∃ y0 ∈ Lam, pdist y0 z + 17 ≤ R * M) := by
    intro m
    by_cases hm : m ∈ I
    · obtain ⟨x0, hx0, y0, hy0, hd⟩ := hm
      have hrad : (ell ^ k * (6 * Mc + 4 * ell) + 8 * ell ^ k) + 64 * ell ^ k + 5 ≤ 6 * (M * ell ^ k) - 1 := by
        have h1 : ell ^ k * (6 * Mc + 4 * ell + 165) ≤ ell ^ k * (4 * M) := Nat.mul_le_mul_left _ hMbig
        have e1 : ell ^ k * (6 * Mc + 4 * ell + 165) = ell ^ k * (6 * Mc + 4 * ell) + 165 * ell ^ k := by ring
        have e2 : ell ^ k * (4 * M) = 4 * (M * ell ^ k) := by ring
        omega
      obtain ⟨g, V, h1, h2⟩ := chart_of_ballU hell (by omega : 0 < M) hk1 hS hL1 hthick hR6 hy0 x0 (by omega)
        (ell ^ k * (6 * Mc + 4 * ell) + 8 * ell ^ k) hrad hC hα hBall
      refine ⟨g, V, fun _ => ⟨AdalyFormal.AllU.M1RegularU.mono (by positivity) hα1 h1, fun x hx z hz => ⟨?_, ?_⟩⟩⟩
      · have hxx0 := hpart_pdist hPO m hx0 hx
        have hz' : pdist x z ≤ 4 * (1 * ell) := hz
        have h3 : pdist x0 z ≤ 6 * Mc + 4 * ell := by
          have := pdist_triangle x0 x z; omega
        refine AgreeAt.mono h2 (fun w hw => ?_)
        have hw' : pdist (embY ell k Lu hell z) w ≤ rhoT ell k := hw
        have e := pdist_embY (k := k) hell x0 z
        have h4 := pdist_triangle (embY ell k Lu hell x0) (embY ell k Lu hell z) w
        show pdist _ _ ≤ _
        have h5 : ell ^ k * pdist x0 z ≤ ell ^ k * (6 * Mc + 4 * ell) := Nat.mul_le_mul_left _ h3
        omega
      · refine ⟨y0, hy0, ?_⟩
        have hxx0 := hpart_pdist hPO m hx0 hx
        have hz' : pdist x z ≤ 4 * (1 * ell) := hz
        have h3 := pdist_triangle y0 x0 x
        have h4 := pdist_triangle y0 x z
        have h5 : pdist y0 z ≤ pdist y0 x + pdist x z := h4
        omega
    · exact ⟨fun _ => 1, U, fun h => absurd h hm⟩
  choose γc Vc hc using hchc
  have hI : ∀ m (b : Bond Lu), (b.1 ∈ Lam ∨ periodicLatticeShift b.1 b.2 ∈ Lam) → hpart Mc m b.1 ≠ 0 → m ∈ I := by
    intro m b hb' hne
    refine ⟨b.1, hne, ?_⟩
    rcases hb' with h | h
    · exact ⟨b.1, h, by rw [AdalyFormal.StatementLane.pdist_self]; exact Nat.zero_le _⟩
    · exact ⟨_, h, by rw [pdist_comm]; exact pdist_shift_le b.1 b.2⟩
  have hnear : ∀ q ∈ Qs, ∃ y0 ∈ Lam, pdist y0 q.1 + 17 ≤ R * M := by
    intro q hq; obtain ⟨y0, hy0, hd⟩ := hQsmem q hq; exact ⟨y0, hy0, by omega⟩
  have hgood : ∀ q ∈ Qs, ∀ c, AdalyFormal.FlatEllGeneral.InBox q.1 c → embY ell k Lu hell c ∈ S.Om k := by
    intro q hq c hc'
    obtain ⟨y0, hy0, hd⟩ := hQsmem q hq
    have := inBox_pdist hc'
    exact embY_mem_Om hell hL1 hy0 (le_trans (pdist_triangle y0 q.1 c) (by omega))
  have hQs : ∀ q, (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt (qb1 q) ≠ 0
        ∨ GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt (qb2 q) ≠ 0
        ∨ GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt (qb3 q) ≠ 0
        ∨ GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt (qb4 q) ≠ 0) → q ∈ Qs := by
    intro q hq4
    have hpd : ∀ (b : Bond Lu), pdist b.1 q.1 ≤ 1 →
        GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt b ≠ 0 → q ∈ Qs := by
      intro b hbq hbn
      obtain ⟨y0, hy0, hd⟩ := qs_near hell S U a Lam Bt hBT q b hbn hbq
      simpa [Qs] using ⟨y0, hy0, hd⟩
    rcases hq4 with h | h | h | h
    · exact hpd (qb1 q) (by show pdist q.1 q.1 ≤ 1; rw [AdalyFormal.StatementLane.pdist_self]; exact Nat.zero_le _) h
    · exact hpd (qb2 q) (by show pdist (periodicLatticeShift q.1 _) q.1 ≤ 1; rw [pdist_comm]; exact pdist_shift_le _ _) h
    · exact hpd (qb3 q) (by show pdist (periodicLatticeShift q.1 _) q.1 ≤ 1; rw [pdist_comm]; exact pdist_shift_le _ _) h
    · exact hpd (qb4 q) (by show pdist q.1 q.1 ≤ 1; rw [AdalyFormal.StatementLane.pdist_self]; exact Nat.zero_le _) h
  exact unit_floor_kfreeU hell2 hT.2.1 hT.1 hPO S hS hroom Lam hL U a hb Bt hBt hBT α₁ hα1pos.le ha1 hsm4 hsmq hsmA hrr hρ hrg
    ε ε' hε hε' hcoef I hI γc Vc (fun m hm => (hc m hm).1) (fun m hm x hx z hz => (hc m hm).2 x hx z hz) y hQ Qs hQs hgood hnear
    γq Vq (fun q hq' => (hq q hq').1) (fun q hq' => (hq q hq').2)

end AdalyFormal.M2UnitCharts

