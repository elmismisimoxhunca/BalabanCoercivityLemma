import AU_CUT
import UB9
import AU_DK2
import AU_GW2
import AU_TL6b

open AdalyFormal.AllU (M1BoundsU M1RegularU)

/-! AU copy of UB9: M1Regular -> M1RegularU, affected declarations only (lane allc_20261016, uniform-in-c route). -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.M2Unit

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice blockOf)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt rhoT pdist_triangle pdist_coarseShift_le Ball_sub mem_Ball_self)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.FlatEllGeneral (InBox)
open AdalyFormal.CurvBlock (dv)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.TowerLoc (rho1 epsM WM)
open AdalyFormal.M1DK (kapM1 qM1)

/-- **`ChartOK` from one local M1 chart.** -/
theorem chartOK_of_M1U {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell) (hu : ∀ μ, 1 ≤ Lu μ)
    (hT3 : ∀ μ, 3 ≤ Lu μ + 1) (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S) (hroom : 17 * ell ≤ R * M)
    (Lam : Set (PeriodicLatticeSite Lu)) (hL : LambdaOK2 ell M R k S Lam)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (α₀ : ℝ) (hα0 : 0 ≤ α₀) (ha1 : (12 : ℝ) * M * α₀ ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M α₀ ≤ 1)
    (hsmq : 4000000 * (ell : ℝ) ^ 2 * qM1 (12 * M * α₀) ≤ 1)
    (q : PeriodicLatticePlaquette Lu) (hgood : ∀ c, InBox q.1 c → embY ell k Lu (by omega) c ∈ S.Om k)
    {y0 : PeriodicLatticeSite Lu} (hy0 : y0 ∈ Lam) (hnear : pdist y0 q.1 + 17 ≤ R * M)
    (γ : GaugeFn (scaleUp ell k Lu)) (V : LinkCfg (scaleUp ell k Lu))
    (hV : AdalyFormal.AllU.M1RegularU ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ V)
    (hag : AgreeAt (Ball (embY ell k Lu (by omega) q.1) (32 * ell ^ k)) (periodicGaugeTransform γ U) V) :
    ∃ (γ' : GaugeFn (scaleUp ell k Lu)) (Wr : ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu))),
      ChartOK (by omega) S U (gparams ell k Lu (by omega) S U a Lam).unitBgU q γ' (rho1 12 M α₀) (kapM1 (12 * M * α₀))
        (fun l => epsM ell 12 M α₀ k l) Wr := by
  have hell : 0 < ell := by omega
  obtain ⟨g, A, hgA, hB⟩ := hV
  set n := ell ^ k with hn
  have hnpos : 0 < n := pow_pos hell k
  have hrho : rhoT ell k + 8 ≤ 8 * n := AdalyFormal.StatementLaneR8.rhoT_le ell hell2 k
  set γ' : GaugeFn (scaleUp ell k Lu) := fun x => g x * γ x with hγ'
  have hcomp : periodicGaugeTransform γ' U = periodicGaugeTransform g (periodicGaugeTransform γ U) :=
    (AdalyFormal.Lattice.Witness.periodicGaugeTransform_comp g γ U).symm
  have hag' : AgreeAt (Ball (embY ell k Lu hell q.1) (32 * n)) (periodicGaugeTransform γ' U) (periodicGaugeTransform g V) := by
    rw [hcomp]; exact agree_gauge hag g
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hell1 : 1 ≤ ell := by omega
  have ha0 : (0 : ℝ) ≤ (12 : ℕ) * M * α₀ := by positivity
  set Wr : ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)) :=
    fun l => {z | z ∈ WM ell k S k l ∧ pdist (embY ell k Lu hell q.1) z ≤ n + rhoT ell k} with hWr
  have hrows : ∀ b ∈ ({qb1 q, qb2 q, qb3 q, qb4 q} : Finset (Bond Lu)),
      unitBondEmb ell k Lu hell b ∈ bondsLam (geomOf ell k S) k :=
    fun b hb => AdalyFormal.FlatEllGeneral.emb_bondsLam hell hS b (hgood b.1 (qb_inBox q b hb))
  refine ⟨γ', Wr, ⟨?_, ?_, ?_, hrows, ?_, ?_⟩⟩
  · -- window links
    intro x hx i hi j hj
    have hp := AdalyFormal.FlatEllGeneral.window_plaqIn_k hell hu hS q.1 hgood q.2 x hx i j
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
    have hd := pdist_win hnpos (embY ell k Lu hell q.1) q.2 hx (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
    have hball : (winPl q.2 x i j).1 ∈ Ball (embY ell k Lu hell q.1) (32 * n) := by
      show pdist _ _ ≤ 32 * n; omega
    have hlnk := AdalyFormal.M1GaugeW4.hlink_M1U S V g A hgA hB hη hell1 ha0 k le_rfl
    have hmem : ∀ μ' : Fin 3, ((winPl q.2 x i j).1, μ') ∈ periodicPlaquetteBoundaryEdges (winPl q.2 x i j) →
        frobNorm (((periodicGaugeTransform γ' U ((winPl q.2 x i j).1, μ') : SU2) : M2) - 1)
          ≤ rho1 12 M α₀ / (ell : ℝ) ^ k := by
      intro μ' he
      have h2 := hp _ he
      rw [hag' _ hball μ']
      exact hlnk _ h2.1 h2.2
    refine ⟨hmem _ ?_, hmem _ ?_⟩ <;> simp [winPl, periodicPlaquetteBoundaryEdges]
  · -- unit base links (first direction)
    obtain ⟨hlk, hpl⟩ := AdalyFormal.M1DK.chart_boundsU ell M k hell S α₀ V g A _ rfl hgA hB hα0 ha1
    have hsub : AgreeAt (Ball (embY ell k Lu hell q.1) (rhoT ell k)) (periodicGaugeTransform γ' U) (periodicGaugeTransform g V) :=
      hag'.mono (Ball_sub (by rw [AdalyFormal.StatementLaneR8.pdist_self]) (by omega))
    have := unitBgU_chart_small hell hell2 S hS Lam hL hT3 U a γ' (periodicGaugeTransform g V) (12 * M * α₀)
      (qM1 (12 * M * α₀)) (AdalyFormal.M1DK.qM1_nonneg (by positivity)) hlk hpl hsmq q.1 hsub hy0 hnear q.2.1.1
    unfold kapM1; exact this
  · obtain ⟨hlk, hpl⟩ := AdalyFormal.M1DK.chart_boundsU ell M k hell S α₀ V g A _ rfl hgA hB hα0 ha1
    have hsub : AgreeAt (Ball (embY ell k Lu hell q.1) (rhoT ell k)) (periodicGaugeTransform γ' U) (periodicGaugeTransform g V) :=
      hag'.mono (Ball_sub (by rw [AdalyFormal.StatementLaneR8.pdist_self]) (by omega))
    have := unitBgU_chart_small hell hell2 S hS Lam hL hT3 U a γ' (periodicGaugeTransform g V) (12 * M * α₀)
      (qM1 (12 * M * α₀)) (AdalyFormal.M1DK.qM1_nonneg (by positivity)) hlk hpl hsmq q.1 hsub hy0 hnear q.2.1.2
    unfold kapM1; exact this
  · -- regional class
    intro l hl z hz hzA μ
    obtain ⟨hzW, hzd⟩ := hz
    have hrl : rhoT ell l ≤ rhoT ell k := AdalyFormal.StatementLaneR8.rhoT_mono ell hl.le
    have hagz : AgreeAt (Ball z (rhoT ell l)) (periodicGaugeTransform γ' U) (periodicGaugeTransform g V) :=
      hag'.mono (Ball_sub hzd (by omega))
    have hcg := AdalyFormal.StatementLaneR8.bgTower_congr (GF ell k Lu) hell l z hagz μ
    rw [hcg]
    have hzW' : z ∈ WM ell k S ((Fin.last k : Fin (k + 1)) : ℕ) l := by rw [Fin.val_last]; exact hzW
    have := AdalyFormal.TowerLoc.hcl_M1U hell2 hS hroom hT3 V g A hgA hB hη hα0 ha1 hsm4 (Fin.last k) l hl z hzW' hzA μ
    rw [Fin.val_last] at this
    exact this
  · -- the four rows' cones
    intro b hb l hl z hz
    refine ⟨⟨hl, ⟨unitBondEmb ell k Lu hell b, hrows b hb⟩, hz⟩, ?_⟩
    have h1 := qb_pdist (k := k) hell hu q b hb
    have h2 : pdist (embY ell k Lu hell b.1) z ≤ rhoT ell k - rhoT ell l := hz
    have h3 := pdist_triangle (embY ell k Lu hell q.1) (embY ell k Lu hell b.1) z
    omega

end AdalyFormal.M2Unit

