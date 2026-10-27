import DK4
import GW1

/-!
# HB1 -- `hb` (bijectivity of `H₀`) at every `M1Regular` configuration (lane m1_hb_20261014)

`hb_near` : `H₀(Q₁)` is bijective as soon as `Ū^k` is `κ`-small ONLY on the balls the rows of `Λ'` read (+ the three `k`-free
unit conditions); `H0 Lam P.Q1 = H0 Lam (Q1jet (Vcut ..))` by row-locality, and `Vcut` is globally small.
`hb_M1` : the same for `gparams ell k Lu hell S U a Lam` with `U ∈ M1Regular` (route of DK4 `D2in_l1_M1`: gauge of `M1Regular`,
DK2 `chart_bounds` + `tower_near` on the read balls, then gauge invariance of `hb`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1HB

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible pdist scaleUp CRowIn TorusOK)
open AdalyFormal.StatementLaneG (LambdaOK2 gparams)
open AdalyFormal.StatementLaneR8 (Ball pdist_triangle pdist_comm pdist_coarseShift_le lamPrime_sub H0_congr_rows)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.IngredientFamilyR2 (RegBg Q1jet H0 IngrBParams Dset)
open AdalyFormal.NonflatJet (rhoOf r0)
open EstimatesLayer.E1E3 (e2Majorant)
open AdalyFormal.DLayer (H0_drift_l1)
open AdalyFormal.M1DK

theorem hb_near (P : IngrBParams) (hd : ∀ μ, P.ell ∣ P.Lu μ + 1) (hell2 : 2 ≤ P.ell) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hnear : ∀ c : CoarseBond P.Lu P.ell, CRowIn P.ell P.Lam c → ∀ z ∈ Ball c.1.1 (4 * (1 * P.ell)), ∀ μ : Fin 3,
      frobNorm (((P.unitBgU (z, μ) : SU2) : M2) - 1) ≤ κ)
    (u1 : κ ≤ 1 / (1000 * (P.ell : ℝ) ^ 4))
    (u2 : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound P.ell : ℝ) * κ) < r0)
    (hKDc : 192 * (8 * (P.ell : ℝ) * κ + 8 * e2Majorant (rhoOf P.ell κ)) ≤ 1 / (2 * (P.ell : ℝ) ^ 3)) :
    Function.Bijective (H0 P.Lam P.Q1) := by
  have hell : 0 < P.ell := P.hell
  set ell := P.ell with hellP
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set Lam := P.Lam with hLam
  set V := Vcut ell Lam P.unitBgU with hVdef
  have hV : ∀ e', frobNorm (((V e' : SU2) : M2) - 1) ≤ κ := Vcut_small ell Lam P.unitBgU κ hκ0 hnear
  have hns := AdalyFormal.NonflatJet.numeric_small hell κ hκ0 u1
  have hreg1 : RegBg 1 ell V := AdalyFormal.NonflatJet.regBg_of_small Nat.one_pos V κ hκ0 hV u2
  set δ := 192 * (8 * (ell : ℝ) * κ + 8 * e2Majorant (rhoOf ell κ)) with hδ
  have hδlt : δ < 1 / (ell : ℝ) ^ 3 := by
    have : 1 / (2 * (ell : ℝ) ^ 3) < 1 / (ell : ℝ) ^ 3 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_pos hellR 3]
    linarith
  have hdrift := fun w => H0_drift_l1 hell hd Lam V κ hκ0 hV hns.1 hreg1 w
  have hbV : Function.Bijective (H0 Lam (Q1jet ell V)) := H0_bij_of_drift hell hd Lam (Q1jet ell V) δ hδlt hdrift
  have hQ : H0 Lam P.Q1 = H0 Lam (Q1jet ell V) :=
    H0_congr_rows Lam (fun B c hc => Q1jet_cut ell Lam P.unitBgU B hc)
  rw [hQ]; exact hbV

/-- **`hb` at `M1Regular`**, with the k-free smallness `KDsmall ℓ (12 M α₀)`. -/
theorem hb_M1 (ell M R k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (α₀ : ℝ)
    (hA : Admissible ell M R k S) (hell2 : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hT : TorusOK ell M Lu)
    (hL : LambdaOK2 ell M R k S Lam) (hU : AdalyFormal.M1.M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hα : 0 ≤ α₀) (hsm : KDsmall ell (12 * M * α₀)) :
    Function.Bijective (H0 (gparams ell k Lu hell S U a Lam).Lam (gparams ell k Lu hell S U a Lam).Q1) := by
  obtain ⟨g, A, hg, hb⟩ := hU
  set β : ℝ := 12 * M * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  obtain ⟨hlk, hpl⟩ := chart_bounds ell M k hell S α₀ U g A _ rfl hg hb hα hsm.h1
  have hd : ∀ μ, ell ∣ Lu μ + 1 := hT.1
  have hT3 : ∀ μ, 3 ≤ Lu μ + 1 := fun μ => by have := hT.2.1 μ; omega
  set P := gparams ell k Lu hell S U a Lam with hP
  set P' := AdalyFormal.GaugeCov.gaugeP P g with hP'
  have hnear : ∀ c, CRowIn P'.ell P'.Lam c → ∀ z ∈ Ball c.1.1 (4 * (1 * P'.ell)), ∀ μ : Fin 3,
      frobNorm (((P'.unitBgU (z, μ) : SU2) : M2) - 1) ≤ kapM1 β := by
    intro c hc z hz μ
    have hz' : pdist c.1.1 z ≤ 4 * (1 * ell) := hz
    obtain ⟨y, hy, hyz⟩ : ∃ y ∈ Lam, pdist y z + 17 ≤ R * M := by
      rcases hc with h | h
      · exact ⟨c.1.1, lamPrime_sub hell h, by omega⟩
      · refine ⟨coarseShift c.1.1 ell c.2, lamPrime_sub hell h, ?_⟩
        have h1 : pdist (coarseShift c.1.1 ell c.2) c.1.1 ≤ ell := by
          rw [pdist_comm]; exact pdist_coarseShift_le _ _ _
        have h2 := pdist_triangle (coarseShift c.1.1 ell c.2) c.1.1 z
        omega
    exact tower_near ell M R k Lu hell2 hell S hA Lam hL hT3 (periodicGaugeTransform g U) β (qM1 β)
      (qM1_nonneg hβ0) hlk hpl hsm.hcb hy hyz μ
  have hmain := hb_near P' hd hell2 (kapM1 β) (kapM1_nonneg hβ0) hnear hsm.u1 hsm.u2 hsm.kd
  exact (AdalyFormal.M1GaugeW4.hb_gauge_iff hell S a Lam U g).1 hmain

/-- **`hb` at `M1Regular`, threshold form** `12 M α₀ ≤ beta0 ℓ`. -/
theorem hb_M1' (ell M R k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (α₀ : ℝ)
    (hA : Admissible ell M R k S) (hell2 : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hT : TorusOK ell M Lu)
    (hL : LambdaOK2 ell M R k S Lam) (hU : AdalyFormal.M1.M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hα : 0 ≤ α₀) (hsm : (12 : ℝ) * M * α₀ ≤ beta0 ell) :
    Function.Bijective (H0 (gparams ell k Lu hell S U a Lam).Lam (gparams ell k Lu hell S U a Lam).Q1) :=
  hb_M1 ell M R k Lu hell S U a Lam α₀ hA hell2 hroom hT hL hU hα (KDsmall_of_le ell hell _ (by positivity) hsm)

end AdalyFormal.M1HB

#print axioms AdalyFormal.M1HB.hb_near
#print axioms AdalyFormal.M1HB.hb_M1
#print axioms AdalyFormal.M1HB.hb_M1'
