import RI4
import OL15

/-!
# RI5 -- **`ClassRightInvCov` is proved**; the frozen r8 headline from the thin-torus case alone (lane m2_rightinv_20261015)

* `num_RI` : `ρs(ℓ) > 0` such that for `0 ≤ ρ ≤ ρs` the W6 numerics hold at `ε = epsC ℓ ρ` (OG13 `numerics_epsC`), `ρ ≤ 1`,
  `4ℓ⁴ρ·4·10⁶ ≤ 1`, the `nD` smallness `4 sD (1 + AD) ≤ 1/2` and `AD ≤ Abar ℓ` hold at `S* = SstarC ℓ ρ`.
* `rightInv_cfg` : at one configuration with ball charts, the twisted sources `EU` composed with the inverse of `T = Q_U ∘ EU`
  give `x` with `Q x = u`, `wnormSq x ≤ cWR ℓ nD u`, `gradWU U x ν ≤ cGR ℓ nD u`.
* **`classRightInvCov : ClassRightInvCov`** (OL15), `classRightInv : ClassRightInv` (OL11, via OL15 `classRightInv_of_cov`).
* **`target8_of_thin : ThinTori → P428Target8`**.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.M2RightInv

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.NonflatJet (rhoOf r0)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.BondComposite (thetaOf rr)
open AdalyFormal.TowerLoc (delStar Ctheta)
open AdalyFormal.W6 (nD nD_nonneg CE CE_pos)
open AdalyFormal.M2W6 (mult0 EU EU_mem Tlin Tlin_apply)
open AdalyFormal.M1DStrat (gradWU)
open AdalyFormal.OneGap (BallChartsAt epsC SstarC numerics_epsC epsC_nonneg)

/-- the defect constant of `source_bounds` at level sum `S*` -/
def cSof (ell : ℕ) (Sst : ℝ) : ℝ := 3 * delStar ell Sst ^ 2 * CE
/-- the full-vector constant of `source_bounds` at level sum `S*` -/
def cTof (ell : ℕ) (Sst : ℝ) : ℝ := 3 * (Real.exp (Sst / rr ell)) ^ 2 * CE

/-- a `k`-, `m`-free bound of `AD` -/
def Abar (ell : ℕ) : ℝ := 4 * (mult0 ell * ((ell : ℝ) ^ 2 * (27 * CE))) + 4 + 2 * (mult0 ell * ((ell : ℝ) ^ 2 * (27 * CE)))

/-- the weighted-norm constant of the right inverse -/
def cWR (ell : ℕ) : ℝ := 2187 * ((ell : ℝ) ^ 2 * CE) * (8 * (1 + Abar ell))
/-- the covariant-gradient constant of the right inverse -/
def cGR (ell : ℕ) : ℝ := 4374 * Cg1 ((1 + 3 * Real.pi) * ell) * (8 * (1 + Abar ell))

theorem Abar_nonneg (ell : ℕ) : 0 ≤ Abar ell := by
  unfold Abar; have := mult0_nonneg ell; have := CE_pos; positivity

theorem cWR_nonneg (ell : ℕ) : 0 ≤ cWR ell := by
  unfold cWR; have := Abar_nonneg ell; have := CE_pos; positivity

theorem cGR_nonneg (ell : ℕ) : 0 ≤ cGR ell := by
  unfold cGR; have := Abar_nonneg ell; have := Cg1_nonneg ((1 + 3 * Real.pi) * ell); positivity

/-- **the numerics of the right inverse** -/
theorem num_RI (ell : ℕ) (hell2 : 2 ≤ ell) :
    ∃ ρs : ℝ, 0 < ρs ∧ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ ρs →
      ρ ≤ 1 ∧ 4000000 * (ell : ℝ) ^ 4 * ρ ≤ 1 ∧
      (∀ j' l : ℕ, rhoOf ell (epsC ell ρ j' l) < Real.pi / 2) ∧
      (∀ j' l : ℕ, Real.pi / 2 * ((loopFactorBound ell : ℝ) * epsC ell ρ j' l) < r0) ∧
      (∀ j' : ℕ, ∑ l ∈ range j', thetaOf ell (epsC ell ρ j' l) ≤ SstarC ell ρ) ∧
      4 * sD ell (cSof ell (SstarC ell ρ)) * (1 + AD ell (cSof ell (SstarC ell ρ)) (cTof ell (SstarC ell ρ))) ≤ 1 / 2 ∧
      AD ell (cSof ell (SstarC ell ρ)) (cTof ell (SstarC ell ρ)) ≤ Abar ell := by
  have hell : 0 < ell := by omega
  obtain ⟨ρn, hρn, hnum⟩ := numerics_epsC ell hell2
  have hrr := AdalyFormal.OneGap.rr_pos ell hell
  have hCE := CE_pos
  have hm := mult0_nonneg ell
  have hpi := Real.pi_pos
  have hl2 : (0 : ℝ) ≤ (ell : ℝ) ^ 2 := by positivity
  have hAb := Abar_nonneg ell
  set K : ℝ := 4 * (mult0 ell * ((ell : ℝ) ^ 2 * (27 * CE))) * (1 + Abar ell) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hCt : 0 < Ctheta := by unfold Ctheta; positivity
  set Q : ℝ := Ctheta * (ell : ℝ) ^ 2 * (2 * ((ell : ℝ) ^ 2 * (1 + 3 * Real.pi))) with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hSQ : ∀ ρ : ℝ, SstarC ell ρ = Q * ρ := fun ρ => by unfold SstarC; rw [hQ]; ring
  have hq4 : (0 : ℝ) < 1 / (4000000 * (ell : ℝ) ^ 4) := by positivity
  refine ⟨min ρn (min 1 (min (1 / (4000000 * (ell : ℝ) ^ 4)) (rr ell / ((2 * K + 2) * (Q + 1))))),
    lt_min hρn (lt_min one_pos (lt_min hq4 (by positivity))), fun ρ hρ0 hρs => ?_⟩
  have hρ1 : ρ ≤ ρn := hρs.trans (min_le_left _ _)
  have hρ2 : ρ ≤ 1 := hρs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ3 : ρ ≤ 1 / (4000000 * (ell : ℝ) ^ 4) :=
    hρs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hρ4 : ρ ≤ rr ell / ((2 * K + 2) * (Q + 1)) :=
    hρs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨h1, h2, h3, -⟩ := hnum ρ hρ0 hρ1
  have hsm4 : 4000000 * (ell : ℝ) ^ 4 * ρ ≤ 1 := by
    have hp : (0 : ℝ) < 4000000 * (ell : ℝ) ^ 4 := by positivity
    calc 4000000 * (ell : ℝ) ^ 4 * ρ ≤ 4000000 * (ell : ℝ) ^ 4 * (1 / (4000000 * (ell : ℝ) ^ 4)) :=
          mul_le_mul_of_nonneg_left hρ3 hp.le
      _ = 1 := by field_simp
  set Sst : ℝ := SstarC ell ρ with hSst
  have hS0 : 0 ≤ Sst := by rw [hSst, hSQ]; positivity
  set t : ℝ := Sst / rr ell with ht
  have ht0 : 0 ≤ t := div_nonneg hS0 hrr.le
  have hSle : Sst ≤ rr ell / (2 * K + 2) := by
    rw [hSst, hSQ]
    have hq1 : 0 < Q + 1 := by linarith
    have h2K : 0 < 2 * K + 2 := by linarith
    calc Q * ρ ≤ (Q + 1) * ρ := by nlinarith
      _ ≤ (Q + 1) * (rr ell / ((2 * K + 2) * (Q + 1))) := mul_le_mul_of_nonneg_left hρ4 hq1.le
      _ = rr ell / (2 * K + 2) := by field_simp
  have ht1 : t ≤ 1 / (2 * K + 2) := by
    rw [ht, div_le_iff₀ hrr]
    calc Sst ≤ rr ell / (2 * K + 2) := hSle
      _ = 1 / (2 * K + 2) * rr ell := by ring
  have hK1 : 1 / (2 * K + 2) ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith
  have ht1' : t ≤ 1 := by linarith
  have hexp : Real.exp t ≤ 3 := by
    have h1' : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.mpr ht1'
    have := Real.exp_one_lt_d9
    linarith
  have hexp0 : 0 < Real.exp t := Real.exp_pos t
  have hdel : delStar ell Sst ≤ 3 * t := by
    unfold delStar; rw [← ht]; nlinarith
  have hdel0 : 0 ≤ delStar ell Sst := by unfold delStar; rw [← ht]; positivity
  have hcS : cSof ell Sst ≤ 27 * CE * t ^ 2 := by
    unfold cSof
    have : delStar ell Sst ^ 2 ≤ 9 * t ^ 2 := by nlinarith
    nlinarith
  have hcS0 : 0 ≤ cSof ell Sst := by unfold cSof; positivity
  have hcT : cTof ell Sst ≤ 27 * CE := by
    unfold cTof; rw [← ht]
    have : Real.exp t ^ 2 ≤ 9 := by nlinarith
    nlinarith
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hcS1 : cSof ell Sst ≤ 27 * CE := by nlinarith
  have hAD : AD ell (cSof ell Sst) (cTof ell Sst) ≤ Abar ell := by
    unfold AD sD Abar
    have e1 : mult0 ell * ((ell : ℝ) ^ 2 * cTof ell Sst) ≤ mult0 ell * ((ell : ℝ) ^ 2 * (27 * CE)) := by gcongr
    have e2 : mult0 ell * ((ell : ℝ) ^ 2 * cSof ell Sst) ≤ mult0 ell * ((ell : ℝ) ^ 2 * (27 * CE)) := by gcongr
    linarith
  have hsD : sD ell (cSof ell Sst) ≤ mult0 ell * ((ell : ℝ) ^ 2 * (27 * CE)) * t ^ 2 := by
    unfold sD
    have : mult0 ell * ((ell : ℝ) ^ 2 * cSof ell Sst) ≤ mult0 ell * ((ell : ℝ) ^ 2 * (27 * CE * t ^ 2)) := by gcongr
    linarith
  have hsD0 : 0 ≤ sD ell (cSof ell Sst) := sD_nonneg ell hcS0
  have hsmall : 4 * sD ell (cSof ell Sst) * (1 + AD ell (cSof ell Sst) (cTof ell Sst)) ≤ 1 / 2 := by
    have hA0 : 0 ≤ 1 + AD ell (cSof ell Sst) (cTof ell Sst) := by
      have := AD_nonneg ell hcS0 (show 0 ≤ cTof ell Sst by unfold cTof; positivity); linarith
    have e1 : 4 * sD ell (cSof ell Sst) * (1 + AD ell (cSof ell Sst) (cTof ell Sst))
        ≤ 4 * (mult0 ell * ((ell : ℝ) ^ 2 * (27 * CE)) * t ^ 2) * (1 + Abar ell) := by
      have := mul_le_mul hsD (by linarith : 1 + AD ell (cSof ell Sst) (cTof ell Sst) ≤ 1 + Abar ell) hA0 (by positivity)
      nlinarith
    have e2 : 4 * (mult0 ell * ((ell : ℝ) ^ 2 * (27 * CE)) * t ^ 2) * (1 + Abar ell) = K * t ^ 2 := by rw [hK]; ring
    have e3 : K * t ^ 2 ≤ K * t := mul_le_mul_of_nonneg_left (by nlinarith) hK0
    have e4 : K * t ≤ K * (1 / (2 * K + 2)) := mul_le_mul_of_nonneg_left ht1 hK0
    have e5 : K * (1 / (2 * K + 2)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by linarith)]; linarith
    linarith
  exact ⟨hρ2, hsm4, h1, h2, h3, hsmall, hAD⟩

section cfg
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- **the covariant right inverse at one configuration with ball charts** -/
theorem rightInv_cfg (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 73 * ell + 2 ≤ M) (hR37 : 37 * ell ^ 2 ≤ R)
    (hR : 8 * ell ≤ R) (hroom : 17 * ell ≤ R * M) (hRM : 45 * ell + 4 ≤ R * M) (hR1 : 1 ≤ R)
    (hT3 : ∀ μ, 3 ≤ Lu μ + 1)
    {C α₀ η : ℝ} (hη : 0 < η) (hα0 : 0 ≤ C * α₀)
    (ha1 : ((12 : ℕ) : ℝ) * M * (C * α₀) ≤ 1)
    {U : LinkCfg (scaleUp ell k Lu)} (hB : BallChartsAt ell M k S U C α₀ η)
    (ρs : ℝ) (hnum : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ ρs →
      ρ ≤ 1 ∧ 4000000 * (ell : ℝ) ^ 4 * ρ ≤ 1 ∧
      (∀ j' l : ℕ, rhoOf ell (epsC ell ρ j' l) < Real.pi / 2) ∧
      (∀ j' l : ℕ, Real.pi / 2 * ((loopFactorBound ell : ℝ) * epsC ell ρ j' l) < r0) ∧
      (∀ j' : ℕ, ∑ l ∈ range j', thetaOf ell (epsC ell ρ j' l) ≤ SstarC ell ρ) ∧
      4 * sD ell (cSof ell (SstarC ell ρ)) * (1 + AD ell (cSof ell (SstarC ell ρ)) (cTof ell (SstarC ell ρ))) ≤ 1 / 2 ∧
      AD ell (cSof ell (SstarC ell ρ)) (cTof ell (SstarC ell ρ)) ≤ Abar ell)
    (hρ : (4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀)) ≤ ρs)
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (u : FSp (geomOf ell k S)) :
    ∃ x : ↥(bondSupp (geomOf ell k S)),
      (gparams ell k Lu (by omega) S U a Lam).data.Q x = u ∧
      AdalyFormal.M1.wnormSq S ell k (x : BondFnL2 (scaleUp ell k Lu)) ≤ cWR ell * nD u ∧
      ∀ ν : Fin 3, gradWU U (x : BondFnL2 (scaleUp ell k Lu)) ν ≤ cGR ell * nD u := by
  have hell : 0 < ell := by omega
  have hM0 : 0 < M := by omega
  have hM1 : 1 ≤ M := by omega
  have hpi := Real.pi_pos
  have hCE := CE_pos
  set ρ : ℝ := (4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀)) with hρd
  have hρ0 : 0 ≤ ρ := by rw [hρd]; positivity
  obtain ⟨hρ1, hsm4, hsm', hr', hsum', hsmall, hAD⟩ := hnum ρ hρ0 hρ
  obtain ⟨γ, hok, hfine⟩ := gauges_of_balls hell2 hS hM hR37 hR hroom hRM hT3 hη hα0 ha1 hsm4 hB hsm' hr'
    (SstarC ell ρ) hsum'
  have hrr := AdalyFormal.OneGap.rr_pos ell hell
  have hcS0 : 0 ≤ cSof ell (SstarC ell ρ) := by unfold cSof; positivity
  have hcT0 : 0 ≤ cTof ell (SstarC ell ρ) := by unfold cTof; positivity
  obtain ⟨v, hv, hnv⟩ := Tlin_rightInv hell2 hS hM0 hroom hR U γ hok hcS0 hcT0 hsmall u
  have hnv' : nD v ≤ 8 * (1 + Abar ell) * nD u := by
    have hnu := nD_nonneg hell u
    have e : 8 * (1 + AD ell (cSof ell (SstarC ell ρ)) (cTof ell (SstarC ell ρ))) * nD u
        ≤ 8 * (1 + Abar ell) * nD u := by
      apply mul_le_mul_of_nonneg_right _ hnu; linarith
    exact hnv.trans e
  have hτ0 : 0 ≤ (1 + 3 * Real.pi) * ρ * ell := by positivity
  refine ⟨⟨EU hell γ v, EU_mem hell hS γ v⟩, ?_, ?_, fun ν => ?_⟩
  · show (bondSectorOf (geomOf ell k S) U).Qfull (EU hell γ v) = u
    rw [← Tlin_apply]; exact hv
  · have h1 := EU_wnorm hell hell2 hS hR1 hM1 γ v
    have h2 : nD v ≤ 8 * (1 + Abar ell) * nD u := hnv'
    have hc : 0 ≤ 2187 * ((ell : ℝ) ^ 2 * CE) := by positivity
    show AdalyFormal.M1.wnormSq S ell k (EU hell γ v) ≤ _
    calc AdalyFormal.M1.wnormSq S ell k (EU hell γ v) ≤ 2187 * ((ell : ℝ) ^ 2 * CE) * nD v := h1
      _ ≤ 2187 * ((ell : ℝ) ^ 2 * CE) * (8 * (1 + Abar ell) * nD u) := mul_le_mul_of_nonneg_left h2 hc
      _ = cWR ell * nD u := by unfold cWR; ring
  · have h1 := EU_grad hell hell2 hS U γ hτ0 hfine v ν
    have h2 : nD v ≤ 8 * (1 + Abar ell) * nD u := hnv'
    have hC : Cg1 ((1 + 3 * Real.pi) * ρ * ell) ≤ Cg1 ((1 + 3 * Real.pi) * ell) := by
      unfold Cg1
      have e1 : (1 + 3 * Real.pi) * ρ * ell ≤ (1 + 3 * Real.pi) * ell := by
        have : (0 : ℝ) ≤ (1 + 3 * Real.pi) * ell := by positivity
        nlinarith
      have e2 := pow_le_pow_left₀ hτ0 e1 2
      nlinarith
    have hC0 := Cg1_nonneg ((1 + 3 * Real.pi) * ρ * ell)
    have hnv0 := nD_nonneg hell v
    show gradWU U (EU hell γ v) ν ≤ _
    calc gradWU U (EU hell γ v) ν ≤ 4374 * Cg1 ((1 + 3 * Real.pi) * ρ * ell) * nD v := h1
      _ ≤ 4374 * Cg1 ((1 + 3 * Real.pi) * ell) * nD v := by gcongr
      _ ≤ 4374 * Cg1 ((1 + 3 * Real.pi) * ell) * (8 * (1 + Abar ell) * nD u) := by
          have := Cg1_nonneg ((1 + 3 * Real.pi) * ell)
          gcongr
      _ = cGR ell * nD u := by unfold cGR; ring

end cfg

/-- **`ClassRightInvCov` (OL15) holds** -/
theorem classRightInvCov : AdalyFormal.M2OpLayer.ClassRightInvCov := by
  intro ell hell2 a ha
  have hell0 : 0 < ell := by omega
  have hpi := Real.pi_pos
  obtain ⟨m₁B, hBm⟩ := AdalyFormal.OneGap.ballCharts_of_G AdalyFormal.M2BallCharts.ballChartsG ell hell2
  obtain ⟨ρs, hρs, hnum⟩ := num_RI ell hell2
  refine ⟨m₁B + 8, fun m hm => ?_⟩
  set M : ℕ := ell ^ m with hMdef
  have hM73 : 73 * ell + 2 ≤ M := by
    have h1 : 2 ^ 7 ≤ ell ^ 7 := Nat.pow_le_pow_left hell2 7
    have h2 : ell ^ 8 ≤ ell ^ m := Nat.pow_le_pow_right hell0 (by omega)
    have h3 : ell ^ 8 = ell * ell ^ 7 := by ring
    have h4 : ell * 2 ^ 7 ≤ ell * ell ^ 7 := Nat.mul_le_mul_left ell h1
    rw [hMdef]; omega
  have hM1 : 1 ≤ M := by omega
  obtain ⟨R₁B, hRB⟩ := hBm m (by omega)
  refine ⟨cWR ell, cGR ell, cWR_nonneg ell, cGR_nonneg ell,
    R₁B + 37 * ell ^ 2 + 45 * ell + 4, fun R hR => ?_⟩
  obtain ⟨C, hC1, sB, hsB, hBf⟩ := hRB R (by omega)
  have hCpos : (0 : ℝ) < C := by linarith
  have hq : (0 : ℝ) < (4 * Real.pi + 4) * C := by positivity
  refine ⟨min sB (ρs / ((4 * Real.pi + 4) * C)), lt_min hsB (div_pos hρs hq), ?_⟩
  intro k hk Lu α₀ hα hsα hT S hS hthick Lam hL hLne U hU hloc u
  have hsB' : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sB := hsα.trans (min_le_left _ _)
  have hsρ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ ρs / ((4 * Real.pi + 4) * C) := hsα.trans (min_le_right _ _)
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hBat := hBf k hk Lu α₀ hα hsB' hT S hS Lam hL U hU hloc hLne
  have hR37 : 37 * ell ^ 2 ≤ R := by omega
  have hR8 : 8 * ell ≤ R := by nlinarith
  have hRM : 45 * ell + 4 ≤ R * M := le_trans (by omega) (Nat.le_mul_of_pos_right R (by omega))
  have hroom : 17 * ell ≤ R * M := le_trans (by omega) hRM
  have hT3 : ∀ μ, 3 ≤ Lu μ + 1 := fun μ => by have := hthick μ; omega
  have hρ : (4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀)) ≤ ρs := by
    have e : (4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀))
        = ((4 * Real.pi + 4) * C) * ((12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀) := by rw [hMdef]; push_cast; ring
    rw [e]
    have := (le_div_iff₀' hq).1 hsρ
    linarith
  have hρ1 := (hnum _ (by positivity) hρ).1
  have ha1 : ((12 : ℕ) : ℝ) * M * (C * α₀) ≤ 1 := by
    have h4 : (1 : ℝ) ≤ 4 * Real.pi + 4 := by linarith
    have h0 : 0 ≤ ((12 : ℕ) : ℝ) * M * (C * α₀) := by positivity
    nlinarith
  exact rightInv_cfg hell2 hS hM73 hR37 hR8 hroom hRM (by omega) hT3 hη (by positivity) ha1 hBat ρs hnum hρ a Lam u

/-- **`ClassRightInv` (OL11) holds** -/
theorem classRightInv : AdalyFormal.M2OpLayer.ClassRightInv :=
  AdalyFormal.M2OpLayer.classRightInv_of_cov AdalyFormal.M2BallCharts.ballChartsG classRightInvCov

/-- **the frozen r8 headline from the thin-torus case alone** -/
theorem target8_of_thin (hThin : AdalyFormal.OneGap.ThinTori) : AdalyFormal.StatementLaneG.P428Target8 :=
  AdalyFormal.M2OpLayer.target8_of_rightInvCov classRightInvCov hThin

end AdalyFormal.M2RightInv

#print axioms AdalyFormal.M2RightInv.cSof
#print axioms AdalyFormal.M2RightInv.cTof
#print axioms AdalyFormal.M2RightInv.Abar
#print axioms AdalyFormal.M2RightInv.cWR
#print axioms AdalyFormal.M2RightInv.cGR
#print axioms AdalyFormal.M2RightInv.Abar_nonneg
#print axioms AdalyFormal.M2RightInv.cWR_nonneg
#print axioms AdalyFormal.M2RightInv.cGR_nonneg
#print axioms AdalyFormal.M2RightInv.num_RI
#print axioms AdalyFormal.M2RightInv.rightInv_cfg
#print axioms AdalyFormal.M2RightInv.classRightInvCov
#print axioms AdalyFormal.M2RightInv.classRightInv
#print axioms AdalyFormal.M2RightInv.target8_of_thin
