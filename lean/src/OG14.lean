import OG13

/-!
# OG14 -- F6 (`Q*`-injectivity) from `BallChartsAt` away from level-0 exit rows (lane m2_onegap_20261015)

`ExitFree ell k Lu S` : every level-0 row base `z` has `Ball z (36 ℓ) ⊆ Ω_0`.  (A level-0 row whose ball leaves `Ω_0` has no per-row chart in general: see NOTES.md §exit rows.)
`chartHyp_of_balls` : per-row gauges `γ_p` from the region charts of `BallChartsAt` on `Ball z_p (36 ℓ^{j+1})` (scale `ℓ^{j-1}`), with the GUARDED closeness `epsC`.
`qsInj_exitfree` : `Q_U*` injective, via `W6.qs_injective_charts` and `numerics_epsC`.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.OneGap

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist CubeBond bigSide towerBj)
open AdalyFormal.StatementLaneR8 (Ball pdist_triangle pdist_comm)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.CurvBlock (CubeChart)
open AdalyFormal.M2W6 (ChartHyp link_bound_mono hsm_of row_anchor tower_link_cube qs_injective_charts)
open AdalyFormal.NonflatJet (rhoOf r0)
open SmallnessBridge.Assemble (loopFactorBound)

/-- no level-0 row ball leaves `Ω_0` -/
def ExitFree (ell k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) : Prop :=
  ∀ p : BIdx (geomOf ell k S), (p.1 : ℕ) = 0 → Ball p.2.1.1 (36 * ell) ⊆ S.Om 0

section rows
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

theorem rowChart_of_balls (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 73 * ell + 2 ≤ M) (hR37 : 37 * ell ^ 2 ≤ R)
    (hexit : ExitFree ell k Lu S) {C α₀ η : ℝ} {U : LinkCfg (scaleUp ell k Lu)} (hB : BallChartsAt ell M k S U C α₀ η)
    (p : BIdx (geomOf ell k S)) :
    RegionChart (Ball p.2.1.1 (36 * ell ^ ((p.1 : ℕ) + 1))) ell M 12 (C * α₀) η ((p.1 : ℕ) - 1) U := by
  have hell0 : 0 < ell := by omega
  have hjk : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  obtain ⟨a, ⟨haj, haj1⟩, hpa⟩ := AdalyFormal.M2W6.row_anchor p
  set j : ℕ := (p.1 : ℕ) with hj
  set z0 := p.2.1.1 with hz0
  have hn1 : 1 ≤ ell ^ j := Nat.one_le_pow _ _ hell0
  have hpow : ell ^ (j + 1) = ell * ell ^ j := by rw [pow_succ]; ring
  have hr7 : 36 * ell ^ (j + 1) ≤ 7 * M * ell ^ j := by
    rw [hpow]
    have : 36 * ell ≤ 7 * M := by omega
    nlinarith
  have hbS : ∀ σ : Fin 3, M * ell ^ j ≤ scaleUp ell k Lu σ + 1 := fun σ =>
    Nat.le_of_dvd (Nat.succ_pos _) (hS.2.2.1 j hjk σ)
  have hnw : ∀ σ : Fin 3, 2 * (36 * ell ^ (j + 1)) + 2 ≤ scaleUp ell k Lu σ + 1 := by
    intro σ
    have h1 := hbS σ
    have h2 : (73 * ell + 2) * ell ^ j ≤ M * ell ^ j := Nat.mul_le_mul_right _ hM
    rw [hpow]
    nlinarith
  have hpa' : pdist a z0 ≤ ell ^ j := by
    have h := pdist_comm a z0
    have h' : pdist z0 a ≤ ell ^ j := hpa
    omega
  have hsub : ∀ x ∈ Ball z0 (36 * ell ^ (j + 1)), pdist a x ≤ 37 * ell ^ (j + 1) := by
    intro x hx
    have h1 : pdist z0 x ≤ 36 * ell ^ (j + 1) := hx
    have h2 := pdist_triangle a z0 x
    have h4 : ell ^ j ≤ ell ^ (j + 1) := Nat.pow_le_pow_right hell0 (by omega)
    omega
  have hmem : ∀ x ∈ Ball z0 (36 * ell ^ (j + 1)), x ∈ S.Om (j - 1) := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · intro x hx
      have := hexit p hj0 (by rw [hj0] at hx; simpa using hx)
      rw [hj0] at ⊢
      exact this
    · intro x hx
      have hbelow : 37 * ell ^ (j + 1) ≤ R * bigSide M ell (j - 1) := by
        show 37 * ell ^ (j + 1) ≤ R * (M * ell ^ (j - 1))
        have e : ell ^ (j + 1) = ell ^ 2 * ell ^ (j - 1) := by rw [← pow_add]; congr 1; omega
        rw [e]
        have hRM : 37 * ell ^ 2 ≤ R * M := le_trans hR37 (Nat.le_mul_of_pos_right R (by omega))
        calc 37 * (ell ^ 2 * ell ^ (j - 1)) = (37 * ell ^ 2) * ell ^ (j - 1) := by ring
          _ ≤ (R * M) * ell ^ (j - 1) := Nat.mul_le_mul_right _ hRM
          _ = R * (M * ell ^ (j - 1)) := by ring
      exact ball_mem_below hS hj1 hjk haj (r := 37 * ell ^ (j + 1)) hbelow x (hsub x hx)
  have hnot : ∀ x ∈ Ball z0 (36 * ell ^ (j + 1)), x ∉ S.Om (j + 2) := by
    intro x hx
    have habove : 37 * ell ^ (j + 1) ≤ R * bigSide M ell (j + 1) := by
      show 37 * ell ^ (j + 1) ≤ R * (M * ell ^ (j + 1))
      have h37 : 37 ≤ R := le_trans (by nlinarith) hR37
      have hRM : 37 ≤ R * M := le_trans h37 (Nat.le_mul_of_pos_right R (by omega))
      calc 37 * ell ^ (j + 1) ≤ (R * M) * ell ^ (j + 1) := Nat.mul_le_mul_right _ hRM
        _ = R * (M * ell ^ (j + 1)) := by ring
    exact ball_not_above hS haj1 habove x (hsub x hx)
  have hpa2 : pdist z0 a ≤ ell ^ j := hpa
  exact hB j hjk z0 ⟨a, haj, by
      have : ell ^ j ≤ M * ell ^ j := Nat.le_mul_of_pos_left _ (by omega)
      omega⟩ (36 * ell ^ (j + 1)) hr7 hnw hmem hnot (Or.inl (by omega))

theorem chartHyp_of_balls (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 73 * ell + 2 ≤ M) (hR37 : 37 * ell ^ 2 ≤ R)
    (hexit : ExitFree ell k Lu S) (hT3 : ∀ μ, 3 ≤ Lu μ + 1) {C α₀ η : ℝ} (hη : 0 < η)
    (hα0 : 0 ≤ C * α₀)
    (ha1 : ((12 : ℕ) : ℝ) * M * (C * α₀) ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 4 * ((4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀))) ≤ 1)
    {U : LinkCfg (scaleUp ell k Lu)} (hB : BallChartsAt ell M k S U C α₀ η) :
    ∃ γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu),
      ChartHyp ell k Lu S U γ (epsC ell ((4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀)))) := by
  have hell : 0 < ell := by omega
  have ha0 : 0 ≤ ((12 : ℕ) : ℝ) * M * (C * α₀) := by positivity
  have key : ∀ p : BIdx (geomOf ell k S), ∃ g : GaugeFn (scaleUp ell k Lu),
      ∀ j' : ℕ, (p.1 : ℕ) ≤ j' + 1 → j' ≤ (p.1 : ℕ) + 1 → ∀ l, l < k → l < j' →
        ∀ z ∈ Ball p.2.1.1 (20 * ell ^ ((p.1 : ℕ) + 1)), z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
          frobNorm (((bgTower (GF ell k Lu) (periodicGaugeTransform g U) l (z, μ) : SU2) : M2) - 1)
            ≤ epsC ell ((4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀))) j' l := by
    intro p
    obtain ⟨g, A, hexp, hd⟩ := rowChart_of_balls hell2 hS hM hR37 hexit hB p
    set j : ℕ := (p.1 : ℕ) with hj
    let K : CubeChart U (fun b : Bond (scaleUp ell k Lu) => CubeBond (Ball p.2.1.1 (36 * ell ^ (j + 1))) b) η
        (((12 : ℕ) : ℝ) * M * (C * α₀) * (((ell : ℝ) ^ (j - 1) * η)⁻¹ ^ 1))
        (((12 : ℕ) : ℝ) * M * (C * α₀) * (((ell : ℝ) ^ (j - 1) * η)⁻¹ ^ 2)) :=
      ⟨g, A, fun e he => ⟨hd.ht e he, hexp e he, hd.c1 e he⟩, fun μ ν x h1 h2 => hd.c2 μ ν x h1 h2⟩
    refine ⟨K.g, fun j' hj1 hj2 l hlk hlj z hz hza μ => ?_⟩
    have hl : l ≤ j := by omega
    have hpow : ell ^ l ≤ ell ^ (j + 1) := Nat.pow_le_pow_right hell (by omega)
    have hcone' : ∀ w, pdist z w ≤ 14 * ell ^ l → w ∈ Ball p.2.1.1 (36 * ell ^ (j + 1)) := by
      intro w hw
      have h1 : pdist p.2.1.1 z ≤ 20 * ell ^ (j + 1) := hz
      have h2 := pdist_triangle p.2.1.1 z w
      show pdist p.2.1.1 w ≤ 36 * ell ^ (j + 1)
      omega
    have hl' : l ≤ (j - 1) + 1 := by omega
    have hsm := hsm_of hell (by positivity : (0 : ℝ) ≤ (4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀))) hsm4 hl'
    have h := tower_link_cube hell2 hell hT3 U (Ball p.2.1.1 (36 * ell ^ (j + 1))) (j - 1) K hη ha0 ha1 l hlk hsm z hza μ hcone'
    have h' : frobNorm (((bgTower (GF ell k Lu) (periodicGaugeTransform K.g U) l (z, μ) : SU2) : M2) - 1)
        ≤ (ell : ℝ) ^ l * ((4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀)) / (ell : ℝ) ^ (j - 1))
          + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ l * ((4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀)) / (ell : ℝ) ^ (2 * (j - 1)))) := h
    refine h'.trans ?_
    unfold epsC
    rw [if_pos hlj]
    exact AdalyFormal.M2W6.link_bound_mono hell (by positivity) (by omega) l
  choose γ hγ using key
  exact ⟨γ, fun p j' h1 h2 l hlk hlj z hz hza μ => hγ p j' h1 h2 l hlk hlj z hz hza μ⟩

/-- **F6 away from exit rows**: threshold `ρ1(ℓ)` on the chart constant. -/
theorem qsInj_exitfree (ell : ℕ) (hell2 : 2 ≤ ell) :
    ∃ ρ1 : ℝ, 0 < ρ1 ∧ ∀ {M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)},
      Admissible ell M R k S → 73 * ell + 2 ≤ M → 37 * ell ^ 2 ≤ R → 8 * ell ≤ R → 17 * ell ≤ R * M →
      ExitFree ell k Lu S → (∀ μ, 3 ≤ Lu μ + 1) →
      ∀ {C α₀ η : ℝ} {U : LinkCfg (scaleUp ell k Lu)}, 1 ≤ C → 0 < α₀ → 0 < η →
      (4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀)) ≤ ρ1 → BallChartsAt ell M k S U C α₀ η →
      ∀ (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)),
        Function.Injective (gparams ell k Lu (by omega : 0 < ell) S U a Lam).data.Qs := by
  obtain ⟨ρs, hρs, hnum⟩ := numerics_epsC ell hell2
  have hell : 0 < ell := by omega
  have hq : (0 : ℝ) < 1 / (4000000 * (ell : ℝ) ^ 4) := by positivity
  refine ⟨min ρs (1 / (4000000 * (ell : ℝ) ^ 4)), lt_min hρs hq, ?_⟩
  intro M R k Lu S hS hM hR37 hR8 hroom hexit hT3 C α₀ η U hC hα hη hρ hB a Lam
  have hpi := Real.pi_pos
  have hCα : 0 < C * α₀ := by positivity
  have hM0 : 0 < M := by omega
  set a1 : ℝ := ((12 : ℕ) : ℝ) * M * (C * α₀) with ha1d
  have ha1pos : 0 < a1 := by rw [ha1d]; have : (0 : ℝ) < M := by exact_mod_cast hM0
                             positivity
  set ρ : ℝ := (4 * Real.pi + 4) * a1 with hρd
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ ρs := hρ.trans (min_le_left _ _)
  have hρ2 : ρ ≤ 1 / (4000000 * (ell : ℝ) ^ 4) := hρ.trans (min_le_right _ _)
  have hsm4 : 4000000 * (ell : ℝ) ^ 4 * ρ ≤ 1 := by
    have hp : (0 : ℝ) < 4000000 * (ell : ℝ) ^ 4 := by positivity
    calc 4000000 * (ell : ℝ) ^ 4 * ρ ≤ 4000000 * (ell : ℝ) ^ 4 * (1 / (4000000 * (ell : ℝ) ^ 4)) :=
          mul_le_mul_of_nonneg_left hρ2 hp.le
      _ = 1 := by field_simp
  have ha1 : a1 ≤ 1 := by
    have h1 : a1 ≤ ρ := by rw [hρd]; nlinarith
    have h2 : 1 / (4000000 * (ell : ℝ) ^ 4) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ (ell : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hell)
      linarith
    linarith
  obtain ⟨hsm', hr', hsum', hsmall'⟩ := hnum ρ hρ0 hρ1
  obtain ⟨γ, hch⟩ := chartHyp_of_balls hell2 hS hM hR37 hexit hT3 hη hCα.le ha1 hsm4 hB
  exact qs_injective_charts hell2 hS hM0 hR8 hroom U γ (epsC ell ρ) hch (fun j' l _ => epsC_nonneg ell hρ0 j' l)
    (fun j' l _ => hsm' j' l) (fun j' l _ => hr' j' l) (SstarC ell ρ) (fun j' _ => hsum' j') a Lam hsmall'

end rows

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.rowChart_of_balls
#print axioms AdalyFormal.OneGap.chartHyp_of_balls
#print axioms AdalyFormal.OneGap.qsInj_exitfree
