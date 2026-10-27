import RI3

/-!
# RI4 -- per-row gauges from the ball charts; exit rows; `SrcOK` and `FineOK` at the printed class (lane m2_rightinv_20261015)

* `rowChart_ne` : OG14 `rowChart_of_balls` (text copy) with `ExitFree` replaced by the per-row condition
  `lev p = 0 → Ball z_p (36 ℓ) ⊆ Ω₀` (the only place it was used).
* `rowGauge_ne` : the per-row body of OG14 `chartHyp_of_balls` (text copy): blocked-link closeness `epsC` on `Ball z_p (20 ℓ^{lev+1})`.
* `lev1_not_inter`, `Qfull_lev0`, **`Q_exit`** : at an exit row (level `0`, `Ball z_p (36 ℓ) ⊄ Ω₀`) `Q_V ψ_p = Q_1 ψ_p` for EVERY `V`
  (no level-1 row interacts, by the collar; level-0 rows of `Q` are `U`-independent, `QlinB_zero`).
* `srcOK_rows` : the W6 per-source bounds for every row (chart rows: W6 `source_bounds`; exit rows: `Q_exit` + `flat_F`).
* `fineOK_rows` : the fine-link closeness `FineOK` with `τ = (1 + 3π) ρ ℓ` (blocked level `0` = fine links).
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.M2RightInv

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

open AdalyFormal.OneGap
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.W6 (nF wF CE CE_pos flat_F)
open AdalyFormal.M2W6 (Inter psiL psiL_norm_sq Dvec Tvec Dfun Tvec_eq source_bounds Qfull_zero_of_not_inter nF_rot)
open AdalyFormal.Balaban.AlphaAnalyticity (norm_RMap)
open AdalyFormal.TowerLoc (delStar)
open AdalyFormal.BondComposite (thetaOf rr)

section rows
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

theorem rowChart_ne (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 73 * ell + 2 ≤ M) (hR37 : 37 * ell ^ 2 ≤ R)
    {C α₀ η : ℝ} {U : LinkCfg (scaleUp ell k Lu)} (hB : BallChartsAt ell M k S U C α₀ η)
    (p : BIdx (geomOf ell k S)) (hne : (p.1 : ℕ) = 0 → Ball p.2.1.1 (36 * ell) ⊆ S.Om 0) :
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
      have := hne hj0 (by rw [hj0] at hx; simpa using hx)
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

theorem rowGauge_ne (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 73 * ell + 2 ≤ M) (hR37 : 37 * ell ^ 2 ≤ R)
    (hT3 : ∀ μ, 3 ≤ Lu μ + 1) {C α₀ η : ℝ} (hη : 0 < η)
    (hα0 : 0 ≤ C * α₀)
    (ha1 : ((12 : ℕ) : ℝ) * M * (C * α₀) ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 4 * ((4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀))) ≤ 1)
    {U : LinkCfg (scaleUp ell k Lu)} (hB : BallChartsAt ell M k S U C α₀ η)
    (p : BIdx (geomOf ell k S)) (hne : (p.1 : ℕ) = 0 → Ball p.2.1.1 (36 * ell) ⊆ S.Om 0) :
    ∃ g : GaugeFn (scaleUp ell k Lu),
      ∀ j' : ℕ, (p.1 : ℕ) ≤ j' + 1 → j' ≤ (p.1 : ℕ) + 1 → ∀ l, l < k → l < j' →
        ∀ z ∈ Ball p.2.1.1 (20 * ell ^ ((p.1 : ℕ) + 1)), z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
          frobNorm (((bgTower (GF ell k Lu) (periodicGaugeTransform g U) l (z, μ) : SU2) : M2) - 1)
            ≤ epsC ell ((4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀))) j' l := by
  have hell : 0 < ell := by omega
  have ha0 : 0 ≤ ((12 : ℕ) : ℝ) * M * (C * α₀) := by positivity
  obtain ⟨g, A, hexp, hd⟩ := rowChart_ne hell2 hS hM hR37 hB p hne
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

/-- at a level-0 exit row no level-1 row interacts (collar `45 ℓ + 4 ≤ R M`) -/
theorem lev1_not_inter (hS : Admissible ell M R k S) (hRM : 45 * ell + 4 ≤ R * M) (p p' : BIdx (geomOf ell k S))
    (hp0 : (p.1 : ℕ) = 0) (hex : ¬ Ball p.2.1.1 (36 * ell) ⊆ S.Om 0) (hI : Inter p' p) : (p'.1 : ℕ) = 0 := by
  have hle : (p'.1 : ℕ) ≤ 1 := by have := hI.1; omega
  by_contra hne
  have h1 : (p'.1 : ℕ) = 1 := by omega
  apply hex
  obtain ⟨a, ⟨haj, -⟩, hpa⟩ := row_anchor p'
  rw [h1] at haj
  have hk : 1 ≤ k := by
    have h := p'.1.isLt
    have e : (geomOf ell k S).k = k := rfl
    omega
  have e1 : ell ^ (p'.1 : ℕ) = ell := by rw [h1, pow_one]
  have e0 : ell ^ (p.1 : ℕ) = 1 := by rw [hp0, pow_zero]
  have hpa' : pdist p'.2.1.1 a ≤ ell := le_of_le_of_eq hpa e1
  have hd : pdist p'.2.1.1 p.2.1.1 ≤ 8 * ell + 4 :=
    le_of_le_of_eq hI.2.2 (by rw [e1, e0, mul_one])
  intro x hx
  have hx' : pdist p.2.1.1 x ≤ 36 * ell := hx
  have t1 := pdist_triangle a p'.2.1.1 x
  have t2 := pdist_triangle p'.2.1.1 p.2.1.1 x
  have c1 := pdist_comm a p'.2.1.1
  have hax : pdist a x ≤ 45 * ell + 4 := by omega
  have hbelow : 45 * ell + 4 ≤ R * bigSide M ell (1 - 1) := by
    show 45 * ell + 4 ≤ R * (M * ell ^ (1 - 1))
    simpa using hRM
  exact ball_mem_below hS (j := 1) le_rfl hk haj hbelow x hax

/-- level-0 rows of `Q` do not see the configuration -/
theorem Qfull_lev0 {L : PeriodicLatticeExtent} (G : TowerGeom L) (V : Cfg L) (A : BondFnL2 L) (q : BIdx G)
    (h0 : (q.1 : ℕ) = 0) : (bondSectorOf G V).Qfull A q = A q.2.1 := by
  have key : ∀ j : ℕ, j = 0 → ∀ b : Bond L, (((G.ell : ℝ) ^ j)⁻¹) • (WithLp.ofLp (QlinB G V j A)) b = A b := by
    intro j hj b
    subst hj
    rw [QlinB_zero, pow_zero, inv_one, one_smul]
  exact key _ h0 q.2.1

/-- **at an exit row, `Q_V ψ_p = Q_1 ψ_p` for every `V`** -/
theorem Q_exit (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hroom : 17 * ell ≤ R * M)
    (hRM : 45 * ell + 4 ≤ R * M) (p : BIdx (geomOf ell k S)) (hp0 : (p.1 : ℕ) = 0)
    (hex : ¬ Ball p.2.1.1 (36 * ell) ⊆ S.Om 0) (V : Cfg (scaleUp ell k Lu)) (w : SuTwo) :
    (bondSectorOf (geomOf ell k S) V).Qfull (psiL (by omega) p w)
      = (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (psiL (by omega) p w) := by
  refine PiLp.ext (fun p' => ?_)
  by_cases hI : Inter p' p
  · have h0 := lev1_not_inter hS hRM p p' hp0 hex hI
    rw [Qfull_lev0 _ _ _ p' h0, Qfull_lev0 _ _ _ p' h0]
  · rw [Qfull_zero_of_not_inter hell2 hS hM hroom V p p' hI w,
      Qfull_zero_of_not_inter hell2 hS hM hroom (trivialU _) p p' hI w]

/-- **the W6 per-source bounds for every row**: chart rows by `source_bounds`, exit rows by `Q_exit` + `flat_F` -/
theorem srcOK_rows (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R)
    (hroom : 17 * ell ≤ R * M) (hRM : 45 * ell + 4 ≤ R * M) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (ε : ℕ → ℕ → ℝ)
    (hγ : ∀ p : BIdx (geomOf ell k S), ((p.1 : ℕ) = 0 → Ball p.2.1.1 (36 * ell) ⊆ S.Om 0) →
      ∀ j' : ℕ, (p.1 : ℕ) ≤ j' + 1 → j' ≤ (p.1 : ℕ) + 1 → ∀ l, l < k → l < j' →
        ∀ z ∈ Ball p.2.1.1 (20 * ell ^ ((p.1 : ℕ) + 1)), z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
          frobNorm (((bgTower (GF ell k Lu) (periodicGaugeTransform (γ p) U) l (z, μ) : SU2) : M2) - 1) ≤ ε j' l)
    (hε0 : ∀ j' l, l < k → 0 ≤ ε j' l) (hsm : ∀ j' l, l < k → rhoOf ell (ε j' l) < Real.pi / 2)
    (hr : ∀ j' l, l < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j' l) < r0)
    (Sstar : ℝ) (hSstar : ∀ j' : ℕ, j' ≤ k → ∑ l ∈ range j', thetaOf ell (ε j' l) ≤ Sstar) :
    SrcOK (by omega) U γ (3 * delStar ell Sstar ^ 2 * CE) (3 * (Real.exp (Sstar / rr ell)) ^ 2 * CE) := by
  have hell : 0 < ell := by omega
  have hCE := CE_pos
  have hT1 : ∀ (p : BIdx (geomOf ell k S)) (w : SuTwo), nF (Tvec hell U γ p w)
      = nF ((bondSectorOf (geomOf ell k S) (periodicGaugeTransform (γ p) U)).Qfull
          (psiL hell p (RMap ((γ p) p.2.1.1) w))) := by
    intro p w
    have : Tvec hell U γ p w = WithLp.toLp 2 (fun p' : BIdx (geomOf ell k S) =>
        RMap (((γ p) p'.2.1.1)⁻¹) (((bondSectorOf (geomOf ell k S) (periodicGaugeTransform (γ p) U)).Qfull
        (psiL hell p (RMap ((γ p) p.2.1.1) w))) p')) := PiLp.ext (fun p' => Tvec_eq hell U γ p p' w)
    rw [this]
    exact nF_rot hell (fun p' => ((γ p) p'.2.1.1)⁻¹) _
  intro p w
  by_cases hne : (p.1 : ℕ) = 0 → Ball p.2.1.1 (36 * ell) ⊆ S.Om 0
  · have hcl := hγ p hne
    constructor
    · have h1 : nF (Dvec hell U γ p w) = nF (Dfun hell U γ p (RMap ((γ p) p.2.1.1) w)) :=
        nF_rot hell (fun p' => ((γ p) p'.2.1.1)⁻¹) _
      rw [h1]
      have h2 := (source_bounds hell2 hS hM hroom (periodicGaugeTransform (γ p) U) p ε hcl hε0 hsm hr Sstar hSstar
        (RMap ((γ p) p.2.1.1) w)).1
      have h3 := psiL_norm_sq hell hell2 hS p (RMap ((γ p) p.2.1.1) w)
      rw [norm_RMap] at h3
      have h4 : 0 ≤ 3 * delStar ell Sstar ^ 2 := by positivity
      calc _ ≤ _ := h2
        _ ≤ 3 * delStar ell Sstar ^ 2 * (CE * (wF p * ‖w‖ ^ 2)) := mul_le_mul_of_nonneg_left h3 h4
        _ = _ := by ring
    · rw [hT1]
      have h2 := (source_bounds hell2 hS hM hroom (periodicGaugeTransform (γ p) U) p ε hcl hε0 hsm hr Sstar hSstar
        (RMap ((γ p) p.2.1.1) w)).2
      have h3 := psiL_norm_sq hell hell2 hS p (RMap ((γ p) p.2.1.1) w)
      rw [norm_RMap] at h3
      have h4 : 0 ≤ 3 * (Real.exp (Sstar / rr ell)) ^ 2 := by positivity
      calc _ ≤ _ := h2
        _ ≤ 3 * (Real.exp (Sstar / rr ell)) ^ 2 * (CE * (wF p * ‖w‖ ^ 2)) := mul_le_mul_of_nonneg_left h3 h4
        _ = _ := by ring
  · have hp0 : (p.1 : ℕ) = 0 := by
      by_contra h; exact hne (fun h' => absurd h' h)
    have hex : ¬ Ball p.2.1.1 (36 * ell) ⊆ S.Om 0 := fun h => hne (fun _ => h)
    have hQ := fun V => Q_exit hell2 hS hM hroom hRM p hp0 hex V (RMap ((γ p) p.2.1.1) w)
    have hwF : 0 ≤ wF p * ‖w‖ ^ 2 := by unfold AdalyFormal.W6.wF; positivity
    constructor
    · have hD : Dvec hell U γ p w = 0 := by
        refine PiLp.ext (fun p' => ?_)
        show RMap _ ((Dfun hell U γ p (RMap ((γ p) p.2.1.1) w)) p') = _
        unfold Dfun
        rw [hQ (periodicGaugeTransform (γ p) U), sub_self]
        simp
      rw [hD]
      have h0 : nF (0 : FSp (geomOf ell k S)) = 0 := by unfold nF; simp
      rw [h0]
      positivity
    · rw [hT1, hQ (periodicGaugeTransform (γ p) U)]
      have h3 : nF ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (psiL hell p (RMap ((γ p) p.2.1.1) w)))
          ≤ 3 * ‖psiL hell p (RMap ((γ p) p.2.1.1) w)‖ ^ 2 := flat_F hell2 hS hM hR _
      have h4 := psiL_norm_sq hell hell2 hS p (RMap ((γ p) p.2.1.1) w)
      rw [norm_RMap] at h4
      have hS0 : 0 ≤ Sstar := by have := hSstar 0 (Nat.zero_le _); simpa using this
      have hrr := AdalyFormal.OneGap.rr_pos ell hell
      have he1 : 1 ≤ Real.exp (Sstar / rr ell) := Real.one_le_exp (div_nonneg hS0 hrr.le)
      have he : 1 ≤ (Real.exp (Sstar / rr ell)) ^ 2 := one_le_pow₀ he1
      have h5 : 3 * CE * (wF p * ‖w‖ ^ 2) ≤ 3 * (Real.exp (Sstar / rr ell)) ^ 2 * CE * (wF p * ‖w‖ ^ 2) := by
        have : 0 ≤ CE * (wF p * ‖w‖ ^ 2) := by positivity
        nlinarith
      nlinarith

/-- the fine-link closeness at blocked level `0` -/
theorem epsC_fine (hell : 0 < ell) {ρ : ℝ} (hρ : 0 ≤ ρ) (j : ℕ) (hj : 1 ≤ j) :
    epsC ell ρ (j + 1) 0 ≤ (1 + 3 * Real.pi) * ρ * ell * ((ell : ℝ) ^ j)⁻¹ := by
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  unfold epsC
  rw [if_pos (by omega)]
  have e : j + 1 - 2 = j - 1 := by omega
  rw [e]
  have hj' : (ell : ℝ) ^ j = ell * (ell : ℝ) ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
  have h2 : (ell : ℝ) ^ (2 * (j - 1)) = ((ell : ℝ) ^ (j - 1)) ^ 2 := by ring
  rw [hj', h2]
  set a : ℝ := (ell : ℝ) ^ (j - 1) with ha
  have ha1 : 1 ≤ a := one_le_pow₀ hl1
  have ha0 : 0 < a := by linarith
  simp only [pow_zero, one_mul]
  have h3 : ρ / a ^ 2 ≤ ρ / a := div_le_div_of_nonneg_left hρ ha0 (by nlinarith)
  have hpi := Real.pi_pos
  have e2 : (1 + 3 * Real.pi) * ρ * ell * ((ell : ℝ) * a)⁻¹ = (1 + 3 * Real.pi) * (ρ / a) := by
    have : (ell : ℝ) ≠ 0 := by positivity
    field_simp
  rw [e2]
  nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 3 * Real.pi)]

/-- **fine-link closeness of the row gauges** (rows of level `≥ 1`) -/
theorem fineOK_rows (hell2 : 2 ≤ ell) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hγ : ∀ p : BIdx (geomOf ell k S), ((p.1 : ℕ) = 0 → Ball p.2.1.1 (36 * ell) ⊆ S.Om 0) →
      ∀ j' : ℕ, (p.1 : ℕ) ≤ j' + 1 → j' ≤ (p.1 : ℕ) + 1 → ∀ l, l < k → l < j' →
        ∀ z ∈ Ball p.2.1.1 (20 * ell ^ ((p.1 : ℕ) + 1)), z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
          frobNorm (((bgTower (GF ell k Lu) (periodicGaugeTransform (γ p) U) l (z, μ) : SU2) : M2) - 1)
            ≤ epsC ell ρ j' l) :
    FineOK U γ ((1 + 3 * Real.pi) * ρ * ell) := by
  have hell : 0 < ell := by omega
  intro p hp x hx μ
  have hk : 0 < k := by
    have h := p.1.isLt
    have e : (geomOf ell k S).k = k := rfl
    omega
  have hcl := hγ p (fun h => absurd h (by omega))
  have hz : x ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ 0) := by
    rw [pow_zero]; exact mem_CoarseLattice.mpr (fun μ => Nat.mod_one _)
  have h := hcl ((p.1 : ℕ) + 1) (by omega) le_rfl 0 hk (by omega) x hx hz μ
  have h' : frobNorm (((periodicGaugeTransform (γ p) U (x, μ) : SU2) : M2) - 1)
      ≤ epsC ell ρ ((p.1 : ℕ) + 1) 0 := h
  exact h'.trans (epsC_fine hell hρ _ hp)

/-- **gauges at the printed class**: `SrcOK` and `FineOK` from the ball charts -/
theorem gauges_of_balls (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 73 * ell + 2 ≤ M) (hR37 : 37 * ell ^ 2 ≤ R)
    (hR : 8 * ell ≤ R) (hroom : 17 * ell ≤ R * M) (hRM : 45 * ell + 4 ≤ R * M) (hT3 : ∀ μ, 3 ≤ Lu μ + 1)
    {C α₀ η : ℝ} (hη : 0 < η) (hα0 : 0 ≤ C * α₀)
    (ha1 : ((12 : ℕ) : ℝ) * M * (C * α₀) ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 4 * ((4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀))) ≤ 1)
    {U : LinkCfg (scaleUp ell k Lu)} (hB : BallChartsAt ell M k S U C α₀ η)
    (hsm' : ∀ j' l : ℕ, rhoOf ell (epsC ell ((4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀))) j' l) < Real.pi / 2)
    (hr' : ∀ j' l : ℕ, Real.pi / 2 * ((loopFactorBound ell : ℝ) *
      epsC ell ((4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀))) j' l) < r0)
    (Sstar : ℝ) (hsum : ∀ j' : ℕ, ∑ l ∈ range j',
      thetaOf ell (epsC ell ((4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀))) j' l) ≤ Sstar) :
    ∃ γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu),
      SrcOK (by omega) U γ (3 * delStar ell Sstar ^ 2 * CE) (3 * (Real.exp (Sstar / rr ell)) ^ 2 * CE) ∧
      FineOK U γ ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀))) * ell) := by
  classical
  have hell : 0 < ell := by omega
  have hM0 : 0 < M := by omega
  have key : ∀ p : BIdx (geomOf ell k S), ∃ g : GaugeFn (scaleUp ell k Lu),
      ((p.1 : ℕ) = 0 → Ball p.2.1.1 (36 * ell) ⊆ S.Om 0) →
      ∀ j' : ℕ, (p.1 : ℕ) ≤ j' + 1 → j' ≤ (p.1 : ℕ) + 1 → ∀ l, l < k → l < j' →
        ∀ z ∈ Ball p.2.1.1 (20 * ell ^ ((p.1 : ℕ) + 1)), z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
          frobNorm (((bgTower (GF ell k Lu) (periodicGaugeTransform g U) l (z, μ) : SU2) : M2) - 1)
            ≤ epsC ell ((4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀))) j' l := by
    intro p
    by_cases h : (p.1 : ℕ) = 0 → Ball p.2.1.1 (36 * ell) ⊆ S.Om 0
    · obtain ⟨g, hg⟩ := rowGauge_ne hell2 hS hM hR37 hT3 hη hα0 ha1 hsm4 hB p h
      exact ⟨g, fun _ => hg⟩
    · exact ⟨fun _ => 1, fun h' => absurd h' h⟩
  choose γ hγ using key
  have hρ0 : 0 ≤ (4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * (C * α₀)) := by
    have := Real.pi_pos; positivity
  exact ⟨γ, srcOK_rows hell2 hS hM0 hR hroom hRM U γ _ hγ (fun j' l _ => epsC_nonneg ell hρ0 j' l)
    (fun j' l _ => hsm' j' l) (fun j' l _ => hr' j' l) Sstar (fun j' _ => hsum j'),
    fineOK_rows hell2 U γ hρ0 hγ⟩

end rows

end AdalyFormal.M2RightInv

#print axioms AdalyFormal.M2RightInv.rowChart_ne
#print axioms AdalyFormal.M2RightInv.rowGauge_ne
#print axioms AdalyFormal.M2RightInv.lev1_not_inter
#print axioms AdalyFormal.M2RightInv.Qfull_lev0
#print axioms AdalyFormal.M2RightInv.Q_exit
#print axioms AdalyFormal.M2RightInv.srcOK_rows
#print axioms AdalyFormal.M2RightInv.epsC_fine
#print axioms AdalyFormal.M2RightInv.fineOK_rows
#print axioms AdalyFormal.M2RightInv.gauges_of_balls
