import DX4
import DX3
import DK5

/-!
# DX5 -- the SECOND clause of `DLayerStrat` on the whole M1 regime, constants `k`-free (M1 D-layer lane, 2026-10-14)

* `clause2_ungauge` : the `hJ` form at `U^γ` gives it at `U` (r8-transfer `genFormHyps_gauge`: `H₁in`, `D̃⁽²⁾`, `J` are
  gauge covariant and `adBL` is an isometry);
* `delN_le` : the two `Δ⁽²⁾` constants are `≤ Cδ · 12Mα₀` with a `k`-free `Cδ`;
* **`clause2_M1`** : for `ℓ ≥ 2`, `a > 0`, a W4 constant `cw > 0` there are `C ≥ 0`, `N₀`, `t₀ > 0` such that for every
  `k`, `Lu` (`TorusOK`, `5 ≤ N_u`), admissible `S`, `M, R` (`8ℓ ≤ R`, `18ℓ ≤ RM`, `N₀ ≤ RM`), `0 < α₀`, `12Mα₀ ≤ t₀`,
  `Λ` (`LambdaOK2`), `U ∈ M1Regular`, with W4 at `U`:
  `|⟪H₁in(D̃⁽²⁾B), J⟫| ≤ C · (12Mα₀) · ‖B‖²` for every unit-bond field `B`.
Named input: W4 at `U` with the FIXED constant `cw`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (rho1 SstarM)
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.M1 (M1Regular M1Bounds wnormSq)
open AdalyFormal.M1DStrat.DQ
open AdalyFormal.M1GaugeW4 (rhoT)

/-- **the `hJ` form is gauge invariant** -/
theorem clause2_ungauge (P : IngrBParams) (γ : GaugeFn P.Lf) (C : ℝ)
    (h : ∀ B : BondFnL2 P.Lu,
      |⟪({ P with U := periodicGaugeTransform γ P.U } : IngrBParams).H1in
          (({ P with U := periodicGaugeTransform γ P.U } : IngrBParams).D2in B),
        ({ P with U := periodicGaugeTransform γ P.U } : IngrBParams).Jf⟫| ≤ C * ‖B‖ ^ 2)
    (B : BondFnL2 P.Lu) : |⟪P.H1in (P.D2in B), P.Jf⟫| ≤ C * ‖B‖ ^ 2 := by
  have hG := AdalyFormal.GaugeCov.genFormHyps_gauge P γ
  have h1 := h (AdalyFormal.GaugeCov.adBL (AdalyFormal.GaugeCov.uOf P.ell P.k P.Lu P.hell γ) B)
  rw [hG.D2, hG.H1in, hG.base.J, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map] at h1
  exact h1

/-- the `Δ⁽²⁾` constants are linear in the amplitude -/
theorem delN_le (ell : ℕ) (a θ CH t K2 kW Ω Kβ KWb Ωm : ℝ) (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hCH : 0 ≤ CH) (ht : 0 ≤ t)
    (hK2 : 0 ≤ K2) (hK : K2 ≤ Kβ) (hkW : kW ^ 2 ≤ KWb) (hΩ : Ω ≤ Ωm) (hCg : 0 ≤ Cgeo ell θ) :
    delN ell a θ CH t K2 kW Ω
      ≤ (2 * (Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH) * (400 * (ell : ℝ) ^ 3) * Kβ * Real.exp (2 * Ωm)
          * 44217 * ((ell : ℝ) ^ 2 * KWb)) * t := by
  unfold delN
  have hs : 0 ≤ Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) := Real.sqrt_nonneg _
  have he : Real.exp (2 * Ω) ≤ Real.exp (2 * Ωm) := Real.exp_le_exp.mpr (by linarith)
  have hk2 : ((ell : ℝ) * kW) ^ 2 ≤ (ell : ℝ) ^ 2 * KWb := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hkW (by positivity)
  have hP : 0 ≤ 2 * (Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH) * (400 * (ell : ℝ) ^ 3) * t := by positivity
  have hm1 : K2 * Real.exp (2 * Ω) ≤ Kβ * Real.exp (2 * Ωm) :=
    mul_le_mul hK he (Real.exp_pos _).le (hK2.trans hK)
  have hm2 : K2 * Real.exp (2 * Ω) * (44217 * ((ell : ℝ) * kW) ^ 2)
      ≤ Kβ * Real.exp (2 * Ωm) * (44217 * ((ell : ℝ) ^ 2 * KWb)) :=
    mul_le_mul hm1 (by linarith) (by positivity) (mul_nonneg (hK2.trans hK) (Real.exp_pos _).le)
  calc 2 * ((Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH) * (400 * (ell : ℝ) ^ 3 * t)) * K2 * Real.exp (2 * Ω)
        * 44217 * ((ell : ℝ) * kW) ^ 2
      = (2 * (Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH) * (400 * (ell : ℝ) ^ 3) * t)
        * (K2 * Real.exp (2 * Ω) * (44217 * ((ell : ℝ) * kW) ^ 2)) := by ring
    _ ≤ (2 * (Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH) * (400 * (ell : ℝ) ^ 3) * t)
        * (Kβ * Real.exp (2 * Ωm) * (44217 * ((ell : ℝ) ^ 2 * KWb))) := mul_le_mul_of_nonneg_left hm2 hP
    _ = _ := by ring

/-- **the second D-layer clause on the M1 regime** -/
theorem clause2_M1 {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) {cw : ℝ} (hcw : 0 < cw) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∃ t₀ : ℝ, 0 < t₀ ∧
    ∀ {M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ} (hell0 : 0 < ell),
      Admissible ell M R k S → 0 < M → 8 * ell ≤ R → 18 * ell ≤ R * M → N₀ ≤ R * M →
      (∀ μ, 5 ≤ Lu μ + 1) → TorusOK ell M Lu → 0 < α₀ → (12 : ℝ) * M * α₀ ≤ t₀ →
      ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
      ∀ (U : LinkCfg (scaleUp ell k Lu)), M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      (∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G),
        cw * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫) →
      ∀ Bt : BondFnL2 Lu,
        |⟪(gparams ell k Lu hell0 S U a Lam).H1in ((gparams ell k Lu hell0 S U a Lam).D2in Bt),
          (gparams ell k Lu hell0 S U a Lam).Jf⟫| ≤ C * ((12 : ℝ) * M * α₀) * ‖Bt‖ ^ 2 := by
  obtain ⟨CHb, hCHb, CWb, hCWb, KWb, hKWb, CH1b, hCH1b, δ, hδ, hball⟩ := num_ball2 hell ha hcw
  obtain ⟨β₀, hβ₀, hDQall⟩ := dqSmall_exists ell hell
  have hl1 : 1 ≤ ell := by omega
  have hlR : (1 : ℝ) ≤ ell := by exact_mod_cast hl1
  have hlg : 0 ≤ Real.log ell := Real.log_nonneg hlR
  set θ : ℝ := δ / 2 with hθdef
  have hθ : 0 < θ := by positivity
  have hpi : (0 : ℝ) < 4 * Real.pi + 4 := by have := Real.pi_pos; positivity
  have hDQβ := hDQall β₀ hβ₀.le le_rfl
  have hKβ : 0 ≤ K2strat ell β₀ := by
    unfold K2strat
    have := K2free_nonneg ell ((1 + 3 * Real.pi) * alphaQ ell β₀) (thetaK2_lt_of ell _ hDQβ.hK2c)
    positivity
  have hCg : 0 ≤ Cgeo ell θ := by unfold Cgeo; positivity
  set Cδ : ℝ := 2 * (Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CHb) * (400 * (ell : ℝ) ^ 3) * K2strat ell β₀
    * Real.exp (2 * (32 * θ * ell)) * 44217 * ((ell : ℝ) ^ 2 * KWb) with hCδ
  have hCδ0 : 0 ≤ Cδ := by positivity
  have hb0 := AdalyFormal.M1DK.beta0_pos ell (by omega)
  set t₀ : ℝ := min β₀ (min (1 / 4) (min (δ / (2 * (4 * Real.pi + 4)))
    (min (δ / (2 * (Cδ + 1))) (AdalyFormal.M1DK.beta0 ell)))) with ht₀
  have ht₀0 : 0 < t₀ := lt_min hβ₀ (lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) hb0)))
  set B : ℝ := max (2 * (ell : ℝ) ^ 2 * Real.log ell / δ)
    (max (3 * (ell : ℝ) * Real.log ell / δ) (Real.log (2 * (ell : ℝ) ^ 3) / θ)) with hBdef
  refine ⟨Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH1b * (400 * (ell : ℝ) ^ 3)
      * AdalyFormal.DLayer.KDfree ell, by have := AdalyFormal.M1DK.KDfree_nonneg ell; positivity,
    Nat.ceil B + 1, t₀, ht₀0, ?_⟩
  intro M R k Lu S α₀ hell0 hS hM hR8 hroom hN₀ hLu5 hT hα0 ht Lam hLam U hreg hW4 Bt
  have hLu : ∀ μ, ell < Lu μ + 1 := hT.2.1
  obtain ⟨g, A, hU, hB⟩ := hreg
  have hα0' : 0 ≤ α₀ := hα0.le
  -- the four coordinates
  have ht14 : (12 : ℝ) * M * α₀ ≤ 1 / 4 := ht.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htδ : (12 : ℝ) * M * α₀ ≤ δ / (2 * (4 * Real.pi + 4)) :=
    ht.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr_eq : rho1 12 M α₀ = (4 * Real.pi + 4) * ((12 : ℝ) * M * α₀) := by unfold rho1; push_cast; ring
  have hr0 : 0 ≤ rho1 12 M α₀ := by rw [hr_eq]; positivity
  have hrδ : rho1 12 M α₀ < δ := by
    rw [hr_eq]
    have h1 : (4 * Real.pi + 4) * ((12 : ℝ) * M * α₀) ≤ (4 * Real.pi + 4) * (δ / (2 * (4 * Real.pi + 4))) :=
      mul_le_mul_of_nonneg_left htδ hpi.le
    have h2 : (4 * Real.pi + 4) * (δ / (2 * (4 * Real.pi + 4))) = δ / 2 := by field_simp
    linarith
  have hRM1 : B < (R : ℝ) * M := by
    have h1 := Nat.le_ceil B
    have h2 : ((Nat.ceil B + 1 : ℕ) : ℝ) ≤ ((R * M : ℕ) : ℝ) := by exact_mod_cast hN₀
    push_cast at h2
    linarith
  have hW1 : 1 ≤ R * M * ell := by
    have : 1 ≤ R * M := le_trans (by omega) hN₀
    nlinarith
  have hWpos : (0 : ℝ) < ((R * M * ell : ℕ) : ℝ) := by exact_mod_cast (show 0 < R * M * ell by omega)
  have hWge : (R : ℝ) * M ≤ ((R * M * ell : ℕ) : ℝ) := by
    have e : ((R * M * ell : ℕ) : ℝ) = (R : ℝ) * M * ell := by push_cast; ring
    rw [e]; exact le_mul_of_one_le_right (by positivity) hlR
  have hpδ : 2 * (ell : ℝ) ^ 2 * Real.log ell / ((R * M * ell : ℕ) : ℝ) < δ := by
    rw [div_lt_iff₀ hWpos]
    have h1 : 2 * (ell : ℝ) ^ 2 * Real.log ell / δ < ((R * M * ell : ℕ) : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hRM1 hWge)
    rw [div_lt_iff₀ hδ] at h1; linarith
  have hqδ : 3 * (ell : ℝ) * Real.log ell / ((R * M * ell : ℕ) : ℝ) < δ := by
    rw [div_lt_iff₀ hWpos]
    have h1 : 3 * (ell : ℝ) * Real.log ell / δ < ((R * M * ell : ℕ) : ℝ) :=
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) (lt_of_lt_of_le hRM1 hWge)
    rw [div_lt_iff₀ hδ] at h1; linarith
  have hp0 : 0 ≤ 2 * (ell : ℝ) ^ 2 * Real.log ell / ((R * M * ell : ℕ) : ℝ) := by positivity
  have hq0 : 0 ≤ 3 * (ell : ℝ) * Real.log ell / ((R * M * ell : ℕ) : ℝ) := by positivity
  have hdist : dist ((θ, rho1 12 M α₀, 2 * (ell : ℝ) ^ 2 * Real.log ell / ((R * M * ell : ℕ) : ℝ),
      3 * (ell : ℝ) * Real.log ell / ((R * M * ell : ℕ) : ℝ)) : ℝ × ℝ × ℝ × ℝ) 0 < δ := by
    rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
    simp only [Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero]
    rw [abs_of_pos hθ, abs_of_nonneg hr0, abs_of_nonneg hp0, abs_of_nonneg hq0]
    exact max_lt (by rw [hθdef]; linarith) (max_lt hrδ (max_lt hpδ hqδ))
  -- the clause-2 coordinates
  have htβ : (12 : ℝ) * M * α₀ ≤ β₀ := ht.trans (min_le_left _ _)
  have htC : (12 : ℝ) * M * α₀ ≤ δ / (2 * (Cδ + 1)) :=
    ht.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have htK : (12 : ℝ) * M * α₀ ≤ AdalyFormal.M1DK.beta0 ell :=
    ht.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have ht0 : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
  have hDQt := hDQall _ ht0 htβ
  have hK2t : 0 ≤ (K2strat ell (12 * M * α₀)) := by
    unfold K2strat
    have := K2free_nonneg ell ((1 + 3 * Real.pi) * alphaQ ell (12 * M * α₀)) (thetaK2_lt_of ell _ hDQt.hK2c)
    positivity
  have hKle := K2strat_mono ell hl1 ht0 htβ hDQβ
  -- the clause-1 ball at `(x, 0)` gives the `kW` bound
  have hz0 : dist ((((θ, rho1 12 M α₀, 2 * (ell : ℝ) ^ 2 * Real.log ell / ((R * M * ell : ℕ) : ℝ), 3 * (ell : ℝ) * Real.log ell / ((R * M * ell : ℕ) : ℝ)) : ℝ × ℝ × ℝ × ℝ), ((0 : ℝ), (0 : ℝ))) : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)) 0 < δ := by
    rw [Prod.dist_eq]
    refine max_lt hdist ?_
    show dist ((0 : ℝ), (0 : ℝ)) (0 : ℝ × ℝ) < δ
    rw [Prod.dist_eq]
    simp only [Prod.fst_zero, Prod.snd_zero, dist_self, max_self]
    exact hδ
  obtain ⟨-, hkW0, -⟩ := hball _ hz0
  have hkWb : (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell (R * M * ell) θ) (DeN ell (R * M * ell) θ) (gamN ell (R * M * ell) a (rhoT ell 12 M α₀))) ^ 2 ≤ KWb := hkW0.le
  have hd0 := delN_le ell a θ CHb ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell (R * M * ell) θ) (DeN ell (R * M * ell) θ) (gamN ell (R * M * ell) a (rhoT ell 12 M α₀))) 0 (K2strat ell β₀) KWb (32 * θ * ell)
    ha.le hθ.le hCHb ht0 hK2t hKle hkWb (by positivity) hCg
  have hd1 := delN_le ell a θ CHb ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell (R * M * ell) θ) (DeN ell (R * M * ell) θ) (gamN ell (R * M * ell) a (rhoT ell 12 M α₀))) (32 * θ * ell) (K2strat ell β₀) KWb
    (32 * θ * ell) ha.le hθ.le hCHb ht0 hK2t hKle hkWb le_rfl hCg
  have hCt : Cδ * ((12 : ℝ) * M * α₀) < δ := by
    have h1 : Cδ * ((12 : ℝ) * M * α₀) ≤ Cδ * (δ / (2 * (Cδ + 1))) := mul_le_mul_of_nonneg_left htC hCδ0
    have h2 : Cδ * (δ / (2 * (Cδ + 1))) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have hδ0 : 0 ≤ (delN ell a θ CHb ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell (R * M * ell) θ) (DeN ell (R * M * ell) θ) (gamN ell (R * M * ell) a (rhoT ell 12 M α₀))) 0) := by unfold delN; positivity
  have hδ1 : 0 ≤ (delN ell a θ CHb ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell (R * M * ell) θ) (DeN ell (R * M * ell) θ) (gamN ell (R * M * ell) a (rhoT ell 12 M α₀))) (32 * θ * ell)) := by unfold delN; positivity
  have hzd : dist ((((θ, rho1 12 M α₀, 2 * (ell : ℝ) ^ 2 * Real.log ell / ((R * M * ell : ℕ) : ℝ), 3 * (ell : ℝ) * Real.log ell / ((R * M * ell : ℕ) : ℝ)) : ℝ × ℝ × ℝ × ℝ), ((delN ell a θ CHb ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell (R * M * ell) θ) (DeN ell (R * M * ell) θ) (gamN ell (R * M * ell) a (rhoT ell 12 M α₀))) 0), (delN ell a θ CHb ((12 : ℝ) * M * α₀) (K2strat ell (12 * M * α₀)) (kWcN ell a (csOf a (rhoT ell 12 M α₀)) (ThN ell (R * M * ell) θ) (DeN ell (R * M * ell) θ) (gamN ell (R * M * ell) a (rhoT ell 12 M α₀))) (32 * θ * ell)))) : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)) 0 < δ := by
    rw [Prod.dist_eq]
    refine max_lt hdist ?_
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · show dist _ (0 : ℝ) < δ
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hδ0]; exact lt_of_le_of_lt hd0 hCt
    · show dist _ (0 : ℝ) < δ
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hδ1]; exact lt_of_le_of_lt hd1 hCt
  obtain ⟨⟨N1, N2, N3, N4, N5, N6, N7, N8, N9, N10, N11, N12, N13, N14, N15, N16⟩, -, hlt, hκ1, hEN1, hCH1⟩ :=
    hball _ hzd
  have hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2 := by
    refine exp_tail ell hl1 θ hθ _ ?_
    have h1 : Real.log (2 * (ell : ℝ) ^ 3) / θ ≤ B := (le_max_right _ _).trans (le_max_right _ _)
    linarith
  have hW4V := coercive_to_gauge hell0 S a Lam U g cw hW4
  -- `M1Regular` at `V = U^g` (trivial gauge) and the `D̃⁽²⁾` bound there
  have hUV : M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ (periodicGaugeTransform g U) := by
    refine ⟨fun _ => 1, A, fun e => ?_, hB⟩
    have e1 : periodicGaugeTransform (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) (periodicGaugeTransform g U) e
        = periodicGaugeTransform g U e := by simp [periodicGaugeTransform]
    rw [e1]; exact hU e
  have hKD : ∀ Bt' : BondFnL2 Lu, ∑ e, ‖((gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam).D2in Bt') e‖
      ≤ AdalyFormal.DLayer.KDfree ell * ‖Bt'‖ ^ 2 := fun Bt' =>
    AdalyFormal.M1DK.D2in_l1_M1' ell M R k Lu hell0 S (periodicGaugeTransform g U) a Lam α₀ hS hell (by omega) hT hLam hUV
      hα0' htK Bt'
  have hV := clause2_Ug (W := R * M * ell) hell hS hroom hM hR8 hLu5 hW1 le_rfl U g A hU hB hα0'
    (ht14.trans (by norm_num)) N6.le a ha θ hθ N1.le N2.le N3.le N4.le N5 N7.le N8 N9 N10.le 1 one_pos hLu
    (by linarith) hDQt cw hcw N11.le N12 N13 (sub_pos.mpr N14) CHb hCHb N15.le hq
    (AdalyFormal.DLayer.KDfree ell) (AdalyFormal.M1DK.KDfree_nonneg ell) CH1b hCH1b (by linarith) hκ1
    (sub_pos.mpr hEN1) hCH1.le Lam hW4V hKD
  have hU0 := clause2_ungauge (gparams ell k Lu hell0 S U a Lam) g _ hV Bt
  refine hU0.trans (le_of_eq ?_)
  ring

#print axioms clause2_ungauge
#print axioms delN_le
#print axioms clause2_M1

end AdalyFormal.M1DStrat
