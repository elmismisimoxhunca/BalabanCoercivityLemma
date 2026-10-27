import DX2
import DN2

/-!
# DX3 -- the FIRST clause of `DLayerStrat` on the whole M1 regime, constants `k`-free (M1 D-layer lane, 2026-10-14)

* **`clause1_M1`** : for `ℓ ≥ 2`, `a > 0` and a W4 constant `cw > 0` there are `C ≥ 0`, `N₀`, `t₀ > 0` such that for
  EVERY `k`, `Lu`, admissible `S`, `M, R` with `8ℓ ≤ R`, `18ℓ ≤ RM`, `N₀ ≤ RM` (and the torus sizes), every `α₀ ≥ 0`
  with `12 M α₀ ≤ t₀`, every `U` in `M1Regular … 12 … α₀ ℓ^{-k}`, every `Λ`: IF W4 holds at `U` with constant `cw`, THEN
  `|⟪A, Δ⁽²⁾ A⟫| ≤ C · (12 M α₀) · wnormSq A` for every `A ∈ E₀`.
* **`clause1_eps`** : the same with any prescribed tolerance `ε₂ > 0` in place of `C·12Mα₀` (smaller `t₀`).
Named input: W4 at `U` with the FIXED constant `cw` (not derived here).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (rho1 SstarM)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1 (M1Regular wnormSq)
open AdalyFormal.M1DStrat.DQ
open AdalyFormal.M1GaugeW4 (rhoT)

theorem wnormSq_nonneg' {L : PeriodicLatticeExtent} {ell k : ℕ} (S : Tower L) (x : BondFnL2 L) :
    0 ≤ wnormSq S ell k x := by
  unfold wnormSq; exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- the output constant is linear in `12 M α₀` -/
theorem eps2N_le (ell M W : ℕ) (hell : 1 ≤ ell) (a θ α₀ CH cs γ CWb : ℝ) (ha : 0 ≤ a) (hCH : 0 ≤ CH) (hα0 : 0 ≤ α₀)
    (t₀ : ℝ) (ht : (12 : ℝ) * M * α₀ ≤ t₀) (hDQt : DQSmall ell (12 * M * α₀)) (hDQ : DQSmall ell t₀)
    (hCW : CWcN ell W a cs γ ^ 2 ≤ CWb) :
    eps2N ell M W a θ α₀ CH cs γ
      ≤ (2 * (Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH) * (400 * (ell : ℝ) ^ 3) * K2strat ell t₀
          * ((ell : ℝ) ^ 2 * CWb)) * ((12 : ℝ) * M * α₀) := by
  have ht0 : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
  have hK := K2strat_mono ell hell ht0 ht hDQ
  have hK0 : 0 ≤ K2strat ell (12 * M * α₀) := by
    unfold K2strat
    have := K2free_nonneg ell ((1 + 3 * Real.pi) * alphaQ ell (12 * M * α₀)) (thetaK2_lt_of ell _ hDQt.hK2c)
    positivity
  have hP : 0 ≤ 2 * (Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH) * (400 * (ell : ℝ) ^ 3)
      * ((ell : ℝ) ^ 2) * ((12 : ℝ) * M * α₀) := by positivity
  have hm : K2strat ell (12 * M * α₀) * CWcN ell W a cs γ ^ 2 ≤ K2strat ell t₀ * CWb :=
    mul_le_mul hK hCW (sq_nonneg _) (hK0.trans hK)
  have e1 : eps2N ell M W a θ α₀ CH cs γ
      = (2 * (Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH) * (400 * (ell : ℝ) ^ 3)
          * ((ell : ℝ) ^ 2) * ((12 : ℝ) * M * α₀)) * (K2strat ell (12 * M * α₀) * CWcN ell W a cs γ ^ 2) := by
    unfold eps2N; ring
  have e2 : (2 * (Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH) * (400 * (ell : ℝ) ^ 3) * K2strat ell t₀
          * ((ell : ℝ) ^ 2 * CWb)) * ((12 : ℝ) * M * α₀)
      = (2 * (Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH) * (400 * (ell : ℝ) ^ 3)
          * ((ell : ℝ) ^ 2) * ((12 : ℝ) * M * α₀)) * (K2strat ell t₀ * CWb) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hm hP

/-- `ℓ³ e^{−θ N} ≤ 1/2` once `N ≥ ln(2ℓ³)/θ` -/
theorem exp_tail (ell : ℕ) (hell : 1 ≤ ell) (θ : ℝ) (hθ : 0 < θ) (N : ℝ) (hN : Real.log (2 * (ell : ℝ) ^ 3) / θ ≤ N) :
    (ell : ℝ) ^ 3 * Real.exp (-(θ * N)) ≤ 1 / 2 := by
  have hl : (0 : ℝ) < (ell : ℝ) ^ 3 := by have : (0 : ℝ) < ell := by exact_mod_cast hell
                                          positivity
  have h1 : Real.log (2 * (ell : ℝ) ^ 3) ≤ θ * N := by
    have := (div_le_iff₀ hθ).mp hN; linarith
  have h2 : Real.exp (-(θ * N)) ≤ Real.exp (-Real.log (2 * (ell : ℝ) ^ 3)) := Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (-Real.log (2 * (ell : ℝ) ^ 3)) = (2 * (ell : ℝ) ^ 3)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
  rw [h3] at h2
  calc (ell : ℝ) ^ 3 * Real.exp (-(θ * N)) ≤ (ell : ℝ) ^ 3 * (2 * (ell : ℝ) ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_left h2 hl.le
    _ = 1 / 2 := by field_simp

/-- **the first D-layer clause on the M1 regime** -/
theorem clause1_M1 {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) {cw : ℝ} (hcw : 0 < cw) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∃ t₀ : ℝ, 0 < t₀ ∧
    ∀ {M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ} (hell0 : 0 < ell),
      Admissible ell M R k S → 0 < M → 8 * ell ≤ R → 18 * ell ≤ R * M → N₀ ≤ R * M →
      (∀ μ, 5 ≤ Lu μ + 1) → (∀ μ, ell < Lu μ + 1) → 0 ≤ α₀ → (12 : ℝ) * M * α₀ ≤ t₀ →
      ∀ (U : LinkCfg (scaleUp ell k Lu)), M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      ∀ (Lam : Set (PeriodicLatticeSite Lu)),
      (∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G),
        cw * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫) →
      ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G),
        |⟪A, (gparams ell k Lu hell0 S U a Lam).data.Delta2 (gparams ell k Lu hell0 S U a Lam).data_laws A⟫|
          ≤ C * ((12 : ℝ) * M * α₀) * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) := by
  obtain ⟨CHb, hCHb, CWb, hCWb, δ, hδ, hball⟩ := num_ball hell ha hcw
  obtain ⟨β₀, hβ₀, hDQall⟩ := dqSmall_exists ell hell
  have hl1 : 1 ≤ ell := by omega
  have hlR : (1 : ℝ) ≤ ell := by exact_mod_cast hl1
  have hlg : 0 ≤ Real.log ell := Real.log_nonneg hlR
  set θ : ℝ := δ / 2 with hθdef
  have hθ : 0 < θ := by positivity
  have hpi : (0 : ℝ) < 4 * Real.pi + 4 := by have := Real.pi_pos; positivity
  set t₀ : ℝ := min β₀ (min (1 / 4) (δ / (2 * (4 * Real.pi + 4)))) with ht₀
  have ht₀0 : 0 < t₀ := lt_min hβ₀ (lt_min (by norm_num) (by positivity))
  have hCg : 0 ≤ Cgeo ell θ := by unfold Cgeo; positivity
  set B : ℝ := max (2 * (ell : ℝ) ^ 2 * Real.log ell / δ)
    (max (3 * (ell : ℝ) * Real.log ell / δ) (Real.log (2 * (ell : ℝ) ^ 3) / θ)) with hBdef
  refine ⟨2 * (Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CHb) * (400 * (ell : ℝ) ^ 3) * K2strat ell t₀
      * ((ell : ℝ) ^ 2 * CWb), ?_, Nat.ceil B + 1, t₀, ht₀0, ?_⟩
  · have hDQ0 := hDQall t₀ ht₀0.le (min_le_left _ _)
    have : 0 ≤ K2strat ell t₀ := by
      unfold K2strat
      have := K2free_nonneg ell ((1 + 3 * Real.pi) * alphaQ ell t₀) (thetaK2_lt_of ell _ hDQ0.hK2c)
      positivity
    positivity
  intro M R k Lu S α₀ hell0 hS hM hR8 hroom hN₀ hLu5 hLu hα0 ht U hreg Lam hW4 A0
  obtain ⟨g, A, hU, hB⟩ := hreg
  -- the four coordinates
  have ht14 : (12 : ℝ) * M * α₀ ≤ 1 / 4 := ht.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htδ : (12 : ℝ) * M * α₀ ≤ δ / (2 * (4 * Real.pi + 4)) := ht.trans ((min_le_right _ _).trans (min_le_right _ _))
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
  obtain ⟨N1, N2, N3, N4, N5, N6, N7, N8, N9, N10, N11, N12, N13, N14, N15, N16⟩ := hball _ hdist
  have hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2 := by
    refine exp_tail ell hl1 θ hθ _ ?_
    have h1 : Real.log (2 * (ell : ℝ) ^ 3) / θ ≤ B := (le_max_right _ _).trans (le_max_right _ _)
    linarith
  have hDQt := hDQall _ (by positivity) (ht.trans (min_le_left _ _))
  have hDQ0 := hDQall t₀ ht₀0.le (min_le_left _ _)
  have hW4V := coercive_to_gauge hell0 S a Lam U g cw hW4
  have hV := clause1_Ug (W := R * M * ell) hell hS hroom hM hR8 hLu5 hW1 le_rfl U g A hU hB hα0
    (ht14.trans (by norm_num)) N6.le a ha θ hθ N1.le N2.le N3.le N4.le N5 N7.le N8 N9 N10.le 1 one_pos hLu
    (by linarith) hDQt cw hcw N11.le N12 N13 (sub_pos.mpr N14) CHb hCHb N15.le hq Lam hW4V
  have hU0 := dlayer_form_ungauge hell0 S a Lam U g _ hV A0
  refine hU0.trans ?_
  have hle := eps2N_le ell M (R * M * ell) hl1 a θ α₀ CHb (csOf a (rhoT ell 12 M α₀)) (gamN ell (R * M * ell) a
    (rhoT ell 12 M α₀)) CWb ha.le hCHb hα0 t₀ ht hDQt hDQ0 N16.le
  exact mul_le_mul_of_nonneg_right hle (wnormSq_nonneg' S _)

#print axioms wnormSq_nonneg'
#print axioms eps2N_le
#print axioms exp_tail
#print axioms clause1_M1

end AdalyFormal.M1DStrat
