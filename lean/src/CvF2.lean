import CvF1

/-!
# CvF2 -- a pole with nonzero residue refutes `P428Target8NCWDH` (lane cover_finish_20261016)

Proved here:
* `pole_below` (scalar): if `d → 0` at `t₀` taking both signs arbitrarily close to `t₀`, and `p`, `r` are continuous at `t₀`
  with `p t₀ ≠ 0`, then `p/d + r` takes values below every `K` at points `t` arbitrarily close to `t₀` with `d t ≠ 0`.
  Only `p t₀ ≠ 0` matters: neither the SIZE of `p t₀` nor its SIGN.
* `quad_inv_eq` (Cramer): `yᵀ N⁻¹ y = (yᵀ adj(N) y) / det N` for every real square matrix (also when `det N = 0`).
* `matrix_pole`: for a continuous path of real matrices whose determinant vanishes at `t₀` and takes both signs arbitrarily
  close to `t₀`, if the residue `yᵀ adj(N t₀) y ≠ 0`, then `yᵀ (N t)⁻¹ y + r t` is unbounded below near `t₀` at points with
  `det (N t) ≠ 0`.
* `PoleAt`: a predicate on one `(ell, M, R, a)`: an in-regime instance and a path `t ↦ U t` of configurations in the factor-12
  class at every `α > 0`, along which (for `d t ≠ 0` near `t₀`) every printed object exists and the printed form of one admissible
  `B̃` equals `p t / d t + r t`, with `d` vanishing and changing sign at `t₀`, and nonzero residue `p t₀ ≠ 0`.
* **`failAt_of_poleAt`** and **`not_WDH_of_poles`**: `PoleAt` gives `FailAt` (CvF1), so poles for infinitely many `m` and,
  for each, infinitely many `R` refute `P428Target8NCWDH`, and give `coverage_necessary_strong`.

NOT proved here: the existence of such poles (`PoleAt`) at any in-regime point (see the lane REPORT).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverFinish

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverStrong
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open scoped Matrix

/-! ## 1. the scalar pole lemma -/

/-- one-sided form: `d` takes the sign opposite to `p t₀` arbitrarily close to `t₀`. -/
theorem pole_below_of_sign {d p r : ℝ → ℝ} {t₀ : ℝ}
    (hd : ContinuousAt d t₀) (hd0 : d t₀ = 0) (hp : ContinuousAt p t₀) (hp0 : p t₀ ≠ 0)
    (hr : ContinuousAt r t₀)
    (hsign : ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, |t - t₀| < ε ∧ d t * p t₀ < 0) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, |t - t₀| < ε ∧ d t ≠ 0 ∧ p t / d t + r t < K := by
  have hc2 : 0 < p t₀ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hp0))
  have hh : 0 < p t₀ ^ 2 / 2 := by positivity
  have hA : 0 < |K - r t₀ - 1| + 1 := by positivity
  have hδs : 0 < (p t₀ ^ 2 / 2) / (|K - r t₀ - 1| + 1) := div_pos hh hA
  have e1 : ∀ᶠ t in nhds t₀, p t₀ ^ 2 / 2 < p t * p t₀ := by
    have hc : ContinuousAt (fun t => p t * p t₀) t₀ := hp.mul continuousAt_const
    have hlim : p t₀ ^ 2 / 2 < p t₀ * p t₀ := by nlinarith
    exact hc.eventually (lt_mem_nhds hlim)
  have e2 : ∀ᶠ t in nhds t₀, r t < r t₀ + 1 := hr.eventually (gt_mem_nhds (by linarith))
  have e3 : ∀ᶠ t in nhds t₀, -((p t₀ ^ 2 / 2) / (|K - r t₀ - 1| + 1)) < d t * p t₀ := by
    have hc : ContinuousAt (fun t => d t * p t₀) t₀ := hd.mul continuousAt_const
    have hlim : -((p t₀ ^ 2 / 2) / (|K - r t₀ - 1| + 1)) < d t₀ * p t₀ := by
      rw [hd0, zero_mul]; linarith
    exact hc.eventually (lt_mem_nhds hlim)
  obtain ⟨δ, hδ, hall⟩ := Metric.eventually_nhds_iff.mp (e1.and (e2.and e3))
  obtain ⟨t, ht, hneg⟩ := hsign (min ε δ) (lt_min hε hδ)
  have htδ : dist t t₀ < δ := by
    rw [Real.dist_eq]; exact lt_of_lt_of_le ht (min_le_right _ _)
  obtain ⟨h1, h2, h3⟩ := hall htδ
  refine ⟨t, lt_of_lt_of_le ht (min_le_left _ _), ?_, ?_⟩
  · intro h0
    rw [h0, zero_mul] at hneg
    exact lt_irrefl 0 hneg
  · have hq : p t / d t = (p t * p t₀) / (d t * p t₀) := by rw [mul_div_mul_right _ _ hp0]
    have hmul : (|K - r t₀ - 1| + 1) * ((p t₀ ^ 2 / 2) / (|K - r t₀ - 1| + 1)) = p t₀ ^ 2 / 2 := by
      field_simp
    have hkey : (p t * p t₀) / (d t * p t₀) < -(|K - r t₀ - 1| + 1) := by
      rw [div_lt_iff_of_neg hneg]
      have hlt : (|K - r t₀ - 1| + 1) * (-(d t * p t₀))
          < (|K - r t₀ - 1| + 1) * ((p t₀ ^ 2 / 2) / (|K - r t₀ - 1| + 1)) :=
        mul_lt_mul_of_pos_left (by linarith) hA
      nlinarith
    have habs := neg_abs_le (K - r t₀ - 1)
    rw [hq]
    linarith

/-- two-sided form: `d` takes BOTH signs arbitrarily close to `t₀` (a sign change); the sign of `p t₀` is irrelevant. -/
theorem pole_below {d p r : ℝ → ℝ} {t₀ : ℝ}
    (hd : ContinuousAt d t₀) (hd0 : d t₀ = 0) (hp : ContinuousAt p t₀) (hp0 : p t₀ ≠ 0)
    (hr : ContinuousAt r t₀)
    (hboth : ∀ ε : ℝ, 0 < ε → (∃ t : ℝ, |t - t₀| < ε ∧ d t < 0) ∧ (∃ t : ℝ, |t - t₀| < ε ∧ 0 < d t))
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, |t - t₀| < ε ∧ d t ≠ 0 ∧ p t / d t + r t < K := by
  refine pole_below_of_sign hd hd0 hp hp0 hr (fun ε' hε' => ?_) K hε
  rcases lt_or_gt_of_ne hp0 with hneg | hpos
  · obtain ⟨t, ht, hdt⟩ := (hboth ε' hε').2
    exact ⟨t, ht, mul_neg_of_pos_of_neg hdt hneg⟩
  · obtain ⟨t, ht, hdt⟩ := (hboth ε' hε').1
    exact ⟨t, ht, mul_neg_of_neg_of_pos hdt hpos⟩

/-! ## 2. the matrix form (Cramer) -/

/-- `yᵀ N⁻¹ y = (yᵀ adj(N) y) / det N` (both sides `0` when `det N = 0`). -/
theorem quad_inv_eq {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    y ⬝ᵥ (N⁻¹ *ᵥ y) = (y ⬝ᵥ (N.adjugate *ᵥ y)) / N.det := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, div_eq_inv_mul]

/-- **matrix pole**: residue `yᵀ adj(N t₀) y ≠ 0` at a sign change of `det N` gives `yᵀ (N t)⁻¹ y + r t → -∞` along points
with `det (N t) ≠ 0`. -/
theorem matrix_pole {n : ℕ} {N : ℝ → Matrix (Fin n) (Fin n) ℝ} (hN : Continuous N) (y : Fin n → ℝ)
    {r : ℝ → ℝ} {t₀ : ℝ} (hr : ContinuousAt r t₀) (hdet0 : (N t₀).det = 0)
    (hres : y ⬝ᵥ ((N t₀).adjugate *ᵥ y) ≠ 0)
    (hboth : ∀ ε : ℝ, 0 < ε →
      (∃ t : ℝ, |t - t₀| < ε ∧ (N t).det < 0) ∧ (∃ t : ℝ, |t - t₀| < ε ∧ 0 < (N t).det))
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, |t - t₀| < ε ∧ (N t).det ≠ 0 ∧ y ⬝ᵥ ((N t)⁻¹ *ᵥ y) + r t < K := by
  have hd : Continuous (fun t => (N t).det) := hN.matrix_det
  have hp : Continuous (fun t => y ⬝ᵥ ((N t).adjugate *ᵥ y)) :=
    continuous_const.dotProduct (hN.matrix_adjugate.matrix_mulVec continuous_const)
  obtain ⟨t, ht, hdt, hlt⟩ := pole_below (d := fun t => (N t).det) (p := fun t => y ⬝ᵥ ((N t).adjugate *ᵥ y))
    hd.continuousAt hdet0 hp.continuousAt hres hr hboth K hε
  refine ⟨t, ht, hdt, ?_⟩
  rw [quad_inv_eq]
  exact hlt

/-! ## 3. poles of the printed form -/

/-- **a pole of the printed form with nonzero residue** at `(ell, M, R, a)`: an in-regime instance, a path `t ↦ U t`, one
admissible `B̃`, and real functions `d, p, r` with: `d t₀ = 0` and `d` takes both signs arbitrarily close to `t₀`; `p t₀ ≠ 0`;
`d, p, r` continuous at `t₀`; and for `|t - t₀| < δ` with `d t ≠ 0`: `U t` is in the factor-12 class at every `α > 0`, every
printed object exists (`WellDefG`), and `⟨C B̃, Δ_k C B̃⟩ = p t / d t + r t`. -/
def PoleAt (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ∃ Lu : PeriodicLatticeExtent, TorusOK ell M Lu ∧
  ∃ S : Tower (scaleUp ell k Lu), Admissible ell M R k S ∧
  ∃ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 ell M R k S Lam ∧
  ∃ (U : ℝ → LinkCfg (scaleUp ell k Lu)) (Bt : Bond Lu → SuTwo) (d p r : ℝ → ℝ) (t₀ δ : ℝ),
    OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧
    ContinuousAt d t₀ ∧ d t₀ = 0 ∧ ContinuousAt p t₀ ∧ p t₀ ≠ 0 ∧ ContinuousAt r t₀ ∧
    (∀ ε : ℝ, 0 < ε → (∃ t : ℝ, |t - t₀| < ε ∧ d t < 0) ∧ (∃ t : ℝ, |t - t₀| < ε ∧ 0 < d t)) ∧
    0 < δ ∧ ∀ t : ℝ, |t - t₀| < δ → d t ≠ 0 →
      (∀ α : ℝ, 0 < α → PerCubeRegular2 ell M 12 k S α ((ell : ℝ) ^ k)⁻¹ (U t)) ∧
      GenP.WellDefG (gparams ell k Lu hell S (U t) a Lam) ∧
      GenP.genForm (gparams ell k Lu hell S (U t) a Lam)
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S (U t) a Lam) Bt)) = p t / d t + r t

theorem failAt_of_poleAt {ell M R : ℕ} {hell : 0 < ell} {a : ℝ} (h : PoleAt ell M R hell a) :
    FailAt ell M R hell a := by
  intro α hα γ hγ
  obtain ⟨k, hk, Lu, hT, S, hS, Lam, hL, U, Bt, d, p, r, t₀, δ, h1, h2, hd, hd0, hp, hp0, hr, hboth, hδ, hpath⟩ := h
  obtain ⟨t, ht, hdt, hlt⟩ := pole_below hd hd0 hp hp0 hr hboth (γ * bondEnergy Bt) hδ
  obtain ⟨hU, hW, hF⟩ := hpath t ht hdt
  exact ⟨k, hk, Lu, hT, S, hS, Lam, hL, U t, hU α hα, hW, Bt, h1, h2, by rw [hF]; exact hlt⟩

/-- **poles with nonzero residue for infinitely many `m` and, for each, infinitely many `R` refute `P428Target8NCWDH`.** -/
theorem not_WDH_of_poles (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ PoleAt ell (ell ^ m) R (by omega) a) :
    ¬ P428Target8NCWDH := by
  refine not_WDH_of_fail ⟨ell, hell, a, ha, fun m₀ => ?_⟩
  obtain ⟨m, hm, hR⟩ := h m₀
  refine ⟨m, hm, fun R₀ => ?_⟩
  obtain ⟨R, hR', hP⟩ := hR R₀
  exact ⟨R, hR', failAt_of_poleAt hP⟩

/-- `coverage_necessary_strong`, conditional on poles. -/
theorem coverage_necessary_strong_of_poles (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ PoleAt ell (ell ^ m) R (by omega) a) :
    AdalyFormal.StatementLaneG.P428Target8 ∧ ¬ P428Target8NCWDH :=
  ⟨AdalyFormal.M2RightInv.p428Target8, not_WDH_of_poles ell hell a ha h⟩

end AdalyFormal.CoverFinish
