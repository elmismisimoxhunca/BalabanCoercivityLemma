import BC1

/-!
# BC1b -- `hQdrift` (the `Q'`-drift `eps0` of `ginv_coercive_FE_named2`) from the tower class

`TowerClass ell k Lu U ε`: `‖Ū^j(b) - 1‖_F ≤ ε_j` on the `ell^j`-aligned bonds of the blocked backgrounds
`Ū^j = bgTower (GF ell k Lu) U j`, `j < k` (the `link_tower_na` shape).
`hQdrift_of_tower`: `‖Qtop U f - Qtop 1 f‖ ≤ eps0Of · ‖f‖`, `eps0Of = (Σ_{i<k} 6 (ell-1) ε_i) · sqrt(1/n³)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.BondComposite

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SliceCoerc (coarseC Qtop GF ubarTower_trivial)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite (Qcomposite)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.StatementLane (scaleUp)

/-- the tower-class link bound. -/
def TowerClass (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℝ) : Prop :=
  ∀ j, j < k → ∀ y ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ j), ∀ μ : Fin 3,
    frobNorm (((bgTower (GF ell k Lu) U j (y, μ) : SU2) : M2) - 1) ≤ ε j

/-- `eps0 = (Σ_{i<k} 6 (ell-1) ε_i) · sqrt(1/n³)`. -/
noncomputable def eps0Of (ell k : ℕ) (ε : ℕ → ℝ) : ℝ :=
  dsum ell ε k * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3)

theorem hdvd_scaleUp (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (j : ℕ) (hj : j ≤ k) (μ : Fin 3) :
    ell ^ j ∣ scaleUp ell k Lu μ + 1 := by
  rw [scaleUp_succ ell k Lu hell μ]
  exact Dvd.dvd.mul_left (pow_dvd_pow ell hj) _

theorem hQdrift_of_tower (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℝ) (hcl : TowerClass ell k Lu U ε)
    (f : SiteL2 (scaleUp ell k Lu)) :
    ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖ ≤ eps0Of ell k ε * ‖f‖ := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hn3 : (0 : ℝ) < ((ell : ℝ) ^ k) ^ 3 := by positivity
  have hd0 : 0 ≤ dsum ell ε k := by
    unfold dsum
    refine Finset.sum_nonneg fun i hi => ?_
    have hik := Finset.mem_range.mp hi
    have h0 := hcl i hik 0 (by rw [mem_CoarseLattice]; intro μ; simp) 0
    have h1 : 0 ≤ ε i := le_trans (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _) h0
    have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by
      have : (1 : ℝ) ≤ ell := by exact_mod_cast hell
      linarith
    positivity
  set dk := dsum ell ε k with hdk
  -- pointwise
  have hpt : ∀ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k},
      ‖(Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f) y‖ ^ 2
        ≤ dk ^ 2 * (((1 / (ell : ℝ) ^ 3) ^ k) ^ 2 * ((ell : ℝ) ^ k) ^ 3)
            * ∑ x ∈ blockOf y.1 (ell ^ k), ‖f x‖ ^ 2 := by
    intro y
    have hal : y.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ k) := by
      rw [mem_CoarseLattice]
      intro μ
      exact Nat.mod_eq_zero_of_dvd (AdalyFormal.FlatExt.dvd_of_lam ell k Lu y μ)
    have hbgflat : bgTower (GF ell k Lu) (trivialU _) = fun _ => trivialU _ :=
      funext (ubarTower_trivial ell)
    have hU : Qtop (GF ell k Lu) U f y = Qcomposite (bgTower (GF ell k Lu) U) ell k (WithLp.ofLp f) y.1 := by
      show Qlev (GF ell k Lu) U (GF ell k Lu).k y.1 f = _
      rw [Qlev_apply]
      rfl
    have h1 : Qtop (GF ell k Lu) (trivialU _) f y
        = ((1 / (ell : ℝ) ^ 3) ^ k) • ∑ x ∈ blockOf y.1 (ell ^ k), f x :=
      AdalyFormal.FlatExt.Qtop_flat ell k Lu hell f y
    have hpd := Qcomposite_drift_pointwise (bgTower (GF ell k Lu) U) ell hell ε k
      (fun j hj μ => hdvd_scaleUp ell k Lu hell j hj μ)
      (fun j hj z hz μ => hcl j hj z hz μ) (WithLp.ofLp f) k le_rfl y.1 hal
    show ‖Qtop (GF ell k Lu) U f y - Qtop (GF ell k Lu) (trivialU _) f y‖ ^ 2 ≤ _
    rw [hU, h1]
    have hc0 : (0 : ℝ) ≤ (1 / (ell : ℝ) ^ 3) ^ k := by positivity
    have hnorm : ‖Qcomposite (bgTower (GF ell k Lu) U) ell k (WithLp.ofLp f) y.1
          - ((1 / (ell : ℝ) ^ 3) ^ k) • ∑ x ∈ blockOf y.1 (ell ^ k), f x‖
        ≤ dk * (((1 / (ell : ℝ) ^ 3) ^ k) * ∑ x ∈ blockOf y.1 (ell ^ k), ‖f x‖) := hpd
    have hCS : (∑ x ∈ blockOf y.1 (ell ^ k), ‖f x‖) ^ 2
        ≤ ((ell : ℝ) ^ k) ^ 3 * ∑ x ∈ blockOf y.1 (ell ^ k), ‖f x‖ ^ 2 :=
      (sq_sum_le_card_mul_sum_sq (s := blockOf y.1 (ell ^ k)) (f := fun x => ‖f x‖)).trans
        (mul_le_mul_of_nonneg_right (AdalyFormal.FlatExt.block_card_le ell k Lu y.1)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    calc ‖Qcomposite (bgTower (GF ell k Lu) U) ell k (WithLp.ofLp f) y.1
          - ((1 / (ell : ℝ) ^ 3) ^ k) • ∑ x ∈ blockOf y.1 (ell ^ k), f x‖ ^ 2
        ≤ (dk * (((1 / (ell : ℝ) ^ 3) ^ k) * ∑ x ∈ blockOf y.1 (ell ^ k), ‖f x‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = dk ^ 2 * ((1 / (ell : ℝ) ^ 3) ^ k) ^ 2 * (∑ x ∈ blockOf y.1 (ell ^ k), ‖f x‖) ^ 2 := by ring
      _ ≤ dk ^ 2 * ((1 / (ell : ℝ) ^ 3) ^ k) ^ 2 * (((ell : ℝ) ^ k) ^ 3 * ∑ x ∈ blockOf y.1 (ell ^ k), ‖f x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hCS (by positivity)
      _ = _ := by ring
  have hQ : ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖ ^ 2
      = ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k},
        ‖(Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f) y‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ _
  have hf : ‖f‖ ^ 2 = ∑ x, ‖f x‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
  have hsum := AdalyFormal.FlatExt.corner_sum_le ell k Lu hell (fun x => ‖f x‖ ^ 2) (fun x => sq_nonneg _)
  have hbig : ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖ ^ 2
      ≤ (dk * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) * ‖f‖) ^ 2 := by
    rw [hQ, mul_pow, mul_pow, Real.sq_sqrt (by positivity), hf]
    calc ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k},
          ‖(Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f) y‖ ^ 2
        ≤ ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k},
          dk ^ 2 * (((1 / (ell : ℝ) ^ 3) ^ k) ^ 2 * ((ell : ℝ) ^ k) ^ 3)
            * ∑ x ∈ blockOf y.1 (ell ^ k), ‖f x‖ ^ 2 := Finset.sum_le_sum fun y _ => hpt y
      _ = dk ^ 2 * (((1 / (ell : ℝ) ^ 3) ^ k) ^ 2 * ((ell : ℝ) ^ k) ^ 3) *
          ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}, ∑ x ∈ blockOf y.1 (ell ^ k), ‖f x‖ ^ 2 := by
          rw [← Finset.mul_sum]
      _ ≤ dk ^ 2 * (((1 / (ell : ℝ) ^ 3) ^ k) ^ 2 * ((ell : ℝ) ^ k) ^ 3) * ∑ x, ‖f x‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = dk ^ 2 * (1 / ((ell : ℝ) ^ k) ^ 3) * ∑ x, ‖f x‖ ^ 2 := by
          congr 2
          have := AdalyFormal.FlatExt.c_sq_mul ell k hell
          field_simp
          field_simp at this
          nlinarith [this]
  have hE : 0 ≤ eps0Of ell k ε * ‖f‖ :=
    mul_nonneg (mul_nonneg hd0 (Real.sqrt_nonneg _)) (norm_nonneg _)
  exact le_of_sq_le' hE hbig

#print axioms hdvd_scaleUp
#print axioms hQdrift_of_tower

end AdalyFormal.BondComposite
