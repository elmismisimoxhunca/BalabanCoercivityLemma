import PSiteC7
import AdalyFormal.Balaban.ClassPropagationUbar

/-!
# SC8 -- instantiations of `site_coercive_nested`: (A) k-uniform under the tower class `frobSupBond (Ū^i) ≤ ρ ell^i / ell^k`;
(B) from `Small n α U` alone, with the tree's blocking estimate `frobSupBond (Ū V) ≤ C(ell)·frobSupBond V`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.SiteCoercivity

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)

variable {L : PeriodicLatticeExtent}

theorem geom_tower_sum (ell k : ℕ) (hell : 2 ≤ ell) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * (ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ k) ≤ 6 * ρ := by
  have hℓ : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hne : (ell : ℝ) ≠ 1 := by linarith
  have hpos : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  have h1 : ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * (ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ k)
      = 6 * ((ell : ℝ) - 1) * ρ / (ell : ℝ) ^ k * ∑ i ∈ Finset.range k, (ell : ℝ) ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    field_simp
  rw [h1, geom_sum_eq hne k]
  have hsub : (ell : ℝ) - 1 ≠ 0 := by intro h; apply hne; linarith
  have h2 : 6 * ((ell : ℝ) - 1) * ρ / (ell : ℝ) ^ k * (((ell : ℝ) ^ k - 1) / ((ell : ℝ) - 1))
      = 6 * ρ * (1 - 1 / (ell : ℝ) ^ k) := by
    field_simp
  rw [h2]
  have : 0 ≤ 1 / (ell : ℝ) ^ k := by positivity
  nlinarith

/-- **(A) k-UNIFORM, VOLUME-UNIFORM nested site coercivity under the tower class.** -/
theorem site_coercive_towerclass (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1) (U : Cfg L)
    (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ) (hU : frobSupBond U ≤ ρ / (ell : ℝ) ^ k)
    (hT : ∀ i, i < k → frobSupBond (bgTower (fullGeom L ell k) U i) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ k)
    (f : SiteL2 L) :
    (1 - 216 * ρ ^ 2) * ‖f‖ ^ 2
      ≤ max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 * ⟪f, DelpA (fullGeom L ell k) U a f⟫ := by
  have h := site_coercive_nested ell k hell hdvd U a ha ρ (6 * ρ) hU
    (fun i => ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ k) hT (geom_tower_sum ell k hell ρ hρ) f
  nlinarith [h]


open AdalyFormal.Balaban.ClassPropagationUbar (blkConstOf frobSupBond_ubarSU2_le)

theorem blkConstOf_pos (ell : ℕ) (hell : 0 < ell) : 0 < blkConstOf ell := by
  have h : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  unfold blkConstOf
  have := Real.pi_pos
  nlinarith

/-- the tree's blocking estimate iterated along the background tower -/
theorem frobSupBond_bgTower_le (ell k : ℕ) (hell : 0 < ell) (U : Cfg L) :
    ∀ i : ℕ, frobSupBond (bgTower (fullGeom L ell k) U i) ≤ (blkConstOf ell) ^ i * frobSupBond U := by
  intro i
  induction i with
  | zero => simp [bgTower, AdalyFormal.Balaban.UbarTowerCov.UbarTower]
  | succ i ih =>
    have e : bgTower (fullGeom L ell k) U (i + 1)
        = AdalyFormal.Balaban.BlockedBackground.ubarSU2 (ell ^ i) ell (bgTower (fullGeom L ell k) U i) := rfl
    rw [e, pow_succ]
    refine le_trans (frobSupBond_ubarSU2_le _ (pow_pos hell i) hell) ?_
    have hC := blkConstOf_pos ell hell
    calc blkConstOf ell * frobSupBond (bgTower (fullGeom L ell k) U i)
        ≤ blkConstOf ell * ((blkConstOf ell) ^ i * frobSupBond U) := by gcongr
      _ = (blkConstOf ell) ^ i * blkConstOf ell * frobSupBond U := by ring

/-- **(B) nested site coercivity from `Small n α U` ALONE** (`frobSupBond U ≤ α/ell^k`), with the tree's blocking
estimate (`frobSupBond (Ū V) ≤ blkConstOf ell · frobSupBond V`).  The tower-error `E_k` grows like `(blkConstOf ell / ell)^k`. -/
theorem site_coercive_small (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1) (U : Cfg L)
    (a : ℝ) (ha : 0 < a) (α : ℝ) (hU : frobSupBond U ≤ α / (ell : ℝ) ^ k) (f : SiteL2 L) :
    (1 - 72 * α ^ 2 - 4 * (∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * ((blkConstOf ell) ^ i * (α / (ell : ℝ) ^ k))) ^ 2)
        * ‖f‖ ^ 2
      ≤ max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 * ⟪f, DelpA (fullGeom L ell k) U a f⟫ := by
  have hell0 : 0 < ell := by omega
  have hC := blkConstOf_pos ell hell0
  exact site_coercive_nested ell k hell hdvd U a ha α _ hU
    (fun i => (blkConstOf ell) ^ i * (α / (ell : ℝ) ^ k))
    (fun i _ => le_trans (frobSupBond_bgTower_le ell k hell0 U i) (by gcongr)) le_rfl f

end AdalyFormal.SiteCoercivity
