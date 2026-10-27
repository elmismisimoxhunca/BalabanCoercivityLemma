import NsCvO39

/-!
# CvO40 -- the row pairing `<Q w, zrow rho>` for sigma_3-valued `w` along the staggered path (lane omega)

Setup structure `StagSetup`: the hypotheses on the (tower) geometry that make the Z-reduction work (all proved for the nested instance elsewhere).
Result: `<Q w, zrow rho> = c0 * Σ_x θ_w(x,1) * Wt(x₀)` with `Wt v = Σ_{j<3} ell^{-3j} [isRow j (⌊v⌋_j)] rho_j(⌊v⌋_j)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverNested (cartan cartan_coe)
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)

variable {L : PeriodicLatticeExtent}

/-- hypotheses on the geometry used by the Z-reduction. -/
structure StagSetup (L : PeriodicLatticeExtent) (ell c : ℕ) (G : TowerGeom L) (isRow : ℕ → ℕ → Prop) : Prop where
  hN : 2 ∣ L 1 + 1
  hE : StagPar L ell
  hell : 0 < ell
  hdiv : ∀ μ, ell * ell ∣ L μ + 1
  hc1 : ell ≤ c
  hc2 : c + ell * ell < L 0 + 1
  hG : G.ell = ell
  hk : G.k = 2
  hcrs : ∀ p : BIdx G, Crs (ell ^ (p.1 : ℕ)) p.2.1.1
  hrow : ∀ j, j ≤ 2 → ∀ y : PeriodicLatticeSite L, (y, (1 : Fin 3)) ∈ bondsLam G j ↔ (Crs (ell ^ j) y ∧ isRow j (y 0).val)

/-- the row field with level-`j`, slice-`v` value `rho j v` (direction-1, sigma_3). -/
noncomputable def zrow (G : TowerGeom L) (ρ : ℕ → ℕ → ℝ) : FSp G :=
  WithLp.toLp 2 (fun p : BIdx G => if p.2.1.2 = 1 then dgS (ρ (p.1 : ℕ) (p.2.1.1 0).val) else 0)

/-- the transverse-constant profile that `Q*` assigns to the row field `zrow rho`. -/
noncomputable def Wt (ell : ℕ) (isRow : ℕ → ℕ → Prop) (ρ : ℕ → ℕ → ℝ) (v : ℕ) : ℝ :=
  open Classical in
  ∑ j ∈ Finset.range 3, (((ell : ℝ) ^ j)⁻¹) * ((((ell : ℝ) ^ 2)⁻¹) ^ j) *
    (if isRow j (ell ^ j * (v / ell ^ j)) then ρ j (ell ^ j * (v / ell ^ j)) else 0)

/-- `hsInner` of the generator with itself. -/
noncomputable def c0 : ℝ := hsInner (dgS 1) (dgS 1)

theorem crs_one (x : PeriodicLatticeSite L) : Crs 1 x := fun μ => one_dvd _

open Classical in
/-- three-level conservation: the row sums of `thetaSeq` against slice weights `H_j`. -/
theorem lev_sums {ell : ℕ} (hell : 0 < ell) (hdiv : ∀ μ, ell * ell ∣ L μ + 1) (θ : PeriodicLatticeEdge L → ℝ) (H : ℕ → ℕ → ℝ) :
    (∑ y : PeriodicLatticeSite L, (if Crs (ell ^ 0) y then H 0 (y 0).val * thetaSeq ell 0 θ (y, 1) else 0)) =
      ∑ x : PeriodicLatticeSite L, H 0 (ell ^ 0 * ((x 0).val / ell ^ 0)) * θ (x, 1) ∧
    (∑ y : PeriodicLatticeSite L, (if Crs (ell ^ 1) y then H 1 (y 0).val * thetaSeq ell 1 θ (y, 1) else 0)) =
      ((ell : ℝ) ^ 2)⁻¹ * ∑ x : PeriodicLatticeSite L, H 1 (ell ^ 1 * ((x 0).val / ell ^ 1)) * θ (x, 1) ∧
    (∑ y : PeriodicLatticeSite L, (if Crs (ell ^ 2) y then H 2 (y 0).val * thetaSeq ell 2 θ (y, 1) else 0)) =
      (((ell : ℝ) ^ 2)⁻¹) ^ 2 * ∑ x : PeriodicLatticeSite L, H 2 (ell ^ 2 * ((x 0).val / ell ^ 2)) * θ (x, 1) := by
  have hdiv1 : ∀ μ, 1 * ell ∣ L μ + 1 := fun μ => by rw [one_mul]; exact Dvd.dvd.trans (Dvd.intro ell rfl) (hdiv μ)
  have hdive : ∀ μ, ell * ell ∣ L μ + 1 := hdiv
  refine ⟨?_, ?_, ?_⟩
  · simp only [pow_zero, thetaSeq, one_mul, Nat.div_one]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [if_pos (crs_one y)]
  · have := cons1 (one_pos) hell hdiv1 θ (H 1)
    simp only [thetaSeq, pow_zero, pow_one, one_mul] at this ⊢
    rw [this]
    congr 1
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [if_pos (crs_one x)]
  · have h1 := cons1 (s := ell) hell hell hdiv (Rsig 1 ell θ) (H 2)
    have h2 := cons1 (s := 1) (ell := ell) one_pos hell hdiv1 θ (fun v => H 2 ((ell * ell) * (v / (ell * ell))))
    simp only [thetaSeq, pow_zero, pow_one, one_mul, pow_two] at h1 h2 ⊢
    rw [h1, h2]
    have hfl : ∀ z : ℕ, ell * ell * ((ell * (z / ell)) / (ell * ell)) = ell * ell * (z / (ell * ell)) := by
      intro z
      rw [Nat.mul_div_mul_left _ _ hell, Nat.div_div_eq_div_mul]
    have hS : (∑ x : PeriodicLatticeSite L, (if Crs 1 x then H 2 (ell * ell * ((ell * ((x 0).val / ell)) / (ell * ell))) * θ (x, 1) else 0)) =
        ∑ x : PeriodicLatticeSite L, H 2 (ell * ell * ((x 0).val / (ell * ell))) * θ (x, 1) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [if_pos (crs_one x), hfl]
    rw [hS]
    ring

end AdalyFormal.CoverOmega
