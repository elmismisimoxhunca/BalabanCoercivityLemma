import TL1m

set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

theorem classCoupled_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (hstrict : ∀ μ : Fin 3, L μ + 1 < Lt μ + 1)
    {ell M R c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} (hS : Admissible ell M R k S) (hc : 2 ≤ c)
    (hCU : ClassCoupled ell M c k S α₀ η U) :
    ClassCoupled ell M c k (liftTower h S) α₀ η (liftU h U) :=
  ⟨⟨coversSites_lift h hstrict hS hc hCU.1.1, coversPlaq_lift h hstrict hS hc hCU.1.2⟩, perCube_lift h hS hCU.2⟩

theorem covers_scaleUp_strict (ell k : ℕ) (hell : 0 < ell) {Lut Lu : PeriodicLatticeExtent}
    (hstrict : ∀ μ : Fin 3, Lu μ + 1 < Lut μ + 1) :
    ∀ μ : Fin 3, scaleUp ell k Lu μ + 1 < scaleUp ell k Lut μ + 1 := by
  intro μ
  rw [scaleUp_add_one ell k hell, scaleUp_add_one ell k hell]
  exact Nat.mul_lt_mul_of_pos_right (hstrict μ) (pow_pos hell k)

/-- the geometric lift: unit torus `Lut` over `Lu` (strict cover), fine tori `scaleUp ell k`. -/
structure GeomLift (ell k : ℕ) (hell : 0 < ell) (Lut Lu : PeriodicLatticeExtent) : Prop where
  cover : Covers Lut Lu
  strict : ∀ μ : Fin 3, Lu μ + 1 < Lut μ + 1

theorem GeomLift.fine {ell k : ℕ} {hell : 0 < ell} {Lut Lu : PeriodicLatticeExtent} (g : GeomLift ell k hell Lut Lu) :
    Covers (scaleUp ell k Lut) (scaleUp ell k Lu) := covers_scaleUp ell k hell g.cover

theorem geometry_lift {ell M R c k : ℕ} {hell : 0 < ell} {Lut Lu : PeriodicLatticeExtent}
    (g : GeomLift ell k hell Lut Lu) (hc : 2 ≤ c)
    (hT : TorusOK ell M Lu) {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK2 ell M R k S Lam)
    {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)}
    (hCU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) :
    TorusOK ell M Lut ∧ Admissible ell M R k (liftTower g.fine S) ∧
      LambdaOK2 ell M R k (liftTower g.fine S) (projS g.cover ⁻¹' Lam) ∧
      ClassCoupled ell M c k (liftTower g.fine S) α₀ ((ell : ℝ) ^ k)⁻¹ (liftU g.fine U) :=
  ⟨torusOK_lift g.cover hT, admissible_lift g.fine hS,
    ⟨lambdaOK_lift g.cover hell hT hL.1, lamBlockSum_lift g.cover hell hT.1 hL.2⟩,
    classCoupled_lift g.fine (covers_scaleUp_strict ell k hell g.strict) hS hc hCU⟩

end AdalyFormal.Thin
