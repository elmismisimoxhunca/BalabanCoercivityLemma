import BC8

/-!
# BC9 -- the global-sup variant: `RegTower` (the chain's `hreg`) is DERIVED from a link-sup bound on all edges

If `frobSupBond (Ū^j) ≤ ε_j` on ALL edges (not only aligned ones) and `(π/2)(loopFactorBound ell · ε_j) < r0`, then
`RegTower` (nonflat-jet `regTower_of_small`) and `TowerClass` both follow, so `ginv_coercive_BC` needs no `hreg` premise.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.BondComposite

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SliceCoerc (coarseC Qtop GF PhiF)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond)
open AdalyFormal.NonflatJet (r0)
open SmallnessBridge.Assemble (loopFactorBound)

theorem regTower_of_sup (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (ε : ℕ → ℝ) (hε : ∀ j, 0 ≤ ε j)
    (hsup : ∀ j, j < k → frobSupBond (bgTower (GF ell k Lu) U j) ≤ ε j)
    (hr : ∀ j, j < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j) < r0) :
    RegTower ell (bgTower (GF ell k Lu) U) k :=
  regTower_of_small_bc hell (bgTower (GF ell k Lu) U) k ε hε
    (fun j hj e => (frobNorm_le_frobSupBond _ e).trans (hsup j hj)) hr

theorem towerClass_of_sup (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu))
    (ε : ℕ → ℝ) (hsup : ∀ j, j < k → frobSupBond (bgTower (GF ell k Lu) U j) ≤ ε j) :
    TowerClass ell k Lu U ε :=
  fun j hj y _ μ => (frobNorm_le_frobSupBond _ (y, μ)).trans (hsup j hj)

/-- non-vacuity of `TowerClass`: it holds at the trivial background with `ε = 0`. -/
theorem towerClass_trivial (ell k : ℕ) (Lu : PeriodicLatticeExtent) :
    TowerClass ell k Lu (trivialU _) (fun _ => 0) := by
  intro j _ y _ μ
  have hbg : bgTower (GF ell k Lu) (trivialU _) = fun _ => trivialU _ :=
    funext (AdalyFormal.SliceCoerc.ubarTower_trivial ell)
  rw [hbg]
  exact le_of_eq (frob_trivial_sub_one _ (y, μ))

#print axioms regTower_of_sup
#print axioms towerClass_of_sup
#print axioms towerClass_trivial

end AdalyFormal.BondComposite
