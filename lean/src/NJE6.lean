import NJE5

/-!
# NJE6 -- THE LEVEL-`j+1` JET OF THE GENUINE COMPOSITE `Q_{j+1}(U)` (CMP99b (3.14)/(3.15)), exact printed (124):
`D(qCompX_{j+1})(0) a (embE c') = ell • fromM2 (q124Principal 1 ell (resV (Ū^j)) (D(qCompX_j)(0) a ∘ embE) c')`,
for the level-`(j+1)` coarse bonds `c = embE c'` (stride `ell^j` sublattice torus `Lq`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.NonflatJet

open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2NegOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.DeltaKR85 (q124Principal)
open AdalyFormal.IngredientFamilyR2

variable {L Lq : PeriodicLatticeExtent}

theorem QlinCompX_succ_apply_emb (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower ell bg J) (j : ℕ) (hj : j < J)
    (hs : ∀ μ, L μ + 1 = ell ^ j * (Lq μ + 1)) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (Lq μ + 1)) (c : PeriodicLatticeEdge Lq)
    (hcell : c.1 ∈ CoarseLattice Lq ell)
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell (resV hs (bg j)) c x ≠ su2NegOne)
    (a : XS L) :
    QlinCompX ell bg (j + 1) a (embE hs c)
      = (ell : ℝ) • fromM2
          ((q124Principal 1 ell (resV hs (bg j))
              (fineDirToUnitBond (fun e => toM2 (resA hs (QlinCompX ell bg j a) e))
                (fun e => (toM2_mem (resA hs (QlinCompX ell bg j a) e)).1)
                (fun e => (toM2_mem (resA hs (QlinCompX ell bg j a) e)).2))
              (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond Lq (1 * ell)) : SuTwo) : M2) := by
  rw [QlinCompX_succ ell bg J hreg j hj]
  exact fderiv_qStepX_stride_apply hs (bg j) ell (hreg j hj) c hcell hell hdvd hnc2 _

#print axioms QlinCompX_succ_apply_emb

end AdalyFormal.NonflatJet
