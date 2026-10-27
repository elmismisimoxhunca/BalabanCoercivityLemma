import NJL2m
import NJ7T1

/-!
# NJ20a -- volume-free `L²` bound for the covariant main-term drift  `T1(V) - T1(1)`:  `Σ_c ‖(T1(V)-T1(1))A(c)‖² ≤ 192 ell² ε₀² ‖A‖²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_one)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarsePathHolonomy coarseTransportPath
  coarsePathHolonomy_trivialU unitToCoarseCov)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm norm_RMap_sub_self_le)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem pathSite_succ_add (u : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    pathSite u μ (i + 1) = pathSite (u + Pi.single μ 1) μ i := by
  rw [pathSite_eq_add, pathSite_eq_add]
  have : (i + 1) • (Pi.single μ 1 : PeriodicLatticeSite L) = Pi.single μ 1 + i • Pi.single μ 1 := by
    rw [add_comm i 1, add_nsmul, one_nsmul]
  rw [this, add_assoc]

theorem pathSum_rep (f : PeriodicLatticeEdge L → ℝ) (u : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    pathSum f u (List.replicate n μ) = ∑ i ∈ Finset.range n, f (pathSite u μ i, μ) := by
  induction n generalizing u with
  | zero => simp [pathSum, bondsOf]
  | succ n ih =>
      rw [Finset.sum_range_succ', List.replicate_succ]
      have h1 : pathSum f u (μ :: List.replicate n μ)
          = f (u, μ) + pathSum f (u + Pi.single μ 1) (List.replicate n μ) := by
        simp [pathSum, bondsOf]
      rw [h1, ih (u + Pi.single μ 1), add_comm]
      simp only [pathSite_succ_add, AdalyFormal.Balaban.QOne.pathSite_zero]

#print axioms pathSum_rep

end AdalyFormal.NonflatJet
