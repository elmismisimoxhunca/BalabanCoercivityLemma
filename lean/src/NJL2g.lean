import NJL2f

/-!
# NJL2g -- pointwise bound of `‖Δ_c A‖` by the four absolute path sums (stride 1, block `ell`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open AdalyFormal.Balaban.QOne (pathSite)
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

/-- the edge-norm function of a unit-bond field. -/
def fA (A : CoarseBond L 1 → SuTwo) : PeriodicLatticeEdge L → ℝ :=
  fun e => ‖A (⟨e.1, mem_coarseLattice_one e.1⟩, e.2)‖

theorem fA_nonneg (A : CoarseBond L 1 → SuTwo) (e : PeriodicLatticeEdge L) : 0 ≤ fA A e := norm_nonneg _

theorem pathSum_nonneg (f : PeriodicLatticeEdge L → ℝ) (hf : ∀ e, 0 ≤ f e) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) : 0 ≤ pathSum f y p :=
  List.sum_nonneg (fun x hx => by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    exact hf e)

/-- the four absolute path sums. -/
def N1 (ℓ : ℕ) (A : CoarseBond L 1 → SuTwo) (c : CoarseBond L (1 * ℓ)) (u : PeriodicLatticeSite L) : ℝ :=
  pathSum (fA A) c.1.1 (stair (u - c.1.1))
def N2 (ℓ : ℕ) (A : CoarseBond L 1 → SuTwo) (c : CoarseBond L (1 * ℓ)) (u : PeriodicLatticeSite L) : ℝ :=
  pathSum (fA A) (c.1.1 + (u - c.1.1)) (List.replicate ℓ c.2)
def N3 (ℓ : ℕ) (A : CoarseBond L 1 → SuTwo) (c : CoarseBond L (1 * ℓ)) (u : PeriodicLatticeSite L) : ℝ :=
  pathSum (fA A) (c.1.1 + (ℓ * 1) • Pi.single c.2 1) (stair (u - c.1.1))
def N4 (ℓ : ℕ) (A : CoarseBond L 1 → SuTwo) (c : CoarseBond L (1 * ℓ)) : ℝ :=
  pathSum (fA A) c.1.1 (List.replicate ℓ c.2)

#print axioms pathSum_nonneg

end AdalyFormal.NonflatJet
