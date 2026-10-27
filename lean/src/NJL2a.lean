import NJ4Li
import NJ6bSup

/-!
# NJL2a -- (volume-free L2, step 1) bond lists of a path and the translation structure of sites.

`bondsOf y p` : the list of bonds `(y_k, p_k)` traversed by the path `p` from `y` (unit steps).  `pathSum f y p = Σ f(bond)`.
The sites form an additive group (`Fin (n+1)` coordinatewise); the unit shift is `+ Pi.single μ 1`; `bondsOf` is translation-equivariant.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge periodicLatticeShift PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.SuTwoInner
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem shift_eq_add (y : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicLatticeShift y μ = y + Pi.single μ 1 := by
  funext ν
  by_cases h : ν = μ
  · subst h; simp [periodicLatticeShift]
  · simp [periodicLatticeShift, Function.update_of_ne h, Pi.single_eq_of_ne h]

theorem coarseShift_one_add (y : PeriodicLatticeSite L) (μ : Fin 3) :
    coarseShift y 1 μ = y + Pi.single μ 1 := by
  rw [show coarseShift y 1 μ = periodicLatticeShift y μ from rfl, shift_eq_add]

/-- the bonds traversed by `p` from `y`. -/
def bondsOf (y : PeriodicLatticeSite L) : List (Fin 3) → List (PeriodicLatticeEdge L)
  | [] => []
  | μ :: rest => (y, μ) :: bondsOf (y + Pi.single μ 1) rest

theorem bondsOf_add (x y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    bondsOf (x + y) p = (bondsOf y p).map (fun e => (x + e.1, e.2)) := by
  induction p generalizing y with
  | nil => rfl
  | cons μ rest ih =>
      show (x + y, μ) :: bondsOf (x + y + Pi.single μ 1) rest = _
      rw [add_assoc, ih]
      rfl

theorem bondsOf_length (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    (bondsOf y p).length = p.length := by
  induction p generalizing y with
  | nil => rfl
  | cons μ rest ih => simp [bondsOf, ih]

/-- the absolute line integral. -/
def pathSum (f : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) (p : List (Fin 3)) : ℝ :=
  ((bondsOf y p).map f).sum

theorem norm_lineIntegral_le_pathSum (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 1 → SuTwo) (p : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L,
      ‖lineIntegral 1 V A y p‖ ≤ pathSum (fun e => ‖A (⟨e.1, AdalyFormal.Balaban.StridedAveraging.mem_coarseLattice_one e.1⟩, e.2)‖) y p := by
  induction p with
  | nil => intro y; simp [pathSum, bondsOf]
  | cons μ rest ih =>
      intro y
      rw [lineIntegral_cons]
      have h1 : ‖(if h : y ∈ CoarseLattice L 1 then A (⟨y, h⟩, μ) else 0)‖
          = ‖A (⟨y, AdalyFormal.Balaban.StridedAveraging.mem_coarseLattice_one y⟩, μ)‖ := by
        rw [dif_pos (AdalyFormal.Balaban.StridedAveraging.mem_coarseLattice_one y)]
      have h2 : ‖AdalyFormal.Balaban.CovariantOperators.RMap (V (y, μ))
          (lineIntegral 1 V A (coarseShift y 1 μ) rest)‖
          ≤ pathSum (fun e => ‖A (⟨e.1, AdalyFormal.Balaban.StridedAveraging.mem_coarseLattice_one e.1⟩, e.2)‖)
              (y + Pi.single μ 1) rest := by
        rw [AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap, ← coarseShift_one_add]
        exact ih _
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ ‖A (⟨y, AdalyFormal.Balaban.StridedAveraging.mem_coarseLattice_one y⟩, μ)‖ + _ :=
            add_le_add h1.le h2
        _ = _ := by simp [pathSum, bondsOf]

#print axioms bondsOf_add
#print axioms norm_lineIntegral_le_pathSum

end AdalyFormal.NonflatJet
