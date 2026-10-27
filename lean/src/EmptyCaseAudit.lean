import C5G

set_option autoImplicit false
namespace SolCube5EmptyCase
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.P409C5
open AdalyFormal.GeneralClass (IsClassSetW)

def extent : PeriodicLatticeExtent := fun _ => 1

def emptyTower : Tower extent := ⟨fun _ => ∅⟩

def centre : PeriodicLatticeSite extent := fun _ => ⟨0, by norm_num [extent]⟩

theorem admissible : Admissible 2 1 42 0 emptyTower := by
  simp [Admissible, emptyTower, bigSide, BlockClosed]

theorem torus_bound : ∀ μ : Fin 3, bigSide 1 2 0 < extent μ + 1 := by
  intro μ
  norm_num [bigSide, extent]

theorem print_cube : IsDCubePrint 2 1 0 emptyTower 0 centre := by
  refine ⟨by omega, ?_, centre, ?_, Or.inr ⟨rfl, by simp [emptyTower]⟩⟩
  · intro μ
    rfl
  · rw [dCube_eq]
    intro μ
    refine ⟨0, by norm_num [bigSide], by norm_num [bigSide], ?_⟩
    simp

theorem empty_target : printedCube5 (bigSide 1 2 0) centre ∩ emptyTower.Om 0 = ∅ := by
  simp [emptyTower]

theorem no_class_set (F : ℕ) :
    ¬ ∃ (sites : Set (PeriodicLatticeSite extent)) (i : ℕ),
      IsClassSetW 2 1 F 0 emptyTower sites i := by
  rintro ⟨sites, i, hi⟩
  obtain ⟨x, hx, hxB⟩ := hi.2.2.1
  simp [towerBj, emptyTower] at hxB

#print axioms admissible
#print axioms torus_bound
#print axioms print_cube
#print axioms empty_target
#print axioms no_class_set
end SolCube5EmptyCase
