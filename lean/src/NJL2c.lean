import NJL2b

/-!
# NJL2c -- (volume-free L2, step 3) translation sums over coarse base points, and the offset set `D`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge)

variable {L : PeriodicLatticeExtent}

/-- `‖g‖₁`. -/
def l1 (g : PeriodicLatticeEdge L → ℝ) : ℝ := ∑ e : PeriodicLatticeEdge L, g e

theorem sum_translate (g : PeriodicLatticeEdge L → ℝ) (a : PeriodicLatticeSite L) (ν : Fin 3) :
    ∑ y : PeriodicLatticeSite L, g (y + a, ν) = ∑ z : PeriodicLatticeSite L, g (z, ν) :=
  Fintype.sum_equiv (Equiv.addRight a) _ _ (fun y => rfl)

theorem sum_le_l1 (g : PeriodicLatticeEdge L → ℝ) (hg : ∀ e, 0 ≤ g e) (ν : Fin 3) :
    ∑ z : PeriodicLatticeSite L, g (z, ν) ≤ l1 g := by
  unfold l1
  rw [Fintype.sum_prod_type_right]
  exact Finset.single_le_sum (f := fun ν' : Fin 3 => ∑ z : PeriodicLatticeSite L, g (z, ν'))
    (fun ν' _ => Finset.sum_nonneg (fun z _ => hg _)) (Finset.mem_univ ν)

theorem list_sum_swap {ι α : Type*} [Fintype ι] (B : List α) (h : ι → α → ℝ) :
    ∑ y : ι, (B.map (h y)).sum = (B.map (fun e => ∑ y : ι, h y e)).sum := by
  induction B with
  | nil => simp
  | cons e rest ih => simp [Finset.sum_add_distrib, ih]

theorem list_sum_le {α : Type*} (B : List α) (F : α → ℝ) (c : ℝ) (h : ∀ e, F e ≤ c) :
    (B.map F).sum ≤ B.length * c := by
  induction B with
  | nil => simp
  | cons e rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith [h e, ih]

/-- translating the base point of a path and summing over ALL base points: `≤ |path| · ‖g‖₁`. -/
theorem sum_pathSum_translate (g : PeriodicLatticeEdge L → ℝ) (hg : ∀ e, 0 ≤ g e)
    (a : PeriodicLatticeSite L) (q : List (Fin 3)) :
    ∑ y : PeriodicLatticeSite L, pathSum g (y + a) q ≤ q.length * l1 g := by
  have h : ∀ y : PeriodicLatticeSite L, pathSum g (y + a) q
      = ((bondsOf a q).map (fun e => g (y + e.1, e.2))).sum := by
    intro y
    unfold pathSum
    rw [bondsOf_add, List.map_map]
    rfl
  simp_rw [h]
  rw [list_sum_swap (bondsOf a q) (fun y e => g (y + e.1, e.2))]
  have := list_sum_le (bondsOf a q) (fun e => ∑ y : PeriodicLatticeSite L, g (y + e.1, e.2)) (l1 g)
    (fun e => by rw [sum_translate]; exact sum_le_l1 g hg _)
  rwa [bondsOf_length] at this

#print axioms sum_pathSum_translate

end AdalyFormal.NonflatJet
