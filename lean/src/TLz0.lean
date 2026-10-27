import ZT5A

/-!
# TLz0 -- the covering map of periodic lattices (lane m2_thin_20261015)
`Covers Lt L` : every side of `L` divides the corresponding side of `Lt`.  `projS` reduces coordinates modulo the side of `L`.
-/
set_option autoImplicit false
namespace AdalyFormal.Thin

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- `L` is a quotient of `Lt` (side lengths divide). -/
def Covers (Lt L : PeriodicLatticeExtent) : Prop := ∀ μ : Fin 3, (L μ + 1) ∣ (Lt μ + 1)

theorem Covers.refl (L : PeriodicLatticeExtent) : Covers L L := fun _ => dvd_rfl

theorem Covers.trans {A B C : PeriodicLatticeExtent} (h1 : Covers A B) (h2 : Covers B C) : Covers A C :=
  fun μ => (h2 μ).trans (h1 μ)

/-- projection of sites (coordinatewise reduction modulo the smaller side). -/
def projS {Lt L : PeriodicLatticeExtent} (_h : Covers Lt L) (x : PeriodicLatticeSite Lt) : PeriodicLatticeSite L :=
  fun μ => ⟨(x μ).val % (L μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem projS_val {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (x : PeriodicLatticeSite Lt) (μ : Fin 3) :
    (projS h x μ).val = (x μ).val % (L μ + 1) := rfl

theorem fin_add_one_val {n : ℕ} (a : Fin (n + 1)) : (a + 1).val = (a.val + 1) % (n + 1) := by
  rw [Fin.val_add, Fin.val_one']
  simp [Nat.add_mod]

theorem projS_shift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (x : PeriodicLatticeSite Lt) (μ : Fin 3) :
    projS h (periodicLatticeShift x μ) = periodicLatticeShift (projS h x) μ := by
  funext ν
  apply Fin.ext
  by_cases hν : ν = μ
  · subst hν
    simp only [projS_val, periodicLatticeShift, Function.update_self, fin_add_one_val]
    rw [Nat.mod_mod_of_dvd _ (h ν), Nat.mod_add_mod]
  · simp [projS_val, periodicLatticeShift, Function.update_of_ne hν]

end AdalyFormal.Thin
