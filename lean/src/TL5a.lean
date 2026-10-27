import TL4c

/-!
# TL5a -- affine covers `phiS h o : x ↦ (x + o) mod (L+1)`: one map family covering both the projection (`o = 0`) and the deck translations
-/
set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

def phiS {Lt L : PeriodicLatticeExtent} (_h : Covers Lt L) (o : Fin 3 → ℕ) (x : PeriodicLatticeSite Lt) : PeriodicLatticeSite L :=
  fun μ => ⟨((x μ).val + o μ) % (L μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem phiS_val {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (x : PeriodicLatticeSite Lt) (μ : Fin 3) :
    (phiS h o x μ).val = ((x μ).val + o μ) % (L μ + 1) := rfl

theorem mod_shift_nat (a o m N : ℕ) (hmN : m ∣ N) : ((a + 1) % N + o) % m = ((a + o) % m + 1) % m := by
  have e1 : ((a + 1) % N + o) % m = (a + 1 + o) % m := by
    rw [← Nat.mod_add_mod ((a + 1) % N) m o, Nat.mod_mod_of_dvd _ hmN, Nat.mod_add_mod]
  rw [e1, Nat.mod_add_mod, show a + 1 + o = a + o + 1 by omega]

theorem phiS_shift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (x : PeriodicLatticeSite Lt) (μ : Fin 3) :
    phiS h o (periodicLatticeShift x μ) = periodicLatticeShift (phiS h o x) μ := by
  funext ν
  apply Fin.ext
  by_cases hν : ν = μ
  · subst hν
    simp only [phiS_val, periodicLatticeShift, Function.update_self, fin_add_one_val]
    exact mod_shift_nat _ _ _ _ (h ν)
  · simp [phiS_val, periodicLatticeShift, Function.update_of_ne hν]

end AdalyFormal.Thin
