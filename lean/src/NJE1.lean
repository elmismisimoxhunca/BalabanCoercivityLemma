import NJ5Path

/-!
# NJE1 -- the stride-`s` sublattice of a torus `L` is a torus `Lq` (`L μ + 1 = s (Lq μ + 1)`): the site embedding
`embS : Site Lq → Site L`, `x ↦ s·x`, intertwines the strided shift on `L` with the unit shift on `Lq`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.NonflatJet

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.ReparamCDisjoint (pathSite_eq)
open AdalyFormal.Balaban.Q1Real (nsmul_one_val)

variable {L Lq : PeriodicLatticeExtent} {s : ℕ}

theorem s_pos_of (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) : 0 < s := by
  rcases Nat.eq_zero_or_pos s with h | h
  · have := hs 0; rw [h] at this; simp at this
  · exact h

/-- `x ↦ s·x`. -/
def embS (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (x : PeriodicLatticeSite Lq) : PeriodicLatticeSite L :=
  fun μ => ⟨s * (x μ).val, by
    have h1 := (x μ).isLt
    have h2 := hs μ
    have h3 := s_pos_of hs
    rw [h2]; exact Nat.mul_lt_mul_of_pos_left h1 h3⟩

theorem embS_val (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (x : PeriodicLatticeSite Lq) (μ : Fin 3) :
    (embS hs x μ).val = s * (x μ).val := rfl

theorem embS_injective (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) : Function.Injective (embS hs) := by
  intro x y h
  funext μ
  apply Fin.ext
  have := congrArg (fun z => (z μ).val) h
  simp only [embS_val] at this
  exact Nat.eq_of_mul_eq_mul_left (s_pos_of hs) this

theorem embS_shift_gen (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (y : PeriodicLatticeSite Lq) (n : ℕ)
    (μ : Fin 3) : coarseShift (embS hs y) (s * n) μ = embS hs (coarseShift y n μ) := by
  change pathSite (embS hs y) μ (s * n) = embS hs (pathSite y μ n)
  rw [pathSite_eq, pathSite_eq]
  funext ν
  apply Fin.ext
  rw [embS_val]
  by_cases h : ν = μ
  · subst h
    simp only [Function.update_self]
    rw [Fin.val_add, embS_val, nsmul_one_val, Fin.val_add, nsmul_one_val, hs ν, Nat.add_mod_mod,
      ← Nat.mul_add, Nat.mul_mod_mul_left, Nat.add_mod_mod]
  · simp only [Function.update_of_ne h]
    rw [embS_val]

#print axioms embS_injective
#print axioms embS_shift_gen

end AdalyFormal.NonflatJet
