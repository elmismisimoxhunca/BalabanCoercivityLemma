import NB13
/-!
# NB14 -- box bookkeeping for the cone of a coarse plaquette (piece N2, part 4)

`Box y s B z`: every offset of `z` from `y` is a multiple of `s` and `≤ B`.  Strided replicate paths and
staircases stay in the box under explicit linear conditions.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarsePathEndpoint)

variable {L : PeriodicLatticeExtent}

def Box (y : PeriodicLatticeSite L) (s B : ℕ) (z : PeriodicLatticeSite L) : Prop :=
  ∀ σ, s ∣ off y z σ ∧ off y z σ ≤ B

theorem box_shift (y z : PeriodicLatticeSite L) (s B t : ℕ) (ρ : Fin 3) (hz : Box y s B z)
    (h : off y z ρ + s * t ≤ B) (hB : B < L ρ + 1) : Box y s B (coarseShift z (s * t) ρ) := by
  intro σ
  by_cases hσ : σ = ρ
  · subst hσ
    rw [off_shift_self, Nat.mod_eq_of_lt (by omega)]
    exact ⟨Nat.dvd_add (hz σ).1 (Dvd.intro t rfl), h⟩
  · rw [off_shift_ne _ _ _ hσ]; exact hz σ

theorem off_shift_val (y z : PeriodicLatticeSite L) (n : ℕ) (ρ : Fin 3)
    (h : off y z ρ + n < L ρ + 1) : off y (coarseShift z n ρ) ρ = off y z ρ + n := by
  rw [off_shift_self, Nat.mod_eq_of_lt h]

theorem box_rep (y z : PeriodicLatticeSite L) (s B n : ℕ) (ρ : Fin 3) (hz : Box y s B z)
    (h : off y z ρ + s * n ≤ B + s) (hB : B < L ρ + 1) :
    ∀ b ∈ pathBonds s z (List.replicate n ρ), Box y s B b.1 := by
  intro b hb
  obtain ⟨t, ht, rfl⟩ := mem_pathBonds_rep s ρ n z b hb
  refine box_shift y z s B t ρ hz ?_ hB
  have : s * t + s ≤ s * n := by
    have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt ht)
    rwa [Nat.mul_succ] at this
  omega

/-- A three-segment staircase `rep a2 2 ++ (rep a1 1 ++ rep a0 0)` from `z0` stays in the box. -/
theorem box_stair (y z0 : PeriodicLatticeSite L) (s B a0 a1 a2 : ℕ) (hz : Box y s B z0)
    (h2 : off y z0 2 + s * a2 ≤ B) (h1 : off y z0 1 + s * a1 ≤ B) (h0 : off y z0 0 + s * a0 ≤ B)
    (hB : ∀ ρ, B < L ρ + 1) :
    ∀ b ∈ pathBonds s z0 (List.replicate a2 2 ++ (List.replicate a1 1 ++ List.replicate a0 0)),
      Box y s B b.1 := by
  have hz1 : Box y s B (coarseShift z0 (s * a2) 2) := box_shift y z0 s B a2 2 hz h2 (hB 2)
  have o1 : off y (coarseShift z0 (s * a2) 2) 1 = off y z0 1 :=
    off_shift_ne _ _ _ (by decide : (1 : Fin 3) ≠ 2)
  have o0 : off y (coarseShift z0 (s * a2) 2) 0 = off y z0 0 :=
    off_shift_ne _ _ _ (by decide : (0 : Fin 3) ≠ 2)
  have hz2 : Box y s B (coarseShift (coarseShift z0 (s * a2) 2) (s * a1) 1) :=
    box_shift y _ s B a1 1 hz1 (by rw [o1]; exact h1) (hB 1)
  have o0' : off y (coarseShift (coarseShift z0 (s * a2) 2) (s * a1) 1) 0 = off y z0 0 := by
    rw [off_shift_ne _ _ _ (by decide : (0 : Fin 3) ≠ 1), o0]
  intro b hb
  rw [pathBonds_append, pathBonds_append, endpoint_rep, endpoint_rep] at hb
  simp only [List.mem_append] at hb
  rcases hb with hb | hb | hb
  · exact box_rep y z0 s B a2 2 hz (by omega) (hB 2) b hb
  · exact box_rep y _ s B a1 1 hz1 (by rw [o1]; omega) (hB 1) b hb
  · exact box_rep y _ s B a0 0 hz2 (by rw [o0']; omega) (hB 0) b hb

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.box_rep
#print axioms AdalyFormal.CurvBlock.box_stair
