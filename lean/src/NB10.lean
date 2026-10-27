import NB9
/-!
# NB10 -- offset geometry for the corner gauge (piece N2, part 1)

`off y x σ = (x σ − y σ).val` (forward offset, mod the extent).  Elementary facts:
shifts change one offset by `n` (mod `N`), offsets add along a chain when no wrap occurs, the staircase
is three replicate segments, strided replicate paths visit `z + s t e_ρ`.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarseStraightSegment coarseCoordSteps
  coarsePathEndpoint)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS_eq)

variable {L : PeriodicLatticeExtent}

def off (y x : PeriodicLatticeSite L) (σ : Fin 3) : ℕ := (x σ - y σ).val

theorem off_lt (y x : PeriodicLatticeSite L) (σ : Fin 3) : off y x σ < L σ + 1 := (x σ - y σ).isLt

theorem off_self (y : PeriodicLatticeSite L) (σ : Fin 3) : off y y σ = 0 := by simp [off]

theorem off_shift_self (y x : PeriodicLatticeSite L) (n : ℕ) (ρ : Fin 3) :
    off y (coarseShift x n ρ) ρ = (off y x ρ + n) % (L ρ + 1) := by
  unfold off
  rw [shift_self, add_sub_right_comm, Fin.val_add]
  show ((x ρ - y ρ).val + n % (L ρ + 1)) % (L ρ + 1) = _
  rw [Nat.add_mod_mod]

theorem off_shift_ne (y x : PeriodicLatticeSite L) (n : ℕ) {ρ σ : Fin 3} (h : σ ≠ ρ) :
    off y (coarseShift x n ρ) σ = off y x σ := by
  unfold off; rw [shift_ne x n h]

/-- Offsets add along a chain when no wrap occurs. -/
theorem off_add (y c x : PeriodicLatticeSite L) (σ : Fin 3)
    (h : off c x σ + off y c σ < L σ + 1) : off y x σ = off c x σ + off y c σ := by
  unfold off at *
  rw [show x σ - y σ = (x σ - c σ) + (c σ - y σ) by abel, Fin.val_add, Nat.mod_eq_of_lt h]

theorem endpoint_rep (s : ℕ) (z : PeriodicLatticeSite L) (n : ℕ) (ρ : Fin 3) :
    coarsePathEndpoint s z (List.replicate n ρ) = coarseShift z (s * n) ρ := cPlusS_eq s n (z, ρ)

theorem gamma_eq (s : ℕ) (c x : PeriodicLatticeSite L) :
    coarseGammaPath s c x = List.replicate (off c x 2 / s) 2 ++
      (List.replicate (off c x 1 / s) 1 ++ List.replicate (off c x 0 / s) 0) := by
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  simp only [coarseGammaPath, coarseStraightSegment, coarseCoordSteps, off,
    Function.update_of_ne h12, Function.update_of_ne h02, Function.update_of_ne h01]

theorem pathBonds_append (s : ℕ) : ∀ (p q : List (Fin 3)) (z : PeriodicLatticeSite L),
    pathBonds s z (p ++ q) = pathBonds s z p ++ pathBonds s (coarsePathEndpoint s z p) q := by
  intro p q
  induction p with
  | nil => intro z; rfl
  | cons μ r ih => intro z; simp only [List.cons_append, pathBonds, ih]; rfl

theorem mem_pathBonds_rep (s : ℕ) (ρ : Fin 3) : ∀ (n : ℕ) (z : PeriodicLatticeSite L)
    (b : PeriodicLatticeEdge L), b ∈ pathBonds s z (List.replicate n ρ) →
      ∃ t < n, b = (coarseShift z (s * t) ρ, ρ) := by
  intro n
  induction n with
  | zero => intro z b hb; simp [pathBonds] at hb
  | succ k ih =>
      intro z b hb
      rw [List.replicate_succ] at hb
      rcases List.mem_cons.mp hb with h | h
      · exact ⟨0, by omega, by rw [h]; rfl⟩
      · obtain ⟨t, ht, rfl⟩ := ih _ b h
        refine ⟨t + 1, by omega, ?_⟩
        rw [← shift_add, Nat.mul_succ]

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.off_shift_self
#print axioms AdalyFormal.CurvBlock.gamma_eq
#print axioms AdalyFormal.CurvBlock.mem_pathBonds_rep
