import NJE1

/-!
# NJE2 -- holonomies, axial staircases and coordinate step counts commute with the sublattice embedding.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.NonflatJet

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath coarseCoordSteps
  coarseStraightSegment)

variable {L Lq : PeriodicLatticeExtent} {s : ℕ}

/-- the embedded edge. -/
def embE (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (e : PeriodicLatticeEdge Lq) : PeriodicLatticeEdge L :=
  (embS hs e.1, e.2)

/-- restriction of a link configuration to the sublattice. -/
def resV {G : Type*} (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (V : PeriodicLinkConfiguration G L) :
    PeriodicLinkConfiguration G Lq := fun e => V (embE hs e)

theorem embS_shift_one (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (y : PeriodicLatticeSite Lq) (μ : Fin 3) :
    coarseShift (embS hs y) s μ = embS hs (coarseShift y 1 μ) := by
  have := embS_shift_gen hs y 1 μ
  rwa [Nat.mul_one] at this

theorem hol_emb {G : Type*} [Group G] (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1))
    (V : PeriodicLinkConfiguration G L) (p : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite Lq,
      coarsePathHolonomy s V (embS hs y) p = coarsePathHolonomy 1 (resV hs V) y p := by
  induction p with
  | nil => intro y; rfl
  | cons μ rest ih =>
      intro y
      show V (embS hs y, μ) * coarsePathHolonomy s V (coarseShift (embS hs y) s μ) rest
        = resV hs V (y, μ) * coarsePathHolonomy 1 (resV hs V) (coarseShift y 1 μ) rest
      rw [embS_shift_one, ih]
      rfl

theorem embS_update (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (a b : PeriodicLatticeSite Lq) (μ : Fin 3) :
    Function.update (embS hs a) μ (embS hs b μ) = embS hs (Function.update a μ (b μ)) := by
  funext ν
  apply Fin.ext
  by_cases h : ν = μ
  · subst h; simp only [embS_val, Function.update_self]
  · simp only [embS_val, Function.update_of_ne h]

theorem coarseCoordSteps_emb (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (a b : PeriodicLatticeSite Lq)
    (μ : Fin 3) :
    coarseCoordSteps s (embS hs a) (embS hs b) μ = coarseCoordSteps 1 a b μ := by
  unfold coarseCoordSteps
  rw [Nat.div_one]
  have hspos := s_pos_of hs
  rw [Fin.val_sub, Fin.val_sub, embS_val, embS_val, hs μ]
  have h1 : s * (Lq μ + 1) - s * (a μ).val = s * (Lq μ + 1 - (a μ).val) := (Nat.mul_sub _ _ _).symm
  rw [h1, ← Nat.mul_add, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ hspos]

#print axioms hol_emb
#print axioms coarseCoordSteps_emb

end AdalyFormal.NonflatJet
