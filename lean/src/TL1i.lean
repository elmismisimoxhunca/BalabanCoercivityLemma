import TL1h

set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)

def projE {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (e : PeriodicLatticeEdge Lt) : PeriodicLatticeEdge L :=
  (projS h e.1, e.2)

def liftU {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (U : LinkCfg L) : LinkCfg Lt := fun e => U (projE h e)

theorem projE_shift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (e : PeriodicLatticeEdge Lt) :
    projS h (periodicLatticeShift e.1 e.2) = periodicLatticeShift (projE h e).1 (projE h e).2 :=
  projS_shift h e.1 e.2

theorem shift_injective {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) (μ : Fin 3)
    (h : periodicLatticeShift x μ = periodicLatticeShift y μ) : x = y := by
  funext ν
  have := congrFun h ν
  by_cases hν : ν = μ
  · subst hν
    simp only [periodicLatticeShift, Function.update_self] at this
    exact add_right_cancel this
  · simpa [periodicLatticeShift, Function.update_of_ne hν] using this

theorem projS_shiftBack {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (x : PeriodicLatticeSite Lt) (μ : Fin 3) :
    projS h (periodicLatticeShiftBack x μ) = periodicLatticeShiftBack (projS h x) μ := by
  apply shift_injective _ _ μ
  rw [← projS_shift, periodicLatticeShift_shiftBack, periodicLatticeShift_shiftBack]

theorem gauge_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : LinkCfg L) (e : PeriodicLatticeEdge Lt) :
    periodicGaugeTransform (fun x => g (projS h x)) (liftU h U) e = periodicGaugeTransform g U (projE h e) := by
  unfold periodicGaugeTransform liftU
  show g (projS h e.1) * U (projE h e) * (g (projS h (periodicLatticeShift e.1 e.2)))⁻¹ = _
  rw [projE_shift]
  rfl

theorem isClassCube_of_described {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L}
    (hmono : ∀ j, S.Om (j + 1) ⊆ S.Om j) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (hd : DescribedAt ell M f k S sites j) : IsClassCube ell M f k S sites j := by
  refine ⟨hd, fun i hi => ?_⟩
  have anti : ∀ a b, a ≤ b → S.Om b ⊆ S.Om a := by
    intro a b hab
    induction hab with
    | refl => exact fun _ h => h
    | step _ ih => exact fun x hx => ih (hmono _ hx)
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- i < j
    obtain ⟨-, -, hsub, -⟩ := hd
    obtain ⟨-, -, -, ⟨y, hy1, hy2⟩⟩ := hi
    have : y ∈ S.Om (i + 1) := by
      rcases hsub hy1 with h | h
      · exact anti (i + 1) j hlt h.1
      · exact anti (i + 1) (j + 1) (by omega) h.1
    exact hy2.2 this
  · obtain ⟨-, -, -, ⟨y, hy1, hy2⟩⟩ := hd
    obtain ⟨-, -, hsub, -⟩ := hi
    have : y ∈ S.Om (j + 1) := by
      rcases hsub hy1 with h | h
      · exact anti (j + 1) i hgt h.1
      · exact anti (j + 1) (i + 1) (by omega) h.1
    exact hy2.2 this

end AdalyFormal.Thin
