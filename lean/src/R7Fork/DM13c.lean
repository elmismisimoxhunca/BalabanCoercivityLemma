import R7Fork.DM13b

/-!
# DM13c -- box connectedness; the tilted potential `Theta = phi + sum_nu (coordinate nu) c_nu`; the block relation for `Theta`
across a coarse bond (defect `-N c` exactly on seam-crossing bonds).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower Admissible bigSide BlockClosed)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice card_blockOf_of_coarse)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.CoarseShiftCovariance (coarseShift_blockOf_eq_image coarseShift_injective)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)

section tilt
variable {L : PeriodicLatticeExtent}

/-- the shift raises a non-last coordinate by one -/
theorem shift_val_same (hN : ∀ ν, 1 ≤ L ν) (w : PeriodicLatticeSite L) (ν : Fin 3) :
    ((periodicLatticeShift w ν) ν).val = ((w ν).val + 1) % (L ν + 1) := by
  rw [AdalyFormal.StatementLane2.shift_apply]
  simp only [if_true]
  exact AdalyFormal.StatementLane2.fin_succ_val ν (hN ν) (w ν)

theorem shift_val_ne (w : PeriodicLatticeSite L) {ν μ : Fin 3} (h : ν ≠ μ) :
    (periodicLatticeShift w μ) ν = w ν := by
  rw [AdalyFormal.StatementLane2.shift_apply]
  simp [h]

/-- a function with equal values across every in-box bond is constant on the box -/
theorem box_const {V : Type*} (hN : ∀ ν, 1 ≤ L ν) (f : PeriodicLatticeSite L → V) {n : ℕ} (hn : 0 < n)
    {z : PeriodicLatticeSite L} (hz : z ∈ CoarseLattice L n)
    (hadj : ∀ w ∈ blockOf z n, ∀ ν, (w ν).val + 1 < L ν + 1 → periodicLatticeShift w ν ∈ blockOf z n →
      f (periodicLatticeShift w ν) = f w) :
    ∀ w ∈ blockOf z n, f w = f z := by
  classical
  have key : ∀ t : ℕ, ∀ w ∈ blockOf z n, (∑ ρ : Fin 3, ((w ρ).val - (z ρ).val)) = t → f w = f z := by
    intro t
    induction t with
    | zero =>
      intro w hw ht
      have hall : ∀ ρ, (w ρ).val - (z ρ).val = 0 := fun ρ =>
        (Finset.sum_eq_zero_iff.mp ht) ρ (Finset.mem_univ _)
      have : w = z := by
        funext ρ
        apply Fin.ext
        have h1 := ((mem_blockOf.mp hw) ρ).1
        have := hall ρ
        omega
      rw [this]
    | succ t ih =>
      intro w hw ht
      have hex : ∃ ν, (z ν).val < (w ν).val := by
        by_contra hno
        push_neg at hno
        have : (∑ ρ : Fin 3, ((w ρ).val - (z ρ).val)) = 0 :=
          Finset.sum_eq_zero (fun ρ _ => by have := hno ρ; omega)
        omega
      obtain ⟨ν, hν⟩ := hex
      set w' : PeriodicLatticeSite L := Function.update w ν ⟨(w ν).val - 1, by have := (w ν).isLt; omega⟩ with hw'
      have hw'ν : (w' ν).val = (w ν).val - 1 := by simp [hw']
      have hw'ne : ∀ ρ, ρ ≠ ν → w' ρ = w ρ := fun ρ h => by simp [hw', h]
      have hw'b : w' ∈ blockOf z n := by
        rw [mem_blockOf]
        intro ρ
        by_cases h : ρ = ν
        · subst h
          have := (mem_blockOf.mp hw) ρ
          rw [hw'ν]; constructor <;> omega
        · rw [hw'ne ρ h]; exact (mem_blockOf.mp hw) ρ
      have hshift : periodicLatticeShift w' ν = w := by
        funext ρ
        by_cases h : ρ = ν
        · subst h
          apply Fin.ext
          rw [shift_val_same hN, hw'ν]
          have := (w ρ).isLt
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        · rw [shift_val_ne w' h, hw'ne ρ h]
      have hstep : f w = f w' := by
        have := hadj w' hw'b ν (by have := (w ν).isLt; omega) (by rw [hshift]; exact hw)
        rwa [hshift] at this
      rw [hstep]
      refine ih w' hw'b ?_
      have hs : ∑ ρ : Fin 3, ((w' ρ).val - (z ρ).val) + 1 = ∑ ρ : Fin 3, ((w ρ).val - (z ρ).val) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ ν), ← Finset.sum_erase_add _ (fun ρ => (w ρ).val - (z ρ).val) (Finset.mem_univ ν)]
        have : ∑ ρ ∈ Finset.univ.erase ν, ((w' ρ).val - (z ρ).val) = ∑ ρ ∈ Finset.univ.erase ν, ((w ρ).val - (z ρ).val) :=
          Finset.sum_congr rfl (fun ρ hρ => by rw [hw'ne ρ (Finset.ne_of_mem_erase hρ)])
        rw [this, hw'ν]
        omega
      omega
  intro w hw
  exact key _ w hw rfl

/-- the tilted potential: `Theta = phi + sum_nu (coordinate nu) c_nu` -/
noncomputable def Theta (φ : PeriodicLatticeSite L → SuTwo) (c : Fin 3 → SuTwo) (w : PeriodicLatticeSite L) : SuTwo :=
  φ w + ∑ ν : Fin 3, ((w ν).val : ℝ) • c ν

end tilt

end AdalyFormal.DirichletMono
