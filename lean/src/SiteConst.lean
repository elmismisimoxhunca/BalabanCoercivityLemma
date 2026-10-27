import SourceGauge
set_option autoImplicit false
namespace HConstruction.G0CoerceFinal.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
variable {L : PeriodicLatticeExtent}

theorem shift_invariant_of_grad_eq_zero (φ : PeriodicLatticeSite L → SuTwo)
    (h : gradValueCovariant (trivialU L) φ = 0) (s : PeriodicLatticeSite L) (ν : Fin 3) :
    φ (periodicLatticeShift s ν) = φ s := by
  have hR : RMap (trivialU L (s, ν)) = LinearMap.id := by
    show RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = LinearMap.id
    exact RMap_one
  have hb := congrFun h (s, ν)
  simp only [gradValueCovariant, hR, LinearMap.id_coe, id_eq, Pi.zero_apply] at hb
  exact sub_eq_zero.mp hb

theorem const_of_grad_eq_zero (φ : PeriodicLatticeSite L → SuTwo)
    (h : gradValueCovariant (trivialU L) φ = 0) (s t : PeriodicLatticeSite L) : φ s = φ t := by
  have hinv := shift_invariant_of_grad_eq_zero φ h
  -- one unit step in coordinate `ν`, phrased as an `update`
  have hstep : ∀ (ν : Fin 3) (u : PeriodicLatticeSite L) (a : Fin (L ν + 1)),
      φ (Function.update u ν (a + 1)) = φ (Function.update u ν a) := by
    intro ν u a
    have he : Function.update u ν (a + 1) =
        periodicLatticeShift (Function.update u ν a) ν := by
      unfold periodicLatticeShift
      rw [Function.update_self, Function.update_idem]
    rw [he, hinv]
  -- `Fin`-valued induction, done on the `val` (this tree's Mathlib has NO `NatCast (Fin (n+1))`
  -- instance available on `Fin (L ν + 1)` -- measured, see §F's note -- so `↑j` is unavailable and
  -- the induction is carried on the underlying natural number instead)
  have hval : ∀ (m : ℕ) (ν : Fin 3) (u : PeriodicLatticeSite L) (hm : m < L ν + 1),
      φ (Function.update u ν ⟨m, hm⟩) =
        φ (Function.update u ν ⟨0, Nat.succ_pos (L ν)⟩) := by
    intro m
    induction m with
    | zero => intro ν u hm; rfl
    | succ k ih =>
        intro ν u hm
        have hk : k < L ν + 1 := by omega
        have hone : (1 : Fin (L ν + 1)).val = 1 := by
          show 1 % (L ν + 1) = 1
          exact Nat.mod_eq_of_lt (by omega)
        have hadd : (⟨k, hk⟩ : Fin (L ν + 1)) + 1 = ⟨k + 1, hm⟩ := by
          apply Fin.val_injective
          rw [Fin.val_add, hone]
          exact Nat.mod_eq_of_lt hm
        rw [← hadd, hstep, ih ν u hk]
  have hupd : ∀ (ν : Fin 3) (u : PeriodicLatticeSite L) (a : Fin (L ν + 1)),
      φ (Function.update u ν a) = φ u := by
    intro ν u a
    have h1 : φ (Function.update u ν a) =
        φ (Function.update u ν ⟨0, Nat.succ_pos (L ν)⟩) := hval a.val ν u a.isLt
    have h2 : φ (Function.update u ν (u ν)) =
        φ (Function.update u ν ⟨0, Nat.succ_pos (L ν)⟩) := hval (u ν).val ν u (u ν).isLt
    rw [Function.update_eq_self] at h2
    rw [h1, ← h2]
  have hcases : ∀ ρ : Fin 3, ρ = 0 ∨ ρ = 1 ∨ ρ = 2 := by decide
  have hu3 : Function.update (Function.update (Function.update s 0 (t 0)) 1 (t 1)) 2 (t 2) = t := by
    funext ρ
    rcases hcases ρ with hρ | hρ | hρ <;> subst hρ
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self]
    · rw [Function.update_of_ne (by decide), Function.update_self]
    · rw [Function.update_self]
  calc φ s = φ (Function.update s 0 (t 0)) := (hupd 0 s (t 0)).symm
    _ = φ (Function.update (Function.update s 0 (t 0)) 1 (t 1)) := (hupd 1 _ (t 1)).symm
    _ = φ (Function.update (Function.update (Function.update s 0 (t 0)) 1 (t 1)) 2 (t 2)) :=
        (hupd 2 _ (t 2)).symm
    _ = φ t := by rw [hu3]


end HConstruction.G0CoerceFinal.Reproduced
