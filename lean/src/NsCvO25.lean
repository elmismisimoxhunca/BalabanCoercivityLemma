import NsCvO24

/-!
# CvO25 -- coordinates of shifts, `nxt`/`prv` profile maps, hsInner helpers (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShiftEquiv periodicLatticeShiftBack_shift
  periodicLatticeShift_shiftBack periodicLatticeShiftEquiv_apply periodicLatticeShiftEquiv_symm_apply)

variable {L : PeriodicLatticeExtent}

/-- successor on `{0..N}` cyclically. -/
def nxt (N v : ℕ) : ℕ := if v = N then 0 else v + 1
/-- predecessor on `{0..N}` cyclically. -/
def prv (N v : ℕ) : ℕ := if v = 0 then N else v - 1

theorem shift_coord_ne (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) : (periodicLatticeShift x μ) ν = x ν := by
  unfold periodicLatticeShift; exact Function.update_of_ne h _ _

theorem val_shift0 (x : PeriodicLatticeSite L) : ((periodicLatticeShift x 0) 0).val = nxt (L 0) (x 0).val := by
  unfold periodicLatticeShift nxt
  rw [Function.update_self, Fin.val_add_one]
  by_cases h : x 0 = Fin.last (L 0)
  · rw [if_pos h, if_pos (by rw [h]; simp)]
  · rw [if_neg h, if_neg (fun h' => h (Fin.ext (by simp [h'])))]

theorem val_shiftBack0 (y : PeriodicLatticeSite L) : ((periodicLatticeShiftBack y 0) 0).val = prv (L 0) (y 0).val := by
  unfold periodicLatticeShiftBack prv
  rw [Function.update_self, Fin.coe_sub_one]
  by_cases h : y 0 = 0
  · rw [if_pos h, if_pos (by rw [h]; rfl)]
  · rw [if_neg h, if_neg (fun h' => h (Fin.ext (by simpa using h')))]

theorem hsInner_dgS_one (Y : SuTwo) (a : ℝ) : hsInner Y (dgS a) = a * hsInner Y (dgS 1) := by
  simpa using hsInner_dgS_smul Y a 1

#print axioms val_shift0
#print axioms val_shiftBack0
#print axioms hsInner_dgS_one

end AdalyFormal.CoverOmega
