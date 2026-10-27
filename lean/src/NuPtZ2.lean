import NuPtZ
import NtCvOS12

/-!
# PtZ2 -- the row-independence determinant `gOf` of the sibling lane is nonzero at the flat nested point (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmegaTwo
open AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {ell M R : ℕ}

theorem block_Om0 (hP : PGeo ell M R) {j : ℕ} (hj : j ≤ 2) (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (hy : y ∈ (geomOf ell 2 (neS ell M R)).Lam j) (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (hx : x ∈ blockOf y (ell ^ j)) : x ∈ (geomOf ell 2 (neS ell M R)).Om0 := by
  have hell : 0 < ell := by have := hP.hell; omega
  obtain ⟨hc, hO, hN⟩ := (mem_Lam j y ∅).mp hy
  have hxw := (mem_blockOf.mp hx) 0
  have hv := hc 0
  refine (Omv_site 0 _).mpr ?_
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ hell
  have hl2 : ell ≤ ell ^ 2 := by nlinarith [pow_two ell]
  have c1 := hP.hpa; have c2 := hP.hab; have c3 := hP.hba; have c4 := hP.hab2; have c5 := hP.hbq; have c6 := hP.hq1q0
  have hcp := hP.collar_p; have hcq := hP.collar_q; have hrm := hP.rm2
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · simp only [pow_zero, Omv] at hxw hO ⊢; omega
  · simp only [pow_one, Omv] at hxw hO hN ⊢
    have hv1 : ell ∣ (y 0).val := by simpa using hv
    have := step_le hv1 hP.d1q (by omega : (y 0).val < neQ1 ell M R)
    omega
  · simp only [Omv, reg2] at hxw hO ⊢
    rcases hO with h | h
    · have := step_le hv hP.d2b' (show (y 0).val < neB' ell M R from by omega)
      omega
    · have := step_le hv hP.d2b (show (y 0).val < neB ell M R from by omega)
      omega

end AdalyFormal.CoverOmegaTwo
