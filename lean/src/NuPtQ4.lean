import NuPtQ3

/-!
# PtQ4 -- the peak bond of a row lies in `bondsOm0` (lane omega/near2/point)
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
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice)
open AdalyFormal.Balaban.QOne (pathSite)

variable {ell M R : ℕ}

theorem rw0_peak (hP : PGeo ell M R) {j : ℕ} (hj : j ≤ 2) {v : ℕ} (h : Rw0 ell M R j v) :
    (neP0 ell M R ≤ v + (ell ^ j - 1) ∧ v + (ell ^ j - 1) < neQ0 ell M R) ∨
    (neP0 ell M R ≤ v + ell ^ j ∧ v + ell ^ j < neQ0 ell M R) := by
  have hell : 0 < ell := by have := hP.hell; omega
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ hell
  have hl2 : ell ≤ ell ^ 2 := by nlinarith [pow_two ell]
  have c1 := hP.hpa; have c2 := hP.hab; have c3 := hP.hba; have c4 := hP.hab2; have c5 := hP.hbq; have c6 := hP.hq1q0
  have hcp := hP.collar_p; have hcq := hP.collar_q; have hrm := hP.rm2; have hp := hP.hp
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · simp only [Rw0, pow_zero] at h ⊢; omega
  · simp only [Rw0, pow_one] at h ⊢; omega
  · simp only [Rw0] at h ⊢; omega

/-- the peak bond of a row of `bondsLam` lies in `bondsOm0`. -/
theorem peak_mem_Om0 (hP : PGeo ell M R) {j : ℕ} (hj : j ≤ 2) (Y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (μ : Fin 3) (hb : (Y, μ) ∈ bondsLam (geomOf ell 2 (neS ell M R)) j) :
    (pathSite Y μ (ell ^ j - 1), μ) ∈ bondsOm0 (geomOf ell 2 (neS ell M R)) := by
  have hg : NGeo ell M R := AdalyFormal.NcwdhTwo.nGeo_two hP.hell hP.hdell hP.hM hP.hR
  have hell : 0 < ell := by have := hP.hell; omega
  have hpos : 0 < ell ^ j := pow_pos hell j
  by_cases h0 : μ = 0
  · subst h0
    have hRw := row0_cond hP hj Y hb
    have hB := rw0_bound hP hj hRw
    have hpk := rw0_peak hP hj hRw
    have hY0 : (Y 0).val < neN ell M R := lt_of_lt_of_eq (Y 0).isLt (hNLμ hP 0)
    have hv1 : ((pathSite Y 0 (ell ^ j - 1)) 0).val = (Y 0).val + (ell ^ j - 1) := by
      rw [pathSite_self_val]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_eq (by omega) (hNL hP).symm)
    have hv2 : ((periodicLatticeShift (pathSite Y 0 (ell ^ j - 1)) 0) 0).val = (Y 0).val + ell ^ j := by
      rw [shift_val_self, hv1]
      have : (Y 0).val + (ell ^ j - 1) + 1 = (Y 0).val + ell ^ j := by omega
      rw [this]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_eq (by omega) (hNL hP).symm)
    show pathSite Y 0 (ell ^ j - 1) ∈ (geomOf ell 2 (neS ell M R)).Om0 ∨
      periodicLatticeShift (pathSite Y 0 (ell ^ j - 1)) 0 ∈ (geomOf ell 2 (neS ell M R)).Om0
    rcases hpk with h | h
    · left; exact (Omv_site 0 _).mpr (by rw [hv1]; simp only [Omv]; exact h)
    · right; exact (Omv_site 0 _).mpr (by rw [hv2]; simp only [Omv]; exact h)
  · obtain ⟨hcrs, hrow⟩ := (bondsLam_trans_iff hP hj μ h0 Y).mp hb
    show pathSite Y μ (ell ^ j - 1) ∈ (geomOf ell 2 (neS ell M R)).Om0 ∨
      periodicLatticeShift (pathSite Y μ (ell ^ j - 1)) μ ∈ (geomOf ell 2 (neS ell M R)).Om0
    left
    refine (Omv_site 0 _).mpr ?_
    have hx0 : ((pathSite Y μ (ell ^ j - 1)) 0).val = (Y 0).val := by rw [pathSite_ne _ _ _ (Ne.symm h0)]
    rw [hx0]
    have c1 := hP.hpa; have c2 := hP.hab; have c3 := hP.hba; have c4 := hP.hab2; have c5 := hP.hbq; have c6 := hP.hq1q0
    have hcp := hP.collar_p; have hcq := hP.collar_q
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · simp only [isRowN, reg0, Omv] at hrow ⊢; omega
    · simp only [isRowN, reg1, reg2, Omv] at hrow ⊢; omega
    · simp only [isRowN, reg2, Omv] at hrow ⊢; omega

end AdalyFormal.CoverOmegaTwo
