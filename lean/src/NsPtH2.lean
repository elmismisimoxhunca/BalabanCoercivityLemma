import NsPtH1

/-!
# PtH2 -- membership of rows in `bondsLam` for the nested instance (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)

variable {ell M R : ℕ}

theorem hNL (hP : PGeo ell M R) : scaleUp ell 2 (neLu M R) 0 + 1 = neN ell M R :=
  ne_scaleUp (by have := hP.hell; omega) hP.hM 0

theorem cs_x0 (hP : PGeo ell M R) (n : ℕ) (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (h : (y 0).val + n < neN ell M R) : ((coarseShift y n 0) 0).val = (y 0).val + n := by
  rw [coarseShift_val_eq]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_eq h (hNL hP).symm)

theorem sh_x0 (hP : PGeo ell M R) (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (h : (y 0).val + 1 < neN ell M R) : ((periodicLatticeShift y 0) 0).val = (y 0).val + 1 := by
  rw [shift_x0]
  simp only [if_true]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_eq h (hNL hP).symm)

/-- transverse rows: `(y,μ) ∈ bondsLam j ↔ y aligned ∧ the slice is a row slice`. -/
theorem bondsLam_trans_iff (hP : PGeo ell M R) {j : ℕ} (hj : j ≤ 2) (μ : Fin 3) (hμ : μ ≠ 0)
    (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) :
    (y, μ) ∈ bondsLam (geomOf ell 2 (neS ell M R)) j ↔ (Crs (ell ^ j) y ∧ isRowN ell M R j (y 0).val) := by
  have hg : NGeo ell M R := nGeo hP.hell hP.hdell hP.hM hP.hR
  have hM := hP.hM
  have hell : 0 < ell := by have := hP.hell; omega
  have hdiv := dvd_scaleUp (R := R) hell hM
  set z := coarseShift y ((geomOf ell 2 (neS ell M R)).ell ^ j) μ with hz
  have hG : (geomOf ell 2 (neS ell M R)).ell = ell := rfl
  have hz0 : (z 0) = y 0 := coarseShift_apply_ne y _ μ 0 (Ne.symm hμ)
  have hzc : Crs (ell ^ j) z ↔ Crs (ell ^ j) y := by
    rw [hz, hG]
    exact crs_coarseShift_iff (fun μ => hdiv μ hj) y μ (ell ^ j) dvd_rfl
  have o1 := hg.hP0P1; have o2 := hg.hP1A; have o3 := hg.hAB'; have o4 := hg.hB'A; have o5 := hg.hAB; have o6 := hg.hBQ1; have o7 := hg.hQ1Q0
  unfold bondsLam
  simp only [Set.mem_setOf_eq]
  rw [mem_Lam j y ∅, mem_Lam j z ∅, omGe_iff _ y hell hM, omGe_iff _ z hell hM, hz0, hzc]
  simp only [or_self]
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj' with rfl | rfl | rfl
  · have h1 := omGe0_1 hg (y 0).val
    simp only [pow_zero, Omv, isRowN, reg0, zero_add]
    rw [h1]
    constructor
    · rintro ⟨⟨hc, hp, hq⟩, hr⟩
      exact ⟨hc, by omega⟩
    · rintro ⟨hc, hr⟩
      exact ⟨⟨hc, by omega, by omega⟩, by omega⟩
  · have h2 := omGe0_2 hg (y 0).val
    simp only [pow_one, Omv, isRowN, reg1, zero_add, Nat.reduceAdd]
    rw [h2]
    constructor
    · rintro ⟨⟨hc, hp, hq⟩, hr⟩
      exact ⟨hc, hc 0, hp, hq⟩
    · rintro ⟨hc, hdv, hp, hq⟩
      exact ⟨⟨hc, hp, hq⟩, hq⟩
  · have h3 := omGe0_3 (ell := ell) (M := M) (R := R) (y 0).val
    simp only [Omv, isRowN, Nat.reduceAdd]
    constructor
    · rintro ⟨⟨hc, hp, hq⟩, hr⟩
      exact ⟨hc, hc 0, hp⟩
    · rintro ⟨hc, hdv, hp⟩
      exact ⟨⟨hc, hp, fun h => h⟩, h3⟩


theorem bondsLam_dir0_lvl0 (hP : PGeo ell M R) (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (h : (neP0 ell M R ≤ (y 0).val + 1 ∧ (y 0).val + 2 ≤ neP1 ell M R) ∨
         (neQ1 ell M R ≤ (y 0).val ∧ (y 0).val + 1 ≤ neQ0 ell M R)) :
    (y, (0 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) 0 := by
  have hg : NGeo ell M R := nGeo hP.hell hP.hdell hP.hM hP.hR
  have hqN := hP.hqN
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ (by have := hP.hell; omega)
  have c1 := hP.hpa; have c2 := hP.hab; have c3 := hP.hba; have c4 := hP.hab2; have c5 := hP.hbq; have c6 := hP.hq1q0
  have hlt : (y 0).val + 1 < neN ell M R := by omega
  have hs := sh_x0 hP y hlt
  have hcp := hP.collar_p
  have hcq := hP.collar_q
  have hrm := hP.rm2
  refine bondsLam0_of hg hP.hM (y, 0) ?_ ?_ ?_
  · show y ∈ (geomOf ell 2 (neS ell M R)).Om0 ∨ periodicLatticeShift y 0 ∈ (geomOf ell 2 (neS ell M R)).Om0
    rcases h with h | h
    · right; exact (Omv_site 0 _).mpr (by rw [hs]; simp only [Omv]; omega)
    · left; exact (Omv_site 0 _).mpr (by simp only [Omv]; omega)
  · show ¬ Omv ell M R 1 (y 0).val
    simp only [Omv]; omega
  · show ¬ Omv ell M R 1 ((periodicLatticeShift y 0) 0).val
    rw [hs]; simp only [Omv]; omega

theorem bondsLam_dir0_lvl1 (hP : PGeo ell M R) (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (hc : Crs ell y)
    (h : (neP1 ell M R ≤ (y 0).val + ell ∧ (y 0).val + 2 * ell ≤ neA' ell M R) ∨
         (neB' ell M R ≤ (y 0).val ∧ (y 0).val + 2 * ell ≤ neA ell M R) ∨
         (neB ell M R ≤ (y 0).val ∧ (y 0).val + ell ≤ neQ1 ell M R)) :
    (y, (0 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) 1 := by
  have hg : NGeo ell M R := nGeo hP.hell hP.hdell hP.hM hP.hR
  have hell : 0 < ell := by have := hP.hell; omega
  have hM := hP.hM
  have hqN := hP.hqN
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ hell
  have hl2 : ell ≤ ell ^ 2 := by nlinarith [pow_two ell]
  have hdiv := dvd_scaleUp (R := R) hell hM
  have hlt : (y 0).val + ell < neN ell M R := by
    have := hP.hpa; have := hP.hab; have := hP.hba; have := hP.hab2; have := hP.hbq; have := hP.hq1q0; omega
  have hz0 := cs_x0 hP ell y hlt
  have hzc : Crs ell (coarseShift y ell 0) := (crs_coarseShift_iff (fun μ => by simpa using hdiv μ (j := 1) (by norm_num)) y 0 ell dvd_rfl).mpr hc
  have o3 := hP.hpa; have o4 := hP.hab; have o5 := hP.hba; have o6 := hP.hab2; have o7 := hP.hbq
  have hG : (geomOf ell 2 (neS ell M R)).ell = ell := rfl
  unfold bondsLam
  simp only [Set.mem_setOf_eq, hG, pow_one]
  rw [mem_Lam 1 y ∅, mem_Lam 1 _ ∅, omGe_iff _ y hell hM, omGe_iff _ _ hell hM, omGe0_2 hg, omGe0_2 hg, hz0]
  simp only [pow_one, Omv, reg2]
  rcases h with h | h | h
  · refine ⟨Or.inr ⟨hzc, ?_, ?_⟩, ?_⟩ <;> omega
  · refine ⟨Or.inl ⟨hc, ?_, ?_⟩, ?_⟩ <;> omega
  · refine ⟨Or.inl ⟨hc, ?_, ?_⟩, ?_⟩ <;> omega


theorem bondsLam_dir0_lvl2 (hP : PGeo ell M R) (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (hc : Crs (ell ^ 2) y)
    (h : (neA' ell M R ≤ (y 0).val + ell ^ 2 ∧ (y 0).val + ell ^ 2 ≤ neB' ell M R) ∨
         (neA ell M R ≤ (y 0).val + ell ^ 2 ∧ (y 0).val + ell ^ 2 ≤ neB ell M R)) :
    (y, (0 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) 2 := by
  have hg : NGeo ell M R := nGeo hP.hell hP.hdell hP.hM hP.hR
  have hell : 0 < ell := by have := hP.hell; omega
  have hM := hP.hM
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ hell
  have hdiv := dvd_scaleUp (R := R) hell hM
  have hlt : (y 0).val + ell ^ 2 < neN ell M R := by
    have := hP.hpa; have := hP.hab; have := hP.hba; have := hP.hab2; have := hP.hbq; have := hP.hq1q0
    have := hP.hqN; omega
  have hz0 := cs_x0 hP (ell ^ 2) y hlt
  have hzc : Crs (ell ^ 2) (coarseShift y (ell ^ 2) 0) :=
    (crs_coarseShift_iff (fun μ => hdiv μ (j := 2) le_rfl) y 0 (ell ^ 2) dvd_rfl).mpr hc
  have hG : (geomOf ell 2 (neS ell M R)).ell = ell := rfl
  have hy0 := hc 0
  have o4 := hP.hab; have o5 := hP.hba; have o6 := hP.hab2
  unfold bondsLam
  simp only [Set.mem_setOf_eq, hG]
  rw [mem_Lam 2 y ∅, mem_Lam 2 _ ∅, omGe_iff _ y hell hM, omGe_iff _ _ hell hM, hz0]
  have n3 := omGe0_3 (ell := ell) (M := M) (R := R)
  simp only [Omv, reg2, Nat.reduceAdd]
  refine ⟨?_, by simp only [n3, or_self, not_false_eq_true]⟩
  rcases h with h | h
  · by_cases ha : neA' ell M R ≤ (y 0).val
    · exact Or.inl ⟨hc, Or.inl ⟨ha, by omega⟩, fun hh => hh⟩
    · have hlt' : (y 0).val < neA' ell M R := by omega
      have := step_le hy0 hP.d2a' hlt'
      exact Or.inr ⟨hzc, Or.inl ⟨by omega, by omega⟩, fun hh => hh⟩
  · by_cases ha : neA ell M R ≤ (y 0).val
    · exact Or.inl ⟨hc, Or.inr ⟨ha, by omega⟩, fun hh => hh⟩
    · have hlt' : (y 0).val < neA ell M R := by omega
      have := step_le hy0 hP.d2a hlt'
      exact Or.inr ⟨hzc, Or.inr ⟨by omega, by omega⟩, fun hh => hh⟩

end AdalyFormal.CoverOmega
