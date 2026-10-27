import NtCvOH3

/-!
# CvOH4 -- `bondsLam` for the nested instance: direction-1 bonds, and alignment of all base sites (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)

variable {ell M R : ℕ}

theorem dvd_scaleUp (hell : 0 < ell) (hM : 0 < M) (μ : Fin 3) {j : ℕ} (hj : j ≤ 2) : ell ^ j ∣ scaleUp ell 2 (neLu M R) μ + 1 := by
  rw [ne_scaleUp hell hM]
  have h2 : ell ^ 2 ∣ neN ell M R := ⟨M * (4 * R + (2 * CfData.cf + 6)), by unfold neN; ring⟩
  exact dvd_trans (pow_dvd_pow ell hj) h2

theorem bondsLam_one_iff (hg : NGeo ell M R) (hM : 0 < M) {j : ℕ} (hj : j ≤ 2)
    (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) :
    (y, (1 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) j ↔ (Crs (ell ^ j) y ∧ isRowN ell M R j (y 0).val) := by
  have hell : 0 < ell := by have := hg.hell; omega
  have hdiv := dvd_scaleUp (R := R) hell hM
  set z := coarseShift y ((geomOf ell 2 (neS ell M R)).ell ^ j) 1 with hz
  have hG : (geomOf ell 2 (neS ell M R)).ell = ell := rfl
  have hz0 : (z 0) = y 0 := coarseShift_apply_ne y _ 1 0 (by decide)
  have hzc : Crs (ell ^ j) z ↔ Crs (ell ^ j) y := by
    rw [hz, hG]
    exact crs_coarseShift_iff (fun μ => hdiv μ hj) y 1 (ell ^ j) dvd_rfl
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

theorem crs_of_bondsLam (hg : NGeo ell M R) (hM : 0 < M) {j : ℕ} (hj : j ≤ 2)
    (b : Bond (scaleUp ell 2 (neLu M R))) (hb : b ∈ bondsLam (geomOf ell 2 (neS ell M R)) j) : Crs (ell ^ j) b.1 := by
  have hell : 0 < ell := by have := hg.hell; omega
  have hdiv := dvd_scaleUp (R := R) hell hM
  have hG : (geomOf ell 2 (neS ell M R)).ell = ell := rfl
  obtain ⟨h1, -⟩ := hb
  rcases h1 with h | h
  · exact ((mem_Lam j b.1 ∅).mp h).1
  · have hc := ((mem_Lam j _ ∅).mp h).1
    rw [hG] at hc
    exact (crs_coarseShift_iff (fun μ => hdiv μ hj) b.1 b.2 (ell ^ j) dvd_rfl).mp hc

#print axioms bondsLam_one_iff
#print axioms crs_of_bondsLam

end AdalyFormal.CoverOmega
