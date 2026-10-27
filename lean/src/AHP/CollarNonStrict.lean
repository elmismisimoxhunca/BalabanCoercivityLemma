import ZT5A

set_option autoImplicit false
set_option maxRecDepth 8000

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

namespace AdalyFormal.Fidelity.SheetVariants

def AdmissibleNonStrict {L : PeriodicLatticeExtent}
    (ell M R k : ℕ) (S : Tower L) : Prop :=
  (∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j) ∧
  (∀ j : ℕ, k < j → S.Om j = ∅) ∧
  (∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, bigSide M ell j ∣ (L μ + 1)) ∧
  (∀ j : ℕ, j ≤ k → BlockClosed (bigSide M ell j) (S.Om j)) ∧
  (∀ j : ℕ, j ≤ k → ∀ x : PeriodicLatticeSite L, x ∉ S.Om j →
    ∀ y ∈ S.Om (j + 1), R * bigSide M ell j ≤ pdist x y) ∧
  (∀ x : PeriodicLatticeSite L, x ∈ S.Om 0 ↔
    ∃ y ∈ S.Om 1, ∃ z : PeriodicLatticeSite L,
      (∀ μ : Fin 3, (z μ).val / M = (x μ).val / M) ∧ pdist z y ≤ R * M)

def L8 : PeriodicLatticeExtent := fun _ => 7

def collarSep : Tower L8 :=
  ⟨fun j => if j = 0 then Set.univ
    else if j = 1 then {x | ¬ (4 ≤ (x 0).val ∧ (x 0).val < 6 ∧
      4 ≤ (x 1).val ∧ (x 1).val < 6 ∧ (x 2).val < 2)}
    else if j = 2 then {x | ∀ μ : Fin 3, (x μ).val < 4}
    else ∅⟩

theorem admissible_imp_nonstrict {L : PeriodicLatticeExtent} (ell M R k : ℕ)
    (S : Tower L) :
    Admissible ell M R k S → AdmissibleNonStrict ell M R k S := by
  rintro ⟨hn, he, hd, hb, hc, hbase⟩
  exact ⟨hn, he, hd, hb, fun j hj x hx y hy => (hc j hj x hx y hy).le, hbase⟩

theorem admissibleNonStrict_k1_iff {L : PeriodicLatticeExtent} (ell M R : ℕ)
    (S : Tower L) :
    AdmissibleNonStrict ell M R 1 S ↔ Admissible ell M R 1 S := by
  constructor
  · rintro ⟨hn, he, hd, hb, hc, hbase⟩
    refine ⟨hn, he, hd, hb, ?_, hbase⟩
    intro j hj x hx y hy
    interval_cases j
    · by_contra h
      apply hx
      apply (hbase x).mpr
      exact ⟨y, hy, x, fun _ => rfl, by simpa [bigSide] using (Nat.le_of_not_gt h)⟩
    · rw [he 2 (by omega)] at hy
      exact hy.elim
  · exact admissible_imp_nonstrict ell M R 1 S

-- Coordinate expansion keeps the finite geometry proof arithmetic rather than exhaustive.
theorem pdist_L8 (x y : PeriodicLatticeSite L8) :
    pdist x y = pcd 8 (x 0).val (y 0).val +
      pcd 8 (x 1).val (y 1).val + pcd 8 (x 2).val (y 2).val := by
  simp [pdist, L8, Fin.sum_univ_succ, Nat.add_assoc]

theorem collar_separator :
    AdmissibleNonStrict 2 1 1 2 collarSep ∧ ¬ Admissible 2 1 1 2 collarSep := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j x hx
      by_cases h0 : j = 0
      · simp [collarSep, h0]
      by_cases h1 : j = 1
      · subst j
        change (∀ μ : Fin 3, (x μ).val < 4) at hx
        change ¬ (4 ≤ (x 0).val ∧ (x 0).val < 6 ∧
          4 ≤ (x 1).val ∧ (x 1).val < 6 ∧ (x 2).val < 2)
        have := hx 0
        omega
      · have hj : j + 1 ≠ 0 ∧ j + 1 ≠ 1 ∧ j + 1 ≠ 2 := by omega
        simp [collarSep, hj.1, hj.2.1, hj.2.2, h0] at hx
    · intro j hj
      simp [collarSep, show j ≠ 0 by omega, show j ≠ 1 by omega, show j ≠ 2 by omega]
    · intro j hj μ
      interval_cases j <;> norm_num [bigSide, L8]
    · intro j hj x hx y hxy
      interval_cases j
      · simp [collarSep]
      · change ¬ (4 ≤ (x 0).val ∧ (x 0).val < 6 ∧
          4 ≤ (x 1).val ∧ (x 1).val < 6 ∧ (x 2).val < 2) at hx
        change ¬ (4 ≤ (y 0).val ∧ (y 0).val < 6 ∧
          4 ≤ (y 1).val ∧ (y 1).val < 6 ∧ (y 2).val < 2)
        have h0 := hxy 0
        have h1 := hxy 1
        have h2 := hxy 2
        norm_num [bigSide] at h0 h1 h2
        omega
      · change (∀ μ : Fin 3, (x μ).val < 4) at hx
        change ∀ μ : Fin 3, (y μ).val < 4
        intro μ
        have hm := hxy μ
        have hxμ := hx μ
        norm_num [bigSide] at hm
        omega
    · intro j hj x hx y hy
      interval_cases j
      · simp [collarSep] at hx
      · change ¬ ¬ (4 ≤ (x 0).val ∧ (x 0).val < 6 ∧
          4 ≤ (x 1).val ∧ (x 1).val < 6 ∧ (x 2).val < 2) at hx
        have hx := not_not.mp hx
        change (∀ μ : Fin 3, (y μ).val < 4) at hy
        have hy0 := hy 0
        have hy1 := hy 1
        have h0 : 1 ≤ pcd 8 (x 0).val (y 0).val := by
          simp only [pcd, Nat.le_min]
          split_ifs <;> omega
        have h1 : 1 ≤ pcd 8 (x 1).val (y 1).val := by
          simp only [pcd, Nat.le_min]
          split_ifs <;> omega
        simp only [bigSide, pow_one, Nat.one_mul, pdist_L8]
        omega
      · simp [collarSep] at hy
    · intro x
      simp only [collarSep, reduceIte, Set.mem_univ, Set.mem_setOf_eq, Nat.div_one, Nat.mul_one,
        true_iff]
      by_cases hx : ¬ (4 ≤ (x 0).val ∧ (x 0).val < 6 ∧
          4 ≤ (x 1).val ∧ (x 1).val < 6 ∧ (x 2).val < 2)
      · refine ⟨x, hx, x, fun _ => rfl, ?_⟩
        simp [pdist_L8, pcd]
      · have hx := not_not.mp hx
        by_cases h4 : (x 0).val = 4
        · let y : PeriodicLatticeSite L8 := Function.update x 0 3
          refine ⟨y, ?_, x, fun _ => rfl, ?_⟩
          · simp [y, L8]
          · simp [pdist_L8, pcd, y, h4, L8]
        · have h5 : (x 0).val = 5 := by omega
          let y : PeriodicLatticeSite L8 := Function.update x 0 6
          refine ⟨y, ?_, x, fun _ => rfl, ?_⟩
          · simp [y, L8]
          · simp [pdist_L8, pcd, y, h5, L8]
  · intro h
    let x : PeriodicLatticeSite L8 := fun μ => if μ = 2 then 0 else 4
    let y : PeriodicLatticeSite L8 := fun μ => if μ = 2 then 0 else 3
    have hx : x ∉ collarSep.Om 1 := by
      change ¬ ¬ (4 ≤ (x 0).val ∧ (x 0).val < 6 ∧
        4 ≤ (x 1).val ∧ (x 1).val < 6 ∧ (x 2).val < 2)
      decide
    have hy : y ∈ collarSep.Om 2 := by
      change ∀ μ : Fin 3, (y μ).val < 4
      decide
    have hdist : pdist x y = 2 := by decide
    have hc := h.2.2.2.2.1 1 (by omega) x hx y hy
    norm_num [bigSide, hdist] at hc

end AdalyFormal.Fidelity.SheetVariants

