import NtCvOH1

/-!
# CvOH2 -- `Lam` and `OmGe` of the nested geometry as predicates of `x₀`; the three values of `omGe0` (lane omega)
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
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)

variable {ell M R : ℕ}

theorem mem_Lam (j : ℕ) (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (S : Set (PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))) :
    x ∈ (geomOf ell 2 (neS ell M R)).Lam j ↔ Crs (ell ^ j) x ∧ Omv ell M R j (x 0).val ∧ ¬ Omv ell M R (j + 1) (x 0).val := by
  simp only [geomOf, Set.mem_setOf_eq, Crs, Omv_site]

/-- block membership: `w ≤ v < w + m`, all of `m ∣ w, m ∣ q, w < q` give `v < q`. -/
theorem blk_lt {m w q v : ℕ} (hw : m ∣ w) (hq : m ∣ q) (hwq : w < q) (hv : v < w + m) : v < q := by
  have := step_align m w q hw hq hwq
  omega

theorem down_blk {m p q v : ℕ} (hm : 0 < m) (hp : m ∣ p) (hpv : p ≤ v) :
    p ≤ m * (v / m) ∧ m ∣ m * (v / m) ∧ m * (v / m) ≤ v ∧ v < m * (v / m) + m := by
  obtain ⟨a, rfl⟩ := hp
  refine ⟨?_, dvd_mul_right _ _, Nat.mul_div_le v m, ?_⟩
  · have : a ≤ v / m := (Nat.le_div_iff_mul_le hm).mpr (by rw [mul_comm]; exact hpv)
    exact Nat.mul_le_mul_left m this
  · have := Nat.lt_mul_div_succ v hm
    rw [mul_add, mul_one] at this
    exact this

theorem omGe_iff (j : ℕ) (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (hell : 0 < ell) (hM : 0 < M) :
    OmGe (geomOf ell 2 (neS ell M R)) j x ↔ omGe0 ell M R j (x 0).val := by
  constructor
  · rintro ⟨i, hj, hi, y, hy, hb⟩
    have hy' := (mem_Lam i y ∅).mp hy
    obtain ⟨hc, hO, hN⟩ := hy'
    refine ⟨i, hj, hi, (y 0).val, hc 0, hO, hN, (hb 0).1, (hb 0).2⟩
  · rintro ⟨i, hj, hi, w, hd, hO, hN, hw1, hw2⟩
    have hN0 : (x 0).val < scaleUp ell 2 (neLu M R) 0 + 1 := (x 0).isLt
    let y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)) := Function.update (alignDown (ell ^ i) x) 0 ⟨w, by omega⟩
    have hpos : 0 < ell ^ i := pow_pos hell i
    have hy0 : (y 0).val = w := by simp [y]
    have hyne : ∀ μ : Fin 3, μ ≠ 0 → y μ = alignDown (ell ^ i) x μ := fun μ hμ => Function.update_of_ne hμ _ _
    refine ⟨i, hj, hi, y, ?_, ?_⟩
    · rw [mem_Lam i y ∅]
      refine ⟨?_, by rw [hy0]; exact hO, by rw [hy0]; exact hN⟩
      intro μ
      by_cases hμ : μ = 0
      · subst hμ; rw [hy0]; exact hd
      · rw [hyne μ hμ, alignDown_val]; exact dvd_mul_right _ _
    · intro μ
      by_cases hμ : μ = 0
      · subst hμ; rw [hy0]; exact ⟨hw1, hw2⟩
      · rw [hyne μ hμ, alignDown_val]
        refine ⟨Nat.mul_div_le _ _, ?_⟩
        have := Nat.lt_mul_div_succ (x μ).val hpos
        rw [mul_add, mul_one] at this
        exact this

end AdalyFormal.CoverOmega
