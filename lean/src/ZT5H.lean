import ZT5G

/-!
# ZT5H -- the r4-form conclusion (`WellDefG ∧ inequality`) at the closed point, with `GuardsUnit` from `ZT5G`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2

open AdalyFormal.StatementLane (scaleUp)

/-- **the r4-form conclusion (`WellDefG ∧ inequality`) at the closed point, every `k`, `M = 2^m`**: with `GuardsUnit` now proved (`PK_guardsUnit`). -/
theorem closedPt_instAtWD (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (a : ℝ) (ha : 0 < a) :
    InstAtWD 2 k (by norm_num) a (LuM (2 ^ m)) (1 / 1728) (fullTower 2 k (LuM (2 ^ m))) Set.univ flatCfg := by
  have hMpos : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hLu : ∀ μ, LuM (2 ^ m) μ + 1 = 10 * 2 ^ m := LuM_succ hMpos
  have hM2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hM4 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hN : ∀ μ : Fin 3, 1 ≤ LuM (2 ^ m) μ := by intro μ; have := hLu μ; omega
  have hd : ∀ μ, 2 ∣ LuM (2 ^ m) μ + 1 := by
    intro μ; rw [hLu μ]; exact Dvd.dvd.mul_left hM2 10
  have hW : GenP.WellDefG (AdalyFormal.GenuineU1.PK 2 k (LuM (2 ^ m)) (by norm_num) a Set.univ) :=
    AdalyFormal.GenuineU1.PK_wellDefG 2 k (LuM (2 ^ m)) (by norm_num) a Set.univ (le_refl 2) hN hd ha
  have hI := (closedPt_ineq m hm k a ha).2
  exact ⟨hW, hI⟩

/-- the r4-form inner claim consumed at the closed point (`WellDefG` included) -/
theorem closedPt_consumes_WD (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (hk : 1 ≤ k) (R : ℕ) (a : ℝ) (ha : 0 < a)
    {α₀ γ₀ : ℝ} (hα : 0 < α₀)
    (h : CoercG8AtWD 2 (2 ^ m) R k (by norm_num) a (LuM (2 ^ m)) 12 α₀ γ₀) :
    InstAtWD 2 k (by norm_num) a (LuM (2 ^ m)) γ₀ (fullTower 2 k (LuM (2 ^ m))) Set.univ flatCfg := by
  obtain ⟨hT, hA, hC, hL, hU, -, -⟩ := closedPt_hyps m hm k hk R a ha hα
  exact (h.apply_gauge hT hA hL ⟨hC, hU⟩).1

#print axioms closedPt_instAtWD
#print axioms closedPt_consumes_WD

end AdalyFormal.StatementLaneG
