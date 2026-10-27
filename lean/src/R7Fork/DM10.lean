import R7Fork.DM9
import R7Fork.ZT5C

/-!
# DM10 -- consistency check: the NEW general theorem `closed_point_proper` re-derives the inequality at the FULL-tower closed point of `ZT5C`
(every hypothesis incl. `IsUnit G1inv` is Lean-proved there), by a route that does not use the whole-torus Stokes comparison.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2

theorem closed_point_proper_at_full_tower (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (hk : 1 ≤ k) (R : ℕ) (hR : 2 ≤ R)
    (a : ℝ) (ha : 0 < a) :
    InstIneq 2 k (by norm_num) a (LuM (2 ^ m)) (1 / 1728 : ℝ) (fullTower 2 k (LuM (2 ^ m))) Set.univ flatCfg := by
  have h := closedPt_hyps m hm k hk R a ha (α₀ := 1) (by norm_num)
  obtain ⟨-, hadm, -, hLam, -, hWD, -⟩ := h
  have hMpos : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hLu : ∀ μ, LuM (2 ^ m) μ + 1 = 10 * 2 ^ m := LuM_succ hMpos
  have hM4 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine closed_point_proper (fun μ => by have := hLu μ; omega)
    (fun μ => by rw [hLu μ]; exact Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) 10) ?_ (by norm_num) a ha _ hadm _ hLam hWD.2.1
  nlinarith

#print axioms closed_point_proper_at_full_tower

end AdalyFormal.DirichletMono
