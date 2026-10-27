import DLR29

/-!
# WC6a -- counting the `n`-aligned sites of a periodic `ℓ¹` ball (M2 W6 lane)

`card_pball_aligned` : `#{y : n ∣ coordinates, pdist y c ≤ m} ≤ (2m/n + 1)³` (periodic torus, `n ∣ L_ν + 1`).
Copy of `DLayer.card_reach_coarse_le` with `Reach` replaced by the symmetric ball (`ball_disp`: the forward displacement from
`y` to `c + m` is `≤ 2m`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2W6

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (pcd pdist)
open AdalyFormal.DLayer (sub_val_mod)

theorem mod_cases2 (x N : ℕ) (hN : 0 < N) (hx : x < 2 * N) :
    (x < N ∧ x % N = x) ∨ (N ≤ x ∧ x % N = x - N) := by
  by_cases h : x < N
  · left; exact ⟨h, Nat.mod_eq_of_lt h⟩
  · right
    refine ⟨by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem ball_disp (N m c y : ℕ) (hc : c < N) (hy : y < N) (h : pcd N y c ≤ m) :
    (N - y + (c + m) % N) % N ≤ 2 * m := by
  by_cases hN : N ≤ 2 * m
  · have : (N - y + (c + m) % N) % N < N := Nat.mod_lt _ (by omega)
    omega
  · push Not at hN
    have hm : m < N := by omega
    unfold pcd at h
    have e1 : ((c + m) < N ∧ (c + m) % N = c + m) ∨ (N ≤ c + m ∧ (c + m) % N = c + m - N) :=
      mod_cases2 (c + m) N (by omega) (by omega)
    split_ifs at h with hyc
    · rcases e1 with ⟨e1a, e1b⟩ | ⟨e1a, e1b⟩
      · rw [e1b]
        rcases mod_cases2 (N - y + (c + m)) N (by omega) (by omega) with ⟨e2a, e2b⟩ | ⟨e2a, e2b⟩
        · rw [e2b]; omega
        · rw [e2b]; omega
      · rw [e1b]
        rcases mod_cases2 (N - y + (c + m - N)) N (by omega) (by omega) with ⟨e2a, e2b⟩ | ⟨e2a, e2b⟩
        · rw [e2b]; omega
        · rw [e2b]; omega
    · rcases e1 with ⟨e1a, e1b⟩ | ⟨e1a, e1b⟩
      · rw [e1b]
        rcases mod_cases2 (N - y + (c + m)) N (by omega) (by omega) with ⟨e2a, e2b⟩ | ⟨e2a, e2b⟩
        · rw [e2b]; omega
        · rw [e2b]; omega
      · rw [e1b]
        rcases mod_cases2 (N - y + (c + m - N)) N (by omega) (by omega) with ⟨e2a, e2b⟩ | ⟨e2a, e2b⟩
        · rw [e2b]; omega
        · rw [e2b]; omega

open Classical in
theorem card_pball_aligned {L : PeriodicLatticeExtent} (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν : Fin 3, n ∣ L ν + 1)
    (m : ℕ) (c : PeriodicLatticeSite L) :
    (Finset.univ.filter (fun y : PeriodicLatticeSite L => (∀ ν, n ∣ (y ν).val) ∧ pdist y c ≤ m)).card
      ≤ (2 * m / n + 1) ^ 3 := by
  have hcard : (Finset.univ : Finset (Fin 3 → Fin (2 * m / n + 1))).card = (2 * m / n + 1) ^ 3 := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [← hcard]
  let z : PeriodicLatticeSite L := fun ν => ⟨((c ν).val + m) % (L ν + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  have hdisp : ∀ y : PeriodicLatticeSite L, pdist y c ≤ m → ∀ ν, (z ν - y ν).val ≤ 2 * m := by
    intro y hy ν
    have h1 : pcd (L ν + 1) (y ν).val (c ν).val ≤ m :=
      le_trans (Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (y μ).val (c μ).val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ ν)) hy
    rw [Fin.val_sub]
    exact ball_disp (L ν + 1) m (c ν).val (y ν).val (c ν).isLt (y ν).isLt h1
  refine Finset.card_le_card_of_injOn
    (fun y : PeriodicLatticeSite L => fun ν : Fin 3 =>
      (⟨min ((z ν - y ν).val / n) (2 * m / n), Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (2 * m / n + 1))) ?_ ?_
  · intro y _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
  · intro y hy y' hy' hyy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy hy'
    funext ν
    have h1 := congrFun hyy ν
    simp only [Fin.mk.injEq] at h1
    have hm1 : (z ν - y ν).val / n ≤ 2 * m / n := Nat.div_le_div_right (hdisp y hy.2 ν)
    have hm2 : (z ν - y' ν).val / n ≤ 2 * m / n := Nat.div_le_div_right (hdisp y' hy'.2 ν)
    rw [min_eq_left hm1, min_eq_left hm2] at h1
    have h2 : (z ν - y ν).val % n = (z ν - y' ν).val % n := by
      rw [sub_val_mod n (hdvd ν) _ _ (hy.1 ν), sub_val_mod n (hdvd ν) _ _ (hy'.1 ν)]
    have h3 : (z ν - y ν).val = (z ν - y' ν).val := by
      rw [← Nat.div_add_mod (z ν - y ν).val n, ← Nat.div_add_mod (z ν - y' ν).val n, h1, h2]
    have h4 : z ν - y ν = z ν - y' ν := Fin.ext h3
    exact sub_right_injective h4

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.ball_disp
#print axioms AdalyFormal.M2W6.card_pball_aligned
