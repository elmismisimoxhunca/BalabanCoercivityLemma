import UC6
import M2B7

/-!
# UD1 -- circular-coordinate arithmetic for the index-k class cube centred at a given site (lane m2_unitcharts_20261014)

Pure `Nat` facts about `pcd` (the statement's circular distance on `Z/N`) and the corner `zc N B a` of the
12-block cube whose block `a / B` sits at offset 5 blocks:

* `off_bounds`: for every `b` within `pcd`-distance `r ≤ 5B` of `a`, the offset of `b` from the corner lies in `[5B - r, 6B - 1 + r]`;
* `pcd_of_off`: any `b` of offset `< 12 B` from the corner is within `pcd`-distance `7 B` of `a`;
* `pcd_mul`: `pcd (N n) (n a) (n b) = n * pcd N a b`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.M2UnitCharts

open AdalyFormal.StatementLane (pcd)
open AdalyFormal.StatementLaneR8 (pcd_comm pcd_self)

theorem pcd_cases (N a b r : ℕ) (h : pcd N a b ≤ r) :
    (a ≤ b ∧ b - a ≤ r) ∨ (b ≤ a ∧ a - b ≤ r) ∨ (a ≤ b ∧ N + a ≤ b + r) ∨ (b ≤ a ∧ N + b ≤ a + r) := by
  unfold pcd at h
  split_ifs at h <;> omega

theorem pcd_le_N_half (N a b : ℕ) (ha : a < N) (hb : b < N) : 2 * pcd N a b ≤ N := by
  unfold pcd
  split_ifs <;> omega

/-- the corner of the 12-block cube whose `5`-th block (counting from 0) is the block of `a`; `0` when the cube wraps. -/
def zc (N B a : ℕ) : ℕ := if 12 * B ≤ N then (a / B * B + (N - 5 * B)) % N else 0

/-- offset of `c` from the corner `z` on `Z/N` (this is `AdalyFormal.M2Bridge.offc` coordinatewise). -/
def offN (N z c : ℕ) : ℕ := (c + (N - z)) % N

theorem zc_lt {N B a : ℕ} (hN : 0 < N) : zc N B a < N := by
  unfold zc; split_ifs
  · exact Nat.mod_lt _ hN
  · exact hN

theorem zc_mod {N B a : ℕ} (hB : 0 < B) (hBN : B ∣ N) : zc N B a % B = 0 := by
  unfold zc; split_ifs with h
  · apply Nat.mod_eq_zero_of_dvd
    exact (Nat.dvd_mod_iff hBN).mpr (dvd_add (Dvd.intro_left _ rfl) (Nat.dvd_sub hBN (Dvd.intro_left _ rfl)))
  · simp

theorem zc_val {N B a : ℕ} (hB : 0 < B) (h12 : 12 * B ≤ N) (ha : a < N) :
    (5 * B ≤ a / B * B ∧ zc N B a = a / B * B - 5 * B) ∨ (a / B * B < 5 * B ∧ zc N B a = a / B * B + N - 5 * B) := by
  have h1 : a / B * B ≤ a := Nat.div_mul_le_self a B
  have h2 : a < a / B * B + B := by
    have := Nat.mod_add_div a B
    have h3 := Nat.mod_lt a hB
    rw [mul_comm] at this
    omega
  unfold zc; rw [if_pos h12]
  by_cases hc : 5 * B ≤ a / B * B
  · left
    refine ⟨hc, ?_⟩
    have : (a / B * B + (N - 5 * B)) % N = (a / B * B + (N - 5 * B) - N) % N :=
      Nat.mod_eq_sub_mod (by omega)
    rw [this, Nat.mod_eq_of_lt (by omega)]
    omega
  · right
    refine ⟨by omega, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem off_bounds {N B r a b : ℕ} (hB : 0 < B) (h12 : 12 * B ≤ N) (ha : a < N) (hb : b < N) (hr : r ≤ 5 * B)
    (hp : pcd N a b ≤ r) :
    5 * B ≤ offN N (zc N B a) b + r ∧ offN N (zc N B a) b + 1 ≤ 6 * B + r := by
  have hN : 0 < N := by omega
  have ha1 : a / B * B ≤ a := Nat.div_mul_le_self a B
  have ha2 : a < a / B * B + B := by
    have := Nat.mod_add_div a B
    have h3 := Nat.mod_lt a hB
    rw [mul_comm] at this
    omega
  have hz := zc_val hB h12 ha
  have hzl := zc_lt (B := B) (a := a) hN
  have hmod := Nat.mod_add_div (b + (N - zc N B a)) N
  have hlt : (b + (N - zc N B a)) / N < 3 := by
    apply Nat.div_lt_of_lt_mul; omega
  have ho : offN N (zc N B a) b < N := Nat.mod_lt _ hN
  unfold offN at ho ⊢
  generalize (b + (N - zc N B a)) % N = o at *
  generalize (b + (N - zc N B a)) / N = j at *
  rcases pcd_cases N a b r hp with h | h | h | h <;>
  rcases hz with ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩ <;>
  interval_cases j <;> omega

theorem pcd_of_off {N B a b : ℕ} (hB : 0 < B) (h12 : 12 * B ≤ N) (ha : a < N) (hb : b < N)
    (hoff : offN N (zc N B a) b < 12 * B) : pcd N a b ≤ 7 * B := by
  have hN : 0 < N := by omega
  have hoa := off_bounds (r := 0) hB h12 ha ha (Nat.zero_le _) (by rw [pcd_self])
  have hzl := zc_lt (B := B) (a := a) hN
  have hmodb := Nat.mod_add_div (b + (N - zc N B a)) N
  have hmoda := Nat.mod_add_div (a + (N - zc N B a)) N
  have hltb : (b + (N - zc N B a)) / N < 3 := by apply Nat.div_lt_of_lt_mul; omega
  have hlta : (a + (N - zc N B a)) / N < 3 := by apply Nat.div_lt_of_lt_mul; omega
  have hnb : offN N (zc N B a) b < N := Nat.mod_lt _ hN
  unfold offN at hoff hoa hnb
  generalize (b + (N - zc N B a)) % N = ob at *
  generalize (b + (N - zc N B a)) / N = jb at *
  generalize (a + (N - zc N B a)) % N = oa at *
  generalize (a + (N - zc N B a)) / N = ja at *
  unfold pcd
  split_ifs <;>
  interval_cases jb <;> interval_cases ja <;> omega

theorem pcd_mul (Nu n a b : ℕ) (hn : 0 < n) : pcd (Nu * n) (n * a) (n * b) = n * pcd Nu a b := by
  unfold pcd
  rcases le_total a b with h | h
  · have h' : n * a ≤ n * b := Nat.mul_le_mul_left n h
    rw [if_pos h, if_pos h', ← Nat.mul_sub, mul_comm Nu n, ← Nat.mul_sub, Nat.mul_min_mul_left]
  · by_cases hab : a = b
    · subst hab; simp
    · have hlt : b < a := lt_of_le_of_ne h (Ne.symm hab)
      have hna : ¬ a ≤ b := by omega
      have hna' : ¬ n * a ≤ n * b := by
        intro hh
        exact hna (Nat.le_of_mul_le_mul_left hh hn)
      rw [if_neg hna, if_neg hna', ← Nat.mul_sub, mul_comm Nu n, ← Nat.mul_sub, Nat.mul_min_mul_left]

end AdalyFormal.M2UnitCharts

#print axioms AdalyFormal.M2UnitCharts.pcd_cases
#print axioms AdalyFormal.M2UnitCharts.zc_mod
#print axioms AdalyFormal.M2UnitCharts.off_bounds
#print axioms AdalyFormal.M2UnitCharts.pcd_of_off
#print axioms AdalyFormal.M2UnitCharts.pcd_mul
