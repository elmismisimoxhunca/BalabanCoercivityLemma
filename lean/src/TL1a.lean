import TLz0

set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.StatementLane

theorem pcd_comm (N a b : ℕ) : pcd N a b = pcd N b a := by
  unfold pcd
  by_cases h1 : a ≤ b <;> by_cases h2 : b ≤ a
  · have : a = b := le_antisymm h1 h2
    subst this; simp
  · simp [h1, h2]
  · simp [h1, h2]
  · omega

theorem pcd_mod_le_aux (m n a b : ℕ) (hm : 0 < m) (hn : 0 < n) (ha : a < m * n) (hb : b ≤ a) :
    pcd m (a % m) (b % m) ≤ pcd (m * n) a b := by
  have hA := Nat.div_add_mod a m
  have hB := Nat.div_add_mod b m
  have hqa : a / m < n := by
    rw [Nat.div_lt_iff_lt_mul hm]; linarith [Nat.mul_comm m n]
  have hqle : b / m ≤ a / m := Nat.div_le_div_right hb
  have ha' := Nat.mod_lt a hm
  have hb' := Nat.mod_lt b hm
  set qa := a / m with hqa_def
  set qb := b / m with hqb_def
  set ra := a % m with hra
  set rb := b % m with hrb
  unfold pcd
  have e1 : (if a ≤ b then b - a else a - b) = a - b := by split_ifs <;> omega
  have e2 : (if ra ≤ rb then rb - ra else ra - rb) = (if rb ≤ ra then ra - rb else rb - ra) := by
    split_ifs <;> omega
  rw [e1, e2]
  by_cases hr : rb ≤ ra
  · rw [if_pos hr]
    have hq : m * qb ≤ m * qa := Nat.mul_le_mul_left m hqle
    have hqn : m * qa + m ≤ m * n := by
      have := Nat.mul_le_mul_left m (show qa + 1 ≤ n from hqa)
      linarith
    have hqn' : m * qa < m * n := by linarith
    apply le_min
    · refine le_trans (min_le_left _ _) ?_
      omega
    · refine le_trans (min_le_right _ _) ?_
      omega
  · push_neg at hr
    rw [if_neg (by omega)]
    have hq : m * qb ≤ m * qa := Nat.mul_le_mul_left m hqle
    have hqn : m * qa + m ≤ m * n := by
      have := Nat.mul_le_mul_left m (show qa + 1 ≤ n from hqa)
      linarith
    have hqpos : m * qb + m ≤ m * qa := by
      by_contra hcon
      have : qa ≤ qb := by
        by_contra h2
        push_neg at h2
        have := Nat.mul_le_mul_left m (show qb + 1 ≤ qa from h2)
        linarith
      have : qa = qb := le_antisymm this hqle
      rw [this] at hA
      omega
    apply le_min
    · refine le_trans (min_le_right _ _) ?_
      omega
    · refine le_trans (min_le_left _ _) ?_
      omega

theorem pcd_mod_le (m n a b : ℕ) (hm : 0 < m) (hn : 0 < n) (ha : a < m * n) (hb : b < m * n) :
    pcd m (a % m) (b % m) ≤ pcd (m * n) a b := by
  by_cases hab : b ≤ a
  · exact pcd_mod_le_aux m n a b hm hn ha hab
  · rw [pcd_comm m, pcd_comm (m * n)]
    exact pcd_mod_le_aux m n b a hm hn hb (by omega)


/-- a displacement `t` (mod `m`) from `a` is realised by a point `b` with `b % m = y` and circular distance `≤ min t (N - t)`. -/
theorem lift_displace (N m a y t : ℕ) (hmN : m ∣ N) (ha : a < N) (ht : t ≤ N) (hmod : (a % m + t) % m = y) :
    ∃ b, b < N ∧ b % m = y ∧ pcd N a b ≤ t ∧ pcd N a b ≤ N - t := by
  by_cases hlt : a + t < N
  · refine ⟨a + t, hlt, ?_, ?_, ?_⟩
    · rw [← hmod, Nat.mod_add_mod]
    · unfold pcd; rw [if_pos (by omega)]; exact le_trans (min_le_left _ _) (by omega)
    · unfold pcd; rw [if_pos (by omega)]; exact le_trans (min_le_right _ _) (by omega)
  · refine ⟨a + t - N, by omega, ?_, ?_, ?_⟩
    · obtain ⟨s, hs⟩ := hmN
      have : a + t - N = (a + t) - m * s := by rw [hs]
      rw [this, Nat.sub_mul_mod (by rw [← hs]; omega), ← hmod, Nat.mod_add_mod]
    · unfold pcd
      by_cases h : a ≤ a + t - N
      · rw [if_pos h]; have : a + t - N - a = 0 ∨ True := Or.inr trivial
        exact le_trans (min_le_left _ _) (by omega)
      · rw [if_neg h]; exact le_trans (min_le_right _ _) (by omega)
    · unfold pcd
      by_cases h : a ≤ a + t - N
      · rw [if_pos h]; exact le_trans (min_le_left _ _) (by omega)
      · rw [if_neg h]; exact le_trans (min_le_left _ _) (by omega)

theorem pcd_mod_le' (m a y : ℕ) (hm : 0 < m) (hy : y < m) :
    pcd m (a % m) y = min ((y + m - a % m) % m) ((a % m + m - y) % m) := by
  have hc := Nat.mod_lt a hm
  generalize a % m = c at *
  unfold pcd
  by_cases h : c ≤ y
  · rw [if_pos h]
    by_cases h2 : c = y
    · subst h2; simp
    · have e1 : (y + m - c) % m = y - c := by
        rw [show y + m - c = (y - c) + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have e2 : (c + m - y) % m = m - (y - c) := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [e1, e2]
  · rw [if_neg h]
    have e1 : (y + m - c) % m = m - (c - y) := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have e2 : (c + m - y) % m = c - y := by
      rw [show c + m - y = (c - y) + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e1, e2, min_comm]

theorem aux_back (m s c y : ℕ) (hc : c < m) (hy : y < m) (hs : 0 < s) :
    (c + (m * s - (c + m - y) % m)) % m = y := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hms : m * (s' + 1) = m * s' + m := by ring
  by_cases hcy : c < y
  · have h1 : (c + m - y) % m = c + m - y := Nat.mod_eq_of_lt (by omega)
    rw [h1, show c + (m * (s' + 1) - (c + m - y)) = m * s' + y by omega,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hy]
  · by_cases hce : c = y
    · subst hce
      rw [show c + m - c = m by omega, Nat.mod_self, show c + (m * (s' + 1) - 0) = c + m * (s' + 1) by omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
    · have : (c + m - y) % m = c - y := by
        rw [show c + m - y = (c - y) + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [this, show c + (m * (s' + 1) - (c - y)) = y + m * (s' + 1) by omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]

theorem pcd_lift (N m a y : ℕ) (hmN : m ∣ N) (hm : 0 < m) (ha : a < N) (hy : y < m) :
    ∃ b, b < N ∧ b % m = y ∧ pcd N a b ≤ pcd m (a % m) y := by
  have hmle : m ≤ N := Nat.le_of_dvd (by omega) hmN
  have hc := Nat.mod_lt a hm
  obtain ⟨s, hs⟩ := hmN
  rw [pcd_mod_le' m a y hm hy]
  generalize hcdef : a % m = c at *
  by_cases hfg : (y + m - c) % m ≤ (c + m - y) % m
  · rw [min_eq_left hfg]
    obtain ⟨b, hb1, hb2, hb3, -⟩ := lift_displace N m a y ((y + m - c) % m) ⟨s, hs⟩ ha
      (le_trans (le_of_lt (Nat.mod_lt _ hm)) hmle) (by
        rw [hcdef, Nat.add_mod_mod]
        rw [show c + (y + m - c) = y + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hy])
    exact ⟨b, hb1, hb2, hb3⟩
  · rw [min_eq_right (by omega)]
    have hg := Nat.mod_lt (c + m - y) hm
    obtain ⟨b, hb1, hb2, -, hb4⟩ := lift_displace N m a y (N - (c + m - y) % m) ⟨s, hs⟩ ha (by omega) (by
      rw [hcdef]
      have hsp : 0 < s := by
        rcases Nat.eq_zero_or_pos s with h0 | h0
        · rw [h0] at hs; omega
        · exact h0
      rw [hs]
      exact aux_back m s c y hc hy hsp)
    exact ⟨b, hb1, hb2, by omega⟩



end AdalyFormal.Thin
