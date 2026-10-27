import Mathlib

/-!
# FE1 -- the 1D dual kernel of the flat extension, and a Schur test (pure combinatorics, Mathlib only)

Fine circle `Fin N`, `N = Nu * n` (`n` fine sites per coarse block, `Nu` coarse sites).
`phi n Nu v` (`v` = cyclic offset `(x - y).val` from a block corner `y`) is the 1D kernel:
block `0` (the block of `y`): `1`; block `-1`: the quadratic `gq n t = t(3t-2n+1)/n²` (mean zero, `gq 0 = 0`);
block `+1`: `gq n (n-1-t)` (mean zero, vanishes at the far end). Block offsets are read mod `Nu`
(`-1 ↦ Nu-1`, `+1 ↦ 1 % Nu`), so for `Nu ∈ {1,2}` the pieces overlap and ADD (no case is excluded).

* `block_mean`: the mean of `phi (· - y)` over the block at corner `y'` is `[y' = y]` (exact right inverse).
* `abs_phi_le`: `|phi| ≤ chi`;  `abs_phi_step`: `|phi(v+1 mod N) - phi v| ≤ (6/n) chi v`.
* `row_chi_le`: `Σ_{corners y} chi((x-y)) ≤ 3`;  `col_chi_le`: `Σ_x chi((x-y)) ≤ 3n`.
* `schur`: `Σ_x ‖Σ_y K x y • w y‖² ≤ R C Σ_y ‖w y‖²` for a majorant with row sums `≤ R`, column sums `≤ C`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.FlatExt

/-! ## 1. the quadratic profile -/

/-- `gq n t = t (3t - 2n + 1) / n²` (`= 3t(t-c)/n²`, `c = (2n-1)/3`). -/
noncomputable def gq (n t : ℕ) : ℝ := (t : ℝ) * (3 * (t : ℝ) - 2 * (n : ℝ) + 1) / (n : ℝ) ^ 2

theorem sum_range_gq_num (n m : ℕ) :
    ∑ t ∈ Finset.range m, (t : ℝ) * (3 * (t : ℝ) - 2 * (n : ℝ) + 1)
      = (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - n) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_gq (n : ℕ) : ∑ t ∈ Finset.range n, gq n t = 0 := by
  unfold gq
  rw [← Finset.sum_div, sum_range_gq_num]
  simp

theorem sum_gq_rev (n : ℕ) : ∑ t ∈ Finset.range n, gq n (n - 1 - t) = 0 := by
  rw [Finset.sum_range_reflect (fun t => gq n t) n]
  exact sum_gq n

theorem gq_zero (n : ℕ) : gq n 0 = 0 := by simp [gq]

theorem abs_gq_le (n t : ℕ) (hn : 0 < n) (ht : t < n) : |gq n t| ≤ 1 := by
  unfold gq
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hn', div_le_one hn', abs_le]
  have h1 : (t : ℝ) + 1 ≤ n := by exact_mod_cast ht
  have h0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  constructor
  · nlinarith [sq_nonneg (6 * (t : ℝ) - 2 * n + 1)]
  · nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

theorem gq_succ_sub (n t : ℕ) : gq n (t + 1) - gq n t = (6 * (t : ℝ) + 4 - 2 * n) / (n : ℝ) ^ 2 := by
  unfold gq; push_cast; ring

theorem abs_gq_succ_sub_le (n t : ℕ) (hn : 0 < n) (ht : t + 1 < n) :
    |gq n (t + 1) - gq n t| ≤ 4 / n := by
  rw [gq_succ_sub]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (t : ℝ) + 2 ≤ n := by exact_mod_cast ht
  have h0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hab : |6 * (t : ℝ) + 4 - 2 * n| ≤ 4 * n := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
  calc |6 * (t : ℝ) + 4 - 2 * n| / (n : ℝ) ^ 2 ≤ 4 * n / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hab (by positivity)
    _ = 4 / n := by field_simp

theorem abs_one_sub_gq_last (n : ℕ) (hn : 0 < n) : |1 - gq n (n - 1)| ≤ 3 / n := by
  unfold gq
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  have he : 1 - ((n : ℝ) - 1) * (3 * ((n : ℝ) - 1) - 2 * n + 1) / (n : ℝ) ^ 2 = (3 * n - 2) / (n : ℝ) ^ 2 := by
    field_simp; ring
  rw [he, abs_of_nonneg (by apply div_nonneg <;> nlinarith)]
  calc (3 * (n : ℝ) - 2) / (n : ℝ) ^ 2 ≤ 3 * n / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 3 / n := by field_simp

/-! ## 2. the 1D kernel `phi` and its majorant `chi` -/

/-- the 1D dual kernel, as a function of the cyclic offset `v` from the corner. -/
noncomputable def phi (n Nu v : ℕ) : ℝ :=
  (if v / n = 0 then 1 else 0) + (if v / n = Nu - 1 then gq n (v % n) else 0)
    + (if v / n = 1 % Nu then gq n (n - 1 - v % n) else 0)

/-- majorant: the number of the three pieces whose block contains `v`. -/
noncomputable def chi (n Nu v : ℕ) : ℝ :=
  (if v / n = 0 then 1 else 0) + (if v / n = Nu - 1 then 1 else 0) + (if v / n = 1 % Nu then 1 else 0)

theorem chi_nonneg (n Nu v : ℕ) : 0 ≤ chi n Nu v := by
  unfold chi; split_ifs <;> norm_num

theorem abs_phi_le (n Nu v : ℕ) (hn : 0 < n) : |phi n Nu v| ≤ chi n Nu v := by
  have hr : v % n < n := Nat.mod_lt _ hn
  have h1 := abs_gq_le n (v % n) hn hr
  have h2 := abs_gq_le n (n - 1 - v % n) hn (by omega)
  unfold phi chi
  refine le_trans (abs_add_le _ _) ?_
  refine add_le_add (le_trans (abs_add_le _ _) (add_le_add ?_ ?_)) ?_ <;> split_ifs <;> simp_all

theorem one_mod_cases (Nu : ℕ) (hNu : 0 < Nu) : (Nu = 1 ∧ 1 % Nu = 0) ∨ (2 ≤ Nu ∧ 1 % Nu = 1) := by
  rcases Nat.lt_or_ge Nu 2 with h | h
  · left; have : Nu = 1 := by omega
    subst this; simp
  · right; exact ⟨h, Nat.mod_eq_of_lt (by omega)⟩

theorem abs_phi_step (n Nu v : ℕ) (hn : 0 < n) (hNu : 0 < Nu) (hv : v < Nu * n) :
    |phi n Nu ((v + 1) % (Nu * n)) - phi n Nu v| ≤ 6 / n * chi n Nu v := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hi : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have h4 : (4 : ℝ) / n = 4 * (1 / n) := by ring
  have h6 : (6 : ℝ) / n = 6 * (1 / n) := by ring
  have h3 : (3 : ℝ) / n = 3 * (1 / n) := by ring
  obtain ⟨q, hq⟩ : ∃ q, v / n = q := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, v % n = r := ⟨_, rfl⟩
  obtain ⟨T1, hT1⟩ : ∃ T1, 1 % Nu = T1 := ⟨_, rfl⟩
  have hT : (Nu = 1 ∧ T1 = 0) ∨ (2 ≤ Nu ∧ T1 = 1) := hT1 ▸ one_mod_cases Nu hNu
  have hvqr : v = r + n * q := by have := Nat.div_add_mod v n; rw [hq, hr] at this; omega
  have hrn : r < n := hr ▸ Nat.mod_lt _ hn
  have hqNu : q < Nu := hq ▸ (Nat.div_lt_iff_lt_mul hn).mpr hv
  have hNn : Nu * n = n * Nu := Nat.mul_comm Nu n
  rcases Nat.lt_or_ge (r + 1) n with hr1 | hr1
  · -- interior step: same block
    have hle : n * (q + 1) ≤ n * Nu := Nat.mul_le_mul_left n (by omega)
    rw [Nat.mul_succ] at hle
    have hlt : v + 1 < Nu * n := by omega
    have hv1 : (v + 1) % (Nu * n) = (r + 1) + n * q := by rw [Nat.mod_eq_of_lt hlt]; omega
    have hd : ((r + 1) + n * q) / n = q := by
      rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hr1, zero_add]
    have hm : ((r + 1) + n * q) % n = r + 1 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr1]
    have e1 := abs_gq_succ_sub_le n r hn hr1
    have e2 : |gq n (n - 1 - (r + 1)) - gq n (n - 1 - r)| ≤ 4 / n := by
      have ha : n - 1 - r = (n - 1 - (r + 1)) + 1 := by omega
      rw [ha, abs_sub_comm]
      exact abs_gq_succ_sub_le n _ hn (by omega)
    rw [hv1]
    unfold phi chi
    rw [hd, hm, hq, hr, hT1]
    rw [h4] at e1 e2
    rw [h6]
    have e1' := abs_le.mp e1
    have e2' := abs_le.mp e2
    split_ifs <;> first
      | (exfalso; omega)
      | (rw [abs_le]; constructor <;> nlinarith [e1'.1, e1'.2, e2'.1, e2'.2])
  · -- boundary step: r = n - 1
    have hrn1 : r = n - 1 := by omega
    have eG := abs_one_sub_gq_last n hn
    rw [h3] at eG
    have eG' := abs_le.mp eG
    have hg0 : gq n 0 = 0 := gq_zero n
    rcases Nat.lt_or_ge (q + 1) Nu with hq1 | hq1
    · have hle : n * (q + 1 + 1) ≤ n * Nu := Nat.mul_le_mul_left n (by omega)
      rw [Nat.mul_succ, Nat.mul_succ] at hle
      have hlt : v + 1 < Nu * n := by omega
      have hv1 : (v + 1) % (Nu * n) = 0 + n * (q + 1) := by
        rw [Nat.mod_eq_of_lt hlt, Nat.mul_succ]; omega
      have hd : (0 + n * (q + 1)) / n = q + 1 := by rw [Nat.add_mul_div_left _ _ hn]; simp
      have hm : (0 + n * (q + 1)) % n = 0 := by simp
      rw [hv1]
      unfold phi chi
      rw [hd, hm, hq, hr, hT1, hrn1]
      simp only [Nat.sub_self, Nat.sub_zero, hg0]
      split_ifs <;> first
        | (exfalso; omega)
        | (rw [abs_le]; constructor <;> nlinarith [eG'.1, eG'.2])
    · have hqe : q = Nu - 1 := by omega
      have hle : n * (q + 1) = n * Nu := by congr 1; omega
      rw [Nat.mul_succ] at hle
      have heq : v + 1 = Nu * n := by omega
      have hv1 : (v + 1) % (Nu * n) = 0 := by rw [heq, Nat.mod_self]
      rw [hv1]
      unfold phi chi
      rw [Nat.zero_div, Nat.zero_mod, hq, hr, hT1, hrn1]
      simp only [Nat.sub_self, Nat.sub_zero, hg0]
      split_ifs <;> first
        | (exfalso; omega)
        | (rw [abs_le]; constructor <;> nlinarith [eG'.1, eG'.2])

/-! ## 3. cyclic offsets on `Fin N` -/

theorem sub_val_mod {N n : ℕ} [NeZero N] (hnN : n ∣ N) (x y : Fin N) (hy : n ∣ y.val) :
    (x - y).val % n = x.val % n := by
  rw [Fin.sub_def]
  simp only
  rw [Nat.mod_mod_of_dvd _ hnN]
  have hd : n ∣ N - y.val := Nat.dvd_sub hnN hy
  obtain ⟨c, hc⟩ := hd
  rw [hc, Nat.add_comm, Nat.add_mul_mod_self_left]

theorem row_ind_le_one {N : ℕ} [NeZero N] (n : ℕ) (hnN : n ∣ N) (x : Fin N) (T : ℕ) :
    ∑ y : Fin N, (if n ∣ y.val ∧ (x - y).val / n = T then (1 : ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun y : Fin N => n ∣ y.val ∧ (x - y).val / n = T)).card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hma := sub_val_mod hnN x a ha.1
    have hmb := sub_val_mod hnN x b hb.1
    have hval : (x - a).val = (x - b).val := by
      rw [← Nat.div_add_mod (x - a).val n, ← Nat.div_add_mod (x - b).val n, ha.2, hb.2, hma, hmb]
    have := Fin.ext hval
    exact sub_right_injective this
  exact_mod_cast this

theorem col_ind_le {N : ℕ} [NeZero N] (n : ℕ) (hn : 0 < n) (y : Fin N) (T : ℕ) :
    ∑ x : Fin N, (if (x - y).val / n = T then (1 : ℝ) else 0) ≤ n := by
  have hs : ∑ x : Fin N, (if (x - y).val / n = T then (1 : ℝ) else 0)
      = ∑ d : Fin N, (if d.val / n = T then (1 : ℝ) else 0) :=
    Fintype.sum_equiv (Equiv.subRight y) _ _ (fun x => rfl)
  rw [hs, Finset.sum_boole]
  have : (Finset.univ.filter (fun d : Fin N => d.val / n = T)).card ≤ (Finset.range n).card := by
    refine Finset.card_le_card_of_injOn (fun d => d.val % n) ?_ ?_
    · intro d _; simp only [Finset.coe_range, Set.mem_Iio]; exact Nat.mod_lt _ hn
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      apply Fin.ext
      rw [← Nat.div_add_mod a.val n, ← Nat.div_add_mod b.val n, ha, hb]
      exact congrArg (fun z => n * T + z) hab
  rw [Finset.card_range] at this
  exact_mod_cast this

theorem row_chi_le {N : ℕ} [NeZero N] (n Nu : ℕ) (hnN : n ∣ N) (x : Fin N) :
    ∑ y : Fin N, (if n ∣ y.val then chi n Nu (x - y).val else 0) ≤ 3 := by
  have h : ∀ y : Fin N, (if n ∣ y.val then chi n Nu (x - y).val else 0)
      = (if n ∣ y.val ∧ (x - y).val / n = 0 then (1 : ℝ) else 0)
        + (if n ∣ y.val ∧ (x - y).val / n = Nu - 1 then (1 : ℝ) else 0)
        + (if n ∣ y.val ∧ (x - y).val / n = 1 % Nu then (1 : ℝ) else 0) := by
    intro y; unfold chi; by_cases hy : n ∣ y.val <;> simp [hy]
  simp only [h, Finset.sum_add_distrib]
  have := row_ind_le_one n hnN x 0
  have := row_ind_le_one n hnN x (Nu - 1)
  have := row_ind_le_one n hnN x (1 % Nu)
  linarith

theorem col_chi_le {N : ℕ} [NeZero N] (n Nu : ℕ) (hn : 0 < n) (y : Fin N) :
    ∑ x : Fin N, chi n Nu (x - y).val ≤ 3 * n := by
  unfold chi
  simp only [Finset.sum_add_distrib]
  have := col_ind_le n hn y 0
  have := col_ind_le n hn y (Nu - 1)
  have := col_ind_le n hn y (1 % Nu)
  linarith

/-! ## 4. block means: `phi` is an exact dual system for the block average -/

theorem block_mean (Nu n : ℕ) (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = Nu * n) (y y' : Fin N)
    (hy : n ∣ y.val) (hy' : n ∣ y'.val) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin N => y'.val ≤ a.val ∧ a.val < y'.val + n),
      phi n Nu (a - y).val = if y' = y then (n : ℝ) else 0 := by
  have hnN : n ∣ N := ⟨Nu, by rw [hN, Nat.mul_comm]⟩
  have hNn : N = n * Nu := by rw [hN, Nat.mul_comm]
  have hNpos : 0 < N := NeZero.pos N
  obtain ⟨D, hD⟩ : ∃ D, (y' - y).val = D := ⟨_, rfl⟩
  have hDm : D % n = 0 := by rw [← hD, sub_val_mod hnN y' y hy]; exact Nat.mod_eq_zero_of_dvd hy'
  obtain ⟨d, hd⟩ : ∃ d, D / n = d := ⟨_, rfl⟩
  have hDnd : D = n * d := by have := Nat.div_add_mod D n; rw [hDm, hd] at this; omega
  have hDN : D < N := hD ▸ (y' - y).isLt
  have hdNu : d + 1 ≤ Nu := by
    have h1 : n * d < n * Nu := by rw [← hDnd, ← hNn]; exact hDN
    have := Nat.lt_of_mul_lt_mul_left h1; omega
  have hDn : D + n ≤ N := by
    have := Nat.mul_le_mul_left n hdNu; rw [Nat.mul_succ] at this; omega
  obtain ⟨e, he⟩ := hy'
  have heNu : e + 1 ≤ Nu := by
    have h1 : n * e < n * Nu := by rw [← he, ← hNn]; exact y'.isLt
    have := Nat.lt_of_mul_lt_mul_left h1; omega
  have hy'n : y'.val + n ≤ N := by
    have := Nat.mul_le_mul_left n heNu; rw [Nat.mul_succ] at this; omega
  have key : ∀ a : Fin N, y'.val ≤ a.val → a.val < y'.val + n → (a - y).val = D + (a.val - y'.val) := by
    intro a h1 h2
    have hDv : D = (N - y.val + y'.val) % N := by rw [← hD, Fin.val_sub]
    rw [Fin.val_sub]
    have hsplit : N - y.val + a.val = (N - y.val + y'.val) + (a.val - y'.val) := by omega
    rw [hsplit, Nat.add_mod, ← hDv, Nat.mod_eq_of_lt (by omega : a.val - y'.val < N),
      Nat.mod_eq_of_lt (by omega : D + (a.val - y'.val) < N)]
  have hre : ∑ a ∈ Finset.univ.filter (fun a : Fin N => y'.val ≤ a.val ∧ a.val < y'.val + n),
      phi n Nu (a - y).val = ∑ t ∈ Finset.range n, phi n Nu (D + t) := by
    refine Finset.sum_nbij' (fun a => a.val - y'.val)
      (fun t => (⟨(y'.val + t) % N, Nat.mod_lt _ hNpos⟩ : Fin N)) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at ha
      simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_range]; omega
    · intro t ht
      simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_range] at ht
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at ha
      apply Fin.ext
      simp only
      rw [show y'.val + (a.val - y'.val) = a.val by omega, Nat.mod_eq_of_lt a.isLt]
    · intro t ht
      simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_range] at ht
      simp only
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at ha
      rw [key a ha.1 ha.2]
  rw [hre]
  have hphi : ∀ t ∈ Finset.range n, phi n Nu (D + t) = (if d = 0 then 1 else 0)
      + (if d = Nu - 1 then gq n t else 0) + (if d = 1 % Nu then gq n (n - 1 - t) else 0) := by
    intro t ht
    rw [Finset.mem_range] at ht
    have h1 : (D + t) / n = d := by
      rw [hDnd, Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt ht, zero_add]
    have h2 : (D + t) % n = t := by
      rw [hDnd, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
    unfold phi; rw [h1, h2]
  rw [Finset.sum_congr rfl hphi]
  have hyy : (y' = y) ↔ d = 0 := by
    constructor
    · intro h
      rw [h, sub_self] at hD
      have : D = 0 := by rw [← hD]; rfl
      rw [← hd, this, Nat.zero_div]
    · intro h0
      have hD0 : D = 0 := by rw [hDnd, h0, Nat.mul_zero]
      have : y' - y = 0 := Fin.ext (by rw [hD, hD0]; rfl)
      exact sub_eq_zero.mp this
  simp only [hyy]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  by_cases h0 : d = 0 <;> by_cases h1 : d = Nu - 1 <;> by_cases h2 : d = 1 % Nu <;>
    simp [h0, h1, h2, sum_gq, sum_gq_rev]

#print axioms sum_gq
#print axioms abs_gq_le
#print axioms abs_phi_le
#print axioms abs_phi_step
#print axioms sub_val_mod
#print axioms row_chi_le
#print axioms col_chi_le
#print axioms block_mean

end AdalyFormal.FlatExt
