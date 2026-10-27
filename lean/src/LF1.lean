import FE2

/-!
# LF1 -- a 1D partition-of-unity kernel with EXACT block means (Mathlib + FlatExt FE1/FE2 only)

Fine circle `Fin N`, `N = Nu * n` (`n` fine sites per block, `Nu` blocks).  `v` = cyclic offset `(x - y).val` from a block
corner `y`.  The kernel lives on the block of `y` (offset block `0`) and the next one (offset block `1 % Nu`); for `Nu = 1`
the two pieces sit on the same block and ADD (no case is excluded):
* block `0`:   `p0 t = (t+1)/n + λ β(t)`,   block `+1`: `p1 t = (n-1-t)/n - λ β(t)`,
  `β(t) = 6(t+1)(n-t)/((n+1)(n+2))` (mean one), `λ = (n-1)/(2n)`.
Facts: `p0 + p1 = 1`; `Σ_t p0 = n`, `Σ_t p1 = 0`;
* `kk_partition`: `Σ_{a corner} kk((x-a)) = 1` (partition of unity);
* `kk_block_mean`: the sum of `kk(· - y)` over the block at corner `y'` is `n [y' = y]` (exact right inverse);
* `abs_kk_le`: `|kk| ≤ 2 chi`;  `abs_kk_step`: `|kk(v+1) - kk(v)| ≤ (7/n) chi(v)`;
* `chi_corner`: if `chi((x-a)) ≠ 0` (`a` a corner) then `a` is the corner of `x`, the next corner, or the previous one.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.LemIFlat

open AdalyFormal.FlatExt (chi chi_nonneg sub_val_mod one_mod_cases row_ind_le_one pos_of_neZero_eq_mul)

/-- the bump `β(t) = 6(t+1)(n-t)/((n+1)(n+2))` (mean one on `[0,n)`). -/
noncomputable def bump (n t : ℕ) : ℝ := 6 * ((t : ℝ) + 1) * ((n : ℝ) - t) / (((n : ℝ) + 1) * ((n : ℝ) + 2))

/-- `λ = (n-1)/(2n)`. -/
noncomputable def lam (n : ℕ) : ℝ := ((n : ℝ) - 1) / (2 * n)

noncomputable def p0 (n t : ℕ) : ℝ := ((t : ℝ) + 1) / n + lam n * bump n t
noncomputable def p1 (n t : ℕ) : ℝ := ((n : ℝ) - 1 - t) / n - lam n * bump n t

/-- the 1D kernel as a function of the cyclic offset. -/
noncomputable def kk (n Nu v : ℕ) : ℝ :=
  (if v / n = 0 then p0 n (v % n) else 0) + (if v / n = 1 % Nu then p1 n (v % n) else 0)

theorem p0_add_p1 (n t : ℕ) (hn : 0 < n) : p0 n t + p1 n t = 1 := by
  unfold p0 p1
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp; ring

theorem sum_range_bump_num (n m : ℕ) :
    ∑ t ∈ Finset.range m, ((t : ℝ) + 1) * ((n : ℝ) - t)
      = (m : ℝ) * ((m : ℝ) + 1) * (3 * (n : ℝ) - 2 * (m : ℝ) + 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_range_add_one (m : ℕ) : ∑ t ∈ Finset.range m, ((t : ℝ) + 1) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_bump (n : ℕ) : ∑ t ∈ Finset.range n, bump n t = n := by
  unfold bump
  have h : ∀ t : ℕ, 6 * ((t : ℝ) + 1) * ((n : ℝ) - t) / (((n : ℝ) + 1) * ((n : ℝ) + 2))
      = (6 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) * (((t : ℝ) + 1) * ((n : ℝ) - t)) := fun t => by ring
  simp_rw [h]
  rw [← Finset.mul_sum, sum_range_bump_num]
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  field_simp; ring

theorem sum_p0 (n : ℕ) (hn : 0 < n) : ∑ t ∈ Finset.range n, p0 n t = n := by
  unfold p0
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, sum_range_add_one, sum_bump]
  unfold lam
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp; ring

theorem sum_p1 (n : ℕ) (hn : 0 < n) : ∑ t ∈ Finset.range n, p1 n t = 0 := by
  have h := sum_p0 n hn
  have h2 : ∑ t ∈ Finset.range n, (p0 n t + p1 n t) = ∑ t ∈ Finset.range n, (1 : ℝ) :=
    Finset.sum_congr rfl (fun t _ => p0_add_p1 n t hn)
  rw [Finset.sum_add_distrib, h] at h2
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h2
  linarith

/-! ## pointwise bounds -/

theorem bump_nonneg (n t : ℕ) (ht : t < n) : 0 ≤ bump n t := by
  unfold bump
  have h1 : (t : ℝ) + 1 ≤ n := by exact_mod_cast ht
  have h0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  apply div_nonneg
  · have : (0 : ℝ) ≤ (n : ℝ) - t := by linarith
    positivity
  · positivity

theorem bump_le (n t : ℕ) (ht : t < n) : bump n t ≤ 3 / 2 := by
  unfold bump
  have h1 : (t : ℝ) + 1 ≤ n := by exact_mod_cast ht
  have h0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hd : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  rw [div_le_iff₀ hd]
  nlinarith [sq_nonneg (((t : ℝ) + 1) - ((n : ℝ) - t))]

theorem lam_nonneg (n : ℕ) (hn : 0 < n) : 0 ≤ lam n := by
  unfold lam
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply div_nonneg <;> linarith

theorem lam_le (n : ℕ) (hn : 0 < n) : lam n ≤ 1 / 2 := by
  unfold lam
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_iff₀ (by positivity)]; linarith

/-- the two boundary values of the bump: `β(0) = β(n-1) = 6n/((n+1)(n+2)) ≤ 6/n`. -/
noncomputable def bstar (n : ℕ) : ℝ := 6 * (n : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2))

theorem bump_zero (n : ℕ) : bump n 0 = bstar n := by unfold bump bstar; push_cast; ring

theorem bump_last (n : ℕ) (hn : 0 < n) : bump n (n - 1) = bstar n := by
  unfold bump bstar; rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring

theorem bstar_nonneg (n : ℕ) : 0 ≤ bstar n := by unfold bstar; positivity

theorem bstar_le (n : ℕ) (hn : 0 < n) : bstar n ≤ 6 / n := by
  unfold bstar
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) hnr]
  nlinarith

theorem bump_step (n t : ℕ) : bump n (t + 1) - bump n t = 6 * ((n : ℝ) - 2 * t - 2) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  unfold bump; push_cast; field_simp; ring

theorem abs_bump_step (n t : ℕ) (hn : 0 < n) (ht : t + 1 < n) : |bump n (t + 1) - bump n t| ≤ 6 / n := by
  rw [bump_step]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (t : ℝ) + 2 ≤ n := by exact_mod_cast ht
  have h0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hd : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  rw [abs_div, abs_of_pos hd, div_le_div_iff₀ hd hnr, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  have hab : |(n : ℝ) - 2 * t - 2| ≤ n := abs_le.mpr ⟨by linarith, by linarith⟩
  nlinarith [abs_nonneg ((n : ℝ) - 2 * t - 2)]

theorem p0_nonneg (n t : ℕ) (hn : 0 < n) (ht : t < n) : 0 ≤ p0 n t := by
  unfold p0
  have := bump_nonneg n t ht
  have := lam_nonneg n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem p0_le (n t : ℕ) (hn : 0 < n) (ht : t < n) : p0 n t ≤ 7 / 4 := by
  unfold p0
  have hb := bump_le n t ht
  have hb0 := bump_nonneg n t ht
  have hl := lam_le n hn
  have hl0 := lam_nonneg n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ((t : ℝ) + 1) / n ≤ 1 := by
    rw [div_le_one hnr]; exact_mod_cast ht
  have h2 : lam n * bump n t ≤ (1 / 2) * (3 / 2) := mul_le_mul hl hb hb0 (by norm_num)
  linarith

theorem p1_le (n t : ℕ) (hn : 0 < n) (ht : t < n) : p1 n t ≤ 1 := by
  unfold p1
  have hb0 := bump_nonneg n t ht
  have hl0 := lam_nonneg n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have h1 : ((n : ℝ) - 1 - t) / n ≤ 1 := by rw [div_le_one hnr]; linarith
  have h2 : 0 ≤ lam n * bump n t := mul_nonneg hl0 hb0
  linarith

theorem p1_ge (n t : ℕ) (hn : 0 < n) (ht : t < n) : -1 ≤ p1 n t := by
  unfold p1
  have hb := bump_le n t ht
  have hb0 := bump_nonneg n t ht
  have hl := lam_le n hn
  have hl0 := lam_nonneg n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (t : ℝ) + 1 ≤ n := by exact_mod_cast ht
  have h2 : 0 ≤ ((n : ℝ) - 1 - t) / n := div_nonneg (by linarith) hnr.le
  have h3 : lam n * bump n t ≤ (1 / 2) * (3 / 2) := mul_le_mul hl hb hb0 (by norm_num)
  linarith

theorem abs_p0_le (n t : ℕ) (hn : 0 < n) (ht : t < n) : |p0 n t| ≤ 2 := by
  rw [abs_le]; constructor <;> linarith [p0_nonneg n t hn ht, p0_le n t hn ht]

theorem abs_p1_le (n t : ℕ) (hn : 0 < n) (ht : t < n) : |p1 n t| ≤ 2 := by
  rw [abs_le]; constructor <;> linarith [p1_ge n t hn ht, p1_le n t hn ht]

theorem abs_kk_le (n Nu v : ℕ) (hn : 0 < n) : |kk n Nu v| ≤ 2 * chi n Nu v := by
  have hr : v % n < n := Nat.mod_lt _ hn
  have h0 := abs_p0_le n (v % n) hn hr
  have h1 := abs_p1_le n (v % n) hn hr
  have hA : |(if v / n = 0 then p0 n (v % n) else 0)| ≤ 2 * (if v / n = 0 then (1 : ℝ) else 0) := by
    split_ifs <;> simp [h0]
  have hB : |(if v / n = 1 % Nu then p1 n (v % n) else 0)| ≤ 2 * (if v / n = 1 % Nu then (1 : ℝ) else 0) := by
    split_ifs <;> simp [h1]
  have hC : (0 : ℝ) ≤ (if v / n = Nu - 1 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  unfold kk chi
  calc |(if v / n = 0 then p0 n (v % n) else 0) + (if v / n = 1 % Nu then p1 n (v % n) else 0)|
      ≤ |(if v / n = 0 then p0 n (v % n) else 0)| + |(if v / n = 1 % Nu then p1 n (v % n) else 0)| :=
        abs_add_le _ _
    _ ≤ _ := by linarith

/-- interior steps of the two pieces. -/
theorem abs_p0_step (n t : ℕ) (hn : 0 < n) (ht : t + 1 < n) : |p0 n (t + 1) - p0 n t| ≤ 4 / n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := abs_bump_step n t hn ht
  have hl := lam_le n hn
  have hl0 := lam_nonneg n hn
  have he : p0 n (t + 1) - p0 n t = 1 / n + lam n * (bump n (t + 1) - bump n t) := by
    unfold p0; push_cast; field_simp; ring
  rw [he]
  have h1 : |lam n * (bump n (t + 1) - bump n t)| ≤ 3 / n := by
    rw [abs_mul, abs_of_nonneg hl0]
    calc lam n * |bump n (t + 1) - bump n t| ≤ (1 / 2) * (6 / n) :=
          mul_le_mul hl hb (abs_nonneg _) (by norm_num)
      _ = 3 / n := by ring
  have h2 : |(1 : ℝ) / n| = 1 / n := abs_of_pos (by positivity)
  calc |1 / (n : ℝ) + lam n * (bump n (t + 1) - bump n t)| ≤ |(1 : ℝ) / n| + |lam n * (bump n (t + 1) - bump n t)| :=
        abs_add_le _ _
    _ ≤ 1 / n + 3 / n := by rw [h2]; linarith
    _ = 4 / n := by ring

theorem abs_p1_step (n t : ℕ) (hn : 0 < n) (ht : t + 1 < n) : |p1 n (t + 1) - p1 n t| ≤ 4 / n := by
  have e : p1 n (t + 1) - p1 n t = -(p0 n (t + 1) - p0 n t) := by
    have a := p0_add_p1 n t hn
    have b := p0_add_p1 n (t + 1) hn
    linarith
  rw [e, abs_neg]; exact abs_p0_step n t hn ht

/-- boundary values. -/
theorem p0_last (n : ℕ) (hn : 0 < n) : p0 n (n - 1) = 1 + lam n * bstar n := by
  unfold p0; rw [bump_last n hn, Nat.cast_sub (by omega : 1 ≤ n)]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast; field_simp; ring

theorem p1_last (n : ℕ) (hn : 0 < n) : p1 n (n - 1) = - (lam n * bstar n) := by
  unfold p1; rw [bump_last n hn, Nat.cast_sub (by omega : 1 ≤ n)]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast; field_simp; ring

theorem p0_first (n : ℕ) : p0 n 0 = 1 / n + lam n * bstar n := by
  unfold p0; rw [bump_zero]; push_cast; ring

theorem p1_first (n : ℕ) (hn : 0 < n) : p1 n 0 = 1 - 1 / n - lam n * bstar n := by
  unfold p1; rw [bump_zero]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast; field_simp; ring

theorem lam_bstar_le (n : ℕ) (hn : 0 < n) : 0 ≤ lam n * bstar n ∧ lam n * bstar n ≤ 3 / n := by
  have hl := lam_le n hn
  have hl0 := lam_nonneg n hn
  have hb := bstar_le n hn
  have hb0 := bstar_nonneg n
  refine ⟨mul_nonneg hl0 hb0, ?_⟩
  calc lam n * bstar n ≤ (1 / 2) * (6 / n) := mul_le_mul hl hb hb0 (by norm_num)
    _ = 3 / n := by ring

/-- **step bound**: `|kk((v+1) mod N) - kk(v)| ≤ (7/n) chi(v)`. -/
theorem abs_kk_step (n Nu v : ℕ) (hn : 0 < n) (hNu : 0 < Nu) (hv : v < Nu * n) :
    |kk n Nu ((v + 1) % (Nu * n)) - kk n Nu v| ≤ 7 / n * chi n Nu v := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hin : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have h7 : (7 : ℝ) / n = 7 * (1 / n) := by ring
  have h4 : (4 : ℝ) / n = 4 * (1 / n) := by ring
  have h3 : (3 : ℝ) / n = 3 * (1 / n) := by ring
  obtain ⟨q, hq⟩ : ∃ q, v / n = q := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, v % n = r := ⟨_, rfl⟩
  obtain ⟨T1, hT1⟩ : ∃ T1, 1 % Nu = T1 := ⟨_, rfl⟩
  have hT : (Nu = 1 ∧ T1 = 0) ∨ (2 ≤ Nu ∧ T1 = 1) := hT1 ▸ one_mod_cases Nu hNu
  have hvqr : v = r + n * q := by have := Nat.div_add_mod v n; rw [hq, hr] at this; omega
  have hrn : r < n := hr ▸ Nat.mod_lt _ hn
  have hqNu : q < Nu := hq ▸ (Nat.div_lt_iff_lt_mul hn).mpr hv
  have hLB := lam_bstar_le n hn
  rcases Nat.lt_or_ge (r + 1) n with hr1 | hr1
  · -- interior step
    have hle : n * (q + 1) ≤ n * Nu := Nat.mul_le_mul_left n (by omega)
    rw [Nat.mul_succ] at hle
    have hlt : v + 1 < Nu * n := by rw [Nat.mul_comm]; omega
    have hv1 : (v + 1) % (Nu * n) = (r + 1) + n * q := by rw [Nat.mod_eq_of_lt hlt]; omega
    have hd : ((r + 1) + n * q) / n = q := by
      rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hr1, zero_add]
    have hm : ((r + 1) + n * q) % n = r + 1 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr1]
    have e1 := abs_p0_step n r hn hr1
    have e2 := abs_p1_step n r hn hr1
    rw [hv1]
    unfold kk chi
    rw [hd, hm, hq, hr, hT1]
    rw [h4] at e1 e2
    rw [h7]
    have e1' := abs_le.mp e1
    have e2' := abs_le.mp e2
    split_ifs <;> first
      | (exfalso; omega)
      | (rw [abs_le]; constructor <;> nlinarith [e1'.1, e1'.2, e2'.1, e2'.2])
  · -- boundary step: r = n - 1
    have hrn1 : r = n - 1 := by omega
    have hP0L := p0_last n hn
    have hP1L := p1_last n hn
    have hP0F := p0_first n
    have hP1F := p1_first n hn
    rcases Nat.lt_or_ge (q + 1) Nu with hq1 | hq1
    · have hle : n * (q + 1 + 1) ≤ n * Nu := Nat.mul_le_mul_left n (by omega)
      rw [Nat.mul_succ, Nat.mul_succ] at hle
      have hlt : v + 1 < Nu * n := by rw [Nat.mul_comm]; omega
      have hv1 : (v + 1) % (Nu * n) = 0 + n * (q + 1) := by
        rw [Nat.mod_eq_of_lt hlt, Nat.mul_succ]; omega
      have hd : (0 + n * (q + 1)) / n = q + 1 := by rw [Nat.add_mul_div_left _ _ hn]; simp
      have hm : (0 + n * (q + 1)) % n = 0 := by simp
      rw [hv1]
      unfold kk chi
      rw [hd, hm, hq, hr, hT1, hrn1, hP0L, hP1L, hP0F, hP1F]
      rw [h7]; rw [h3] at hLB
      split_ifs <;> first
        | (exfalso; omega)
        | (rw [abs_le]; constructor <;> nlinarith [hLB.1, hLB.2])
    · have hqe : q = Nu - 1 := by omega
      have hle : n * (q + 1) = n * Nu := by congr 1; omega
      rw [Nat.mul_succ] at hle
      have heq : v + 1 = Nu * n := by rw [Nat.mul_comm]; omega
      have hv1 : (v + 1) % (Nu * n) = 0 := by rw [heq, Nat.mod_self]
      rw [hv1]
      unfold kk chi
      rw [Nat.zero_div, Nat.zero_mod, hq, hr, hT1, hrn1, hP0L, hP1L, hP0F, hP1F]
      rw [h7]; rw [h3] at hLB
      split_ifs <;> first
        | (exfalso; omega)
        | (rw [abs_le]; constructor <;> nlinarith [hLB.1, hLB.2])

/-! ## cyclic offsets: partition of unity and exact block means -/

theorem mod_mul_add (n m k t : ℕ) (ht : t < n) (hm : 0 < m) : (n * k + t) % (n * m) = n * (k % m) + t := by
  have hlt : n * (k % m) + t < n * m := by
    have h1 : k % m + 1 ≤ m := Nat.mod_lt _ hm
    have := Nat.mul_le_mul_left n h1
    rw [Nat.mul_succ] at this; omega
  have hsplit : n * k + t = n * (k % m) + t + n * m * (k / m) := by
    have := Nat.div_add_mod k m
    calc n * k + t = n * (m * (k / m) + k % m) + t := by rw [this]
      _ = _ := by ring
  rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- a corner at block offset `T` from `x`. -/
theorem exists_corner (Nu n : ℕ) (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = Nu * n) (x : Fin N) (T : ℕ) (hT : T < Nu) :
    ∃ a : Fin N, n ∣ a.val ∧ (x - a).val / n = T := by
  have hNu : 0 < Nu := pos_of_neZero_eq_mul hN
  have hNn : N = n * Nu := by rw [hN, Nat.mul_comm]
  obtain ⟨t, ht⟩ : ∃ t, x.val % n = t := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, x.val / n = c := ⟨_, rfl⟩
  have htn : t < n := ht ▸ Nat.mod_lt _ hn
  have hxv : x.val = n * c + t := by have := Nat.div_add_mod x.val n; rw [hc, ht] at this; omega
  have hcNu : c < Nu := by
    have : n * c < n * Nu := by have := x.isLt; omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hTt : n * T + t < N := by
    have h1 : T + 1 ≤ Nu := hT
    have := Nat.mul_le_mul_left n h1
    rw [Nat.mul_succ] at this; omega
  have hs : (c + Nu - T) % Nu < Nu := Nat.mod_lt _ hNu
  have has : n * ((c + Nu - T) % Nu) < N := by
    have h2 : n * ((c + Nu - T) % Nu) < n * Nu := Nat.mul_lt_mul_of_pos_left hs hn
    omega
  let a : Fin N := ⟨n * ((c + Nu - T) % Nu), has⟩
  let b : Fin N := ⟨n * T + t, hTt⟩
  have hab : a + b = x := by
    apply Fin.ext
    rw [Fin.val_add]
    show (n * ((c + Nu - T) % Nu) + (n * T + t)) % N = x.val
    rw [hxv, hNn, show n * ((c + Nu - T) % Nu) + (n * T + t) = n * ((c + Nu - T) % Nu + T) + t by ring,
      mod_mul_add n Nu _ t htn hNu, Nat.mod_add_mod, show c + Nu - T + T = c + Nu by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hcNu]
  refine ⟨a, ⟨_, rfl⟩, ?_⟩
  have hxa : x - a = b := by rw [← hab]; abel
  rw [hxa]
  show (n * T + t) / n = T
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt htn, zero_add]

theorem card_corner_eq_one (Nu n : ℕ) (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = Nu * n) (x : Fin N) (T : ℕ)
    (hT : T < Nu) :
    ∑ a : Fin N, (if n ∣ a.val ∧ (x - a).val / n = T then (1 : ℝ) else 0) = 1 := by
  have hnN : n ∣ N := ⟨Nu, by rw [hN, Nat.mul_comm]⟩
  have hle := row_ind_le_one n hnN x T
  obtain ⟨a, ha⟩ := exists_corner Nu n hn hN x T hT
  have hge : (1 : ℝ) ≤ ∑ a : Fin N, (if n ∣ a.val ∧ (x - a).val / n = T then (1 : ℝ) else 0) := by
    calc (1 : ℝ) = (if n ∣ a.val ∧ (x - a).val / n = T then (1 : ℝ) else 0) := by rw [if_pos ha]
      _ ≤ _ := Finset.single_le_sum (f := fun a : Fin N => if n ∣ a.val ∧ (x - a).val / n = T then (1 : ℝ) else 0)
          (fun b _ => by split_ifs <;> norm_num) (Finset.mem_univ a)
  linarith

/-- **partition of unity**: `Σ_{corners a} kk((x - a)) = 1`. -/
theorem kk_partition (Nu n : ℕ) (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = Nu * n) (x : Fin N) :
    ∑ a : Fin N, (if n ∣ a.val then kk n Nu (x - a).val else 0) = 1 := by
  have hnN : n ∣ N := ⟨Nu, by rw [hN, Nat.mul_comm]⟩
  have hNu : 0 < Nu := pos_of_neZero_eq_mul hN
  have hpt : ∀ a : Fin N, (if n ∣ a.val then kk n Nu (x - a).val else 0)
      = p0 n (x.val % n) * (if n ∣ a.val ∧ (x - a).val / n = 0 then (1 : ℝ) else 0)
        + p1 n (x.val % n) * (if n ∣ a.val ∧ (x - a).val / n = 1 % Nu then (1 : ℝ) else 0) := by
    intro a
    by_cases ha : n ∣ a.val
    · have hm := sub_val_mod hnN x a ha
      unfold kk
      rw [if_pos ha, hm]
      simp only [ha, true_and]
      split_ifs <;> simp
    · simp [ha]
  simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [card_corner_eq_one Nu n hn hN x 0 hNu, card_corner_eq_one Nu n hn hN x (1 % Nu) (Nat.mod_lt _ hNu),
    mul_one, mul_one, p0_add_p1 n _ hn]

/-- **block means**: `Σ_{a ∈ block(y')} kk((a - y)) = n [y' = y]` (`y, y'` corners). -/
theorem kk_block_mean (Nu n : ℕ) (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = Nu * n) (y y' : Fin N)
    (hy : n ∣ y.val) (hy' : n ∣ y'.val) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin N => y'.val ≤ a.val ∧ a.val < y'.val + n),
      kk n Nu (a - y).val = if y' = y then (n : ℝ) else 0 := by
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
      kk n Nu (a - y).val = ∑ t ∈ Finset.range n, kk n Nu (D + t) := by
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
  have hk : ∀ t ∈ Finset.range n, kk n Nu (D + t) = (if d = 0 then p0 n t else 0)
      + (if d = 1 % Nu then p1 n t else 0) := by
    intro t ht
    rw [Finset.mem_range] at ht
    have h1 : (D + t) / n = d := by
      rw [hDnd, Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt ht, zero_add]
    have h2 : (D + t) % n = t := by
      rw [hDnd, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
    unfold kk; rw [h1, h2]
  rw [Finset.sum_congr rfl hk]
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
  rw [Finset.sum_add_distrib]
  by_cases h0 : d = 0 <;> by_cases h2 : d = 1 % Nu <;>
    simp [h0, h2, sum_p0 n hn, sum_p1 n hn]

/-! ## the support of `chi`: which corners interact with `x` -/

/-- if `chi((x - a)) ≠ 0` for a corner `a`, then `a` is the corner `c` of `x`, or `c + n`, or `a + n = c` (cyclic). -/
theorem chi_corner (Nu n : ℕ) (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = Nu * n) (x a : Fin N) (ha : n ∣ a.val)
    (hchi : chi n Nu (x - a).val ≠ 0) :
    a.val = n * (x.val / n) ∨ a.val = (n * (x.val / n) + n) % N ∨ (a.val + n) % N = n * (x.val / n) := by
  have hNu : 0 < Nu := pos_of_neZero_eq_mul hN
  have hNn : N = n * Nu := by rw [hN, Nat.mul_comm]
  have hnN : n ∣ N := ⟨Nu, hNn⟩
  have hm := sub_val_mod hnN x a ha
  obtain ⟨α, hα⟩ := ha
  have hαNu : α < Nu := by
    have : n * α < n * Nu := by rw [← hα, ← hNn]; exact a.isLt
    exact Nat.lt_of_mul_lt_mul_left this
  obtain ⟨β, hβ⟩ : ∃ β, x.val / n = β := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, x.val % n = t := ⟨_, rfl⟩
  have htn : t < n := ht ▸ Nat.mod_lt _ hn
  have hxv : x.val = n * β + t := by have := Nat.div_add_mod x.val n; rw [hβ, ht] at this; omega
  obtain ⟨q, hq⟩ : ∃ q, (x - a).val / n = q := ⟨_, rfl⟩
  have hxa : (x - a).val = n * q + t := by
    have := Nat.div_add_mod (x - a).val n; rw [hm, ht, hq] at this; omega
  have hsum : x.val = (n * α + (n * q + t)) % (n * Nu) := by
    have hx : x = a + (x - a) := by abel
    have h0 : x.val = (a.val + (x - a).val) % N := by
      conv_lhs => rw [hx]
      rw [Fin.val_add]
    rw [h0, hα, hxa, hNn]
  rw [hxv, show n * α + (n * q + t) = n * (α + q) + t by ring, mod_mul_add n Nu _ t htn hNu] at hsum
  have hβq : β = (α + q) % Nu := by
    have : n * β = n * ((α + q) % Nu) := by omega
    exact Nat.eq_of_mul_eq_mul_left hn this
  rw [hβ, hα, hNn]
  unfold chi at hchi
  rw [hq] at hchi
  have hcase : q = 0 ∨ q = Nu - 1 ∨ q = 1 % Nu := by
    by_contra hcon
    push_neg at hcon
    apply hchi
    rw [if_neg hcon.1, if_neg hcon.2.1, if_neg hcon.2.2]; norm_num
  rcases hcase with h0 | h1 | h2
  · left
    rw [hβq, h0, Nat.add_zero, Nat.mod_eq_of_lt hαNu]
  · right; left
    rw [← Nat.mul_succ, Nat.mul_mod_mul_left, hβq, h1, Nat.succ_eq_add_one, Nat.mod_add_mod,
      show α + (Nu - 1) + 1 = α + Nu by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hαNu]
  · right; right
    rw [← Nat.mul_succ, Nat.mul_mod_mul_left, hβq, h2, Nat.succ_eq_add_one, Nat.add_mod_mod]

#print axioms p0_add_p1
#print axioms sum_bump
#print axioms sum_p0
#print axioms sum_p1
#print axioms abs_kk_le
#print axioms abs_kk_step
#print axioms mod_mul_add
#print axioms exists_corner
#print axioms card_corner_eq_one
#print axioms kk_partition
#print axioms kk_block_mean
#print axioms chi_corner

#print axioms sum_range_bump_num
#print axioms sum_range_add_one
#print axioms bump_nonneg
#print axioms bump_le
#print axioms lam_nonneg
#print axioms lam_le
#print axioms bump_zero
#print axioms bump_last
#print axioms bstar_nonneg
#print axioms bstar_le
#print axioms bump_step
#print axioms abs_bump_step
#print axioms p0_nonneg
#print axioms p0_le
#print axioms p1_le
#print axioms p1_ge
#print axioms abs_p0_le
#print axioms abs_p1_le
#print axioms abs_p0_step
#print axioms abs_p1_step
#print axioms p0_last
#print axioms p1_last
#print axioms p0_first
#print axioms p1_first
#print axioms lam_bstar_le

end AdalyFormal.LemIFlat
