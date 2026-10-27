import NsOdd3

/-!
# NsOdd5a -- alternating sums with at most one deviating term; at most one seam position on a stride-`ell` progression (lane ncwdh_strong_20261017)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]

/-- `|Σ_{j<n} (-1)^j m_j| ≤ 2` when `0 ≤ m_j ≤ 1` and `m_j = 1` except for at most one index. -/
theorem alt_sum_one_dev (n : ℕ) (m : ℕ → ℝ) (h0 : ∀ j, 0 ≤ m j) (h1 : ∀ j, m j ≤ 1)
    (hone : ∀ j j', j < n → j' < n → m j < 1 → m j' < 1 → j = j') :
    |∑ j ∈ Finset.range n, pmN j * m j| ≤ 2 := by
  have hpm : ∀ j, |pmN j| = 1 := by intro j; unfold pmN; split_ifs <;> norm_num
  have hsum1 : ∑ j ∈ Finset.range n, pmN j = ((n % 2 : ℕ) : ℝ) := sum_pmN n
  by_cases hex : ∃ j0, j0 < n ∧ m j0 < 1
  · obtain ⟨j0, hj0, hm0⟩ := hex
    have hsplit : ∑ j ∈ Finset.range n, pmN j * m j = ∑ j ∈ Finset.range n, pmN j - pmN j0 * (1 - m j0) := by
      have : ∑ j ∈ Finset.range n, pmN j * (1 - m j) = pmN j0 * (1 - m j0) := by
        rw [Finset.sum_eq_single j0]
        · intro j hj hne
          have hj' : j < n := Finset.mem_range.mp hj
          have : m j = 1 := by
            by_contra hc
            have hlt : m j < 1 := lt_of_le_of_ne (h1 j) hc
            exact hne (hone j j0 hj' hj0 hlt hm0)
          rw [this]; ring
        · intro h; exact absurd (Finset.mem_range.mpr hj0) h
      have h2 : ∑ j ∈ Finset.range n, pmN j * m j = ∑ j ∈ Finset.range n, pmN j - ∑ j ∈ Finset.range n, pmN j * (1 - m j) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      rw [h2, this]
    rw [hsplit]
    have hn2 : ((n % 2 : ℕ) : ℝ) ≤ 1 := by
      have : n % 2 ≤ 1 := by omega
      exact_mod_cast this
    have hn2' : (0 : ℝ) ≤ ((n % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hb : |pmN j0 * (1 - m j0)| ≤ 1 := by
      rw [abs_mul, hpm]
      have := h0 j0
      rw [abs_of_nonneg (by linarith)]
      linarith
    rw [hsum1]
    rw [abs_le] at hb ⊢
    constructor <;> linarith [hb.1, hb.2]
  · push Not at hex
    have hall : ∀ j, j < n → m j = 1 := fun j hj => le_antisymm (h1 j) (hex j hj)
    have : ∑ j ∈ Finset.range n, pmN j * m j = ∑ j ∈ Finset.range n, pmN j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [hall j (Finset.mem_range.mp hj)]; ring
    rw [this, hsum1]
    have : n % 2 ≤ 1 := by omega
    have h' : ((n % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast this
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    linarith

/-- at most one position of a stride-`ell` progression mod `N` lies in the last `ell` residues. -/
theorem seam_once (N ell b : ℕ) (hell : 0 < ell) (hN : ell * ell + ell < N) (n : ℕ) (hn : n ≤ ell) (j j' : ℕ)
    (hj : j < n) (hj' : j' < n) (h1 : N - ell < (b + ell * j) % N) (h2 : N - ell < (b + ell * j') % N) : j = j' := by
  by_contra hne
  have hNpos : 0 < N := by omega
  have hr : (b + ell * j) % N < N := Nat.mod_lt _ hNpos
  have hr' : (b + ell * j') % N < N := Nat.mod_lt _ hNpos
  have e1 := Nat.div_add_mod (b + ell * j) N
  have e2 := Nat.div_add_mod (b + ell * j') N
  set q := (b + ell * j) / N with hq
  set q' := (b + ell * j') / N with hq'
  set r := (b + ell * j) % N with hrdef
  set r' := (b + ell * j') % N with hrdef'
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · -- j < j'
    have hd : ell * (j' - j) = ell * j' - ell * j := by rw [Nat.mul_sub]
    have hle : ell * j + ell ≤ ell * j' := by nlinarith
    have hlt2 : ell * j' < ell * ell := by nlinarith
    rcases lt_trichotomy q' q with h | h | h
    · have : N * q' + N ≤ N * q := by nlinarith
      omega
    · rw [h] at e2; omega
    · have : N * q + N ≤ N * q' := by nlinarith
      omega
  · have hle : ell * j' + ell ≤ ell * j := by nlinarith
    have hlt2 : ell * j < ell * ell := by nlinarith
    rcases lt_trichotomy q q' with h | h | h
    · have : N * q + N ≤ N * q' := by nlinarith
      omega
    · rw [h] at e1; omega
    · have : N * q' + N ≤ N * q := by nlinarith
      omega

#print axioms alt_sum_one_dev
#print axioms seam_once

end AdalyFormal.CoverOmega
