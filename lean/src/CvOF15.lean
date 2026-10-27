import CvOF14

/-!
# CvOF15 -- the unit profile `g = gU p` is an admissible `B~` (lane omega)

`zfun (gU M R p)` has zero `ell`-block sums, is supported on the slices `u0+p`, `u0+p+1` (non-aligned, strictly inside `neLam`);
the staircase / dropped bonds of `Lambda'` in direction `1` all sit at aligned `x_0`, so they miss the support.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega

open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG

variable {ell M R : ℕ}

theorem mod_aux (hdvd : ell ∣ M) (c : ℕ) (hc : c < ell) (R : ℕ) : (M * (2 * R + 14) + c) % ell = c := by
  obtain ⟨m, rfl⟩ := hdvd
  rw [show ell * m * (2 * R + 14) = ell * (m * (2 * R + 14)) by ring, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hc

theorem gU_ne_zero {p u : ℕ} (h : gU M R p u ≠ 0) : u = u0N M R + p ∨ u = u0N M R + p + 1 := by
  unfold gU at h
  by_contra hc
  push_neg at hc
  simp [hc.1, hc.2] at h

theorem sum_ite_block (hell : 0 < ell) (a q : ℕ) :
    ∑ n ∈ Finset.range ell, (if ell * q + n = a then (1 : ℝ) else 0) = if a / ell = q then 1 else 0 := by
  by_cases h : a / ell = q
  · rw [if_pos h, Finset.sum_eq_single (a % ell)]
    · have : ell * q + a % ell = a := by rw [← h]; exact Nat.div_add_mod a ell
      simp [this]
    · intro n hn hne
      have : ell * q + n ≠ a := by
        intro h2
        apply hne
        have h3 : a % ell = n := by
          rw [← h2, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (Finset.mem_range.mp hn)
        exact h3.symm
      simp [this]
    · intro hn; exact absurd (Finset.mem_range.mpr (Nat.mod_lt a hell)) hn
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun n hn => ?_)
    have : ell * q + n ≠ a := by
      intro h2
      apply h
      rw [← h2, Nat.mul_add_div hell, Nat.div_eq_of_lt (Finset.mem_range.mp hn)]; simp
    simp [this]

theorem gU_block (hE : 2 ∣ ell) (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) {p : ℕ} (hp : p ≤ 1) (q : ℕ) :
    ∑ n ∈ Finset.range ell, gU M R p (ell * q + n) = 0 := by
  have hell : 0 < ell := by omega
  have hell4 : 4 ≤ ell := by omega
  unfold gU
  simp only [Finset.sum_sub_distrib, sum_ite_block hell]
  have h1 : (u0N M R + p) / ell = (u0N M R + p + 1) / ell := by
    have e1 : u0N M R + p = M * (2 * R + 14) + (1 + p) := by unfold u0N; ring
    have e2 : u0N M R + p + 1 = M * (2 * R + 14) + (2 + p) := by unfold u0N; ring
    obtain ⟨m, rfl⟩ := hdvd
    rw [e2, e1, show ell * m * (2 * R + 14) = ell * (m * (2 * R + 14)) by ring, Nat.mul_add_div hell, Nat.mul_add_div hell,
      Nat.div_eq_of_lt (by omega : 1 + p < ell), Nat.div_eq_of_lt (by omega : 2 + p < ell)]
  rw [h1]; ring

end AdalyFormal.CoverOmega
