import Mathlib

/-!
# S-4 — odd `ell` sites-only cell (UNCOMPILED DRAFT)

This file is not a Lake root and was not compiled. Nothing here is a theorem of the
project tree. It imports only Mathlib. It does not import `SoA1`, `SoM3`, `SoPar`, or any
frozen module.

The sites-only body `CovAssume.FamilyTorusSitesConstAt` is not decided here, for any odd
`ell` and in particular not for Balaban's odd `L > 11` (CMP 109 p.251, as recorded in
`paper/OPEN_ITEMS.md` item S-4). These lemmas are the obstruction to copying the even-`ell`
refutation, not a negation and not a proof.

What is proved, as integer arithmetic only:

* A profile with every horizontal step in `{+d, -d}`, `d ≠ 0`, cannot have both aligned
  `ell × ell` block sums equal to `0` when `ell` is odd (`no_const_step_blockzero_odd`).
  The case `d = 1` is the shape of `AdalyFormal.SitesOnly.no_uniform_step_blockzero_odd`
  (`lean/src/SoPar.lean`). It is not that declaration.
* The numeric window of `not_familyTorusSitesConstAt_div` (`ell ∣ 2(c-1)`, `9 ell ≤ 2(c-1)`,
  `c ≥ 10`, `w ≥ 10`) is inhabited for every odd `ell ≥ 3`, hence for every odd `ell > 11`,
  while `2 ∣ ell` is false there (`odd_arith_window`, `balaban_odd_window`).
* Whenever the two block sums are not both zero, some single `τ ≠ 0` meets the homogeneous
  conditions `τ S_q ∈ 2 π ell² ℤ` (`homogeneous_one_tau`). Together with the block-sum
  obstruction, every such odd profile has at least one such `τ`
  (`const_step_one_lattice_tau`). This is not a blocking criterion. The docstring of
  `no_nearby_tau_odd` that treats it as one is wrong (Sol's correction, recorded in the
  paper). Branch offsets are not formalized here.

No declaration mentions `SU(2)`, a blocked gauge, `genForm`, `CovSitesF`, or
`FamilyTorusSitesConstAt`.
-/

set_option autoImplicit false

namespace AdalyFormal.AHP.OddSites

theorem odd_succ_double (ell : ℕ) (hodd : ell % 2 = 1) : ell = 2 * (ell / 2) + 1 := by
  have h := Nat.mod_add_div ell 2
  omega

theorem not_two_dvd_of_odd (ell : ℕ) (hodd : ell % 2 = 1) : ¬ 2 ∣ ell := by
  intro hdv
  obtain ⟨k, hk⟩ := hdv
  have : ell % 2 = 0 := by rw [hk, Nat.mul_mod_right]
  omega

theorem odd_cube_form (ell : ℕ) (hodd : ell % 2 = 1) :
    (ell : ℤ) ^ 3 =
      2 * (4 * ((ell / 2 : ℕ) : ℤ) ^ 3 + 6 * ((ell / 2 : ℕ) : ℤ) ^ 2 + 3 * ((ell / 2 : ℕ) : ℤ)) + 1 := by
  have hform : (ell : ℤ) = 2 * ((ell / 2 : ℕ) : ℤ) + 1 := by
    exact_mod_cast odd_succ_double ell hodd
  rw [hform]
  ring

/-- Every step `±d` advances the class of `h` by `d` in `ZMod (2d)`, because `-d ≡ d`. -/
theorem walk_zmod (d : ℕ) (h : ℕ → ℤ)
    (hstep : ∀ x, h (x + 1) = h x + (d : ℤ) ∨ h (x + 1) = h x - (d : ℤ)) :
    ∀ n, ((h n - h 0 - ((n : ℕ) : ℤ) * (d : ℤ) : ℤ) : ZMod (2 * d)) = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rcases hstep n with hp | hm
    · rw [hp]
      have heq :
          h n + (d : ℤ) - h 0 - (((n + 1 : ℕ) : ℤ) * (d : ℤ)) =
            h n - h 0 - (((n : ℕ) : ℤ) * (d : ℤ)) := by
        push_cast
        ring
      rw [heq]
      exact ih
    · rw [hm]
      have heq :
          h n - (d : ℤ) - h 0 - (((n + 1 : ℕ) : ℤ) * (d : ℤ)) =
            (h n - h 0 - (((n : ℕ) : ℤ) * (d : ℤ))) - ((2 * d : ℕ) : ℤ) := by
        push_cast
        ring
      rw [heq, Int.cast_sub, ih, zero_sub, neg_eq_zero, Int.cast_natCast]
      exact ZMod.natCast_self (2 * d)

theorem delta_zmod (d ell i : ℕ) (h : ℕ → ℤ)
    (hstep : ∀ x, h (x + 1) = h x + (d : ℤ) ∨ h (x + 1) = h x - (d : ℤ)) :
    ((h (ell + i) - h i - ((ell : ℕ) : ℤ) * (d : ℤ) : ℤ) : ZMod (2 * d)) = 0 := by
  have ha := walk_zmod d h hstep (ell + i)
  have hb := walk_zmod d h hstep i
  have heq :
      h (ell + i) - h i - ((ell : ℕ) : ℤ) * (d : ℤ) =
        (h (ell + i) - h 0 - (((ell + i : ℕ) : ℤ) * (d : ℤ))) -
          (h i - h 0 - (((i : ℕ) : ℤ) * (d : ℤ))) := by
    push_cast
    ring
  rw [heq, Int.cast_sub, ha, hb, sub_zero]
  rfl

/-- Both aligned block sums cannot vanish when every `x₁`-step has constant magnitude `d ≠ 0`
and `ell` is odd. The two blocks are `[0, ell)²` and `[ell, 2ell) × [0, ell)`. -/
theorem no_const_step_blockzero_odd (ell d : ℕ) (hodd : ell % 2 = 1) (hd : 0 < d)
    (h : ℕ → ℕ → ℤ)
    (hstep : ∀ x y, h (x + 1) y = h x y + (d : ℤ) ∨ h (x + 1) y = h x y - (d : ℤ)) :
    ¬ ((∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h i j = 0) ∧
        (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h (ell + i) j = 0)) := by
  rintro ⟨h0, h1⟩
  have hzero :
      (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, (h (ell + i) j - h i j)) = 0 := by
    calc
      (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, (h (ell + i) j - h i j))
        = ∑ i ∈ Finset.range ell,
            ((∑ j ∈ Finset.range ell, h (ell + i) j) - (∑ j ∈ Finset.range ell, h i j)) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact Finset.sum_sub_distrib
      _ = (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h (ell + i) j) -
            (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h i j) := Finset.sum_sub_distrib
      _ = 0 := by simp [h0, h1]
  let c : ZMod (2 * d) := (((ell : ℤ) * (d : ℤ) : ℤ) : ZMod (2 * d))
  have hterm : ∀ i j, ((h (ell + i) j - h i j : ℤ) : ZMod (2 * d)) = c := by
    intro i j
    have hδ := delta_zmod d ell i (fun n => h n j) (fun x => hstep x j)
    have hsub :
        ((h (ell + i) j - h i j : ℤ) : ZMod (2 * d)) - c =
          ((h (ell + i) j - h i j - (ell : ℤ) * (d : ℤ) : ℤ) : ZMod (2 * d)) := by
      unfold c
      rw [← Int.cast_sub]
      rfl
    exact sub_eq_zero.mp (hsub.trans hδ)
  have hsumcast :
      (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
        ((h (ell + i) j - h i j : ℤ) : ZMod (2 * d))) = 0 := by
    have hcast :
        (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
          ((h (ell + i) j - h i j : ℤ) : ZMod (2 * d))) =
          (((∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
            (h (ell + i) j - h i j)) : ℤ) : ZMod (2 * d)) := by
      symm
      rw [Int.cast_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Int.cast_sum]
      rfl
    rw [hcast, hzero]
    simp
  have hsumconst :
      (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
        ((h (ell + i) j - h i j : ℤ) : ZMod (2 * d))) =
        (((ell : ℤ) ^ 3 * (d : ℤ) : ℤ) : ZMod (2 * d)) := by
    have hrewrite :
        (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
          ((h (ell + i) j - h i j : ℤ) : ZMod (2 * d))) =
          ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, c := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      exact hterm i j
    rw [hrewrite]
    calc
      ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, c
        = ∑ i ∈ Finset.range ell, ((Finset.range ell).card • c) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_const]
      _ = ∑ i ∈ Finset.range ell, ((ell : ZMod (2 * d)) * c) := by
          simp only [Finset.card_range, nsmul_eq_mul]
      _ = (Finset.range ell).card • ((ell : ZMod (2 * d)) * c) := Finset.sum_const
      _ = (ell : ZMod (2 * d)) * ((ell : ZMod (2 * d)) * c) := by
          simp only [Finset.card_range, nsmul_eq_mul]
      _ = ((ell : ℤ) : ZMod (2 * d)) * (((ell : ℤ) : ZMod (2 * d)) *
            (((ell : ℤ) : ZMod (2 * d)) * ((d : ℤ) : ZMod (2 * d)))) := by
          rw [← Int.cast_natCast, ← Int.cast_natCast, Int.cast_mul]
          rfl
      _ = (((ell : ℤ) * ((ell : ℤ) * ((ell : ℤ) * (d : ℤ))) : ℤ) : ZMod (2 * d)) := by
          rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_mul]
          rfl
      _ = (((ell : ℤ) ^ 3 * (d : ℤ) : ℤ) : ZMod (2 * d)) := by
          apply congrArg (fun z : ℤ => (z : ZMod (2 * d)))
          ring
  have hcong : (((ell : ℤ) ^ 3 * (d : ℤ) : ℤ) : ZMod (2 * d)) = ((d : ℤ) : ZMod (2 * d)) := by
    have hdiffZ :
        (ell : ℤ) ^ 3 * (d : ℤ) - (d : ℤ) =
          ((2 * d : ℕ) : ℤ) *
            (4 * ((ell / 2 : ℕ) : ℤ) ^ 3 + 6 * ((ell / 2 : ℕ) : ℤ) ^ 2 + 3 * ((ell / 2 : ℕ) : ℤ)) := by
      have hcube := odd_cube_form ell hodd
      calc
        (ell : ℤ) ^ 3 * (d : ℤ) - (d : ℤ)
          = (2 * (4 * ((ell / 2 : ℕ) : ℤ) ^ 3 + 6 * ((ell / 2 : ℕ) : ℤ) ^ 2 +
                3 * ((ell / 2 : ℕ) : ℤ)) + 1) * (d : ℤ) - (d : ℤ) := by rw [hcube]
        _ = ((2 * d : ℕ) : ℤ) *
              (4 * ((ell / 2 : ℕ) : ℤ) ^ 3 + 6 * ((ell / 2 : ℕ) : ℤ) ^ 2 +
                3 * ((ell / 2 : ℕ) : ℤ)) := by
            push_cast
            ring
    rw [← sub_eq_zero, ← Int.cast_sub, hdiffZ, Int.cast_mul]
    have hself : ((((2 * d : ℕ) : ℤ) : ZMod (2 * d))) = 0 := by
      rw [Int.cast_natCast]
      exact ZMod.natCast_self (2 * d)
    rw [hself, zero_mul]
    rfl
  have hdne : ((d : ℤ) : ZMod (2 * d)) ≠ 0 := by
    intro hz
    have hdiv : ((2 * d : ℕ) : ℤ) ∣ (d : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (d : ℤ) (2 * d)).mp hz
    obtain ⟨q, hq⟩ := hdiv
    have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
    have hq' : (d : ℤ) = (2 * (d : ℤ)) * q := by
      have hcoe : ((2 * d : ℕ) : ℤ) = 2 * (d : ℤ) := by push_cast; ring
      rw [← hcoe]
      exact hq
    have hfac : (d : ℤ) * (1 - 2 * q) = 0 := by
      calc
        (d : ℤ) * (1 - 2 * q) = (d : ℤ) - (d : ℤ) * (2 * q) := by ring
        _ = (d : ℤ) - (2 * (d : ℤ)) * q := by ring
        _ = (d : ℤ) - (d : ℤ) := by rw [← hq']
        _ = 0 := sub_self _
    rcases mul_eq_zero.mp hfac with h | h
    · exact hdZ h
    · omega
  have hbad : ((d : ℤ) : ZMod (2 * d)) = 0 := by
    rw [← hcong, ← hsumconst, hsumcast]
    rfl
  exact hdne hbad

theorem no_unit_step_blockzero_odd (ell : ℕ) (hodd : ell % 2 = 1) (h : ℕ → ℕ → ℤ)
    (hstep : ∀ x y, h (x + 1) y = h x y + 1 ∨ h (x + 1) y = h x y - 1) :
    ¬ ((∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h i j = 0) ∧
        (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h (ell + i) j = 0)) :=
  no_const_step_blockzero_odd ell 1 hodd (by decide) h hstep

/-- The side conditions of the even refutation are numerically inhabited at every odd `ell ≥ 3`.
`w = 19` and `c = 9 ell + 1` give `ell (w - 1) = 2 (c - 1) = 18 ell`, so `9 ell ≤ 2 (c - 1)`.
This does not build a tower and does not inhabit `CfData`. -/
theorem odd_arith_window (ell : ℕ) (hodd : ell % 2 = 1) (hell : 3 ≤ ell) :
    ∃ c w : ℕ, 10 ≤ c ∧ 10 ≤ w ∧ ell * (w - 1) = 2 * (c - 1) ∧
      ell ∣ 2 * (c - 1) ∧ 9 * ell ≤ 2 * (c - 1) ∧ ¬ 2 ∣ ell := by
  refine ⟨9 * ell + 1, 19, ?_, ?_, ?_, ?_, ?_, not_two_dvd_of_odd ell hodd⟩
  · omega
  · decide
  · have hw : (19 : ℕ) - 1 = 18 := by decide
    have hc : (9 * ell + 1) - 1 = 9 * ell := by omega
    rw [hw, hc]
    ring
  · refine ⟨18, ?_⟩
    have hc : (9 * ell + 1) - 1 = 9 * ell := by omega
    rw [hc]
    ring
  · have hc : (9 * ell + 1) - 1 = 9 * ell := by omega
    rw [hc]
    omega

/-- Balaban's range, CMP 109 p.251 as quoted in `paper/OPEN_ITEMS.md` S-4: odd and `> 11`.
Same arithmetic window, still with `¬ 2 ∣ ell`. -/
theorem balaban_odd_window (ell : ℕ) (hodd : ell % 2 = 1) (hgt : 11 < ell) :
    ∃ c w : ℕ, 10 ≤ c ∧ 10 ≤ w ∧ ell * (w - 1) = 2 * (c - 1) ∧
      ell ∣ 2 * (c - 1) ∧ 9 * ell ≤ 2 * (c - 1) ∧ ¬ 2 ∣ ell :=
  odd_arith_window ell hodd (by omega)

/-- One homogeneous lattice parameter. Not two nearby parameters, and not a statement that a
blocked angle vanishes. If `S₀ ≠ 0`, take `τ = 2 π ell² S₀`. If `S₀ = 0`, then `S₁ ≠ 0` and
take `τ = 2 π ell² S₁`. -/
theorem homogeneous_one_tau (ell : ℕ) (hell : 0 < ell) (S₀ S₁ : ℤ)
    (hneq : ¬ (S₀ = 0 ∧ S₁ = 0)) :
    ∃ τ : ℝ, τ ≠ 0 ∧
      (∃ m : ℤ, τ * (S₀ : ℝ) = 2 * Real.pi * (ell : ℝ) ^ 2 * (m : ℝ)) ∧
      (∃ m : ℤ, τ * (S₁ : ℝ) = 2 * Real.pi * (ell : ℝ) ^ 2 * (m : ℝ)) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hpi : 2 * Real.pi * (ell : ℝ) ^ 2 ≠ 0 := by
    have hpos : 0 < 2 * Real.pi * (ell : ℝ) ^ 2 := by positivity
    exact ne_of_gt hpos
  by_cases h0 : S₀ = 0
  · have h1 : S₁ ≠ 0 := by
      intro hS
      exact hneq ⟨h0, hS⟩
    refine ⟨2 * Real.pi * (ell : ℝ) ^ 2 * (S₁ : ℝ), ?_, ?_, ?_⟩
    · exact mul_ne_zero hpi (by exact_mod_cast h1)
    · exact ⟨0, by simp [h0, mul_zero]⟩
    · refine ⟨S₁ * S₁, ?_⟩
      push_cast
      ring
  · refine ⟨2 * Real.pi * (ell : ℝ) ^ 2 * (S₀ : ℝ), ?_, ?_, ?_⟩
    · exact mul_ne_zero hpi (by exact_mod_cast h0)
    · refine ⟨S₀ * S₀, ?_⟩
      push_cast
      ring
    · refine ⟨S₀ * S₁, ?_⟩
      push_cast
      ring

/-- Exact cancellation is impossible, and a single homogeneous `τ` still exists.
Neither clause is `FamilyTorusSitesConstAt`. -/
theorem const_step_one_lattice_tau (ell d : ℕ) (hodd : ell % 2 = 1) (hd : 0 < d)
    (h : ℕ → ℕ → ℤ)
    (hstep : ∀ x y, h (x + 1) y = h x y + (d : ℤ) ∨ h (x + 1) y = h x y - (d : ℤ)) :
    ∃ τ : ℝ, τ ≠ 0 ∧
      (∃ m : ℤ, τ * ((∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h i j : ℤ) : ℝ) =
          2 * Real.pi * (ell : ℝ) ^ 2 * (m : ℝ)) ∧
      (∃ m : ℤ, τ * ((∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h (ell + i) j : ℤ) : ℝ) =
          2 * Real.pi * (ell : ℝ) ^ 2 * (m : ℝ)) := by
  let S₀ : ℤ := ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h i j
  let S₁ : ℤ := ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h (ell + i) j
  have hneq : ¬ (S₀ = 0 ∧ S₁ = 0) := by
    simpa [S₀, S₁] using no_const_step_blockzero_odd ell d hodd hd h hstep
  have hell : 0 < ell := by omega
  simpa [S₀, S₁] using homogeneous_one_tau ell hell S₀ S₁ hneq

/-- Sol's integer example, sums only. `h x y = x` at `ell = 3` has steps `+1`,
`S₀ = 9`, `S₁ = 36`. The blocked-angle reading at `τ = 2π/3` is not proved here. -/
theorem ell_three_linear_is_unit_step :
    ∀ x y : ℕ, ((x + 1 : ℕ) : ℤ) = (x : ℤ) + 1 ∨ ((x + 1 : ℕ) : ℤ) = (x : ℤ) - 1 := by
  intro x _
  left
  push_cast
  ring

theorem ell_three_linear_sums :
    (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, (i : ℤ)) = 9 ∧
      (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, (3 + (i : ℤ))) = 36 := by
  have three : ∀ c : ℤ, ∑ j ∈ Finset.range 3, c = 3 * c := by
    intro c
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  constructor
  · simp_rw [three]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  · simp_rw [three]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num

end AdalyFormal.AHP.OddSites
