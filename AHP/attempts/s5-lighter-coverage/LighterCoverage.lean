import Mathlib

/-!
# S-5 — lighter coverage (UNCOMPILED DRAFT)

This file is not a Lake root and was not compiled. Nothing here is a theorem of the
project tree. It imports only Mathlib. It does not import `CJ3`, `CJ4`, `ZR8Read`,
or any frozen module.

The lighter hypothesis, as recorded in `notes/external_ymx/HARVEST.md` and
`notes/external_ymx/SCOUT_FINDINGS.md`, puts a gauge only on each cube of side `M`
that contains a bond of the active set. This file does not copy that account.

What is proved, as integer arithmetic only:

* The read radius copied below is strictly larger than a block of side `ell ^ m`
  (`block_lt_readRadius`). The recursion is the same clause as `rhoT` in
  `lean/src/ZR8Read.lean`. The radius is the same expression as the ball in
  `read_region` (`lean/src/CJ4.lean`). Neither equality is definitional: those
  declarations are not imported.
* A side-`s` interval that contains the unit bond at `0` does not contain the site
  at offset `s` (`no_side_containing_bond_and_far`).
* A factor-`c` class side `c * (M * ell ^ i)`, the side in `DescribedAt`
  (`lean/src/ZStatementP428.lean`, `siteBox` of `f * bigSide`), is strictly longer
  than `M` whenever `c ≥ 2` and `M ≥ 1` (`class_side_gt_block`).

`plaq_small_class` (`lean/src/CJ3.lean`) is the lemma that asks for the plaquette.
`classRows_read` (`lean/src/CJ4.lean`) applies it on this ball. The arithmetic does
not build a tower, a gauge, or a quadratic form.
-/

set_option autoImplicit false

namespace AdalyFormal.AHP.S5Lighter

/-- Same recursion as `rhoT` in `lean/src/ZR8Read.lean`. Not that declaration. -/
def rhoT (ell : ℕ) : ℕ → ℕ
  | 0 => 0
  | l + 1 => rhoT ell l + 4 * (ell ^ l * ell)

/-- Radius of the ball passed to `plaq_small_class` by `read_region`:
`4 * (ell ^ l * ell) + 2 * rhoT ell l`. Not the frozen `Ball`. -/
def readRadius (ell l : ℕ) : ℕ :=
  4 * (ell ^ l * ell) + 2 * rhoT ell l

theorem readRadius_ge (ell l : ℕ) : 4 * ell ^ (l + 1) ≤ readRadius ell l := by
  unfold readRadius
  rw [Nat.pow_succ]
  exact Nat.le_add_right _ _

theorem block_lt_readRadius (ell m : ℕ) (hell : 2 ≤ ell) : ell ^ m < readRadius ell m := by
  have h4 : 4 * ell ^ (m + 1) ≤ readRadius ell m := readRadius_ge ell m
  have hpow : ell ^ (m + 1) = ell ^ m * ell := Nat.pow_succ ell m
  have h8 : 8 * ell ^ m ≤ 4 * ell ^ (m + 1) := by
    rw [hpow]
    have hc : 8 ≤ 4 * ell := by omega
    calc
      8 * ell ^ m ≤ (4 * ell) * ell ^ m := Nat.mul_le_mul_right (ell ^ m) hc
      _ = 4 * (ell * ell ^ m) := by rw [Nat.mul_assoc]
      _ = 4 * (ell ^ m * ell) := by rw [Nat.mul_comm ell (ell ^ m)]
  have hpos : 0 < ell ^ m := Nat.pow_pos (by omega)
  have hM : ell ^ m < 8 * ell ^ m := by
    have h1 : 1 * ell ^ m < 8 * ell ^ m := Nat.mul_lt_mul_of_pos_right (by omega) hpos
    rwa [Nat.one_mul] at h1
  omega

/-- The headline shape `M = ell ^ m`, read at level `l = m`. -/
theorem block_in_read_ball (ell m : ℕ) (hell : 2 ≤ ell) : ell ^ m ≤ readRadius ell m :=
  Nat.le_of_lt (block_lt_readRadius ell m hell)

theorem readRadius_two_one : readRadius 2 1 = 32 := by
  unfold readRadius rhoT
  rfl

/-- Sites of one axis-aligned block of `s` consecutive positions. -/
def Side (s a x : ℕ) : Prop :=
  a ≤ x ∧ x < a + s

/-- A side-`s` block that contains both endpoints of the unit bond at `0`
does not contain the site at offset `s`. -/
theorem no_side_containing_bond_and_far (s : ℕ) (hs : 2 ≤ s) :
    ¬ ∃ a, Side s a 0 ∧ Side s a 1 ∧ Side s a s := by
  rintro ⟨a, h0, h1, hz⟩
  have ha : a = 0 := by omega
  subst ha
  omega

/-- `DescribedAt` uses side `c * bigSide M ell i = c * (M * ell ^ i)`.
That side is longer than `M` for every factor `c ≥ 2`. -/
theorem class_side_gt_block (c M ell i : ℕ) (hc : 2 ≤ c) (hM : 1 ≤ M) (hell : 1 ≤ ell) :
    M < c * (M * ell ^ i) := by
  have hpos : 0 < ell ^ i := Nat.pow_pos (by omega)
  have hM0 : 0 < M := by omega
  have hcM : M < c * M := by
    have h1 : 1 * M < c * M := Nat.mul_lt_mul_of_pos_right (by omega) hM0
    rwa [Nat.one_mul] at h1
  have hrest : c * M ≤ c * M * ell ^ i := by
    have hone : 1 ≤ ell ^ i := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos)
    have hmul : c * M * 1 ≤ c * M * ell ^ i := Nat.mul_le_mul_left (c * M) hone
    rwa [Nat.mul_one] at hmul
  have hstep : c * M ≤ c * (M * ell ^ i) := by
    rw [← Nat.mul_assoc]
    exact hrest
  omega

end AdalyFormal.AHP.S5Lighter
