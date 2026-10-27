import MR7

/-!
# CovA -- block arithmetic on a torus of `N` level-0 blocks, and the tower `GT` (m2_coverage, 2026-10-14)

Generalises the route lane's `VTM` (MR7, torus of exactly `26` blocks) to a torus of `N = 2n` blocks of side `M`
(fine side `N·M`), `ell = 2`, `k = 1`:
* `Ω₀` = the whole torus;
* `Ω₁` = the torus minus six level-1 big blocks (side `2M`) at level-1 column coordinates
  `(6,0,0), (n-6,0,0), (0,6,0), (0,n-6,0), (0,0,6), (0,0,n-6)` (`holeQ`);
* `Ω₂ = ∅`.
For `n = 13` this is MR7's `VTM`.  Here `n` is free, so the torus can be as large as the `Λ`-collar `R·M` requires.
This module: the arithmetic (`inB_iff`, `modK`, `shift_blk`), the tower, `gt_admissible`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Coverage

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-! ## arithmetic -/

/-- `a` lies in the cyclic window `[b, b + c)` of `ℤ/N`. -/
def inB (N b c a : ℕ) : Prop := (a + N - b) % N < c

theorem inB_iff {N b c a : ℕ} (ha : a < N) (hb : b < N) :
    inB N b c a ↔ (b ≤ a ∧ a - b < c) ∨ (a < b ∧ a + N - b < c) := by
  unfold inB
  rcases Nat.lt_or_ge a b with h | h
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · have e : a + N - b = (a - b) + N := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega

theorem mod_split (M N X r : ℕ) (hM : 0 < M) (hN : 0 < N) (hr : r < M) :
    (M * X + r) % (N * M) = M * (X % N) + r := by
  have h1 : M * X + r = (M * (X % N) + r) + (N * M) * (X / N) := by
    have := Nat.div_add_mod X N
    calc M * X + r = M * (N * (X / N) + X % N) + r := by rw [this]
      _ = (M * (X % N) + r) + (N * M) * (X / N) := by ring
  rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have h2 : X % N + 1 ≤ N := Nat.mod_lt _ hN
  have h3 := Nat.mul_le_mul_left M h2
  have h4 : M * (X % N + 1) = M * (X % N) + M := by ring
  have h5 : M * N = N * M := by ring
  omega

theorem lt_mul_iff (M t r c : ℕ) (hr : r < M) : M * t + r < c * M ↔ t < c := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have := Nat.mul_le_mul_left M hc
    have e : M * c = c * M := by ring
    omega
  · intro h
    have := Nat.mul_le_mul_left M (show t + 1 ≤ c by omega)
    have e : M * c = c * M := by ring
    have e2 : M * (t + 1) = M * t + M := by ring
    omega

theorem blk_lt (M N v : ℕ) (hM : 0 < M) (hv : v < N * M) : v / M < N := (Nat.div_lt_iff_lt_mul hM).2 hv

/-- block-window form of box membership along one axis. -/
theorem modK (M N v b c : ℕ) (hM : 0 < M) (hv : v < N * M) (hb : b < N) :
    (v + N * M - M * b) % (N * M) < c * M ↔ inB N b c (v / M) := by
  have hN : 0 < N := by omega
  have hr : v % M < M := Nat.mod_lt _ hM
  have hv' : M * (v / M) + v % M = v := Nat.div_add_mod v M
  have ha : v / M < N := blk_lt M N v hM hv
  have hMb : M * b ≤ N * M := by
    have := Nat.mul_le_mul_left M (le_of_lt hb); rw [mul_comm M N] at this; exact this
  have e : v + N * M - M * b = M * (v / M + N - b) + v % M := by
    have hab : b ≤ v / M + N := le_trans (le_of_lt hb) (Nat.le_add_left _ _)
    have e1 : M * (v / M + N - b) = M * (v / M) + N * M - M * b := by
      rw [Nat.mul_sub, Nat.mul_add, mul_comm M N]
    rw [e1]
    have : M * b ≤ M * (v / M) + N * M := le_trans hMb (Nat.le_add_left _ _)
    omega
  rw [e, mod_split M N _ _ hM hN hr, lt_mul_iff M _ _ c hr]
  rfl

/-- the block of `v + 1` is the block of `v` or the next one. -/
theorem shift_blk (M N v : ℕ) (hM : 0 < M) (hv : v < N * M) :
    ((v + 1) % (N * M)) / M = v / M ∨ ((v + 1) % (N * M)) / M = (v / M + 1) % N := by
  have hv' : M * (v / M) + v % M = v := Nat.div_add_mod v M
  have hr : v % M < M := Nat.mod_lt _ hM
  have ha := blk_lt M N v hM hv
  by_cases h1 : v + 1 < N * M
  · rw [Nat.mod_eq_of_lt h1]
    have e : v + 1 = (v % M + 1) + M * (v / M) := by omega
    rw [e, Nat.add_mul_div_left _ _ hM]
    by_cases h2 : v % M + 1 < M
    · left; rw [Nat.div_eq_of_lt h2]; ring
    · right
      have h3 : v % M + 1 = M := by omega
      rw [h3, Nat.div_self hM]
      have h4 : v / M + 1 < N := by
        by_contra hc
        have := Nat.mul_le_mul_left M (show N ≤ v / M + 1 by omega)
        have e2 : M * (v / M + 1) = M * (v / M) + M := by ring
        have e3 : M * N = N * M := by ring
        omega
      rw [Nat.mod_eq_of_lt h4]; ring
  · have h1' : v + 1 = N * M := by omega
    rw [h1', Nat.mod_self, Nat.zero_div]
    right
    have h5 : v / M + 1 = N := by
      have h6 : v / M + 1 ≤ N := ha
      by_contra hc
      have h7 : v / M + 2 ≤ N := by omega
      have := Nat.mul_le_mul_left M h7
      have e2 : M * (v / M + 2) = M * (v / M) + 2 * M := by ring
      have e3 : M * N = N * M := by ring
      omega
    rw [h5, Nat.mod_self]

/-! ## the tower `GT` -/

/-- the six holes, in level-1 column coordinates. -/
def holeQ (n a b c : ℕ) : Prop :=
  ((a = 6 ∨ a = n - 6) ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ (b = 6 ∨ b = n - 6) ∧ c = 0) ∨
    (a = 0 ∧ b = 0 ∧ (c = 6 ∨ c = n - 6))

def GH {L : PeriodicLatticeExtent} (n M : ℕ) (x : PeriodicLatticeSite L) : Prop :=
  holeQ n ((x 0).val / (M * 2)) ((x 1).val / (M * 2)) ((x 2).val / (M * 2))

def GT (L : PeriodicLatticeExtent) (n M : ℕ) : Tower L :=
  ⟨fun j => if j = 0 then Set.univ else if j = 1 then {x | ¬ GH n M x} else ∅⟩

theorem gt_om0 {L : PeriodicLatticeExtent} {n M : ℕ} : (GT L n M).Om 0 = Set.univ := by simp [GT]
theorem gt_om1 {L : PeriodicLatticeExtent} {n M : ℕ} : (GT L n M).Om 1 = {x | ¬ GH n M x} := by simp [GT]
theorem gt_omj {L : PeriodicLatticeExtent} {n M j : ℕ} (hj : 2 ≤ j) : (GT L n M).Om j = ∅ := by
  simp only [GT]; rw [if_neg (by omega), if_neg (by omega)]

/-- two coordinates that are not column `0`: no hole. -/
theorem two_ne_zero_noHole (n : ℕ) (q : Fin 3 → ℕ) (α β : Fin 3) (hab : α ≠ β) (hα : q α ≠ 0) (hβ : q β ≠ 0) :
    ¬ holeQ n (q 0) (q 1) (q 2) := by
  intro hc
  unfold holeQ at hc
  fin_cases α <;> fin_cases β <;> simp at hab hα hβ <;> omega

/-- one coordinate outside `{0, 6, n-6}`: no hole. -/
theorem one_free_noHole (n : ℕ) (q : Fin 3 → ℕ) (γ : Fin 3) (h0 : q γ ≠ 0) (h6 : q γ ≠ 6) (h7 : q γ ≠ n - 6) :
    ¬ holeQ n (q 0) (q 1) (q 2) := by
  intro hc
  unfold holeQ at hc
  fin_cases γ <;> simp at h0 h6 h7 <;> omega

theorem bs0 (M : ℕ) : bigSide M 2 0 = M := by simp [bigSide]
theorem bs1 (M : ℕ) : bigSide M 2 1 = M * 2 := by simp [bigSide]

section tower
variable {L : PeriodicLatticeExtent} {n M : ℕ} (hM : 0 < M) (hn : 25 ≤ n) (hL : ∀ μ, L μ + 1 = 2 * n * M)
include hM hn hL

theorem xlt (x : PeriodicLatticeSite L) (σ : Fin 3) : (x σ).val < 2 * n * M := by
  have := (x σ).isLt; have := hL σ; omega

theorem gt_admissible {R : ℕ} (hR : 2 ≤ R) : Admissible 2 M R 1 (GT L n M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this; rw [gt_om0]; trivial
    · rw [gt_omj (by omega)] at hx; exact hx.elim
  · intro j hj; exact gt_omj (by omega)
  · intro j hj μ
    rw [hL μ]
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this; rw [bs0]; exact Dvd.intro_left (2 * n) rfl
    · have : j = 1 := by omega
      subst this; rw [bs1]; exact ⟨n, by ring⟩
  · intro j hj
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this; rw [gt_om0]; intro x _ y _; trivial
    · have : j = 1 := by omega
      subst this; rw [gt_om1, bs1]
      intro x hx y hy
      simp only [Set.mem_setOf_eq, GH] at hx ⊢
      rw [hy 0, hy 1, hy 2]; exact hx
  · intro j hj x hx y hy
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this; rw [gt_om0] at hx; exact (hx trivial).elim
    · rw [gt_omj (by omega)] at hy; exact hy.elim
  · intro x
    rw [gt_om0]
    simp only [Set.mem_univ, true_iff]
    by_cases hx : GH n M x
    · -- move one column-0 coordinate to column 1
      have h2M : M * 2 < L 0 + 1 ∧ M * 2 < L 1 + 1 := by
        rw [hL 0, hL 1]
        have : M * 2 < 2 * n * M := by nlinarith
        exact ⟨this, this⟩
      have hM2 : (M * 2) / (M * 2) = 1 := Nat.div_self (by omega)
      have hsmall : ∀ σ : Fin 3, (x σ).val / (M * 2) = 0 → (x σ).val < M * 2 := by
        intro σ h0
        by_contra hc; push Not at hc
        have := Nat.div_le_div_right (c := M * 2) hc
        rw [hM2] at this; omega
      have hcol0 : (x 0).val / (M * 2) = 0 ∨ (x 1).val / (M * 2) = 0 := by
        unfold GH holeQ at hx; omega
      have pcd_small : ∀ (T a : ℕ), a < M * 2 → M * 2 < T → pcd T a (M * 2) ≤ R * M := by
        intro T a ha hT
        have : 2 * M ≤ R * M := Nat.mul_le_mul_right _ hR
        unfold pcd; split_ifs <;> omega
      rcases hcol0 with h0 | h0
      · refine ⟨Function.update x 0 ⟨M * 2, h2M.1⟩, ?_, x, fun _ => rfl, ?_⟩
        · rw [gt_om1]
          simp only [Set.mem_setOf_eq, GH, Function.update_self]
          rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0), Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
          simp only [hM2]
          intro hc; unfold holeQ at hc; omega
        · unfold pdist
          rw [Fin.sum_univ_three]
          simp only [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
            Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
          have h1 : pcd (L 1 + 1) (x 1).val (x 1).val = 0 := by unfold pcd; simp
          have h2 : pcd (L 2 + 1) (x 2).val (x 2).val = 0 := by unfold pcd; simp
          rw [h1, h2]
          have := pcd_small (L 0 + 1) _ (hsmall 0 h0) h2M.1
          omega
      · refine ⟨Function.update x 1 ⟨M * 2, h2M.2⟩, ?_, x, fun _ => rfl, ?_⟩
        · rw [gt_om1]
          simp only [Set.mem_setOf_eq, GH, Function.update_self]
          rw [Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1), Function.update_of_ne (by decide : (2 : Fin 3) ≠ 1)]
          simp only [hM2]
          intro hc; unfold holeQ at hc; omega
        · unfold pdist
          rw [Fin.sum_univ_three]
          simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1),
            Function.update_of_ne (by decide : (2 : Fin 3) ≠ 1)]
          have h1 : pcd (L 0 + 1) (x 0).val (x 0).val = 0 := by unfold pcd; simp
          have h2 : pcd (L 2 + 1) (x 2).val (x 2).val = 0 := by unfold pcd; simp
          rw [h1, h2]
          have := pcd_small (L 1 + 1) _ (hsmall 1 h0) h2M.2
          omega
    · refine ⟨x, by rw [gt_om1]; exact hx, x, fun _ => rfl, ?_⟩
      have : pdist x x = 0 := by
        unfold pdist pcd; simp
      omega

end tower

end AdalyFormal.M2Coverage
