import M2B3

/-!
# P409A -- generic arithmetic of periodic boxes, the one-slab tower family `TG`, class cubes on it.

Everything is stated over abstract naturals so that `omega` sees only linear data (atoms `M * ell`, `R * M`, ...).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice)

theorem off_eq (N a c : ℕ) (ha : a < N) (hc : c < N) :
    (a + N - c) % N = if c ≤ a then a - c else a + N - c := by
  split_ifs with h
  · have : a + N - c = (a - c) + N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem off_lt_iff (N a c s : ℕ) (ha : a < N) (hc : c < N) :
    (a + N - c) % N < s ↔ (c ≤ a ∧ a - c < s) ∨ (a < c ∧ a + N - c < s) := by
  rw [off_eq N a c ha hc]
  split_ifs with h <;> omega

theorem site_lt {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (y : PeriodicLatticeSite L) (μ : Fin 3) :
    (y μ).val < N := by
  have := (y μ).isLt; have := hN μ; omega

theorem memBox {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (z y : PeriodicLatticeSite L) (s : ℕ) :
    y ∈ siteBox z s ↔
      ((y 0).val + N - (z 0).val) % N < s ∧ ((y 1).val + N - (z 1).val) % N < s ∧
        ((y 2).val + N - (z 2).val) % N < s := by
  simp only [siteBox, Set.mem_setOf_eq, hN]
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ μ
    fin_cases μ <;> assumption

/-- a box of side `s'` is never contained in a box of side `s < s'` (`s + s' ≤ N`). -/
theorem box_not_sub {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N)
    (z z' : PeriodicLatticeSite L) (s s' : ℕ) (hs : 0 < s) (hss : s < s') (hsN : s + s' ≤ N) :
    ¬ (siteBox z s' ⊆ siteBox z' s) := by
  intro h
  have hz0 := site_lt hN z 0
  have hz0' := site_lt hN z' 0
  have hv : (if (z 0).val + s' ≤ N then (z 0).val + s' - 1 else (z 0).val + s' - 1 - N) < L 0 + 1 := by
    have := hN 0; split_ifs <;> omega
  let w : PeriodicLatticeSite L := Function.update z 0 ⟨_, hv⟩
  have hw0 : (w 0).val = (if (z 0).val + s' ≤ N then (z 0).val + s' - 1 else (z 0).val + s' - 1 - N) := by
    simp [w]
  have hw1 : w 1 = z 1 := by simp only [w, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]
  have hw2 : w 2 = z 2 := by simp only [w, Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
  have hww := site_lt hN w 0
  have hzz : z ∈ siteBox z s' := by
    rw [memBox hN]
    refine ⟨?_, ?_, ?_⟩ <;> (rw [off_lt_iff _ _ _ _ (site_lt hN _ _) (site_lt hN _ _)]; omega)
  have hwz : w ∈ siteBox z s' := by
    rw [memBox hN]
    refine ⟨?_, ?_, ?_⟩
    · rw [off_lt_iff _ _ _ _ hww hz0]; rw [hw0]; split_ifs <;> omega
    · rw [hw1, off_lt_iff _ _ _ _ (site_lt hN _ _) (site_lt hN _ _)]; omega
    · rw [hw2, off_lt_iff _ _ _ _ (site_lt hN _ _) (site_lt hN _ _)]; omega
  have h1 := ((memBox hN _ _ _).mp (h hzz)).1
  have h2 := ((memBox hN _ _ _).mp (h hwz)).1
  rw [off_lt_iff _ _ _ _ hz0 hz0'] at h1
  rw [off_lt_iff _ _ _ _ hww hz0'] at h2
  rw [hw0] at h2 hww
  split_ifs at h2 <;> omega

theorem bigSide0 (M ell : ℕ) : bigSide M ell 0 = M := by simp [bigSide]
theorem bigSide1 (M ell : ℕ) : bigSide M ell 1 = M * ell := by simp [bigSide]

/-- a box of index `i ∈ {0,1}` that is `DescribedAt` is a class cube (uniqueness of the index). -/
theorem isClassCube_of {L : PeriodicLatticeExtent} {N ell M : ℕ} {S : Tower L} (hN : ∀ μ, L μ + 1 = N)
    (hM : 0 < M) (hell : 2 ≤ ell) (hNb : 12 * M + 12 * (M * ell) ≤ N)
    {i : ℕ} (hi : i ≤ 1) {z : PeriodicLatticeSite L}
    (hd : DescribedAt ell M 12 1 S (siteBox z (12 * bigSide M ell i)) i) :
    IsClassCube ell M 12 1 S (siteBox z (12 * bigSide M ell i)) i := by
  refine ⟨hd, fun i' hi' => ?_⟩
  obtain ⟨hi'1, ⟨z', _, hz'⟩, _⟩ := hi'
  by_contra hne
  have hg : M * 2 ≤ M * ell := Nat.mul_le_mul_left M hell
  have hcases : (i = 0 ∧ i' = 1) ∨ (i = 1 ∧ i' = 0) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [bigSide0, bigSide1] at hz'
    exact box_not_sub hN z' z (12 * M) (12 * (M * ell)) (by omega) (by omega) (by omega) hz'.symm.subset
  · rw [bigSide0, bigSide1] at hz'
    exact box_not_sub hN z z' (12 * M) (12 * (M * ell)) (by omega) (by omega) (by omega) hz'.subset

/-! ## the family of towers -/

def TG (A0 A B B0 : ℕ) (L : PeriodicLatticeExtent) : Tower L :=
  ⟨fun j => if j = 0 then {x | A0 ≤ (x 0).val ∧ (x 0).val < B0}
            else if j = 1 then {x | A ≤ (x 0).val ∧ (x 0).val < B} else ∅⟩

theorem TG_om0 {A0 A B B0 : ℕ} {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) :
    x ∈ (TG A0 A B B0 L).Om 0 ↔ A0 ≤ (x 0).val ∧ (x 0).val < B0 := by simp [TG]

theorem TG_om1 {A0 A B B0 : ℕ} {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) :
    x ∈ (TG A0 A B B0 L).Om 1 ↔ A ≤ (x 0).val ∧ (x 0).val < B := by simp [TG]

theorem TG_om2 {A0 A B B0 : ℕ} {L : PeriodicLatticeExtent} (j : ℕ) :
    (TG A0 A B B0 L).Om (j + 2) = ∅ := by simp [TG]

theorem TG_bj0 {A0 A B B0 : ℕ} {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) :
    x ∈ towerBj (TG A0 A B B0 L) 0 ↔ (A0 ≤ (x 0).val ∧ (x 0).val < B0) ∧ ¬ (A ≤ (x 0).val ∧ (x 0).val < B) := by
  unfold towerBj
  rw [Set.mem_sdiff, TG_om0]
  show _ ∧ ¬ (x ∈ (TG A0 A B B0 L).Om 1) ↔ _
  rw [TG_om1]

theorem TG_bj1 {A0 A B B0 : ℕ} {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) :
    x ∈ towerBj (TG A0 A B B0 L) 1 ↔ A ≤ (x 0).val ∧ (x 0).val < B := by
  unfold towerBj
  rw [Set.mem_sdiff, TG_om1]
  have h2 : (TG A0 A B B0 L).Om (1 + 1) = ∅ := TG_om2 0
  rw [h2]
  simp

theorem TG_bj2 {A0 A B B0 : ℕ} {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) :
    x ∉ towerBj (TG A0 A B B0 L) (1 + 1) := by
  unfold towerBj
  have h2 : (TG A0 A B B0 L).Om (1 + 1) = ∅ := TG_om2 0
  rw [h2]
  simp

end AdalyFormal.P409
