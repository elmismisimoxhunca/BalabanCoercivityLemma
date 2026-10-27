import NVC2

/-!
# NVC3 -- box geometry on a torus of side `N` (lane nonvac_c_20261017)

`clamp1D`: a window of `c s` (`c ≥ 2`) aligned to multiples of `s` placed inside `[lo, hi)` containing `v` and `w ≤ v+1`.
`box_exists`: the 3-dimensional corner `z` (coordinate 0 from `clamp1D`, coordinates 1, 2 rounded down to multiples of `s`) such that every
`y` adjacent to `x` (each coordinate equal or one step up, mod `N`) with `y₀ ≤ w` lies in `siteBox z (c s)`, and every site of the box has
`lo ≤ y₀ < hi`.   `isClassCube_of`: uniqueness of the class index is automatic from the disjointness of the strata.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NonVacC

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

theorem clamp1D {c s lo hi v w : ℕ} (hc : 2 ≤ c) (hs : 0 < s) (hlo : s ∣ lo) (hhi : s ∣ hi) (hwid : lo + c * s ≤ hi)
    (hv : lo ≤ v) (_hvw : v ≤ w) (hw1 : w ≤ v + 1) (hwh : w < hi) :
    ∃ t, s ∣ t ∧ lo ≤ t ∧ t + c * s ≤ hi ∧ t ≤ v ∧ w < t + c * s := by
  have h2s : 2 * s ≤ c * s := Nat.mul_le_mul_right s hc
  obtain ⟨a, rfl⟩ := hlo
  obtain ⟨b, rfl⟩ := hhi
  have hab : a + c ≤ b := by
    by_contra h
    push Not at h
    have : s * b < s * (a + c) := Nat.mul_lt_mul_of_pos_left h hs
    nlinarith
  have hq1 : s * (v / s) ≤ v := Nat.mul_div_le v s
  have hq2 : v < s * (v / s) + s := by
    have h1 := Nat.div_add_mod v s
    have h2 := Nat.mod_lt v hs
    nlinarith
  have haq : a ≤ v / s := by
    rw [Nat.le_div_iff_mul_le hs]; nlinarith
  refine ⟨s * min (v / s) (b - c), Dvd.intro _ rfl, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_le_mul_left s (le_min haq (by omega))
  · have : min (v / s) (b - c) + c ≤ b := by have := min_le_right (v / s) (b - c); omega
    have := Nat.mul_le_mul_left s this
    nlinarith
  · exact le_trans (Nat.mul_le_mul_left s (min_le_left _ _)) hq1
  · by_cases hm : v / s ≤ b - c
    · rw [min_eq_left hm]; nlinarith
    · push Not at hm
      rw [min_eq_right hm.le]
      have : s * (b - c) + c * s = s * b := by
        have : b - c + c = b := by omega
        calc s * (b - c) + c * s = s * (b - c + c) := by ring
          _ = s * b := by rw [this]
      omega

/-- box membership, coordinatewise -/
theorem mem_box_N {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (z y : PeriodicLatticeSite L) (s : ℕ) :
    y ∈ siteBox z s ↔
      ((y 0).val + N - (z 0).val) % N < s ∧ ((y 1).val + N - (z 1).val) % N < s ∧
        ((y 2).val + N - (z 2).val) % N < s := by
  simp only [siteBox, Set.mem_setOf_eq, hN]
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ μ
    fin_cases μ <;> assumption

theorem coord_adj_in {c N s zc xc yc : ℕ} (hc : 2 ≤ c) (hz : zc ≤ xc) (hx : xc < zc + s) (hxN : xc < N)
    (hy : yc = xc ∨ yc = (xc + 1) % N) : (yc + N - zc) % N < c * s := by
  have hs : 0 < s := by omega
  have h2s : 2 * s ≤ c * s := Nat.mul_le_mul_right s hc
  rcases hy with rfl | rfl
  · have : (yc + N - zc) = (yc - zc) + N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · by_cases h1 : xc + 1 < N
    · rw [Nat.mod_eq_of_lt h1]
      have : (xc + 1 + N - zc) = (xc + 1 - zc) + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · have h2 : xc + 1 = N := by omega
      rw [h2, Nat.mod_self]
      have : (0 + N - zc) % N ≤ 0 + N - zc := Nat.mod_le _ _
      omega

theorem coord_box_sub {N z y side : ℕ} (hside : z + side ≤ N) (hyN : y < N) (h : (y + N - z) % N < side) :
    z ≤ y ∧ y < z + side := by
  by_cases hzy : z ≤ y
  · have : (y + N - z) = (y - z) + N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
    omega
  · push Not at hzy
    rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

theorem coord_box_in {N z y side : ℕ} (hside : z + side ≤ N) (hz : z ≤ y) (hy : y < z + side) :
    (y + N - z) % N < side := by
  have : (y + N - z) = (y - z) + N := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

/-- `y` is adjacent to `x`: each coordinate equal, or one step up (periodic, side `N`). -/
def Adj {L : PeriodicLatticeExtent} (N : ℕ) (x w : PeriodicLatticeSite L) : Prop :=
  ∀ ρ : Fin 3, (w ρ).val = (x ρ).val ∨ (w ρ).val = ((x ρ).val + 1) % N

theorem adj_refl {L : PeriodicLatticeExtent} (N : ℕ) (x : PeriodicLatticeSite L) : Adj N x x := fun _ => Or.inl rfl

theorem box_exists {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) {c s lo hi : ℕ} (hc : 2 ≤ c) (hs : 0 < s)
    (hlo : s ∣ lo) (hhi : s ∣ hi) (hwid : lo + c * s ≤ hi) (hhiN : hi ≤ N)
    (x : PeriodicLatticeSite L) (w : ℕ) (hvlo : lo ≤ (x 0).val) (_hvw : (x 0).val ≤ w) (hw1 : w ≤ (x 0).val + 1)
    (hwhi : w < hi) (hx1 : (x 0).val + 1 < N) :
    ∃ z : PeriodicLatticeSite L, (∀ μ : Fin 3, (z μ).val % s = 0) ∧
      (∀ y : PeriodicLatticeSite L, y ∈ siteBox z (c * s) → lo ≤ (y 0).val ∧ (y 0).val < hi) ∧
      (∀ y : PeriodicLatticeSite L, Adj N x y → (y 0).val ≤ w → y ∈ siteBox z (c * s)) := by
  have hxN : ∀ μ, (x μ).val < N := fun μ => by have := (x μ).isLt; have := hN μ; omega
  obtain ⟨t, ht1, ht2, ht3, ht4, ht5⟩ := clamp1D hc hs hlo hhi hwid hvlo _hvw hw1 hwhi
  let cc : Fin 3 → ℕ := fun μ => if μ = 0 then t else s * ((x μ).val / s)
  have hcc : ∀ μ, cc μ < L μ + 1 := fun μ => by
    rw [hN μ]
    simp only [cc]; split_ifs
    · omega
    · exact lt_of_le_of_lt (Nat.mul_div_le _ _) (hxN μ)
  let z : PeriodicLatticeSite L := fun μ => ⟨cc μ, hcc μ⟩
  have hz0 : (z 0).val = t := by simp [z, cc]
  have hz1 : (z 1).val = s * ((x 1).val / s) := by simp [z, cc]
  have hz2 : (z 2).val = s * ((x 2).val / s) := by simp [z, cc]
  have hq : ∀ μ : Fin 3, μ ≠ 0 → (z μ).val ≤ (x μ).val ∧ (x μ).val < (z μ).val + s := by
    intro μ hμ
    have e : (z μ).val = s * ((x μ).val / s) := by simp [z, cc, hμ]
    have h1 := Nat.div_add_mod (x μ).val s
    have h2 := Nat.mod_lt (x μ).val hs
    refine ⟨by rw [e]; exact Nat.mul_div_le _ _, ?_⟩
    rw [e]
    generalize s * ((x μ).val / s) = A at h1 ⊢
    omega
  refine ⟨z, ?_, ?_, ?_⟩
  · intro μ
    by_cases hμ : μ = 0
    · subst hμ; rw [hz0]; exact Nat.mod_eq_zero_of_dvd ht1
    · have e : (z μ).val = s * ((x μ).val / s) := by simp [z, cc, hμ]
      rw [e]; exact Nat.mul_mod_right _ _
  · intro y hy
    rw [mem_box_N hN] at hy
    have := coord_box_sub (N := N) (z := (z 0).val) (y := (y 0).val) (side := c * s) (by rw [hz0]; omega)
      (by have := (y 0).isLt; have := hN 0; omega) hy.1
    rw [hz0] at this
    omega
  · intro y hadj hyw
    rw [mem_box_N hN]
    refine ⟨?_, ?_, ?_⟩
    · have hy0 : (y 0).val = (x 0).val ∨ (y 0).val = (x 0).val + 1 := by
        rcases hadj 0 with h | h
        · exact Or.inl h
        · right; rw [h, Nat.mod_eq_of_lt hx1]
      refine coord_box_in (N := N) (z := (z 0).val) (y := (y 0).val) (side := c * s) (by rw [hz0]; omega)
        (by rw [hz0]; omega) (by rw [hz0]; omega)
    · have := hq 1 (by decide)
      exact coord_adj_in hc (N := N) (s := s) (zc := (z 1).val) (xc := (x 1).val) (yc := (y 1).val)
        this.1 this.2 (hxN 1) (hadj 1)
    · have := hq 2 (by decide)
      exact coord_adj_in hc (N := N) (s := s) (zc := (z 2).val) (xc := (x 2).val) (yc := (y 2).val)
        this.1 this.2 (hxN 2) (hadj 2)

/-- distinct strata are disjoint, hence the class index is unique. -/
theorem bj_disjoint {L : PeriodicLatticeExtent} {S : Tower L} (hnest : ∀ j, S.Om (j + 1) ⊆ S.Om j)
    {i l : ℕ} (hil : i < l) {y : PeriodicLatticeSite L} (hi : y ∈ towerBj S i) : y ∉ towerBj S l := by
  intro hl
  have mono : ∀ a b : ℕ, a ≤ b → S.Om b ⊆ S.Om a := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact fun _ h => h
    | succ b _ ih => exact fun x hx => ih (hnest b hx)
  exact hi.2 (mono (i + 1) l hil hl.1)

theorem bj_eq {L : PeriodicLatticeExtent} {S : Tower L} (hnest : ∀ j, S.Om (j + 1) ⊆ S.Om j)
    {a b : ℕ} {y : PeriodicLatticeSite L} (ha : y ∈ towerBj S a) (hb : y ∈ towerBj S b) : a = b := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · exact bj_disjoint hnest hl ha hb
  · exact bj_disjoint hnest hl hb ha

theorem isClassCube_of {L : PeriodicLatticeExtent} {ell M k c : ℕ} {S : Tower L}
    (hnest : ∀ j, S.Om (j + 1) ⊆ S.Om j) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (hd : DescribedAt ell M c k S sites j) : IsClassCube ell M c k S sites j := by
  refine ⟨hd, fun i hi => ?_⟩
  obtain ⟨y, hy, hyi⟩ := hi.2.2.2
  obtain ⟨y', hy', hyj⟩ := hd.2.2.2
  have a1 : i = j ∨ i = j + 1 := by
    rcases hd.2.2.1 hy with h | h
    · exact Or.inl (bj_eq hnest hyi h)
    · exact Or.inr (bj_eq hnest hyi h)
  have a2 : j = i ∨ j = i + 1 := by
    rcases hi.2.2.1 hy' with h | h
    · exact Or.inl (bj_eq hnest hyj h)
    · exact Or.inr (bj_eq hnest hyj h)
  omega

end AdalyFormal.NonVacC
