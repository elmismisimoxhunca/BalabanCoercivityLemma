import P4L4
import UNI_Joint

/-!
# L0C1 -- box geometry for the level-0 class (lane level0_class_20261019)

(1) a grid-aligned box of side `f M` with corner on the `M`-grid is a union of `M`-blocks (`box_blockClosed`);
(2) unit-step connectivity of a periodic box (`path_exists`): if the box contains a site of `Omega_1` and a site outside `Omega_1`, it contains a site of `Omega_0 \ Omega_1`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.L0C

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.CoverGeom (coord_cell)

variable {L : PeriodicLatticeExtent}

/-- a grid-aligned box is a union of blocks of the grid width. -/
theorem box_blockClosed {M s : ℕ} {z : PeriodicLatticeSite L} (hM : 0 < M) (hN : ∀ μ : Fin 3, M ∣ L μ + 1)
    (hz : GridCorner M z) (hs : M ∣ s) : BlockClosed M (siteBox z s) := by
  intro x hx y hxy μ
  exact coord_cell hM (hN μ) (Nat.dvd_of_mod_eq_zero (hz μ)) hs (z μ).isLt (x μ).isLt (hxy μ).symm (hx μ)

theorem rel_eq {N z a : ℕ} (hz : z < N) (ha : a < N) :
    (a + N - z) % N = if z ≤ a then a - z else a + N - z := by
  split_ifs with h
  · have : a + N - z = (a - z) + N := by omega
    rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
  · exact Nat.mod_eq_of_lt (by omega)

/-- one unit step in one coordinate, toward a target relative position. -/
theorem coord_step {N z a a₀ : ℕ} (hz : z < N) (ha : a < N) (ha₀ : a₀ < N)
    (hne : (a + N - z) % N ≠ (a₀ + N - z) % N) :
    ∃ b, b < N ∧ (b = (a + 1) % N ∨ a = (b + 1) % N) ∧
      (((b + N - z) % N + 1 = (a + N - z) % N ∧ (a₀ + N - z) % N < (a + N - z) % N) ∨
       ((b + N - z) % N = (a + N - z) % N + 1 ∧ (a + N - z) % N < (a₀ + N - z) % N)) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- rel a < rel a₀ : step forward
    by_cases hc : a + 1 < N
    · refine ⟨a + 1, hc, Or.inl (Nat.mod_eq_of_lt hc).symm, Or.inr ⟨?_, hlt⟩⟩
      rw [rel_eq hz hc, rel_eq hz ha]
      rw [rel_eq hz ha, rel_eq hz ha₀] at hlt
      split_ifs at hlt ⊢ <;> omega
    · have haN : a + 1 = N := by omega
      refine ⟨0, by omega, Or.inl (by rw [haN]; simp), Or.inr ⟨?_, hlt⟩⟩
      rw [rel_eq hz (by omega : 0 < N), rel_eq hz ha]
      rw [rel_eq hz ha, rel_eq hz ha₀] at hlt
      split_ifs at hlt ⊢ <;> omega
  · -- rel a > rel a₀ : step backward
    by_cases hc : 1 ≤ a
    · refine ⟨a - 1, by omega, Or.inr (by rw [Nat.sub_add_cancel hc]; exact (Nat.mod_eq_of_lt ha).symm), Or.inl ⟨?_, hgt⟩⟩
      rw [rel_eq hz (by omega : a - 1 < N), rel_eq hz ha]
      rw [rel_eq hz ha, rel_eq hz ha₀] at hgt
      split_ifs at hgt ⊢ <;> omega
    · have ha0 : a = 0 := by omega
      refine ⟨N - 1, by omega, Or.inr (by rw [ha0, Nat.sub_add_cancel (by omega)]; simp), Or.inl ⟨?_, hgt⟩⟩
      rw [rel_eq hz (by omega : N - 1 < N), rel_eq hz ha]
      rw [rel_eq hz ha, rel_eq hz ha₀] at hgt
      split_ifs at hgt ⊢ <;> omega

theorem pcd_step {N a b : ℕ} (hN : 0 < N) (ha : a < N) (hb : b < N) (h : b = (a + 1) % N ∨ a = (b + 1) % N) :
    pcd N a b ≤ 1 := by
  unfold pcd
  rcases h with h | h
  · by_cases hc : a + 1 < N
    · rw [Nat.mod_eq_of_lt hc] at h; subst h; split_ifs <;> omega
    · have haN : a + 1 = N := by omega
      rw [haN, Nat.mod_self] at h; subst h; split_ifs <;> omega
  · by_cases hc : b + 1 < N
    · rw [Nat.mod_eq_of_lt hc] at h; subst h; split_ifs <;> omega
    · have hbN : b + 1 = N := by omega
      rw [hbN, Nat.mod_self] at h; subst h; split_ifs <;> omega

theorem pcd_self (N a : ℕ) : pcd N a a = 0 := by
  unfold pcd; simp

/-- relative coordinate of `y` in a box with corner `z`. -/
def relc (z y : PeriodicLatticeSite L) (μ : Fin 3) : ℕ := ((y μ).val + (L μ + 1) - (z μ).val) % (L μ + 1)

/-- the box distance from `y` to `x₀`. -/
def bd (z x₀ y : PeriodicLatticeSite L) : ℕ :=
  ∑ μ : Fin 3, ((relc z y μ - relc z x₀ μ) + (relc z x₀ μ - relc z y μ))

theorem mem_siteBox_iff {z x : PeriodicLatticeSite L} {s : ℕ} : x ∈ siteBox z s ↔ ∀ μ : Fin 3, relc z x μ < s := Iff.rfl

theorem relc_inj {z x y : PeriodicLatticeSite L} (h : ∀ μ, relc z x μ = relc z y μ) : x = y := by
  funext μ
  apply Fin.ext
  have h1 := h μ
  unfold relc at h1
  rw [rel_eq (z μ).isLt (x μ).isLt, rel_eq (z μ).isLt (y μ).isLt] at h1
  have := (z μ).isLt
  have := (x μ).isLt
  have := (y μ).isLt
  split_ifs at h1 <;> omega

/-- a unit step inside the box toward `x₀`. -/
theorem exists_step {z x₀ y : PeriodicLatticeSite L} {s : ℕ} (hx₀ : x₀ ∈ siteBox z s) (hy : y ∈ siteBox z s)
    (hne : y ≠ x₀) :
    ∃ y' : PeriodicLatticeSite L, y' ∈ siteBox z s ∧ pdist y y' ≤ 1 ∧ bd z x₀ y' < bd z x₀ y := by
  have hex : ∃ μ, relc z y μ ≠ relc z x₀ μ := by
    by_contra hcon
    push Not at hcon
    exact hne (relc_inj hcon)
  obtain ⟨μ, hμ⟩ := hex
  obtain ⟨b, hbN, hb1, hb2⟩ := coord_step (z μ).isLt (y μ).isLt (x₀ μ).isLt hμ
  let y' : PeriodicLatticeSite L := Function.update y μ ⟨b, hbN⟩
  have hy'μ : relc z y' μ = (b + (L μ + 1) - (z μ).val) % (L μ + 1) := by
    simp [y', relc]
  have hy'ν : ∀ ν, ν ≠ μ → relc z y' ν = relc z y ν := by
    intro ν hν; simp [y', relc, Function.update_of_ne hν]
  have hx₀μ := hx₀ μ
  have hyμ := hy μ
  refine ⟨y', ?_, ?_, ?_⟩
  · intro ν
    by_cases hν : ν = μ
    · subst hν
      have := (mem_siteBox_iff.1 hy) ν
      have := (mem_siteBox_iff.1 hx₀) ν
      show relc z y' ν < s
      rw [hy'μ]; unfold relc at *; omega
    · show relc z y' ν < s
      rw [hy'ν ν hν]; exact (mem_siteBox_iff.1 hy) ν
  · unfold pdist
    calc ∑ ν : Fin 3, pcd (L ν + 1) (y ν).val (y' ν).val ≤ ∑ ν : Fin 3, (if ν = μ then 1 else 0) := by
          apply Finset.sum_le_sum
          intro ν _
          by_cases hν : ν = μ
          · subst hν
            simp only [if_true]
            have hv : ((y' ν) : Fin (L ν + 1)).val = b := by simp [y']
            rw [hv]
            exact pcd_step (by omega) (y ν).isLt hbN hb1
          · simp [hν, y', pcd_self]
      _ = 1 := by simp
  · unfold bd
    apply Finset.sum_lt_sum
    · intro ν _
      by_cases hν : ν = μ
      · subst hν; rw [hy'μ]; unfold relc at *; omega
      · rw [hy'ν ν hν]
    · refine ⟨μ, Finset.mem_univ _, ?_⟩
      rw [hy'μ]; unfold relc at *; omega

/-- **path lemma**: a box meeting `Omega_1` and its complement meets `Omega_0 \ Omega_1`. -/
theorem path_exists {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hMR : 1 ≤ R * M)
    {z : PeriodicLatticeSite L} {s : ℕ} {x₀ : PeriodicLatticeSite L} (hx₀ : x₀ ∈ siteBox z s) (hx₀1 : x₀ ∈ S.Om 1) :
    ∀ n : ℕ, ∀ y : PeriodicLatticeSite L, y ∈ siteBox z s → bd z x₀ y = n → y ∉ S.Om 1 →
      ∃ u ∈ siteBox z s, u ∈ S.Om 0 ∧ u ∉ S.Om 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy hn hy1
    have hne : y ≠ x₀ := fun h => hy1 (h ▸ hx₀1)
    obtain ⟨y', hy'b, hpd, hlt⟩ := exists_step hx₀ hy hne
    by_cases h1 : y' ∈ S.Om 1
    · refine ⟨y, hy, ?_, hy1⟩
      rw [hA.2.2.2.2.2 y]
      exact ⟨y', h1, y, fun μ => rfl, le_trans hpd hMR⟩
    · exact ih (bd z x₀ y') (by omega) y' hy'b rfl h1

end AdalyFormal.L0C
