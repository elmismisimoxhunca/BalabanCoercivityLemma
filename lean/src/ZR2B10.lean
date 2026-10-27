import ZR2B9

/-!
# R2B10 -- `TT` covers Ω₀ (multi-stratum), with correct index uniqueness.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

theorem mem_box_iff {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120) (z y : PeriodicLatticeSite L)
    (s : ℕ) : y ∈ siteBox z s ↔
      ((y 0).val + 120 - (z 0).val) % 120 < s ∧ ((y 1).val + 120 - (z 1).val) % 120 < s ∧
        ((y 2).val + 120 - (z 2).val) % 120 < s := by
  simp only [siteBox, Set.mem_setOf_eq, hN]
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ μ
    fin_cases μ <;> assumption

/-- a box of side 20 is never contained in a box of side 10 (120-torus) -/
theorem box20_not_sub_box10 {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120)
    (z z' : PeriodicLatticeSite L) : ¬ (siteBox z 20 ⊆ siteBox z' 10) := by
  intro h
  have hz0 : (z 0).val < 120 := by have := (z 0).isLt; have := hN 0; omega
  -- two points of the 20-box: z and z shifted by 19 in coordinate 0
  have hv : ((z 0).val + 19) % 120 < L 0 + 1 := by have := hN 0; omega
  let w : PeriodicLatticeSite L := Function.update z 0 ⟨((z 0).val + 19) % 120, hv⟩
  have hw : w ∈ siteBox z 20 := by
    rw [mem_box_iff hN]
    refine ⟨?_, ?_, ?_⟩
    · simp only [w, Function.update_self]; omega
    · simp only [w, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]; omega
    · simp only [w, Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]; omega
  have hzz : z ∈ siteBox z 20 := by
    rw [mem_box_iff hN]; refine ⟨?_, ?_, ?_⟩ <;> omega
  have h1 := (mem_box_iff hN _ _ _).mp (h hzz)
  have h2 := (mem_box_iff hN _ _ _).mp (h hw)
  simp only [w, Function.update_self] at h2
  have hz'0 : (z' 0).val < 120 := by have := (z' 0).isLt; have := hN 0; omega
  omega

theorem TT_covers {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120) (F : ℕ) (hF : 10 ≤ F) :
    CoversOm0 2 1 F 1 (TT L) := by
  intro x hx
  simp only [TT, if_true, OmA, Set.mem_setOf_eq] at hx
  have hx120 : ∀ μ, (x μ).val < 120 := fun μ => by have := (x μ).isLt; have := hN μ; omega
  by_cases hB : 20 ≤ (x 0).val ∧ (x 0).val < 100
  · -- index-1 cube: side 20, even corners
    let c : Fin 3 → ℕ := fun μ => if μ = 0 then min (2 * ((x 0).val / 2)) 80 else 2 * ((x μ).val / 2)
    have hc : ∀ μ, c μ < L μ + 1 := fun μ => by
      have := hN μ; have := hx120 μ; simp only [c]; split_ifs <;> omega
    let z : PeriodicLatticeSite L := fun μ => ⟨c μ, hc μ⟩
    have hz0 : (z 0).val = min (2 * ((x 0).val / 2)) 80 := by simp [z, c]
    have hz1 : (z 1).val = 2 * ((x 1).val / 2) := by simp [z, c]
    have hz2 : (z 2).val = 2 * ((x 2).val / 2) := by simp [z, c]
    have hbox : ∀ y : PeriodicLatticeSite L, y ∈ siteBox z (10 * bigSide 1 2 1) ↔
        ((y 0).val + 120 - (z 0).val) % 120 < 20 ∧ ((y 1).val + 120 - (z 1).val) % 120 < 20 ∧
        ((y 2).val + 120 - (z 2).val) % 120 < 20 := by
      intro y
      have := mem_box_iff hN z y (10 * bigSide 1 2 1)
      simpa [bigSide] using this
    have hxmem : x ∈ siteBox z (10 * bigSide 1 2 1) := by
      rw [hbox]; have := hx120 1; have := hx120 2; rw [hz0, hz1, hz2]; refine ⟨?_, ?_, ?_⟩ <;> omega
    have hsub : ∀ y ∈ siteBox z (10 * bigSide 1 2 1), 20 ≤ (y 0).val ∧ (y 0).val < 100 := by
      intro y hy
      rw [hbox] at hy
      have h0 := hy.1; have := hx120 0; have := (y 0).isLt; have := hN 0; rw [hz0] at h0; omega
    refine ⟨siteBox z (10 * bigSide 1 2 1), 1, 10, le_rfl, hF, ⟨⟨le_rfl, ⟨z, ?_, rfl⟩, ?_, ?_⟩, ?_⟩, hxmem⟩
    · intro μ; fin_cases μ <;> simp [bigSide, hz0, hz1, hz2] <;> omega
    · intro y hy
      left
      simp only [towerBj, TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true,
        if_neg (by decide : (1 + 1 : ℕ) ≠ 0), if_neg (by decide : (1 + 1 : ℕ) ≠ 1), OmB,
        Set.mem_diff, Set.mem_setOf_eq, Set.mem_empty_iff_false, not_false_eq_true, and_true]
      exact hsub y hy
    · refine ⟨x, hxmem, ?_⟩
      simp only [towerBj, TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true,
        if_neg (by decide : (1 + 1 : ℕ) ≠ 0), if_neg (by decide : (1 + 1 : ℕ) ≠ 1), OmB,
        Set.mem_diff, Set.mem_setOf_eq, Set.mem_empty_iff_false, not_false_eq_true, and_true]
      exact hB
    · intro i hi
      by_contra hne
      have hi0 : i = 0 := by have := hi.1; omega
      subst hi0
      obtain ⟨_, ⟨z', _, hz'⟩, _⟩ := hi
      have : siteBox z (10 * bigSide 1 2 1) = siteBox z' (10 * bigSide 1 2 0) := hz'.symm ▸ rfl
      have h20 : siteBox z 20 ⊆ siteBox z' 10 := by
        have h := this.subset
        simpa [bigSide] using h
      exact box20_not_sub_box10 hN z z' h20
  · -- index-0 cube: side 10
    let c : Fin 3 → ℕ := fun μ => if μ = 0 then min (x 0).val 102 else (x μ).val
    have hc : ∀ μ, c μ < L μ + 1 := fun μ => by
      have := hN μ; have := hx120 μ; simp only [c]; split_ifs <;> omega
    let z : PeriodicLatticeSite L := fun μ => ⟨c μ, hc μ⟩
    have hz0 : (z 0).val = min (x 0).val 102 := by simp [z, c]
    have hz1 : (z 1).val = (x 1).val := by simp [z, c]
    have hz2 : (z 2).val = (x 2).val := by simp [z, c]
    have hbox : ∀ y : PeriodicLatticeSite L, y ∈ siteBox z (10 * bigSide 1 2 0) ↔
        ((y 0).val + 120 - (z 0).val) % 120 < 10 ∧ ((y 1).val + 120 - (z 1).val) % 120 < 10 ∧
        ((y 2).val + 120 - (z 2).val) % 120 < 10 := by
      intro y
      have := mem_box_iff hN z y (10 * bigSide 1 2 0)
      simpa [bigSide] using this
    have hxmem : x ∈ siteBox z (10 * bigSide 1 2 0) := by
      rw [hbox]; have := hx120 1; have := hx120 2; rw [hz0, hz1, hz2]; refine ⟨?_, ?_, ?_⟩ <;> omega
    have hsub : ∀ y ∈ siteBox z (10 * bigSide 1 2 0), 8 ≤ (y 0).val ∧ (y 0).val < 112 := by
      intro y hy
      rw [hbox] at hy
      have h0 := hy.1; have := hx120 0; have := (y 0).isLt; have := hN 0; rw [hz0] at h0; omega
    refine ⟨siteBox z (10 * bigSide 1 2 0), 0, 10, by omega, hF, ⟨⟨by omega, ⟨z, ?_, rfl⟩, ?_, ?_⟩, ?_⟩, hxmem⟩
    · intro μ; simp [bigSide, Nat.mod_one]
    · intro y hy
      have h8 := hsub y hy
      by_cases hy20 : 20 ≤ (y 0).val ∧ (y 0).val < 100
      · right
        simp only [towerBj, TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true,
          if_neg (by decide : (0 + 1 : ℕ) ≠ 0), OmB, Set.mem_diff, Set.mem_setOf_eq, if_pos rfl]
        simp only [towerBj, TT, if_pos rfl, if_neg (by decide : (1 + 1 : ℕ) ≠ 0),
          if_neg (by decide : (1 + 1 : ℕ) ≠ 1)]
        exact ⟨hy20, by simp⟩
      · left
        simp only [towerBj, TT, if_true, if_neg (by decide : (0 + 1 : ℕ) ≠ 0), OmA, OmB,
          Set.mem_diff, Set.mem_setOf_eq]
        exact ⟨h8, by omega⟩
    · refine ⟨x, hxmem, ?_⟩
      simp only [towerBj, TT, if_true, if_neg (by decide : (0 + 1 : ℕ) ≠ 0), if_pos rfl, OmA, OmB,
        Set.mem_diff, Set.mem_setOf_eq]
      exact ⟨hx, by omega⟩
    · intro i hi
      by_contra hne
      have hi1 : i = 1 := by have := hi.1; omega
      subst hi1
      obtain ⟨_, ⟨z', _, hz'⟩, _⟩ := hi
      have : siteBox z' (10 * bigSide 1 2 1) = siteBox z (10 * bigSide 1 2 0) := hz'.symm ▸ rfl
      have h20 : siteBox z' 20 ⊆ siteBox z 10 := by
        have h := this.subset
        simpa [bigSide] using h
      exact box20_not_sub_box10 hN z' z h20

#print axioms TT_covers

end AdalyFormal.StatementLane2
