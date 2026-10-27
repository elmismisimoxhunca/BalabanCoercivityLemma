import NV3

/-!
# NV4 -- class-cube coverage of `Ω₀` for the slab tower: `CoversOm0p ell M 12 2 (slab3 ..)` (lane nonvac_20261015)

Five cases by the position of `v = x₀` (index 2 in the core of `Ω₂`; index 1 on `[P₁,P₂)` and on `[Q₂-1,Q₁-1)`; index 0 on the left shell
`[P₀,P₁)` and on `[Q₁-1,Q₀)`), each by `box_exists` with the window clamped inside the stratum-`j` region; uniqueness of the index is `isClassCube_of`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NonVac

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

section strata
variable {L : PeriodicLatticeExtent} {P0 Q0 P1 Q1 P2 Q2 : ℕ}

theorem bj0 (y : PeriodicLatticeSite L) :
    y ∈ towerBj (slab3 L P0 Q0 P1 Q1 P2 Q2) 0 ↔
      (P0 ≤ (y 0).val ∧ (y 0).val < Q0) ∧ ¬ (P1 ≤ (y 0).val ∧ (y 0).val < Q1) := by
  show y ∈ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om 0 \ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om 1 ↔ _
  simp only [Set.mem_sdiff, om0_mem, om1_mem]
theorem bj1 (y : PeriodicLatticeSite L) :
    y ∈ towerBj (slab3 L P0 Q0 P1 Q1 P2 Q2) 1 ↔
      (P1 ≤ (y 0).val ∧ (y 0).val < Q1) ∧ ¬ (P2 ≤ (y 0).val ∧ (y 0).val < Q2) := by
  show y ∈ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om 1 \ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om 2 ↔ _
  simp only [Set.mem_sdiff, om1_mem, om2_mem]
theorem bj2 (y : PeriodicLatticeSite L) :
    y ∈ towerBj (slab3 L P0 Q0 P1 Q1 P2 Q2) 2 ↔ (P2 ≤ (y 0).val ∧ (y 0).val < Q2) := by
  show y ∈ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om 2 \ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om 3 ↔ _
  rw [Set.mem_sdiff, om2_mem]
  exact ⟨fun h => h.1, fun h => ⟨h, om3_mem 3 le_rfl y⟩⟩
theorem bj3 (y : PeriodicLatticeSite L) : y ∉ towerBj (slab3 L P0 Q0 P1 Q1 P2 Q2) 3 := by
  intro h
  exact om3_mem 3 le_rfl y h.1
end strata

theorem adj0 {L : PeriodicLatticeExtent} {N : ℕ} {x y : PeriodicLatticeSite L} (h : Adj N x y)
    (hx1 : (x 0).val + 1 < N) : (y 0).val = (x 0).val ∨ (y 0).val = (x 0).val + 1 := by
  rcases h 0 with h | h
  · exact Or.inl h
  · right; rw [h, Nat.mod_eq_of_lt hx1]

/-- one cube from one region. -/
theorem cube_of_region {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) {ell M : ℕ} {S : Tower L}
    (hnest : ∀ j, S.Om (j + 1) ⊆ S.Om j) {j : ℕ} (hj : j ≤ 2) {lo hi : ℕ}
    (hs : 0 < bigSide M ell j) (hlo : bigSide M ell j ∣ lo) (hhi : bigSide M ell j ∣ hi)
    (hwid : lo + 12 * bigSide M ell j ≤ hi) (hhiN : hi ≤ N)
    (x : PeriodicLatticeSite L) (w : ℕ) (hvlo : lo ≤ (x 0).val) (hvw : (x 0).val ≤ w) (hw1 : w ≤ (x 0).val + 1)
    (hwhi : w < hi) (hx1 : (x 0).val + 1 < N)
    (hreg : ∀ y : PeriodicLatticeSite L, lo ≤ (y 0).val → (y 0).val < hi →
      y ∈ towerBj S j ∪ towerBj S (j + 1))
    (hwit : ∃ t : ℕ, (t = (x 0).val ∨ t = (x 0).val + 1) ∧ t ≤ w ∧
      ∀ y : PeriodicLatticeSite L, (y 0).val = t → y ∈ towerBj S j) :
    ∃ sites : Set (PeriodicLatticeSite L), IsClassCube ell M 12 2 S sites j ∧
      ∀ y : PeriodicLatticeSite L, Adj N x y → (y 0).val ≤ w → y ∈ sites := by
  obtain ⟨z, hz, hbox, hadj⟩ := box_exists hN hs hlo hhi hwid hhiN x w hvlo hvw hw1 hwhi hx1
  refine ⟨siteBox z (12 * bigSide M ell j), isClassCube_of hnest ⟨hj, ⟨z, hz, rfl⟩, ?_, ?_⟩, hadj⟩
  · intro y hy
    have := hbox y hy
    exact hreg y this.1 this.2
  · obtain ⟨t, ht, htw, hB⟩ := hwit
    have htN : t < L 0 + 1 := by rw [hN 0]; omega
    let y : PeriodicLatticeSite L := Function.update x 0 ⟨t, htN⟩
    have hy0 : (y 0).val = t := by simp [y]
    have hyadj : Adj N x y := by
      intro ρ
      by_cases h : ρ = 0
      · subst h
        rcases ht with h | h
        · left; rw [hy0, h]
        · right; rw [hy0, h, Nat.mod_eq_of_lt hx1]
      · left; simp [y, Function.update_of_ne h]
    exact ⟨y, hadj y hyadj (by rw [hy0]; exact htw), hB y hy0⟩

section cov
variable {M ell R N P0 Q0 P1 Q1 P2 Q2 : ℕ}

theorem cube_nbhd (G : SlabGeo M ell R N P0 Q0 P1 Q1 P2 Q2)
    (w0L : P0 + 12 * M ≤ P2) (w0R : Q2 + 12 * M ≤ Q0) (w1 : P1 + 12 * (M * ell) ≤ Q1)
    (w2 : P2 + 12 * (M * ell ^ 2) ≤ Q2) (hQN : Q0 < N) (hP12 : P1 < P2) (hQ21 : Q2 < Q1) (hQ10 : Q1 < Q0)
    {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = N) (x : PeriodicLatticeSite L)
    (hx : P0 ≤ (x 0).val ∧ (x 0).val < Q0) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M 12 2 (slab3 L P0 Q0 P1 Q1 P2 Q2) sites j ∧
      ∀ y : PeriodicLatticeSite L, Adj N x y → P0 ≤ (y 0).val → (y 0).val < Q0 → y ∈ sites := by
  have hnest : ∀ j, (slab3 L P0 Q0 P1 Q1 P2 Q2).Om (j + 1) ⊆ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om j :=
    (slab3_admissible G hN).1
  have hM := G.hM
  have hell := G.hell
  have hs0 : bigSide M ell 0 = M := by simp [bigSide]
  have hs1 : bigSide M ell 1 = M * ell := by simp [bigSide]
  have hs2 : bigSide M ell 2 = M * ell ^ 2 := by simp [bigSide]
  have hp1 : 0 < M * ell := Nat.mul_pos hM hell
  have hp2 : 0 < M * ell ^ 2 := Nat.mul_pos hM (pow_pos hell 2)
  have hM2 : M ∣ P2 := Dvd.dvd.trans (Dvd.intro _ rfl) G.b2P
  have hM2' : M ∣ Q2 := Dvd.dvd.trans (Dvd.intro _ rfl) G.b2Q
  have hv := hx
  have hx1 : (x 0).val + 1 < N := by omega
  have hQ2N : Q2 ≤ N := by have := G.nest21; have := G.nest10; have := G.QN; omega
  have hQ1N : Q1 ≤ N := by have := G.nest10; have := G.QN; omega
  have hP2N : P2 ≤ N := by have := G.nestw; omega
  by_cases hA : (x 0).val < P1
  · -- index 0, left shell, region [P0, P2)
    obtain ⟨sites, hc, hall⟩ := cube_of_region (ell := ell) (M := M) (j := 0) hN hnest (by norm_num) (lo := P0) (hi := P2)
      (by rw [hs0]; exact hM) (by rw [hs0]; exact G.b0P) (by rw [hs0]; exact hM2) (by rw [hs0]; exact w0L) hP2N
      x ((x 0).val + 1) hx.1 (by omega) le_rfl (by omega) hx1
      (by
        intro y h1 h2
        by_cases h3 : (y 0).val < P1
        · left; rw [bj0]; omega
        · right; rw [bj1]; omega)
      ⟨(x 0).val, Or.inl rfl, by omega, by intro y hy; rw [bj0]; omega⟩
    refine ⟨sites, 0, hc, fun y hy h1 h2 => hall y hy ?_⟩
    rcases adj0 hy hx1 with h | h <;> omega
  · by_cases hB : (x 0).val < P2
    · -- index 1, region [P1, Q1)
      obtain ⟨sites, hc, hall⟩ := cube_of_region (ell := ell) (M := M) (j := 1) hN hnest (by norm_num) (lo := P1) (hi := Q1)
        (by rw [hs1]; exact hp1) (by rw [hs1]; exact G.b1P) (by rw [hs1]; exact G.b1Q) (by rw [hs1]; exact w1) hQ1N
        x ((x 0).val + 1) (by omega) (by omega) le_rfl (by omega) hx1
        (by
          intro y h1 h2
          by_cases h3 : P2 ≤ (y 0).val ∧ (y 0).val < Q2
          · right; rw [bj2]; exact h3
          · left; rw [bj1]; omega)
        ⟨(x 0).val, Or.inl rfl, by omega, by intro y hy; rw [bj1]; omega⟩
      refine ⟨sites, 1, hc, fun y hy h1 h2 => hall y hy ?_⟩
      rcases adj0 hy hx1 with h | h <;> omega
    · by_cases hC : (x 0).val + 1 < Q2
      · -- index 2, region [P2, Q2)
        obtain ⟨sites, hc, hall⟩ := cube_of_region (ell := ell) (M := M) (j := 2) hN hnest (by norm_num) (lo := P2) (hi := Q2)
          (by rw [hs2]; exact hp2) (by rw [hs2]; exact G.b2P) (by rw [hs2]; exact G.b2Q) (by rw [hs2]; exact w2) hQ2N
          x ((x 0).val + 1) (by omega) (by omega) le_rfl (by omega) hx1
          (by
            intro y h1 h2
            left; rw [bj2]; omega)
          ⟨(x 0).val, Or.inl rfl, by omega, by intro y hy; rw [bj2]; omega⟩
        refine ⟨sites, 2, hc, fun y hy h1 h2 => hall y hy ?_⟩
        rcases adj0 hy hx1 with h | h <;> omega
      · by_cases hD : (x 0).val + 1 < Q1
        · -- index 1 again, window straddling the top of Ω₂
          obtain ⟨sites, hc, hall⟩ := cube_of_region (ell := ell) (M := M) (j := 1) hN hnest (by norm_num) (lo := P1) (hi := Q1)
            (by rw [hs1]; exact hp1) (by rw [hs1]; exact G.b1P) (by rw [hs1]; exact G.b1Q) (by rw [hs1]; exact w1) hQ1N
            x ((x 0).val + 1) (by omega) (by omega) le_rfl (by omega) hx1
            (by
              intro y h1 h2
              by_cases h3 : P2 ≤ (y 0).val ∧ (y 0).val < Q2
              · right; rw [bj2]; exact h3
              · left; rw [bj1]; omega)
            ⟨(x 0).val + 1, Or.inr rfl, le_rfl, by intro y hy; rw [bj1]; omega⟩
          refine ⟨sites, 1, hc, fun y hy h1 h2 => hall y hy ?_⟩
          rcases adj0 hy hx1 with h | h <;> omega
        · -- index 0, right shell, region [Q2, Q0)
          obtain ⟨sites, hc, hall⟩ := cube_of_region (ell := ell) (M := M) (j := 0) hN hnest (by norm_num) (lo := Q2) (hi := Q0)
            (by rw [hs0]; exact hM) (by rw [hs0]; exact hM2') (by rw [hs0]; exact G.b0Q) (by rw [hs0]; exact w0R) G.QN
            x (min ((x 0).val + 1) (Q0 - 1)) (by omega) (by omega) (by omega) (by omega) hx1
            (by
              intro y h1 h2
              by_cases h3 : Q1 ≤ (y 0).val
              · left; rw [bj0]; omega
              · right; rw [bj1]; omega)
            ⟨if Q1 ≤ (x 0).val then (x 0).val else (x 0).val + 1, by split_ifs <;> simp, by split_ifs <;> omega,
              by intro y hy; rw [bj0]; split_ifs at hy <;> omega⟩
          refine ⟨sites, 0, hc, fun y hy h1 h2 => hall y hy ?_⟩
          rcases adj0 hy hx1 with h | h <;> omega

end cov

end AdalyFormal.NonVac
