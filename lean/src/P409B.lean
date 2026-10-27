import P409A

/-!
# P409B -- coverage `CoversOm0p ell M 12 1 (TG ..)` for the one-slab tower (abstract numerics).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge

theorem cube1_desc {L : PeriodicLatticeExtent} {N ell M A0 A B B0 : ℕ} (hN : ∀ μ, L μ + 1 = N)
    (hg0 : 0 < M * ell) (z : PeriodicLatticeSite L) (hgc : GridCorner (bigSide M ell 1) z)
    (hz : A ≤ (z 0).val ∧ (z 0).val + 12 * (M * ell) ≤ B) (hBN : B ≤ N) :
    DescribedAt ell M 12 1 (TG A0 A B B0 L) (siteBox z (12 * bigSide M ell 1)) 1 := by
  rw [bigSide1]
  rw [bigSide1] at hgc
  have hz0 := site_lt hN z 0
  have hzz : z ∈ siteBox z (12 * (M * ell)) := by
    rw [memBox hN]
    refine ⟨?_, ?_, ?_⟩ <;> (rw [off_lt_iff _ _ _ _ (site_lt hN _ _) (site_lt hN _ _)]; omega)
  refine ⟨le_rfl, ⟨z, by rw [bigSide1]; exact hgc, by rw [bigSide1]⟩, ?_, ⟨z, hzz, ?_⟩⟩
  · intro y hy
    left
    rw [TG_bj1]
    have h1 := ((memBox hN _ _ _).mp hy).1
    rw [off_lt_iff _ _ _ _ (site_lt hN y 0) hz0] at h1
    omega
  · rw [TG_bj1]; exact ⟨hz.1, by omega⟩

theorem cube0_desc {L : PeriodicLatticeExtent} {N ell M A0 A B B0 : ℕ} (hN : ∀ μ, L μ + 1 = N)
    (hM : 0 < M) (z : PeriodicLatticeSite L) (hgc : GridCorner (bigSide M ell 0) z)
    (hz : A0 ≤ (z 0).val ∧ (z 0).val + 12 * M ≤ B0) (hB0N : B0 ≤ N)
    (hAB : A ≤ B) (q : PeriodicLatticeSite L) (hq : q ∈ siteBox z (12 * bigSide M ell 0))
    (hq0 : (A0 ≤ (q 0).val ∧ (q 0).val < A) ∨ (B ≤ (q 0).val ∧ (q 0).val < B0)) :
    DescribedAt ell M 12 1 (TG A0 A B B0 L) (siteBox z (12 * bigSide M ell 0)) 0 := by
  have hz0 := site_lt hN z 0
  refine ⟨Nat.zero_le _, ⟨z, hgc, rfl⟩, ?_, ⟨q, hq, ?_⟩⟩
  · intro y hy
    rw [bigSide0] at hy
    have h1 := ((memBox hN _ _ _).mp hy).1
    rw [off_lt_iff _ _ _ _ (site_lt hN y 0) hz0] at h1
    by_cases hy1 : A ≤ (y 0).val ∧ (y 0).val < B
    · right
      exact (TG_bj1 y).mpr hy1
    · left
      rw [TG_bj0]
      refine ⟨⟨?_, ?_⟩, hy1⟩ <;> omega
  · rw [TG_bj0]
    rw [bigSide0] at hq
    have h1 := ((memBox hN _ _ _).mp hq).1
    rw [off_lt_iff _ _ _ _ (site_lt hN q 0) hz0] at h1
    refine ⟨?_, ?_⟩ <;> omega

theorem align_ge {g a x : ℕ} (hg : 0 < g) (ha : g ∣ a) (h : a ≤ x) : a ≤ g * (x / g) := by
  obtain ⟨q, rfl⟩ := ha
  have : q ≤ x / g := (Nat.le_div_iff_mul_le hg).mpr (by rw [mul_comm]; exact h)
  exact Nat.mul_le_mul_left g this

theorem div_facts (g x : ℕ) (hg : 0 < g) : g * (x / g) ≤ x ∧ x < g * (x / g) + g := by
  have h1 := Nat.div_add_mod x g
  have h2 := Nat.mod_lt x hg
  omega

theorem exists_corner1 {g A B x0 : ℕ} (hg : 0 < g) (hgA : g ∣ A) (hgB : g ∣ B) (hW : A + 12 * g ≤ B)
    (h : A ≤ x0 ∧ x0 + 1 < B) :
    ∃ c0, g ∣ c0 ∧ A ≤ c0 ∧ c0 + 12 * g ≤ B ∧ c0 ≤ x0 ∧ x0 + 1 < c0 + 12 * g := by
  have hd := div_facts g x0 hg
  have hAt := align_ge hg hgA h.1
  by_cases ht : g * (x0 / g) ≤ B - 12 * g
  · exact ⟨g * (x0 / g), dvd_mul_right _ _, hAt, by omega, hd.1, by omega⟩
  · refine ⟨B - 12 * g, Nat.dvd_sub hgB (Dvd.intro_left 12 rfl), by omega, by omega, by omega, by omega⟩

theorem exists_corner0 {M A0 A B B0 x0 : ℕ} (hM : 0 < M) (hMA0 : M ∣ A0) (hMB0 : M ∣ B0)
    (hsh1 : A0 + 12 * M ≤ A) (hsh2 : B + 12 * M ≤ B0) (hAB : A ≤ B)
    (h : A0 ≤ x0 ∧ x0 < B0) (hII : x0 < A ∨ B ≤ x0 + 1) :
    ∃ c0, M ∣ c0 ∧ A0 ≤ c0 ∧ c0 + 12 * M ≤ B0 ∧ c0 ≤ x0 ∧ x0 < c0 + 12 * M ∧
      (∀ w0, x0 ≤ w0 → w0 ≤ x0 + 1 → w0 < B0 → w0 < c0 + 12 * M) ∧
      ∃ q0, c0 ≤ q0 ∧ q0 < c0 + 12 * M ∧ ((A0 ≤ q0 ∧ q0 < A) ∨ (B ≤ q0 ∧ q0 < B0)) := by
  have hd := div_facts M x0 hM
  have hAt := align_ge hM hMA0 h.1
  have key : ∃ c0, M ∣ c0 ∧ A0 ≤ c0 ∧ c0 + 12 * M ≤ B0 ∧ c0 ≤ x0 ∧ x0 < c0 + 12 * M ∧
      (∀ w0, x0 ≤ w0 → w0 ≤ x0 + 1 → w0 < B0 → w0 < c0 + 12 * M) := by
    by_cases ht : M * (x0 / M) ≤ B0 - 12 * M
    · exact ⟨M * (x0 / M), dvd_mul_right _ _, hAt, by omega, hd.1, by omega, fun w0 h1 h2 h3 => by omega⟩
    · exact ⟨B0 - 12 * M, Nat.dvd_sub hMB0 (Dvd.intro_left 12 rfl), by omega, by omega, by omega, by omega,
        fun w0 h1 h2 h3 => by omega⟩
  obtain ⟨c0, h1, h2, h3, h4, h5, h6⟩ := key
  refine ⟨c0, h1, h2, h3, h4, h5, h6, ?_⟩
  by_cases hx : x0 < A
  · exact ⟨x0, h4, h5, Or.inl ⟨h.1, hx⟩⟩
  · by_cases hxB : x0 < B
    · have := h6 (x0 + 1) (by omega) (le_refl _) (by omega)
      exact ⟨B, by omega, by omega, Or.inr ⟨le_refl _, by omega⟩⟩
    · exact ⟨x0, h4, h5, Or.inr ⟨by omega, h.2⟩⟩

theorem adj_coord (N x w : ℕ) (hx : x < N) (h : w = x ∨ w = (x + 1) % N) :
    w = x ∨ (w = x + 1 ∧ x + 1 < N) ∨ (w = 0 ∧ x + 1 = N) := by
  rcases h with h | h
  · exact Or.inl h
  · right
    by_cases h1 : x + 1 < N
    · left; rw [h, Nat.mod_eq_of_lt h1]; exact ⟨rfl, h1⟩
    · right
      have : x + 1 = N := by omega
      exact ⟨by rw [h, this, Nat.mod_self], this⟩

theorem cell_off (N G s x w : ℕ) (hG : 0 < G) (h2G : 2 * G ≤ N) (hGs : G < s) (hx : x < N)
    (hadj : w = x ∨ w = (x + 1) % N) : (w + N - G * (x / G)) % N < s := by
  have hd := div_facts G x hG
  have hw := adj_coord N x w hx hadj
  have hwN : w < N := by omega
  have ht : G * (x / G) < N := by omega
  rw [off_lt_iff _ _ _ _ hwN ht]
  omega

/-- adjacency on the torus with `N` sites per direction: each coordinate equal or one step up. -/
def AdjN {L : PeriodicLatticeExtent} (N : ℕ) (x w : PeriodicLatticeSite L) : Prop :=
  ∀ ρ : Fin 3, (w ρ).val = (x ρ).val ∨ (w ρ).val = ((x ρ).val + 1) % N

theorem adjN_refl {L : PeriodicLatticeExtent} (N : ℕ) (x : PeriodicLatticeSite L) : AdjN N x x := fun _ => Or.inl rfl

theorem shift_valN {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (hN1 : 1 < N)
    (s : PeriodicLatticeSite L) (μ ρ : Fin 3) :
    ((periodicLatticeShift s μ) ρ).val = if ρ = μ then ((s ρ).val + 1) % N else (s ρ).val := by
  unfold periodicLatticeShift
  by_cases h : ρ = μ
  · subst h
    simp only [Function.update_self, if_true]
    rw [Fin.val_add, Fin.val_one']
    have h1 := hN ρ
    have h2 : 1 % (L ρ + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h2]
    generalize ((s ρ).val) = v
    rw [h1]
  · simp [h]

theorem adjN_shift {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (hN1 : 1 < N)
    {x s : PeriodicLatticeSite L} (h : AdjN N x s) (μ : Fin 3) (hμ : (s μ).val = (x μ).val) :
    AdjN N x (periodicLatticeShift s μ) := by
  intro ρ
  rw [shift_valN hN hN1]
  by_cases hρ : ρ = μ
  · subst hρ; simp only [if_true]; right; rw [hμ]
  · simp only [if_neg hρ]; exact h ρ

theorem adjN_shift_coord {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (hN1 : 1 < N)
    (s : PeriodicLatticeSite L) {μ ν : Fin 3} (hne : ν ≠ μ) :
    ((periodicLatticeShift s μ) ν).val = (s ν).val := by
  rw [shift_valN hN hN1, if_neg hne]

/-- the cube for a base site `x ∈ Ω₀`: a class cube containing every neighbour `w` of `x` (coordinates equal or one up) in `Ω₀`. -/
theorem cover_nbhd {L : PeriodicLatticeExtent} {N ell M A0 A B B0 : ℕ} (hN : ∀ μ, L μ + 1 = N)
    (hM : 0 < M) (hell : 2 ≤ ell)
    (hMA0 : M ∣ A0) (hMB0 : M ∣ B0) (hgA : M * ell ∣ A) (hgB : M * ell ∣ B)
    (hsh1 : A0 + 12 * M ≤ A) (hsh2 : B + 12 * M ≤ B0) (hW : A + 12 * (M * ell) ≤ B)
    (hB0N : B0 < N) (hNb : 12 * M + 12 * (M * ell) ≤ N)
    (x : PeriodicLatticeSite L) (hx : A0 ≤ (x 0).val ∧ (x 0).val < B0) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M 12 1 (TG A0 A B B0 L) sites j ∧
      ∀ w : PeriodicLatticeSite L, AdjN N x w → A0 ≤ (w 0).val → (w 0).val < B0 → w ∈ sites := by
  have hg2 : M * 2 ≤ M * ell := Nat.mul_le_mul_left M hell
  have hg0 : 0 < M * ell := by omega
  have hx0 := site_lt hN x 0
  by_cases hI : A ≤ (x 0).val ∧ (x 0).val + 1 < B
  · -- index 1
    obtain ⟨c0, hc0d, hc0A, hc0B, hc0x, hc0y⟩ := exists_corner1 hg0 hgA hgB hW hI
    have hc0N : c0 < N := by omega
    let c : Fin 3 → ℕ := fun μ => if μ = 0 then c0 else (M * ell) * ((x μ).val / (M * ell))
    have hc : ∀ μ, c μ < L μ + 1 := fun μ => by
      have h1 := hN μ
      have h2 := site_lt hN x μ
      have h3 := (div_facts (M * ell) (x μ).val hg0).1
      simp only [c]; split_ifs <;> omega
    let z : PeriodicLatticeSite L := fun μ => ⟨c μ, hc μ⟩
    have hz0 : (z 0).val = c0 := by simp [z, c]
    have hz1 : (z 1).val = (M * ell) * ((x 1).val / (M * ell)) := by simp [z, c]
    have hz2 : (z 2).val = (M * ell) * ((x 2).val / (M * ell)) := by simp [z, c]
    have hgc : GridCorner (bigSide M ell 1) z := by
      intro μ
      rw [bigSide1]
      fin_cases μ
      · show (z 0).val % (M * ell) = 0
        rw [hz0]; exact Nat.mod_eq_zero_of_dvd hc0d
      · show (z 1).val % (M * ell) = 0
        rw [hz1]; exact Nat.mul_mod_right _ _
      · show (z 2).val % (M * ell) = 0
        rw [hz2]; exact Nat.mul_mod_right _ _
    refine ⟨siteBox z (12 * bigSide M ell 1), 1,
      isClassCube_of hN hM hell hNb (le_refl 1) (cube1_desc hN hg0 z hgc ⟨by omega, by omega⟩ (by omega)), ?_⟩
    intro w hw _ _
    rw [bigSide1, memBox hN]
    have hw0 := adj_coord N (x 0).val (w 0).val hx0 (hw 0)
    have hwN := site_lt hN w 0
    refine ⟨?_, ?_, ?_⟩
    · rw [off_lt_iff _ _ _ _ hwN (by omega), hz0]; omega
    · rw [hz1]; exact cell_off N _ _ _ _ hg0 (by omega) (by omega) (site_lt hN x 1) (hw 1)
    · rw [hz2]; exact cell_off N _ _ _ _ hg0 (by omega) (by omega) (site_lt hN x 2) (hw 2)
  · -- index 0
    have hII : (x 0).val < A ∨ B ≤ (x 0).val + 1 := by omega
    obtain ⟨c0, hc0d, hc0A, hc0B, hc0x, hc0y, hc0w, q0, hq1, hq2, hq3⟩ :=
      exists_corner0 hM hMA0 hMB0 hsh1 hsh2 (by omega) hx hII
    have hc0N : c0 < N := by omega
    let c : Fin 3 → ℕ := fun μ => if μ = 0 then c0 else M * ((x μ).val / M)
    have hc : ∀ μ, c μ < L μ + 1 := fun μ => by
      have h1 := hN μ
      have h2 := site_lt hN x μ
      have h3 := (div_facts M (x μ).val hM).1
      simp only [c]; split_ifs <;> omega
    let z : PeriodicLatticeSite L := fun μ => ⟨c μ, hc μ⟩
    have hz0 : (z 0).val = c0 := by simp [z, c]
    have hz1 : (z 1).val = M * ((x 1).val / M) := by simp [z, c]
    have hz2 : (z 2).val = M * ((x 2).val / M) := by simp [z, c]
    have hgc : GridCorner (bigSide M ell 0) z := by
      intro μ
      rw [bigSide0]
      fin_cases μ
      · show (z 0).val % M = 0
        rw [hz0]; exact Nat.mod_eq_zero_of_dvd hc0d
      · show (z 1).val % M = 0
        rw [hz1]; exact Nat.mul_mod_right _ _
      · show (z 2).val % M = 0
        rw [hz2]; exact Nat.mul_mod_right _ _
    have hq0N : q0 < L 0 + 1 := by have := hN 0; omega
    let q : PeriodicLatticeSite L := Function.update x 0 ⟨q0, hq0N⟩
    have hqv0 : (q 0).val = q0 := by simp [q]
    have hq1v : q 1 = x 1 := by simp only [q, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]
    have hq2v : q 2 = x 2 := by simp only [q, Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
    have hqbox : q ∈ siteBox z (12 * bigSide M ell 0) := by
      rw [bigSide0, memBox hN]
      refine ⟨?_, ?_, ?_⟩
      · rw [off_lt_iff _ _ _ _ (site_lt hN q 0) (by omega), hz0, hqv0]; omega
      · rw [hq1v, hz1]; exact cell_off N _ _ _ _ hM (by omega) (by omega) (site_lt hN x 1) (Or.inl rfl)
      · rw [hq2v, hz2]; exact cell_off N _ _ _ _ hM (by omega) (by omega) (site_lt hN x 2) (Or.inl rfl)
    refine ⟨siteBox z (12 * bigSide M ell 0), 0,
      isClassCube_of hN hM hell hNb (Nat.zero_le 1)
        (cube0_desc hN hM z hgc ⟨by omega, by omega⟩ (by omega) (by omega) q hqbox (by rw [hqv0]; exact hq3)), ?_⟩
    intro w hw hwA hwB
    rw [bigSide0, memBox hN]
    have hw0 := adj_coord N (x 0).val (w 0).val hx0 (hw 0)
    have hwN := site_lt hN w 0
    refine ⟨?_, ?_, ?_⟩
    · rw [off_lt_iff _ _ _ _ hwN (by omega), hz0]
      have := hc0w (w 0).val (by omega) (by omega) hwB
      omega
    · rw [hz1]; exact cell_off N _ _ _ _ hM (by omega) (by omega) (site_lt hN x 1) (hw 1)
    · rw [hz2]; exact cell_off N _ _ _ _ hM (by omega) (by omega) (site_lt hN x 2) (hw 2)

end AdalyFormal.P409
