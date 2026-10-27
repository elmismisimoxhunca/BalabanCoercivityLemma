import C5C
import P409D
import GenCl1

/-!
# C5D -- LOWER BOUND for the print's cube.  On the one-slab witness tower `TG` (the tower of `p409_percube_counterexample_pow`),
for the cube `tilde-square^5 = cubeR w (6 g)` (side `12 g`, `g = M ell`, centre `w = (A,0,0)`), NO `IsClassSetW ell M F 1 ..` with `F + 1 <= 12 ell`
contains `printedCube5 g w cap Omega_0`.  Together with `cube5_in_union` (factor `12 ell` suffices on every admissible tower, `R >= 21 ell`)
the threshold for the print's cube is EXACTLY `12 ell` on this family.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409C5

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.GeneralClass
open AdalyFormal.P409

theorem tg_cube5_needs_12ell {L : PeriodicLatticeExtent} {N ell M A0 A B B0 : ℕ} (hN : ∀ μ, L μ + 1 = N)
    (hM : 0 < M) (hell : 2 ≤ ell) (hA0 : A0 + 1 ≤ A) (hAB : A < B) (hBB0 : B ≤ B0) (hAN : A < N)
    (hN24 : 24 * (M * ell) ≤ N)
    (F : ℕ) (hF : F + 1 ≤ 12 * ell) (w : PeriodicLatticeSite L) (hw0 : (w 0).val = A) (hw1 : (w 1).val = 0)
    (hw2 : (w 2).val = 0) :
    ¬ ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassSetW ell M F 1 (TG A0 A B B0 L) sites i ∧
      (printedCube5 (M * ell) w ∩ (TG A0 A B B0 L).Om 0) ⊆ sites := by
  obtain ⟨g, hgd⟩ : ∃ g, g = M * ell := ⟨_, rfl⟩
  have hg2 : M * 2 ≤ g := by rw [hgd]; exact Nat.mul_le_mul_left M hell
  have hg0 : 0 < g := by omega
  rw [← hgd] at hN24 ⊢
  rintro ⟨sites, j, ⟨hj1, hjs, -, ⟨z, hz⟩, -⟩, hsub⟩
  rw [printedCube5_eq] at hsub
  have hvlt : A - 1 < L 0 + 1 := by have := hN 0; omega
  let v : PeriodicLatticeSite L := Function.update w 0 ⟨A - 1, hvlt⟩
  have hv0 : (v 0).val = A - 1 := by simp [v]
  have hvB : v ∈ towerBj (TG A0 A B B0 L) 0 := (TG_bj0 v).mpr (by rw [hv0]; omega)
  have hvOm : v ∈ (TG A0 A B B0 L).Om 0 := (TG_om0 v).mpr (by rw [hv0]; omega)
  have h6lt : 6 * g - 1 < L 1 + 1 := by have := hN 1; omega
  have hN6lt : N - 6 * g < L 1 + 1 := by have := hN 1; omega
  let p1 : PeriodicLatticeSite L := Function.update w 1 ⟨6 * g - 1, h6lt⟩
  let p2 : PeriodicLatticeSite L := Function.update w 1 ⟨N - 6 * g, hN6lt⟩
  have hvc : v ∈ cubeR w (6 * g) := by
    intro μ
    fin_cases μ
    · refine ⟨-1, by omega, by omega, ?_⟩
      show (((v 0).val : ℕ) : ℤ) ≡ (((w 0).val : ℕ) : ℤ) + -1 [ZMOD ((L 0 + 1 : ℕ) : ℤ)]
      rw [hv0, hw0]
      have e : ((A - 1 : ℕ) : ℤ) = (A : ℤ) + -1 := by omega
      rw [e]
    · have : v 1 = w 1 := by simp [v]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((v 1).val : ℕ) : ℤ) ≡ (((w 1).val : ℕ) : ℤ) + 0 [ZMOD ((L 1 + 1 : ℕ) : ℤ)]
      rw [this]; simp
    · have : v 2 = w 2 := by simp [v]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((v 2).val : ℕ) : ℤ) ≡ (((w 2).val : ℕ) : ℤ) + 0 [ZMOD ((L 2 + 1 : ℕ) : ℤ)]
      rw [this]; simp
  have hp1c : p1 ∈ cubeR w (6 * g) := by
    intro μ
    fin_cases μ
    · have : p1 0 = w 0 := by simp [p1]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((p1 0).val : ℕ) : ℤ) ≡ (((w 0).val : ℕ) : ℤ) + 0 [ZMOD ((L 0 + 1 : ℕ) : ℤ)]
      rw [this]; simp
    · refine ⟨(6 * g : ℕ) - 1, by omega, by omega, ?_⟩
      show (((p1 1).val : ℕ) : ℤ) ≡ (((w 1).val : ℕ) : ℤ) + _ [ZMOD ((L 1 + 1 : ℕ) : ℤ)]
      have h1 : (p1 1).val = 6 * g - 1 := by simp [p1]
      rw [h1, hw1]
      have e : ((6 * g - 1 : ℕ) : ℤ) = (0 : ℕ) + (((6 * g : ℕ) : ℤ) - 1) := by omega
      rw [e]
    · have : p1 2 = w 2 := by simp [p1]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((p1 2).val : ℕ) : ℤ) ≡ (((w 2).val : ℕ) : ℤ) + 0 [ZMOD ((L 2 + 1 : ℕ) : ℤ)]
      rw [this]; simp
  have hp2c : p2 ∈ cubeR w (6 * g) := by
    intro μ
    fin_cases μ
    · have : p2 0 = w 0 := by simp [p2]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((p2 0).val : ℕ) : ℤ) ≡ (((w 0).val : ℕ) : ℤ) + 0 [ZMOD ((L 0 + 1 : ℕ) : ℤ)]
      rw [this]; simp
    · refine ⟨-((6 * g : ℕ) : ℤ), by omega, by omega, ?_⟩
      show (((p2 1).val : ℕ) : ℤ) ≡ (((w 1).val : ℕ) : ℤ) + _ [ZMOD ((L 1 + 1 : ℕ) : ℤ)]
      have h1 : (p2 1).val = N - 6 * g := by simp [p2]
      rw [h1, hw1, hN 1]
      apply Int.modEq_iff_dvd.2
      refine ⟨-1, ?_⟩
      have : ((N - 6 * g : ℕ) : ℤ) = (N : ℤ) - ((6 * g : ℕ) : ℤ) := by omega
      rw [this]
      push_cast
      ring
    · have : p2 2 = w 2 := by simp [p2]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((p2 2).val : ℕ) : ℤ) ≡ (((w 2).val : ℕ) : ℤ) + 0 [ZMOD ((L 2 + 1 : ℕ) : ℤ)]
      rw [this]; simp
  have hp10 : p1 ∈ (TG A0 A B B0 L).Om 0 := (TG_om0 p1).mpr (by
    simp only [p1, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1)]; rw [hw0]; omega)
  have hp20 : p2 ∈ (TG A0 A B B0 L).Om 0 := (TG_om0 p2).mpr (by
    simp only [p2, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1)]; rw [hw0]; omega)
  have hvs : v ∈ sites := hsub ⟨hvc, hvOm⟩
  have hj0 : j = 0 := by
    interval_cases j
    · rfl
    · exfalso
      rcases hjs hvs with h | h
      · rw [TG_bj1, hv0] at h; omega
      · exact TG_bj2 v h
  subst hj0
  have m1 := hz (hsub ⟨hp1c, hp10⟩)
  have m2 := hz (hsub ⟨hp2c, hp20⟩)
  unfold siteBox at m1 m2
  simp only [Set.mem_setOf_eq] at m1 m2
  have hlt := pcd_lt_of_offs (L 1 + 1) (p1 1).val (p2 1).val (z 1).val (s := F * bigSide M ell 0) (Nat.succ_pos _)
    (p1 1).isLt (p2 1).isLt (z 1).isLt (m1 1) (m2 1)
  rw [bigSide0] at hlt
  have h12 : (F + 1) * M ≤ (12 * ell) * M := Nat.mul_le_mul_right M hF
  have e : (12 * ell) * M = 12 * g := by rw [hgd]; ring
  have e2 : (F + 1) * M = F * M + M := by ring
  have hd : pcd (L 1 + 1) (p1 1).val (p2 1).val = 12 * g - 1 := by
    have h1 : (p1 1).val = 6 * g - 1 := by simp [p1]
    have h2 : (p2 1).val = N - 6 * g := by simp [p2]
    rw [h1, h2]; have := hN 1; unfold pcd; split_ifs <;> omega
  omega

end AdalyFormal.P409C5
