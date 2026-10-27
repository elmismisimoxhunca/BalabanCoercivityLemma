import P409D
import GenCl1

/-!
Prosecution probe (scratch, not a lane artifact): on the TG one-slab tower the print's cube `box5 = [w-6g, w+6g)^3`
(l^inf radius 6g: the cube `tilde-square^5` of side 12 g, g = M*ell, centred at a level-1 grid corner) needs factor
>= 12*ell for any IsClassSetW, so factor `10*ell+1` (the p409_setw_holds factor, proved for the l^1 ball of radius 5g)
does NOT contain `tilde-square^5 cap Omega_0`.  We use the l^inf ball of radius 6g-1, a subset of box5.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.GeneralClass

#check @pcd_lt_of_offs
#check @memBox

theorem cube5_needs_12ell {L : PeriodicLatticeExtent} {N ell M A0 A B B0 : ℕ} (hN : ∀ μ, L μ + 1 = N)
    (hM : 2 ≤ M) (hell : 2 ≤ ell) (hA0 : A0 + 1 ≤ A) (hAB : A < B) (hBB0 : B ≤ B0) (hAN : A < N)
    (hN24 : 24 * (M * ell) ≤ N)
    (F : ℕ) (hF : F + 2 ≤ 12 * ell) (w : PeriodicLatticeSite L) (hw0 : (w 0).val = A) (hw1 : (w 1).val = 0)
    (hw2 : (w 2).val = 0) :
    ¬ ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassSetW ell M F 1 (TG A0 A B B0 L) sites i ∧
      {y | (∀ μ : Fin 3, pcd (L μ + 1) (w μ).val (y μ).val ≤ 6 * (M * ell) - 1) ∧ y ∈ (TG A0 A B B0 L).Om 0} ⊆ sites := by
  have hg2 : M * 2 ≤ M * ell := Nat.mul_le_mul_left M hell
  have hg0 : 0 < M * ell := by omega
  rintro ⟨sites, j, ⟨hj1, hjs, -, ⟨z, hz⟩, -⟩, hsub⟩
  have hvlt : A - 1 < L 0 + 1 := by have := hN 0; omega
  let v : PeriodicLatticeSite L := Function.update w 0 ⟨A - 1, hvlt⟩
  have hv0 : (v 0).val = A - 1 := by simp [v]
  have hvB : v ∈ towerBj (TG A0 A B B0 L) 0 := (TG_bj0 v).mpr (by rw [hv0]; omega)
  have hvOm : v ∈ (TG A0 A B B0 L).Om 0 := (TG_om0 v).mpr (by rw [hv0]; omega)
  have hvball : ∀ μ : Fin 3, pcd (L μ + 1) (w μ).val (v μ).val ≤ 6 * (M * ell) - 1 := by
    intro μ
    fin_cases μ
    · show pcd (L 0 + 1) (w 0).val (v 0).val ≤ _
      rw [hw0, hv0]; have := hN 0; unfold pcd; split_ifs <;> omega
    · show pcd (L 1 + 1) (w 1).val (v 1).val ≤ _
      have : v 1 = w 1 := by simp [v]
      rw [this]; unfold pcd; split_ifs <;> omega
    · show pcd (L 2 + 1) (w 2).val (v 2).val ≤ _
      have : v 2 = w 2 := by simp [v]
      rw [this]; unfold pcd; split_ifs <;> omega
  have h5lt : 6 * (M * ell) - 1 < L 1 + 1 := by have := hN 1; omega
  have hN5lt : N - (6 * (M * ell) - 1) < L 1 + 1 := by have := hN 1; omega
  let p1 : PeriodicLatticeSite L := Function.update w 1 ⟨6 * (M * ell) - 1, h5lt⟩
  let p2 : PeriodicLatticeSite L := Function.update w 1 ⟨N - (6 * (M * ell) - 1), hN5lt⟩
  have hp1 : ∀ μ : Fin 3, pcd (L μ + 1) (w μ).val (p1 μ).val ≤ 6 * (M * ell) - 1 := by
    intro μ
    fin_cases μ
    · have : p1 0 = w 0 := by simp [p1]
      show pcd (L 0 + 1) (w 0).val (p1 0).val ≤ _
      rw [this]; unfold pcd; split_ifs <;> omega
    · show pcd (L 1 + 1) (w 1).val (p1 1).val ≤ _
      have : (p1 1).val = 6 * (M * ell) - 1 := by simp [p1]
      rw [this, hw1]; have := hN 1; unfold pcd; split_ifs <;> omega
    · have : p1 2 = w 2 := by simp [p1]
      show pcd (L 2 + 1) (w 2).val (p1 2).val ≤ _
      rw [this]; unfold pcd; split_ifs <;> omega
  have hp2 : ∀ μ : Fin 3, pcd (L μ + 1) (w μ).val (p2 μ).val ≤ 6 * (M * ell) - 1 := by
    intro μ
    fin_cases μ
    · have : p2 0 = w 0 := by simp [p2]
      show pcd (L 0 + 1) (w 0).val (p2 0).val ≤ _
      rw [this]; unfold pcd; split_ifs <;> omega
    · show pcd (L 1 + 1) (w 1).val (p2 1).val ≤ _
      have : (p2 1).val = N - (6 * (M * ell) - 1) := by simp [p2]
      rw [this, hw1]; have := hN 1; unfold pcd; split_ifs <;> omega
    · have : p2 2 = w 2 := by simp [p2]
      show pcd (L 2 + 1) (w 2).val (p2 2).val ≤ _
      rw [this]; unfold pcd; split_ifs <;> omega
  have hp10 : p1 ∈ (TG A0 A B B0 L).Om 0 := (TG_om0 p1).mpr (by
    simp only [p1, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1)]; rw [hw0]; omega)
  have hp20 : p2 ∈ (TG A0 A B B0 L).Om 0 := (TG_om0 p2).mpr (by
    simp only [p2, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1)]; rw [hw0]; omega)
  have hvs : v ∈ sites := hsub ⟨hvball, hvOm⟩
  have hj0 : j = 0 := by
    interval_cases j
    · rfl
    · exfalso
      rcases hjs hvs with h | h
      · rw [TG_bj1, hv0] at h; omega
      · exact TG_bj2 v h
  subst hj0
  have m1 := hz (hsub ⟨hp1, hp10⟩)
  have m2 := hz (hsub ⟨hp2, hp20⟩)
  unfold siteBox at m1 m2
  simp only [Set.mem_setOf_eq] at m1 m2
  have hlt := pcd_lt_of_offs (L 1 + 1) (p1 1).val (p2 1).val (z 1).val (s := F * bigSide M ell 0) (Nat.succ_pos _)
    (p1 1).isLt (p2 1).isLt (z 1).isLt (m1 1) (m2 1)
  rw [bigSide0] at hlt
  have h12 : (F + 2) * M ≤ (12 * ell) * M := Nat.mul_le_mul_right M hF
  have e : (12 * ell) * M = 12 * (M * ell) := by ring
  have e2 : (F + 2) * M = F * M + 2 * M := by ring
  have hd : pcd (L 1 + 1) (p1 1).val (p2 1).val = 12 * (M * ell) - 2 := by
    have h1 : (p1 1).val = 6 * (M * ell) - 1 := by simp [p1]
    have h2 : (p2 1).val = N - (6 * (M * ell) - 1) := by simp [p2]
    rw [h1, h2]; have := hN 1; unfold pcd; split_ifs <;> omega
  omega

end AdalyFormal.P409
