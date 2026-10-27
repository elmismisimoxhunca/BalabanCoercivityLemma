import P409D
import GenCl1

/-!
# Q409L0 -- the "union of slabs" tower `TU` and its admissibility.

`Om 0 = {x | exists mu, A0 <= x_mu < B0}`, `Om 1 = {x | exists mu, A <= x_mu < B}`, `Om j = empty` for `j >= 2`
(the three-coordinate version of the one-slab tower `TG` of `P409A`).  The complement of `Om 0` is the cube
`H = prod_mu ([0,A0) u [B0,N))`; its corner `(B0,B0,B0)` is the obstruction used in `Q409L2`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.GeneralClass
open AdalyFormal.M1 (strat strat_eq_iff IsPatch patch gsp)

theorem pcd_le_pd {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) (σ : Fin 3) :
    pcd (L σ + 1) (x σ).val (y σ).val ≤ pdist x y :=
  Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)

def TU (A0 A B B0 : ℕ) (L : PeriodicLatticeExtent) : Tower L :=
  ⟨fun j => if j = 0 then {x | ∃ μ : Fin 3, A0 ≤ (x μ).val ∧ (x μ).val < B0}
            else if j = 1 then {x | ∃ μ : Fin 3, A ≤ (x μ).val ∧ (x μ).val < B} else ∅⟩

theorem TU_om0 {A0 A B B0 : ℕ} {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) :
    x ∈ (TU A0 A B B0 L).Om 0 ↔ ∃ μ : Fin 3, A0 ≤ (x μ).val ∧ (x μ).val < B0 := by simp [TU]

theorem TU_om1 {A0 A B B0 : ℕ} {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) :
    x ∈ (TU A0 A B B0 L).Om 1 ↔ ∃ μ : Fin 3, A ≤ (x μ).val ∧ (x μ).val < B := by simp [TU]

theorem TU_om2 {A0 A B B0 : ℕ} {L : PeriodicLatticeExtent} (j : ℕ) :
    (TU A0 A B B0 L).Om (j + 2) = ∅ := by simp [TU]

theorem TU_bj0 {A0 A B B0 : ℕ} {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) :
    x ∈ towerBj (TU A0 A B B0 L) 0 ↔
      (∃ μ : Fin 3, A0 ≤ (x μ).val ∧ (x μ).val < B0) ∧ ¬ (∃ μ : Fin 3, A ≤ (x μ).val ∧ (x μ).val < B) := by
  unfold towerBj
  rw [Set.mem_sdiff, TU_om0]
  show _ ∧ ¬ (x ∈ (TU A0 A B B0 L).Om 1) ↔ _
  rw [TU_om1]

theorem TU_bj1 {A0 A B B0 : ℕ} {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) :
    x ∈ towerBj (TU A0 A B B0 L) 1 ↔ ∃ μ : Fin 3, A ≤ (x μ).val ∧ (x μ).val < B := by
  unfold towerBj
  rw [Set.mem_sdiff, TU_om1]
  have h2 : (TU A0 A B B0 L).Om (1 + 1) = ∅ := TU_om2 0
  rw [h2]
  simp

theorem TU_bj2 {A0 A B B0 : ℕ} {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) :
    x ∉ towerBj (TU A0 A B B0 L) (1 + 1) := by
  unfold towerBj
  have h2 : (TU A0 A B B0 L).Om (1 + 1) = ∅ := TU_om2 0
  rw [h2]
  simp

theorem TU_admissible {L : PeriodicLatticeExtent} {N ell M R A0 A B B0 : ℕ} (hN : ∀ μ, L μ + 1 = N)
    (hM : 0 < M) (hell : 2 ≤ ell)
    (hA0 : A0 + R * M = A) (hB0 : B + R * M = B0) (hMA0 : M ∣ A0) (hMB0 : M ∣ B0)
    (hgA : M * ell ∣ A) (hgB : M * ell ∣ B) (hMN : M ∣ N) (hgN : M * ell ∣ N)
    (hAB : A < B) (hB0N : B0 ≤ N) :
    Admissible ell M R 1 (TU A0 A B B0 L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (_ | _ | j) x hx
    · obtain ⟨μ, h⟩ := (TU_om1 x).mp hx
      exact (TU_om0 x).mpr ⟨μ, by omega, by omega⟩
    · have h2 : (TU A0 A B B0 L).Om (0 + 1 + 1) = ∅ := TU_om2 0
      rw [h2] at hx; exact absurd hx (Set.notMem_empty _)
    · have h2 := TU_om2 (L := L) (A0 := A0) (A := A) (B := B) (B0 := B0) (j + 1)
      have hx' : x ∈ (TU A0 A B B0 L).Om (j + 1 + 2) := hx
      rw [h2] at hx'; exact absurd hx' (Set.notMem_empty _)
  · rintro (_ | _ | j) hj
    · omega
    · omega
    · exact TU_om2 j
  · intro j hj μ
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · rw [bigSide0, hN μ]; exact hMN
    · rw [bigSide1, hN μ]; exact hgN
  · intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · intro x hx y hy
      rw [bigSide0] at hy
      obtain ⟨μ, h⟩ := (TU_om0 x).mp hx
      exact (TU_om0 y).mpr ⟨μ, blk_iv hM hMA0 hMB0 (hy μ) h⟩
    · intro x hx y hy
      rw [bigSide1] at hy
      obtain ⟨μ, h⟩ := (TU_om1 x).mp hx
      exact (TU_om1 y).mpr ⟨μ, blk_iv (Nat.mul_pos hM (by omega)) hgA hgB (hy μ) h⟩
  · intro j hj x hx y hy
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · obtain ⟨μ, hyμ⟩ := (TU_om1 y).mp hy
      have hxμ : ¬ (A0 ≤ (x μ).val ∧ (x μ).val < B0) := fun h => hx ((TU_om0 x).mpr ⟨μ, h⟩)
      have hx0 := site_lt hN x μ
      have hy0 := site_lt hN y μ
      have hlt : R * M < pcd (L μ + 1) (x μ).val (y μ).val := by
        have := hN μ; unfold pcd; split_ifs <;> omega
      rw [bigSide0]
      exact lt_of_lt_of_le hlt (pcd_le_pd x y μ)
    · have h2 : (TU A0 A B B0 L).Om (0 + 1 + 1) = ∅ := TU_om2 0
      rw [h2] at hy; exact absurd hy (Set.notMem_empty _)
  · intro x
    rw [TU_om0]
    constructor
    · rintro ⟨μ, hx⟩
      have hx0 := site_lt hN x μ
      let v : ℕ := if (x μ).val < A then A else if (x μ).val < B then (x μ).val else B - 1
      have hv : v < L μ + 1 := by have := hN μ; simp only [v]; split_ifs <;> omega
      refine ⟨Function.update x μ ⟨v, hv⟩, ?_, x, fun ρ => rfl, ?_⟩
      · rw [TU_om1]
        refine ⟨μ, ?_⟩
        simp only [Function.update_self]; simp only [v]; split_ifs <;> omega
      · rw [pdist_update]
        have := hN μ; unfold pcd; simp only [v]; split_ifs <;> omega
    · rintro ⟨y, hy, z, hz, hd⟩
      obtain ⟨μ, hyμ⟩ := (TU_om1 y).mp hy
      have hz0 : (z μ).val / M = (x μ).val / M := hz μ
      have h12 : pcd (L μ + 1) (z μ).val (y μ).val ≤ R * M := le_trans (pcd_le_pd z y μ) hd
      have hzN := site_lt hN z μ
      have hyN := site_lt hN y μ
      have hzr : A0 ≤ (z μ).val ∧ (z μ).val < B0 := by
        have := hN μ; unfold pcd at h12; split_ifs at h12 <;> omega
      exact ⟨μ, blk_iv hM hMA0 hMB0 hz0.symm hzr⟩

end AdalyFormal.P409
