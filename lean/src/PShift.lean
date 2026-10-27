import P4L1
import P4L2
import P409D
import GenCl1
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.P409L
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.GeneralClass
open AdalyFormal.P409
open AdalyFormal.P409W
open AdalyFormal.P409C5

/-- GENERAL lower bound on `TG`: radius `r0`, any enclosing box of side `F * bigSide i`, `i <= 1`. -/
theorem tg_box_lower_shift {L : PeriodicLatticeExtent} {N ell M A0 A B B0 : ℕ} (hN : ∀ μ, L μ + 1 = N)
    (δ : ℕ) (hA0 : A0 + 1 ≤ A) (hδ : A + δ < B) (hAB : A < B) (hBB0 : B ≤ B0) (hAN : A < N)
    (r0 : ℕ) (hr1 : 1 ≤ r0) (hNr : 4 * r0 ≤ N)
    (F : ℕ) (hF : F * M < 2 * r0) (w : PeriodicLatticeSite L) (hw0 : (w 0).val = A + δ) (hrδ : δ + 1 ≤ r0) (hw1 : (w 1).val = 0)
    (hw2 : (w 2).val = 0) :
    ¬ ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), i ≤ 1 ∧
      sites ⊆ towerBj (TG A0 A B B0 L) i ∪ towerBj (TG A0 A B B0 L) (i + 1) ∧
      (∃ z : PeriodicLatticeSite L, sites ⊆ siteBox z (F * bigSide M ell i)) ∧
      (cubeR w r0 ∩ (TG A0 A B B0 L).Om 0) ⊆ sites := by
  rintro ⟨sites, j, hj1, hjs, ⟨z, hz⟩, hsub⟩
  have hvlt : A - 1 < L 0 + 1 := by have := hN 0; omega
  let v : PeriodicLatticeSite L := Function.update w 0 ⟨A - 1, hvlt⟩
  have hv0 : (v 0).val = A - 1 := by simp [v]
  have hvB : v ∈ towerBj (TG A0 A B B0 L) 0 := (TG_bj0 v).mpr (by rw [hv0]; omega)
  have hvOm : v ∈ (TG A0 A B B0 L).Om 0 := (TG_om0 v).mpr (by rw [hv0]; omega)
  have h6lt : r0 - 1 < L 1 + 1 := by have := hN 1; omega
  have hN6lt : N - r0 < L 1 + 1 := by have := hN 1; omega
  let p1 : PeriodicLatticeSite L := Function.update w 1 ⟨r0 - 1, h6lt⟩
  let p2 : PeriodicLatticeSite L := Function.update w 1 ⟨N - r0, hN6lt⟩
  have hvc : v ∈ cubeR w r0 := by
    intro μ
    fin_cases μ
    · refine ⟨-((δ : ℤ) + 1), by omega, by omega, ?_⟩
      show (((v 0).val : ℕ) : ℤ) ≡ (((w 0).val : ℕ) : ℤ) + -((δ : ℤ) + 1) [ZMOD ((L 0 + 1 : ℕ) : ℤ)]
      rw [hv0, hw0]
      have e : ((A - 1 : ℕ) : ℤ) = ((A + δ : ℕ) : ℤ) + -((δ : ℤ) + 1) := by push_cast; omega
      rw [e]
    · have : v 1 = w 1 := by simp [v]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((v 1).val : ℕ) : ℤ) ≡ (((w 1).val : ℕ) : ℤ) + 0 [ZMOD ((L 1 + 1 : ℕ) : ℤ)]
      rw [this]; simp
    · have : v 2 = w 2 := by simp [v]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((v 2).val : ℕ) : ℤ) ≡ (((w 2).val : ℕ) : ℤ) + 0 [ZMOD ((L 2 + 1 : ℕ) : ℤ)]
      rw [this]; simp
  have hp1c : p1 ∈ cubeR w r0 := by
    intro μ
    fin_cases μ
    · have : p1 0 = w 0 := by simp [p1]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((p1 0).val : ℕ) : ℤ) ≡ (((w 0).val : ℕ) : ℤ) + 0 [ZMOD ((L 0 + 1 : ℕ) : ℤ)]
      rw [this]; simp
    · refine ⟨(r0 : ℕ) - 1, by omega, by omega, ?_⟩
      show (((p1 1).val : ℕ) : ℤ) ≡ (((w 1).val : ℕ) : ℤ) + _ [ZMOD ((L 1 + 1 : ℕ) : ℤ)]
      have h1 : (p1 1).val = r0 - 1 := by simp [p1]
      rw [h1, hw1]
      have e : ((r0 - 1 : ℕ) : ℤ) = (0 : ℕ) + (((r0 : ℕ) : ℤ) - 1) := by omega
      rw [e]
    · have : p1 2 = w 2 := by simp [p1]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((p1 2).val : ℕ) : ℤ) ≡ (((w 2).val : ℕ) : ℤ) + 0 [ZMOD ((L 2 + 1 : ℕ) : ℤ)]
      rw [this]; simp
  have hp2c : p2 ∈ cubeR w r0 := by
    intro μ
    fin_cases μ
    · have : p2 0 = w 0 := by simp [p2]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((p2 0).val : ℕ) : ℤ) ≡ (((w 0).val : ℕ) : ℤ) + 0 [ZMOD ((L 0 + 1 : ℕ) : ℤ)]
      rw [this]; simp
    · refine ⟨-((r0 : ℕ) : ℤ), by omega, by omega, ?_⟩
      show (((p2 1).val : ℕ) : ℤ) ≡ (((w 1).val : ℕ) : ℤ) + _ [ZMOD ((L 1 + 1 : ℕ) : ℤ)]
      have h1 : (p2 1).val = N - r0 := by simp [p2]
      rw [h1, hw1, hN 1]
      apply Int.modEq_iff_dvd.2
      refine ⟨-1, ?_⟩
      have : ((N - r0 : ℕ) : ℤ) = (N : ℤ) - ((r0 : ℕ) : ℤ) := by omega
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
  have hd : pcd (L 1 + 1) (p1 1).val (p2 1).val = 2 * r0 - 1 := by
    have h1 : (p1 1).val = r0 - 1 := by simp [p1]
    have h2 : (p2 1).val = N - r0 := by simp [p2]
    rw [h1, h2]; have := hN 1; unfold pcd; split_ifs <;> omega
  omega


end AdalyFormal.P409L
