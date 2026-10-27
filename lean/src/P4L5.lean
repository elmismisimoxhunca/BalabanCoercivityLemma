import P4L4

/-!
# P4L5 -- the two-sided WINDOW for the printed containment with the local `Omega_0(square)`, on ONE tower; and the headline axiom prints.

On the one-slab tower (depth 1, level 1; `ell >= 2`, `M > 0`, `0 < p`, `2 p <= M`, `R >= 21 ell`):
 (lower) no `DescribedAt` set of factor `f <= 10 ell` (any index) contains `Omega_0(square)`;
 (upper) `tilde-square^5` is a class box (`IsClassCubeG`) of factor `12 ell` (index 0) and contains `Omega_0(square)`.
-/
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

theorem local_window {ell M p R : ℕ} {Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hp : 0 < p) (hp2 : 2 * p ≤ M) (hR : 21 * ell ≤ R)
    (hLf : ∀ μ, Lf μ + 1 = M * ell * (4 * R + 8)) :
    ∃ (S : Tower Lf) (c : PeriodicLatticeSite Lf), Admissible ell M R 1 S ∧ IsDCube ell M 1 S 1 c ∧
      (∃ q, q ∈ towerBj S 0) ∧ (∃ q, q ∈ towerBj S 1) ∧
      localOm0 ell p (bigSide M ell 1) 1 c ⊆ printedCube5 (bigSide M ell 1) c ∧
      (∀ f : ℕ, f ≤ 10 * ell → ∀ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ),
        DescribedAt ell M f 1 S sites i → ¬ localOm0 ell p (bigSide M ell 1) 1 c ⊆ sites) ∧
      ∃ i : ℕ, IsClassCubeG ell M (12 * ell) 1 S (printedCube5 (bigSide M ell 1) c) i := by
  obtain ⟨A0, A, B, B0, w, hAdm, hD, hN, hA0, hAB, hBB0, hAN, hw0, hw1, hw2, hq0, hq1, hgt, -, -⟩ :=
    tg_setup (Lf := Lf) hell hM hR hLf
  refine ⟨TG A0 A B B0 Lf, w, hAdm, hD, hq0, hq1, localOm0_sub_cube5 w (localHalf_le_six hell hp2),
    tg_local_lower hell hM hp hp2 hR hN hA0 hAB hBB0 hAN hw0 hw1 hw2, ?_⟩
  obtain ⟨i, f, hif, -, -, hcl⟩ := cube5_is_class_box hell hM hR hAdm hgt hD (le_refl 1)
  -- on this tower `i = 0` (a `B^0` site lies in `tilde-square^5` and the cube is a class cube of ONE index), so `f = 12 ell`
  have hf12 : f = 12 * ell := by
    rcases hif with ⟨hi, hf⟩ | ⟨hi, hf⟩
    · exfalso
      subst hi
      have hvlt : A - 1 < Lf 0 + 1 := by have := hN 0; omega
      let v : PeriodicLatticeSite Lf := Function.update w 0 ⟨A - 1, hvlt⟩
      have hv0 : (v 0).val = A - 1 := by simp [v]
      have hvB : v ∈ towerBj (TG A0 A B B0 Lf) 0 := (TG_bj0 v).mpr (by rw [hv0]; omega)
      have hvc : v ∈ cubeR w (bigSide M ell 1) := by
        intro μ
        fin_cases μ
        · refine ⟨-1, by have := bigSide_pos' hM (show 0 < ell by omega) 1; omega,
            by have := bigSide_pos' hM (show 0 < ell by omega) 1; omega, ?_⟩
          show (((v 0).val : ℕ) : ℤ) ≡ (((w 0).val : ℕ) : ℤ) + -1 [ZMOD ((Lf 0 + 1 : ℕ) : ℤ)]
          rw [hv0, hw0]
          have e : ((A - 1 : ℕ) : ℤ) = (A : ℤ) + -1 := by omega
          rw [e]
        · have : v 1 = w 1 := by simp [v]
          refine ⟨0, by have := bigSide_pos' hM (show 0 < ell by omega) 1; omega,
            by have := bigSide_pos' hM (show 0 < ell by omega) 1; omega, ?_⟩
          show (((v 1).val : ℕ) : ℤ) ≡ (((w 1).val : ℕ) : ℤ) + 0 [ZMOD ((Lf 1 + 1 : ℕ) : ℤ)]
          rw [this]; simp
        · have : v 2 = w 2 := by simp [v]
          refine ⟨0, by have := bigSide_pos' hM (show 0 < ell by omega) 1; omega,
            by have := bigSide_pos' hM (show 0 < ell by omega) 1; omega, ?_⟩
          show (((v 2).val : ℕ) : ℤ) ≡ (((w 2).val : ℕ) : ℤ) + 0 [ZMOD ((Lf 2 + 1 : ℕ) : ℤ)]
          rw [this]; simp
      have hvP : v ∈ printedCube5 (bigSide M ell 1) w := by
        rw [printedCube5_eq]; exact cubeR_mono (by have := bigSide_pos' hM (show 0 < ell by omega) 1; omega) hvc
      obtain ⟨-, -, hsB, -⟩ := hcl.2.1
      rcases hsB hvP with h | h
      · rw [TG_bj1, hv0] at h; omega
      · exact TG_bj2 v h
    · exact hf
  refine ⟨i, ?_⟩
  rw [← hf12]; exact hcl

theorem tg_nonvacuous {ell M R : ℕ} {Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hLf : ∀ μ, Lf μ + 1 = M * ell * (4 * R + 8)) :
    ∃ (S : Tower Lf) (c : PeriodicLatticeSite Lf), Admissible ell M R 1 S ∧ IsDCube ell M 1 S 1 c ∧
      (∀ μ : Fin 3, bigSide M ell 1 < Lf μ + 1) ∧ (∃ q, q ∈ towerBj S 0) ∧ (∃ q, q ∈ towerBj S 1) := by
  obtain ⟨A0, A, B, B0, w, hAdm, hD, -, -, -, -, -, -, -, -, hq0, hq1, hgt, -, -⟩ := tg_setup (Lf := Lf) hell hM hR hLf
  exact ⟨TG A0 A B B0 Lf, w, hAdm, hD, hgt, hq0, hq1⟩

end AdalyFormal.P409L

open AdalyFormal.P409L in
#print axioms local_print_fails
open AdalyFormal.P409L in
#print axioms local_window
open AdalyFormal.P409L in
#print axioms cube5_is_class_box
open AdalyFormal.P409L in
#print axioms local_in_class_box
open AdalyFormal.P409L in
#print axioms local_in_union
open AdalyFormal.P409L in
#print axioms j0_print_holds
open AdalyFormal.P409L in
#print axioms j0_p396_fails
open AdalyFormal.P409L in
#print axioms tg_nonvacuous
open AdalyFormal.P409L in
#print axioms localHalf_le_six
open AdalyFormal.P409L in
#print axioms localHalf_step
open AdalyFormal.P409L in
#print axioms localOm0_sub_Om0
open AdalyFormal.P409L in
#print axioms tg_box_lower
