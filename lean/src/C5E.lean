import C5D
import P409C

/-!
# C5E -- the SHARPNESS PAIR for the print's cube on the percube witness family (same `TG` numerics as `p409_percube_counterexample`).

For `ell >= 2`, `M > 0`, `R >= 21 ell`, torus side `M ell (4R+8)`:  there is an admissible one-level tower (`k = 1`), with both strata nonempty,
a patch/`D_1` cube centre `w`, such that
 (lower) for every `F` with `F + 1 <= 12 ell` there is NO `IsClassSetW ell M F 1 S sites i` containing `printedCube5 (M ell) w cap Omega_0`;
 (upper) `IsClassSetW ell M (12 ell)`, `IsClassUnion`, `BlockClosed` set containing it (instance of `cube5_in_union`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409C5

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.GeneralClass (IsClassSetW)
open UNI.AllC (IsClassUnion)
open AdalyFormal.M1 (strat strat_eq_iff IsPatch patch gsp)
open AdalyFormal.P409

theorem cube5_sharp_pair {ell M R : ℕ} {Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hLf : ∀ μ, Lf μ + 1 = M * ell * (4 * R + 8)) :
    ∃ S : Tower Lf, Admissible ell M R 1 S ∧ (∃ p : PeriodicLatticeSite Lf, p ∈ towerBj S 0) ∧
      (∃ p : PeriodicLatticeSite Lf, p ∈ towerBj S 1) ∧
      ∃ w : PeriodicLatticeSite Lf, IsPatch ell M 1 1 S 1 w ∧ IsDCube ell M 1 S 1 w ∧
        (∀ F : ℕ, F + 1 ≤ 12 * ell →
          ¬ ∃ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ), IsClassSetW ell M F 1 S sites i ∧
            (printedCube5 (bigSide M ell 1) w ∩ S.Om 0) ⊆ sites) ∧
        (∃ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ), IsClassSetW ell M (12 * ell) 1 S sites i ∧
            IsClassUnion ell M 1 S sites i ∧ BlockClosed (bigSide M ell i) sites ∧
            (printedCube5 (bigSide M ell 1) w ∩ S.Om 0) ⊆ sites) := by
  have hg2 : M * 2 ≤ M * ell := Nat.mul_le_mul_left M hell
  have hg0 : 0 < M * ell := by omega
  have hRM12 : 12 * M ≤ R * M := by have := Nat.mul_le_mul_right M (show 12 ≤ R by omega); omega
  have hRMg : R * M ≤ R * (M * ell) := Nat.mul_le_mul_left R (by omega)
  have hge : M * ell * 12 ≤ M * ell * R := Nat.mul_le_mul_left _ (show 12 ≤ R by omega)
  obtain ⟨A, hAd⟩ : ∃ A, A = ell * (R * M + M) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = ell * (3 * (R * M) + 4 * M) := ⟨_, rfl⟩
  obtain ⟨N, hNd⟩ : ∃ N, N = ell * (4 * (R * M) + 8 * M) := ⟨_, rfl⟩
  have hA' : A = M * ell * R + M * ell := by rw [hAd]; ring
  have hB' : B = 3 * (M * ell * R) + 4 * (M * ell) := by rw [hBd]; ring
  have hN' : N = 4 * (M * ell * R) + 8 * (M * ell) := by rw [hNd]; ring
  have hLf' : ∀ μ, Lf μ + 1 = N := fun μ => by rw [hLf μ, hN']; ring
  obtain ⟨q, hq⟩ : ∃ q, ell * (R + 1) = q + R := ⟨ell * (R + 1) - R, by
    have : R ≤ ell * (R + 1) := by nlinarith
    omega⟩
  obtain ⟨A0, hA0d⟩ : ∃ A0, A0 = M * q := ⟨_, rfl⟩
  obtain ⟨B0, hB0d⟩ : ∃ B0, B0 = B + R * M := ⟨_, rfl⟩
  have hA0 : A0 + R * M = A := by
    rw [hA0d, hA', show M * ell * R + M * ell = M * (ell * (R + 1)) by ring, hq]; ring
  have hMA0 : M ∣ A0 := ⟨q, hA0d⟩
  have hgA : M * ell ∣ A := ⟨R + 1, by rw [hA']; ring⟩
  have hgB : M * ell ∣ B := ⟨3 * R + 4, by rw [hB']; ring⟩
  have hgN : M * ell ∣ N := ⟨4 * R + 8, by rw [hN']; ring⟩
  have hMB : M ∣ B := ⟨ell * (3 * R + 4), by rw [hB']; ring⟩
  have hMB0 : M ∣ B0 := by rw [hB0d]; exact Nat.dvd_add hMB ⟨R, by ring⟩
  have hMN : M ∣ N := ⟨ell * (4 * R + 8), by rw [hN']; ring⟩
  have hB0N : B0 < N := by omega
  have hAdm : Admissible ell M R 1 (TG A0 A B B0 Lf) :=
    TG_admissible hLf' hM hell hA0 hB0d.symm hMA0 hMB0 hgA hgB hMN hgN (by omega) (by omega)
  have hAN : A < N := by omega
  let w : PeriodicLatticeSite Lf := fun μ => ⟨if μ = 0 then A else 0, by have := hLf' μ; split_ifs <;> omega⟩
  have hw0 : (w 0).val = A := by simp [w]
  have hw1 : (w 1).val = 0 := by simp [w]
  have hw2 : (w 2).val = 0 := by simp [w]
  have hwOm1 : w ∈ (TG A0 A B B0 Lf).Om 1 := (TG_om1 w).mpr (by rw [hw0]; omega)
  have hwOm0 : w ∈ (TG A0 A B B0 Lf).Om 0 := (TG_om0 w).mpr (by rw [hw0]; omega)
  have hwB : w ∈ towerBj (TG A0 A B B0 Lf) 1 := (TG_bj1 w).mpr (by rw [hw0]; omega)
  have hs1 : strat (TG A0 A B B0 Lf) 1 w = 1 := ((strat_eq_iff hAdm (le_refl 1) w).mp hwB).2
  have hvlt : A - 1 < Lf 0 + 1 := by have := hLf' 0; omega
  let v : PeriodicLatticeSite Lf := Function.update w 0 ⟨A - 1, hvlt⟩
  have hv0 : (v 0).val = A - 1 := by simp [v]
  have hvB : v ∈ towerBj (TG A0 A B B0 Lf) 0 := (TG_bj0 v).mpr (by rw [hv0]; omega)
  have hpatch : IsPatch ell M 1 1 (TG A0 A B B0 Lf) 1 w := by
    refine ⟨le_refl 1, ?_, w, hwOm0, hs1, fun μ => rfl⟩
    intro μ
    show (w μ).val % (1 * bigSide M ell 1) = 0
    rw [one_mul, bigSide1]
    fin_cases μ
    · show (w 0).val % (M * ell) = 0
      rw [hw0]; exact Nat.mod_eq_zero_of_dvd hgA
    · show (w 1).val % (M * ell) = 0
      rw [hw1]; exact Nat.zero_mod _
    · show (w 2).val % (M * ell) = 0
      rw [hw2]; exact Nat.zero_mod _
  have hD : IsDCube ell M 1 (TG A0 A B B0 Lf) 1 w := IsPatch.toDCube hM (by omega) hAdm hpatch
  have hgt : ∀ μ : Fin 3, bigSide M ell 1 < Lf μ + 1 := by
    intro μ; rw [hLf' μ, bigSide1, hN']; nlinarith
  refine ⟨TG A0 A B B0 Lf, hAdm, ⟨v, hvB⟩, ⟨w, hwB⟩, w, hpatch, hD, ?_, ?_⟩
  · intro F hF
    rw [bigSide1]
    exact tg_cube5_needs_12ell hLf' hM hell (by omega) (by omega) (by omega) hAN
      (by rw [hN']; nlinarith) F hF w hw0 hw1 hw2
  · exact cube5_in_union hell hM hR hAdm hgt hD

end AdalyFormal.P409C5
