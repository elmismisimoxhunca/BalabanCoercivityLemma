import P4L2

/-!
# P4L3 -- HEADLINE 1 (refutation).  The printed containment with the locally constructed `Omega_0(square)` and a class cube of factor `f <= 10 ell`
(in particular the printed `O(1) = 12`) is FALSE on an admissible one-slab tower (depth 1), for every `ell >= 2`, `M > 0`, `0 < p`, `2 p <= M`, `R >= 21 ell`.
The same tower satisfies: `Omega_0(square) subset tilde-square^5` (the print's own side claim, `localHalf <= 6 g`) and `Omega_0(square) subset Omega_0` (global), so the
failure is NOT an artefact of the local box leaving the global domain.
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
open AdalyFormal.M1 (strat strat_eq_iff IsPatch patch gsp)

/-- the one-slab family: admissible, `D_1` cube centre `w` on the level-1 grid, both strata non-empty. -/
theorem tg_setup {ell M R : ℕ} {Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hLf : ∀ μ, Lf μ + 1 = M * ell * (4 * R + 8)) :
    ∃ A0 A B B0 : ℕ, ∃ w : PeriodicLatticeSite Lf,
      Admissible ell M R 1 (TG A0 A B B0 Lf) ∧ IsDCube ell M 1 (TG A0 A B B0 Lf) 1 w ∧
      (∀ μ, Lf μ + 1 = M * ell * (4 * R + 8)) ∧ A0 + 1 ≤ A ∧ A < B ∧ B ≤ B0 ∧ A < M * ell * (4 * R + 8) ∧
      (w 0).val = A ∧ (w 1).val = 0 ∧ (w 2).val = 0 ∧
      (∃ q : PeriodicLatticeSite Lf, q ∈ towerBj (TG A0 A B B0 Lf) 0) ∧
      (∃ q : PeriodicLatticeSite Lf, q ∈ towerBj (TG A0 A B B0 Lf) 1) ∧
      (∀ μ : Fin 3, bigSide M ell 1 < Lf μ + 1) ∧ M ∣ A0 ∧ 0 < A0 := by
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
  have hNe : M * ell * (4 * R + 8) = N := by rw [hN']; ring
  refine ⟨A0, A, B, B0, w, hAdm, hD, hLf, by omega, by omega, by omega, by rw [hNe]; exact hAN, hw0, hw1, hw2,
    ⟨v, hvB⟩, ⟨w, hwB⟩, hgt, hMA0, by rw [hA0d]; exact Nat.mul_pos hM (by have h2 : 2 * (R + 1) ≤ ell * (R + 1) := Nat.mul_le_mul_right _ hell; omega)⟩

/-- the lower-bound half of HEADLINE 1, on the data delivered by `tg_setup`. -/
theorem tg_local_lower {ell M p R : ℕ} {Lf : PeriodicLatticeExtent} {A0 A B B0 : ℕ} {w : PeriodicLatticeSite Lf}
    (hell : 2 ≤ ell) (hM : 0 < M) (hp : 0 < p) (hp2 : 2 * p ≤ M) (hR : 21 * ell ≤ R)
    (hN : ∀ μ, Lf μ + 1 = M * ell * (4 * R + 8)) (hA0 : A0 + 1 ≤ A) (hAB : A < B) (hBB0 : B ≤ B0)
    (hAN : A < M * ell * (4 * R + 8)) (hw0 : (w 0).val = A) (hw1 : (w 1).val = 0) (hw2 : (w 2).val = 0) :
    ∀ f : ℕ, f ≤ 10 * ell → ∀ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ),
      DescribedAt ell M f 1 (TG A0 A B B0 Lf) sites i →
        ¬ localOm0 ell p (bigSide M ell 1) 1 w ⊆ sites := by
  intro f hf sites i hDesc hsub
  obtain ⟨hik, ⟨z, hzeq⟩, hsB, -⟩ := hDesc
  have hg : bigSide M ell 1 = M * ell := bigSide1 M ell
  have hcs : collarSum ell 0 1 = 1 := by simp [collarSum]
  have hr0 : localHalf ell p (bigSide M ell 1) 1 0 = 5 * (M * ell) + 2 * p := by
    unfold localHalf; rw [hcs, hg]; ring
  have hg2 : M * 2 ≤ M * ell := Nat.mul_le_mul_left M hell
  refine tg_box_lower (ell := ell) (M := M) hN hA0 hAB hBB0 hAN
    (localHalf ell p (bigSide M ell 1) 1 0) (by omega) ?_ f ?_ w hw0 hw1 hw2 ⟨sites, i, hik, hsB, ⟨z, hzeq.2.subset⟩, ?_⟩
  · rw [hr0]
    have : 24 * (M * ell) ≤ M * ell * (4 * R + 8) := by nlinarith
    omega
  · rw [hr0]
    have : f * M ≤ 10 * ell * M := Nat.mul_le_mul_right M hf
    have e : 10 * ell * M = 10 * (M * ell) := by ring
    omega
  · intro y hy
    exact hsub hy.1

/-- **HEADLINE 1.**  With `Omega_0(square) = localOm0` (half side `5 g + 2 p`, `g = M ell`, depth 1): no set described as a class cube of factor `f <= 10 ell`
(`DescribedAt`: a box of side `f * M ell^i` on the level-`i` grid, inside `B^i u B^{i+1}`, meeting `B^i`) contains `Omega_0(square)`, for ANY index `i`.
In particular the print's `f = 12` (`ell >= 2`).  The same tower has `Omega_0(square) subset tilde-square^5` and `Omega_0(square) subset Omega_0`. -/
theorem local_print_fails {ell M p R : ℕ} {Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hp : 0 < p) (hp2 : 2 * p ≤ M) (hR : 21 * ell ≤ R)
    (hLf : ∀ μ, Lf μ + 1 = M * ell * (4 * R + 8)) :
    ∃ (S : Tower Lf) (c : PeriodicLatticeSite Lf), Admissible ell M R 1 S ∧ IsDCube ell M 1 S 1 c ∧
      (∃ q, q ∈ towerBj S 0) ∧ (∃ q, q ∈ towerBj S 1) ∧
      localOm0 ell p (bigSide M ell 1) 1 c ⊆ printedCube5 (bigSide M ell 1) c ∧
      localOm0 ell p (bigSide M ell 1) 1 c ⊆ S.Om 0 ∧
      ∀ f : ℕ, f ≤ 10 * ell → ∀ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ),
        DescribedAt ell M f 1 S sites i → ¬ localOm0 ell p (bigSide M ell 1) 1 c ⊆ sites := by
  obtain ⟨A0, A, B, B0, w, hAdm, hD, hN, hA0, hAB, hBB0, hAN, hw0, hw1, hw2, hq0, hq1, hgt, -, -⟩ :=
    tg_setup (Lf := Lf) hell hM hR hLf
  refine ⟨TG A0 A B B0 Lf, w, hAdm, hD, hq0, hq1, ?_, ?_, ?_⟩
  · exact localOm0_sub_cube5 w (localHalf_le_six hell hp2)
  · exact localOm0_sub_Om0 hell hM hR hAdm hD (le_refl 1) hp2
  · exact tg_local_lower hell hM hp hp2 hR hN hA0 hAB hBB0 hAN hw0 hw1 hw2

end AdalyFormal.P409L
