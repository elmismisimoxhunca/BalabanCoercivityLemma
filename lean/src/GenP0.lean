import P409D
import GenCl1

/-!
# GenP0 -- the OTHER direction on the witness family: the factor `10*ell + 1` suffices.

On the one-slab tower `TG` (the witness of `P409D`), with the patch centre `w = (A, 0, 0)`, the box of side `(10*ell+1)*M`
(factor `f = 10*ell + 1`, index 0, corner `(A - 5g, N - 5g, N - 5g)`, `g = M*ell`) is a GENERAL class cube
(`IsClassCubeG`, unique index over all factors) and contains `{y | pdist w y <= 5 g} cap Omega_0`.
Together with `GenP1` this makes `10*ell` / `10*ell + 1` the exact threshold on the witness family.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.GeneralClass
open AdalyFormal.M1 (strat strat_eq_iff IsPatch patch gsp)

theorem pcd_le_pdist_coord {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) (σ : Fin 3) :
    pcd (L σ + 1) (x σ).val (y σ).val ≤ pdist x y :=
  Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)

theorem tg_sharp_cube {L : PeriodicLatticeExtent} {N ell M A0 A B B0 : ℕ} (hN : ∀ μ, L μ + 1 = N)
    (hM : 0 < M) (hell : 2 ≤ ell)
    (hgA : M * ell ∣ A) (hgN : M * ell ∣ N)
    (h5A : A0 + 5 * (M * ell) ≤ A) (hAB : A + 5 * (M * ell) + M ≤ B) (hB0 : B ≤ B0) (hB0N : B0 ≤ N)
    (hAN : A < N)
    (w : PeriodicLatticeSite L) (hw0 : (w 0).val = A) (hw1 : (w 1).val = 0) (hw2 : (w 2).val = 0) :
    ∃ z : PeriodicLatticeSite L,
      IsClassCubeG ell M (10 * ell + 1) 1 (TG A0 A B B0 L) (siteBox z ((10 * ell + 1) * bigSide M ell 0)) 0 ∧
      ∀ y : PeriodicLatticeSite L, pdist w y ≤ 5 * (M * ell) → y ∈ (TG A0 A B B0 L).Om 0 →
        y ∈ siteBox z ((10 * ell + 1) * bigSide M ell 0) := by
  have hg2 : M * 2 ≤ M * ell := Nat.mul_le_mul_left M hell
  have hg0 : 0 < M * ell := by omega
  have hs : (10 * ell + 1) * bigSide M ell 0 = 10 * (M * ell) + M := by rw [bigSide0]; ring
  obtain ⟨tA, htA⟩ := hgA
  obtain ⟨tN, htN⟩ := hgN
  have hz0 : A - 5 * (M * ell) < L 0 + 1 := by have := hN 0; omega
  have hz1 : N - 5 * (M * ell) < L 1 + 1 := by have := hN 1; omega
  have hz2 : N - 5 * (M * ell) < L 2 + 1 := by have := hN 2; omega
  let z : PeriodicLatticeSite L := fun μ => ⟨if μ = 0 then A - 5 * (M * ell) else N - 5 * (M * ell), by
    split_ifs with h
    · subst h; exact hz0
    · have := hN μ; omega⟩
  have hzv0 : (z 0).val = A - 5 * (M * ell) := by simp [z]
  have hzv1 : (z 1).val = N - 5 * (M * ell) := by simp [z]
  have hzv2 : (z 2).val = N - 5 * (M * ell) := by simp [z]
  -- membership in the box, from the three circular-distance bounds
  have hmem : ∀ y : PeriodicLatticeSite L, pdist w y ≤ 5 * (M * ell) → y ∈ siteBox z (10 * (M * ell) + M) := by
    intro y hy
    rw [memBox hN]
    have c0 := pcd_le_pdist_coord w y 0
    have c1 := pcd_le_pdist_coord w y 1
    have c2 := pcd_le_pdist_coord w y 2
    have e0 := hN 0
    have e1 := hN 1
    have e2 := hN 2
    have y0 := site_lt hN y 0
    have y1 := site_lt hN y 1
    have y2 := site_lt hN y 2
    refine ⟨?_, ?_, ?_⟩
    · rw [off_lt_iff _ _ _ _ y0 (site_lt hN z 0), hzv0]
      rw [hw0] at c0
      unfold pcd at c0; split_ifs at c0 <;> omega
    · rw [off_lt_iff _ _ _ _ y1 (site_lt hN z 1), hzv1]
      rw [hw1] at c1
      unfold pcd at c1; split_ifs at c1 <;> omega
    · rw [off_lt_iff _ _ _ _ y2 (site_lt hN z 2), hzv2]
      rw [hw2] at c2
      unfold pcd at c2; split_ifs at c2 <;> omega
  -- the point v = (A-1, 0, 0) is in the box, in B^0
  have hvlt : A - 1 < L 0 + 1 := by have := hN 0; omega
  let v : PeriodicLatticeSite L := Function.update w 0 ⟨A - 1, hvlt⟩
  have hv0 : (v 0).val = A - 1 := by simp [v]
  have hvp : pdist w v ≤ 5 * (M * ell) := by
    show pdist w (Function.update w 0 ⟨A - 1, hvlt⟩) ≤ _
    rw [pdist_update]
    unfold pcd; rw [hw0]; split_ifs <;> omega
  have hvbox : v ∈ siteBox z (10 * (M * ell) + M) := hmem v hvp
  have hvB : v ∈ towerBj (TG A0 A B B0 L) 0 := (TG_bj0 v).mpr (by rw [hv0]; omega)
  have hdesc : DescribedAt ell M (10 * ell + 1) 1 (TG A0 A B B0 L) (siteBox z ((10 * ell + 1) * bigSide M ell 0)) 0 := by
    refine ⟨Nat.zero_le _, ⟨z, ?_, rfl⟩, ?_, ⟨v, ?_, hvB⟩⟩
    · intro μ
      rw [bigSide0]
      fin_cases μ
      · show (z 0).val % M = 0
        rw [hzv0, htA]; apply Nat.mod_eq_zero_of_dvd; exact Nat.dvd_sub (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl M) ell) tA) (Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_refl M) ell) 5)
      · show (z 1).val % M = 0
        rw [hzv1, htN]; apply Nat.mod_eq_zero_of_dvd; exact Nat.dvd_sub (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl M) ell) tN) (Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_refl M) ell) 5)
      · show (z 2).val % M = 0
        rw [hzv2, htN]; apply Nat.mod_eq_zero_of_dvd; exact Nat.dvd_sub (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl M) ell) tN) (Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_refl M) ell) 5)
    · intro y hy
      rw [hs] at hy
      have h1 := ((memBox hN _ _ _).mp hy).1
      rw [off_lt_iff _ _ _ _ (site_lt hN y 0) (site_lt hN z 0), hzv0] at h1
      by_cases hy1 : A ≤ (y 0).val ∧ (y 0).val < B
      · right
        exact (TG_bj1 y).mpr hy1
      · left
        rw [TG_bj0]
        refine ⟨⟨?_, ?_⟩, hy1⟩ <;> omega
    · rw [hs]; exact hvbox
  refine ⟨z, ⟨by omega, hdesc, ?_⟩, fun y hy hy0 => ?_⟩
  · intro i f' hi
    obtain ⟨hi1, -, hsub, -⟩ := hi
    have hvs : v ∈ siteBox z ((10 * ell + 1) * bigSide M ell 0) := by rw [hs]; exact hvbox
    interval_cases i
    · rfl
    · exfalso
      rcases hsub hvs with h | h
      · rw [TG_bj1, hv0] at h; omega
      · exact TG_bj2 v h
  · exact (by rw [hs]; exact hmem y hy)

end AdalyFormal.P409
