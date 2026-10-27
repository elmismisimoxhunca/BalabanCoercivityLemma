import P4L6

/-!
# P4L7 -- the EXACT box-class-cube window for `Omega_0(square)` on the one-slab tower: factor `10 ell + 2`.

(lower, uses grid alignment) no `DescribedAt` set of factor `f <= 10 ell + 1` (index `0` forced; `z` aligned to the level-0 grid) contains `Omega_0(square)`;
(upper) the box `cubeR w (5 g + M)` of side `(10 ell + 2) M` is a `DescribedAt` set of factor `10 ell + 2`, index 0, and contains `Omega_0(square)` (`2 p <= M`).
Together with `local_window` (P4L5): on this tower the per-cube factor of a box class cube for `Omega_0(square)` is exactly `10 ell + 2`, while for `tilde-square^5` it is `12 ell`.
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

theorem off_eq (N a z : ℕ) (ha : a < N) (hz : z < N) :
    (a + N - z) % N = if z ≤ a then a - z else a + N - z := by
  split_ifs with h
  · have : a + N - z = (a - z) + N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- ALIGNED lower bound on `TG`: radius `r0 > M a`, `8 r0 <= N`, any `F <= 2a+1`, a box `[z, z + F*M^{(i)})` with `z` on the level-`i` grid. -/
theorem tg_aligned_lower {L : PeriodicLatticeExtent} {N ell M A0 A B B0 a : ℕ} (hN : ∀ μ, L μ + 1 = N)
    (hMN : M ∣ N) (hM : 0 < M) (ha1 : 1 ≤ a) (hA0 : A0 + 1 ≤ A) (hAB : A < B) (hBB0 : B ≤ B0) (hAN : A < N)
    (r0 : ℕ) (hr1 : 1 ≤ r0) (hNr : 8 * r0 ≤ N) (hra : M * a < r0)
    (F : ℕ) (hF : F ≤ 2 * a + 1) (w : PeriodicLatticeSite L) (hw0 : (w 0).val = A) (hw1 : (w 1).val = 0) :
    ¬ ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), i ≤ 1 ∧
      sites ⊆ towerBj (TG A0 A B B0 L) i ∪ towerBj (TG A0 A B B0 L) (i + 1) ∧
      (∃ z : PeriodicLatticeSite L, GridCorner (bigSide M ell i) z ∧ sites ⊆ siteBox z (F * bigSide M ell i)) ∧
      (cubeR w r0 ∩ (TG A0 A B B0 L).Om 0) ⊆ sites := by
  rintro ⟨sites, j, hj1, hjs, ⟨z, hzg, hz⟩, hsub⟩
  have hvlt : A - 1 < L 0 + 1 := by have := hN 0; omega
  let v : PeriodicLatticeSite L := Function.update w 0 ⟨A - 1, hvlt⟩
  have hv0 : (v 0).val = A - 1 := by simp [v]
  have hvOm : v ∈ (TG A0 A B B0 L).Om 0 := (TG_om0 v).mpr (by rw [hv0]; omega)
  have h6lt : r0 - 1 < L 1 + 1 := by have := hN 1; omega
  have hN6lt : N - r0 < L 1 + 1 := by have := hN 1; omega
  let p1 : PeriodicLatticeSite L := Function.update w 1 ⟨r0 - 1, h6lt⟩
  let p2 : PeriodicLatticeSite L := Function.update w 1 ⟨N - r0, hN6lt⟩
  have hvc : v ∈ cubeR w r0 := by
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
  have hvB : v ∈ towerBj (TG A0 A B B0 L) 0 := (TG_bj0 v).mpr (by rw [hv0]; omega)
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
  have m1' := m1 1
  have m2' := m2 1
  rw [bigSide0] at m1' m2'
  have m1'' : ((p1 1).val + N - (z 1).val) % N < F * M := by have h := hN 1; rw [← h]; exact m1'
  have m2'' : ((p2 1).val + N - (z 1).val) % N < F * M := by have h := hN 1; rw [← h]; exact m2'
  clear m1' m2' m1 m2
  have hg1 : (z 1).val % M = 0 := by have := hzg 1; rwa [bigSide0] at this
  obtain ⟨k, hk⟩ : ∃ k, (z 1).val = M * k := ⟨(z 1).val / M, by
    have := Nat.div_add_mod (z 1).val M; rw [hg1] at this; omega⟩
  obtain ⟨n, hn⟩ : ∃ n, N = M * n := hMN
  have hzl : (z 1).val < N := by have := (z 1).isLt; have h := hN 1; omega
  have e1 : (p1 1).val = r0 - 1 := by simp [p1]
  have e2 : (p2 1).val = N - r0 := by simp [p2]
  rw [e1] at m1''
  rw [e2] at m2''
  rw [off_eq N (r0 - 1) (z 1).val (by omega) hzl] at m1''
  rw [off_eq N (N - r0) (z 1).val (by omega) hzl] at m2''
  have hMa : M ≤ M * a := Nat.le_mul_of_pos_right M ha1
  have hFM : F * M < 3 * r0 := by
    have h1 : F * M ≤ (2 * a + 1) * M := Nat.mul_le_mul_right M hF
    have h2 : (2 * a + 1) * M = 2 * (M * a) + M := by ring
    omega
  by_cases hA1 : (z 1).val ≤ r0 - 1
  · by_cases hA2 : (z 1).val ≤ N - r0
    · rw [if_pos hA1] at m1''; rw [if_pos hA2] at m2''
      omega
    · omega
  · rw [if_neg hA1] at m1''
    by_cases hA2 : (z 1).val ≤ N - r0
    · rw [if_pos hA2] at m2''
      have h3 : M * (k + a) < M * n := by rw [mul_add]; omega
      have h4 : k + a < n := Nat.lt_of_mul_lt_mul_left h3
      have h5 : M * (n + a) < M * (F + k) := by
        rw [mul_add, mul_add]
        have : F * M = M * F := mul_comm _ _
        omega
      have h6 : n + a < F + k := Nat.lt_of_mul_lt_mul_left h5
      omega
    · rw [if_neg hA2] at m2''
      omega

/-- `tg_setup` with the numerics of the slab exported (copy of P4L3 `tg_setup`, extra conjuncts `A0 + R*M = A`, `A = ..`, `B = ..`, `B0 = B + R*M`). -/
theorem tg_setup2 {ell M R : ℕ} {Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hLf : ∀ μ, Lf μ + 1 = M * ell * (4 * R + 8)) :
    ∃ A0 A B B0 : ℕ, ∃ w : PeriodicLatticeSite Lf,
      Admissible ell M R 1 (TG A0 A B B0 Lf) ∧ IsDCube ell M 1 (TG A0 A B B0 Lf) 1 w ∧
      A0 + R * M = A ∧ A = M * ell * R + M * ell ∧ B = 3 * (M * ell * R) + 4 * (M * ell) ∧ B0 = B + R * M ∧
      A0 + 1 ≤ A ∧ A < B ∧ B ≤ B0 ∧ A < M * ell * (4 * R + 8) ∧ B0 < M * ell * (4 * R + 8) ∧
      (w 0).val = A ∧ (w 1).val = 0 ∧ (w 2).val = 0 := by
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
  have hNe : M * ell * (4 * R + 8) = N := by rw [hN']; ring
  have hAN : A < N := by omega
  let w : PeriodicLatticeSite Lf := fun μ => ⟨if μ = 0 then A else 0, by have := hLf' μ; split_ifs <;> omega⟩
  have hw0 : (w 0).val = A := by simp [w]
  have hw1 : (w 1).val = 0 := by simp [w]
  have hw2 : (w 2).val = 0 := by simp [w]
  have hwOm0 : w ∈ (TG A0 A B B0 Lf).Om 0 := (TG_om0 w).mpr (by rw [hw0]; omega)
  have hwB : w ∈ towerBj (TG A0 A B B0 Lf) 1 := (TG_bj1 w).mpr (by rw [hw0]; omega)
  have hs1 : strat (TG A0 A B B0 Lf) 1 w = 1 := ((strat_eq_iff hAdm (le_refl 1) w).mp hwB).2
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
  refine ⟨A0, A, B, B0, w, hAdm, hD, hA0, hA', hB', hB0d, by omega, by omega, by omega, by rw [hNe]; exact hAN,
    by rw [hNe]; exact hB0N, hw0, hw1, hw2⟩

/-- if `y ∈ cubeR w ρ` and the `μ`-coordinate of `w` is `a` with `ρ ≤ a`, `a + ρ ≤ N`, then `a - ρ ≤ y_μ < a + ρ` exactly (no wrap). -/
theorem coord_of_cubeR {L : PeriodicLatticeExtent} {w y : PeriodicLatticeSite L} {ρ a : ℕ} (μ : Fin 3)
    (hy : y ∈ cubeR w ρ) (hw : (w μ).val = a) (h1 : ρ ≤ a) (h2 : a + ρ ≤ L μ + 1) :
    a - ρ ≤ (y μ).val ∧ (y μ).val < a + ρ := by
  obtain ⟨t, ht1, ht2, ht3⟩ := hy μ
  rw [hw] at ht3
  have hyl : (y μ).val < L μ + 1 := (y μ).isLt
  have e1 : (((y μ).val : ℕ) : ℤ) % ((L μ + 1 : ℕ) : ℤ) = (a + t) % ((L μ + 1 : ℕ) : ℤ) := ht3
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at e1
  omega

theorem tg_local_upper {ell M R : ℕ} {Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hLf : ∀ μ, Lf μ + 1 = M * ell * (4 * R + 8))
    {A0 A B B0 : ℕ} {w : PeriodicLatticeSite Lf}
    (hA0 : A0 + R * M = A) (hA : A = M * ell * R + M * ell) (hB : B = 3 * (M * ell * R) + 4 * (M * ell)) (hB0 : B0 = B + R * M)
    (hw0 : (w 0).val = A) (hw1 : (w 1).val = 0) (hw2 : (w 2).val = 0) :
    DescribedAt ell M (10 * ell + 2) 1 (TG A0 A B B0 Lf) (cubeR w (5 * (M * ell) + M)) 0 := by
  set ρ := 5 * (M * ell) + M with hρ
  have hg0 : 0 < ell := by omega
  have hMle : M ≤ M * ell := Nat.le_mul_of_pos_right M hg0
  have h21 : 21 * (M * ell) ≤ R * M := by
    calc 21 * (M * ell) = (21 * ell) * M := by ring
      _ ≤ R * M := Nat.mul_le_mul_right _ hR
  have h42 : 42 * (M * ell) ≤ M * ell * R := by
    have : 42 ≤ R := by omega
    calc 42 * (M * ell) = (M * ell) * 42 := by ring
      _ ≤ (M * ell) * R := Nat.mul_le_mul_left _ this
  have hNe : ∀ μ, Lf μ + 1 = 4 * (M * ell * R) + 8 * (M * ell) := fun μ => by rw [hLf μ]; ring
  have hgN : ∀ μ : Fin 3, M ∣ Lf μ + 1 := fun μ => ⟨ell * (4 * R + 8), by rw [hLf μ]; ring⟩
  have hgc : ∀ μ : Fin 3, M ∣ (w μ).val := fun μ => by
    fin_cases μ
    · show M ∣ (w 0).val
      rw [hw0, hA]; exact ⟨ell * R + ell, by ring⟩
    · show M ∣ (w 1).val
      rw [hw1]; exact dvd_zero M
    · show M ∣ (w 2).val
      rw [hw2]; exact dvd_zero M
  have hz : GridCorner (bigSide M ell 0) (zsite w ρ) := fun μ => by
    rw [bigSide_zero]
    exact Nat.mod_eq_zero_of_dvd (zsite_dvd w ρ M hgN hgc ⟨5 * ell + 1, by rw [hρ]; ring⟩ μ)
  have hvlt : A - 1 < Lf 0 + 1 := by have := hNe 0; omega
  let v : PeriodicLatticeSite Lf := Function.update w 0 ⟨A - 1, hvlt⟩
  have hv0 : (v 0).val = A - 1 := by simp [v]
  have hvc : v ∈ cubeR w ρ := by
    intro μ
    fin_cases μ
    · refine ⟨-1, by omega, by omega, ?_⟩
      show (((v 0).val : ℕ) : ℤ) ≡ (((w 0).val : ℕ) : ℤ) + -1 [ZMOD ((Lf 0 + 1 : ℕ) : ℤ)]
      rw [hv0, hw0]
      have e : ((A - 1 : ℕ) : ℤ) = (A : ℤ) + -1 := by omega
      rw [e]
    · have : v 1 = w 1 := by simp [v]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((v 1).val : ℕ) : ℤ) ≡ (((w 1).val : ℕ) : ℤ) + 0 [ZMOD ((Lf 1 + 1 : ℕ) : ℤ)]
      rw [this]; simp
    · have : v 2 = w 2 := by simp [v]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((v 2).val : ℕ) : ℤ) ≡ (((w 2).val : ℕ) : ℤ) + 0 [ZMOD ((Lf 2 + 1 : ℕ) : ℤ)]
      rw [this]; simp
  have hvB : v ∈ towerBj (TG A0 A B B0 Lf) 0 := (TG_bj0 v).mpr (by rw [hv0]; omega)
  refine ⟨Nat.zero_le 1, ⟨zsite w ρ, hz, ?_⟩, ?_, ⟨v, hvc, hvB⟩⟩
  · rw [cubeR_eq_siteBox, bigSide_zero]; congr 1; rw [hρ]; ring
  · intro y hy
    have hc := coord_of_cubeR 0 hy hw0 (by omega) (by have := hNe 0; omega)
    by_cases hcase : A ≤ (y 0).val ∧ (y 0).val < B
    · right; exact (TG_bj1 y).mpr hcase
    · left; exact (TG_bj0 y).mpr ⟨by omega, hcase⟩

/-- **HEADLINE 4** (exact window for box class cubes, one tower): `Omega_0(square)` is in a box class cube of factor `10 ell + 2` (index 0) and in none of factor `<= 10 ell + 1`. -/
theorem local_box_window {ell M p R : ℕ} {Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hp : 0 < p) (hp2 : 2 * p ≤ M) (hR : 21 * ell ≤ R)
    (hLf : ∀ μ, Lf μ + 1 = M * ell * (4 * R + 8)) :
    ∃ (S : Tower Lf) (c : PeriodicLatticeSite Lf), Admissible ell M R 1 S ∧ IsDCube ell M 1 S 1 c ∧
      (∃ q, q ∈ towerBj S 0) ∧ (∃ q, q ∈ towerBj S 1) ∧
      (∀ f : ℕ, f ≤ 10 * ell + 1 → ∀ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ),
        DescribedAt ell M f 1 S sites i → ¬ localOm0 ell p (bigSide M ell 1) 1 c ⊆ sites) ∧
      ∃ sites : Set (PeriodicLatticeSite Lf), DescribedAt ell M (10 * ell + 2) 1 S sites 0 ∧
        localOm0 ell p (bigSide M ell 1) 1 c ⊆ sites := by
  obtain ⟨A0, A, B, B0, w, hAdm, hD, hA0e, hAe, hBe, hB0e, hA0, hAB, hBB0, hAN, hB0N, hw0, hw1, hw2⟩ :=
    tg_setup2 (Lf := Lf) hell hM hR hLf
  have hg : bigSide M ell 1 = M * ell := bigSide1 M ell
  have hcs : collarSum ell 0 1 = 1 := by simp [collarSum]
  have hr0 : localHalf ell p (bigSide M ell 1) 1 0 = 5 * (M * ell) + 2 * p := by
    unfold localHalf; rw [hcs, hg]; ring
  have hMle : M ≤ M * ell := Nat.le_mul_of_pos_right M (by omega)
  have hvlt : A - 1 < Lf 0 + 1 := by have h := hLf 0; omega
  let v : PeriodicLatticeSite Lf := Function.update w 0 ⟨A - 1, hvlt⟩
  have hv0 : (v 0).val = A - 1 := by simp [v]
  have hvB : v ∈ towerBj (TG A0 A B B0 Lf) 0 := (TG_bj0 v).mpr (by rw [hv0]; omega)
  have hwB : w ∈ towerBj (TG A0 A B B0 Lf) 1 := (TG_bj1 w).mpr (by rw [hw0]; omega)
  refine ⟨TG A0 A B B0 Lf, w, hAdm, hD, ⟨v, hvB⟩, ⟨w, hwB⟩, ?_, ⟨cubeR w (5 * (M * ell) + M),
    tg_local_upper hell hM hR hLf hA0e hAe hBe hB0e hw0 hw1 hw2, ?_⟩⟩
  · intro f hf sites i hDesc hsub
    obtain ⟨hik, ⟨z, hzg, hzeq⟩, hsB, -⟩ := hDesc
    have hMN : M ∣ M * ell * (4 * R + 8) := ⟨ell * (4 * R + 8), by ring⟩
    refine tg_aligned_lower (ell := ell) (M := M) (a := 5 * ell) hLf hMN hM (by omega) hA0 hAB hBB0 hAN
      (localHalf ell p (bigSide M ell 1) 1 0) (by omega) ?_ ?_ f (by omega) w hw0 hw1
      ⟨sites, i, hik, hsB, ⟨z, hzg, hzeq.subset⟩, fun y hy => hsub hy.1⟩
    · rw [hr0]
      have : 48 * (M * ell) ≤ M * ell * (4 * R + 8) := by nlinarith
      omega
    · rw [hr0]
      have e : M * (5 * ell) = 5 * (M * ell) := by ring
      omega
  · intro y hy
    exact cubeR_mono (show localHalf ell p (bigSide M ell 1) 1 0 ≤ 5 * (M * ell) + M by rw [hr0]; omega) hy

end AdalyFormal.P409L

open AdalyFormal.P409L in
#print axioms tg_aligned_lower
open AdalyFormal.P409L in
#print axioms local_box_window
