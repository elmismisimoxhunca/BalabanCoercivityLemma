import P4L3

/-!
# P4L4 -- positive results for the printed containment with the locally constructed `Omega_0(square)`.

(1) `cube5_is_class_box` (j >= 1): `tilde-square^5` is ITSELF a class box (`DescribedAt`, grid-aligned, `subset B^i u B^{i+1}`, meets `B^i`) with the per-cube factor
    `f = 12` when `i = j` and `f = 12 ell` when `i + 1 = j`; hence so is a box containing `Omega_0(square)` (`localOm0 subset tilde-square^5`).
    (For `j >= 1`, `tilde-square^5 subset Omega_{j-1} subset Omega_0`, so the relaxation "cap Omega_0" is vacuous.)
(2) `j0_print_box` / `j0_print_holds`: at `j = 0`, with the p.408 convention `B^0 := T_1 \ Omega_1`, `Omega_0(square) = tilde-square^4` is a class box of factor 10
    (and `tilde-square^5` one of factor 12): TRUE by construction.
(3) `j0_p396_fails`: at `j = 0` with the p.396 set `Lambda_0 = Omega_0 \ Omega_1` (class cubes inside `Omega_0`), the containment FAILS: `Omega_0(square)` leaves `Omega_0`.
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
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle)

variable {L : PeriodicLatticeExtent}

/-- the periodic half-open cube is exactly the periodic box with corner `c - r` and side `2 r`. -/
theorem cubeR_eq_siteBox (c : PeriodicLatticeSite L) (r : ℕ) : cubeR c r = siteBox (zsite c r) (2 * r) := by
  apply Set.Subset.antisymm (cubeR_box c r)
  intro y hy μ
  set N := L μ + 1 with hN
  have hy' : ((y μ).val + N - ((zsite c r) μ).val) % N < 2 * r := hy μ
  have hNpos : 0 < N := Nat.succ_pos _
  have hrle : r ≤ (c μ).val + N * r := by nlinarith
  have hzlt : ((zsite c r) μ).val < N := ((zsite c r) μ).isLt
  have hz : (((zsite c r) μ).val : ℤ) ≡ ((c μ).val : ℤ) + (N : ℤ) * r - r [ZMOD (N : ℤ)] := by
    show ((((c μ).val + N * r - r) % N : ℕ) : ℤ) ≡ _ [ZMOD (N : ℤ)]
    have := Int.natCast_modEq_iff.2 (Nat.mod_modEq ((c μ).val + N * r - r) N)
    rw [Nat.cast_sub hrle] at this
    push_cast at this
    exact this
  refine ⟨((((y μ).val + N - ((zsite c r) μ).val) % N : ℕ) : ℤ) - r, by omega, by omega, ?_⟩
  have hyl : (y μ).val < N := (y μ).isLt
  have h1 : ((((y μ).val + N - ((zsite c r) μ).val) % N : ℕ) : ℤ) ≡ ((y μ).val : ℤ) + (N : ℤ) - (((zsite c r) μ).val : ℤ) [ZMOD (N : ℤ)] := by
    have := Int.natCast_modEq_iff.2 (Nat.mod_modEq ((y μ).val + N - ((zsite c r) μ).val) N)
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this
    exact this
  apply Int.modEq_iff_dvd.2
  obtain ⟨a, ha⟩ := Int.modEq_iff_dvd.1 h1
  obtain ⟨b, hb⟩ := Int.modEq_iff_dvd.1 hz
  refine ⟨-a + b + 1 - r, ?_⟩
  linear_combination (-1 : ℤ) * ha + hb

/-- **(1)** for `j >= 1`, `tilde-square^5` is itself a class box, with per-cube factor `12` (index `j`) or `12 ell` (index `j-1`). -/
theorem cube5_is_class_box {ell M R k j : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hA : Admissible ell M R k S) (hgt : ∀ μ : Fin 3, bigSide M ell k < L μ + 1)
    (hD : IsDCube ell M k S j c) (hj : 1 ≤ j) :
    ∃ i f : ℕ, ((i = j ∧ f = 12) ∨ (i + 1 = j ∧ f = 12 * ell)) ∧ 10 ≤ f ∧
      DescribedAt ell M f k S (printedCube5 (bigSide M ell j) c) i ∧
      IsClassCubeG ell M f k S (printedCube5 (bigSide M ell j) c) i := by
  have hD' := hD
  obtain ⟨hjk, hgrid, x₀, hx0, hx0c⟩ := hD
  have hell0 : 0 < ell := by omega
  set g := bigSide M ell j with hg
  have hx0c' : x₀ ∈ cubeR c g := by rw [← dCube_eq]; exact hx0c
  have hP : ∀ y, y ∈ printedCube5 g c ↔ y ∈ cubeR c (6 * g) := by intro y; rw [printedCube5_eq]
  obtain ⟨i, hij, hdvd, hle, hsub, hmeet, -⟩ := region_core (K := 21) (P := printedCube5 g c) (x₀ := x₀)
    hell hM (by norm_num) hR hA hgt hjk hx0
    (fun y hy => by
      have := cube_dist hx0c' ((hP y).1 hy)
      omega)
    (by rw [printedCube5_eq]; exact cubeR_mono (by omega) hx0c')
    (fun μ s hs => by
      rw [printedCube5_eq]
      exact sh_mem_cube hx0c' (by omega) μ s hs)
  have hPOm : ∀ y ∈ printedCube5 g c, y ∈ S.Om 0 := fun y hy =>
    AdalyFormal.M1.om_anti hA (Nat.zero_le (j - 1)) (cube5_sub_Om hell hM hR hA hD' hj hy)
  have hx0P : x₀ ∈ printedCube5 g c := by rw [printedCube5_eq]; exact cubeR_mono (by omega) hx0c'
  have hjidx : i = j ∨ i + 1 = j := by
    rcases hsub x₀ hx0P (hPOm x₀ hx0P) with h | h
    · left; exact bj_unique hA.1 h hx0
    · right; exact bj_unique hA.1 h hx0
  have hjk' : i ≤ k := le_trans hij hjk
  have hgi : bigSide M ell i ∣ L 0 + 1 := hA.2.2.1 i hjk' 0
  have hgN : ∀ μ : Fin 3, bigSide M ell i ∣ L μ + 1 := hA.2.2.1 i hjk'
  have hgc : ∀ μ : Fin 3, bigSide M ell i ∣ (c μ).val := fun μ =>
    dvd_trans hdvd (Nat.dvd_of_mod_eq_zero (hgrid μ))
  have hgr : bigSide M ell i ∣ 6 * g := Dvd.dvd.mul_left hdvd 6
  have hzgrid : GridCorner (bigSide M ell i) (zsite c (6 * g)) := fun μ =>
    Nat.mod_eq_zero_of_dvd (zsite_dvd c (6 * g) _ hgN hgc hgr μ)
  have hsubB : printedCube5 g c ⊆ towerBj S i ∪ towerBj S (i + 1) := fun y hy => hsub y hy (hPOm y hy)
  have hmeetB : (printedCube5 g c ∩ towerBj S i).Nonempty := by
    obtain ⟨y, h1, -, h3⟩ := hmeet
    exact ⟨y, h1, h3⟩
  have hbox : ∀ f : ℕ, f * bigSide M ell i = 12 * g → DescribedAt ell M f k S (printedCube5 g c) i := by
    intro f hf
    refine ⟨hjk', ⟨zsite c (6 * g), hzgrid, ?_⟩, hsubB, hmeetB⟩
    rw [printedCube5_eq, cubeR_eq_siteBox, hf]
    congr 1
    ring
  rcases hjidx with h | h
  · subst h
    have hD12 := hbox 12 rfl
    exact ⟨i, 12, Or.inl ⟨rfl, rfl⟩, by norm_num, hD12,
      (isClassCubeG_iff hA.1 _ _).2 ⟨by norm_num, hD12⟩⟩
  · have hb : g = bigSide M ell i * ell := by rw [hg, ← h]; exact AdalyFormal.M1.bigSide_succ M ell i
    have hD12 := hbox (12 * ell) (by rw [hb]; ring)
    exact ⟨i, 12 * ell, Or.inr ⟨h, rfl⟩, by omega, hD12,
      (isClassCubeG_iff hA.1 _ _).2 ⟨by omega, hD12⟩⟩

/-- **(1')** the local domain `Omega_0(square)` (`j >= 1`, `2 p <= M`) lies in a class box with factor `12` / `12 ell`: the printed containment holds with a per-cube `O(1)`. -/
theorem local_in_class_box {ell M R k j p : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hA : Admissible ell M R k S) (hgt : ∀ μ : Fin 3, bigSide M ell k < L μ + 1)
    (hD : IsDCube ell M k S j c) (hj : 1 ≤ j) (hp : 2 * p ≤ M) :
    ∃ i f : ℕ, ((i = j ∧ f = 12) ∨ (i + 1 = j ∧ f = 12 * ell)) ∧
      IsClassCubeG ell M f k S (printedCube5 (bigSide M ell j) c) i ∧
      localOm0 ell p (bigSide M ell j) j c ⊆ printedCube5 (bigSide M ell j) c := by
  obtain ⟨i, f, h1, -, -, h4⟩ := cube5_is_class_box hell hM hR hA hgt hD hj
  exact ⟨i, f, h1, h4, localOm0_sub_cube5 c (localHalf_le_six hell hp)⟩

/-- **(1'')** union-class form for the local domain (`j >= 1`): corollary of `cube5_in_union`, since `Omega_0(square) subset tilde-square^5 cap Omega_0`. -/
theorem local_in_union {ell M R k j p : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hA : Admissible ell M R k S) (hgt : ∀ μ : Fin 3, bigSide M ell k < L μ + 1)
    (hD : IsDCube ell M k S j c) (hj : 1 ≤ j) (hp : 2 * p ≤ M) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ),
      IsClassSetW ell M (12 * ell) k S sites i ∧ UNI.AllC.IsClassUnion ell M k S sites i ∧
      BlockClosed (bigSide M ell i) sites ∧ localOm0 ell p (bigSide M ell j) j c ⊆ sites := by
  obtain ⟨sites, i, h1, h2, h3, h4⟩ := cube5_in_union hell hM hR hA hgt hD
  refine ⟨sites, i, h1, h2, h3, fun y hy => h4 ⟨localOm0_sub_cube5 c (localHalf_le_six hell hp) hy,
    localOm0_sub_Om0 hell hM hR hA hD hj hp hy⟩⟩

/-! ## j = 0 -/

/-- a class cube of index `0` with the p.408 convention `B^0 := T_1 \ Omega_1`. -/
def DescribedAt0 (ell M f : ℕ) (S : Tower L) (sites : Set (PeriodicLatticeSite L)) : Prop :=
  (∃ z : PeriodicLatticeSite L, GridCorner (bigSide M ell 0) z ∧ sites = siteBox z (f * bigSide M ell 0)) ∧
  sites ⊆ (S.Om 1)ᶜ ∪ towerBj S 1 ∧ (sites ∩ (S.Om 1)ᶜ).Nonempty

theorem j0_print_box {ell M R k a : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R) (hA : Admissible ell M R k S)
    (hD : IsDCubePrint ell M k S 0 c) (ha1 : 1 ≤ a) (ha6 : a ≤ 6) :
    DescribedAt0 ell M (2 * a) S (cubeR c (a * M)) := by
  obtain ⟨hjk, hgrid, x₀, hx0c, hx0⟩ := hD
  have hg0 : bigSide M ell 0 = M := bigSide_zero M ell
  have hx0n : x₀ ∉ S.Om 1 := by
    rcases hx0 with h | h
    · exact h.2
    · exact h.2
  have hx0c' : x₀ ∈ cubeR c M := by rw [← dCube_eq, ← hg0]; exact hx0c
  rw [hg0] at hgrid
  have hgN : ∀ μ : Fin 3, M ∣ L μ + 1 := fun μ => by
    have := hA.2.2.1 0 (Nat.zero_le k) μ; rwa [hg0] at this
  have hgc : ∀ μ : Fin 3, M ∣ (c μ).val := fun μ => Nat.dvd_of_mod_eq_zero (hgrid μ)
  have hz : GridCorner M (zsite c (a * M)) := fun μ =>
    Nat.mod_eq_zero_of_dvd (zsite_dvd c (a * M) _ hgN hgc (Dvd.intro_left a rfl) μ)
  have hbox : cubeR c (a * M) = siteBox (zsite c (a * M)) ((2 * a) * M) := by
    rw [cubeR_eq_siteBox]; congr 1; ring
  refine ⟨⟨zsite c (a * M), by rw [hg0]; exact hz, by rw [hg0, ← hbox]⟩, ?_, ?_⟩
  · intro y hy
    have hd := cube_dist hx0c' hy
    have hy2 : y ∉ S.Om 2 := by
      intro hy2
      by_cases hk : 1 ≤ k
      · have hcol := AdalyFormal.M1.collar hA (j := 1) hk hx0n hy2
        rw [bigSide1] at hcol
        have h1 : 21 * (ell * (M * ell)) ≤ R * (M * ell) := by
          calc 21 * (ell * (M * ell)) = (21 * ell) * (M * ell) := by ring
            _ ≤ R * (M * ell) := Nat.mul_le_mul_right _ hR
        have h6 : a * M ≤ 6 * M := Nat.mul_le_mul_right M ha6
        have h4 : M * ell ≤ ell * (M * ell) := Nat.le_mul_of_pos_left _ (by omega)
        have h5 : M ≤ M * ell := Nat.le_mul_of_pos_right _ (by omega)
        omega
      · rw [hA.2.1 2 (by omega)] at hy2; exact hy2
    by_cases hy1 : y ∈ S.Om 1
    · exact Or.inr ⟨hy1, hy2⟩
    · exact Or.inl hy1
  · exact ⟨x₀, cubeR_mono (by have := Nat.mul_le_mul_right M ha1; omega) hx0c', hx0n⟩

/-- **(2)** `j = 0`, p.408 convention: `Omega_0(square) = tilde-square^4` is a class box of factor `10` -- the printed containment is true by construction. -/
theorem j0_print_holds {ell M R k p : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R) (hA : Admissible ell M R k S)
    (hD : IsDCubePrint ell M k S 0 c) :
    localOm0 ell p (bigSide M ell 0) 0 c = cubeR c (5 * M) ∧
      DescribedAt0 ell M 10 S (cubeR c (5 * M)) ∧ DescribedAt0 ell M 12 S (printedCube5 (bigSide M ell 0) c) := by
  refine ⟨?_, j0_print_box (a := 5) hell hM hR hA hD (by norm_num) (by norm_num), ?_⟩
  · unfold localOm0 localOm localHalf collarSum; simp [bigSide_zero]
  · rw [printedCube5_eq, bigSide_zero]
    exact j0_print_box (a := 6) hell hM hR hA hD (by norm_num) (by norm_num)

/-- **(3)** `j = 0` with the p.396 set `Lambda_0 = Omega_0 \ Omega_1` (class cubes inside `Omega_0`): the containment FAILS on an admissible tower, for every `f` and index `i`.
The tower is the one-slab tower; the centre is the lower edge of `Omega_0`, so `Omega_0(square) = tilde-square^4` leaves `Omega_0`. -/
theorem j0_p396_fails {ell M p R : ℕ} {Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hLf : ∀ μ, Lf μ + 1 = M * ell * (4 * R + 8)) :
    ∃ (S : Tower Lf) (c : PeriodicLatticeSite Lf), Admissible ell M R 1 S ∧ IsDCube ell M 1 S 0 c ∧
      (∃ q, q ∈ towerBj S 0) ∧ (∃ q, q ∈ towerBj S 1) ∧ (∃ (f i : ℕ) (sites : Set (PeriodicLatticeSite Lf)), DescribedAt ell M f 1 S sites i) ∧
      ∀ (f i : ℕ) (sites : Set (PeriodicLatticeSite Lf)), DescribedAt ell M f 1 S sites i →
        ¬ localOm0 ell p (bigSide M ell 0) 0 c ⊆ sites := by
  obtain ⟨A0, A, B, B0, w, hAdm, hDw, hN, hA0, hAB, hBB0, hAN, -, -, -, hq0, hq1, hgtw, hMA0, hA0pos⟩ :=
    tg_setup (Lf := Lf) hell hM hR hLf
  have hAN' : A0 < Lf 0 + 1 := by rw [hN 0]; omega
  let c : PeriodicLatticeSite Lf := fun μ => ⟨if μ = 0 then A0 else 0, by have := hN μ; split_ifs <;> omega⟩
  have hc0 : (c 0).val = A0 := by simp [c]
  have hc1 : (c 1).val = 0 := by simp [c]
  have hc2 : (c 2).val = 0 := by simp [c]
  have hcB : c ∈ towerBj (TG A0 A B B0 Lf) 0 := (TG_bj0 c).mpr (by rw [hc0]; omega)
  have hgrid : GridCorner (bigSide M ell 0) c := by
    intro μ
    rw [bigSide_zero]
    fin_cases μ
    · show (c 0).val % M = 0
      rw [hc0]; exact Nat.mod_eq_zero_of_dvd hMA0
    · show (c 1).val % M = 0
      rw [hc1]; exact Nat.zero_mod _
    · show (c 2).val % M = 0
      rw [hc2]; exact Nat.zero_mod _
  have hcself : c ∈ dCube (bigSide M ell 0) c := by
    rw [dCube_eq]
    intro μ
    exact ⟨0, by have := bigSide_pos' hM (show 0 < ell by omega) 0; omega, by have := bigSide_pos' hM (show 0 < ell by omega) 0; omega, by simp⟩
  obtain ⟨iw, fw, -, -, hdw, -⟩ := cube5_is_class_box hell hM hR hAdm hgtw hDw (le_refl 1)
  refine ⟨TG A0 A B B0 Lf, c, hAdm, ⟨by norm_num, hgrid, c, hcB, hcself⟩, hq0, hq1, ⟨fw, iw, _, hdw⟩, ?_⟩
  intro f i sites hDesc hsub
  obtain ⟨-, -, hsB, -⟩ := hDesc
  have hvlt : A0 - 1 < Lf 0 + 1 := by omega
  let v : PeriodicLatticeSite Lf := Function.update c 0 ⟨A0 - 1, hvlt⟩
  have hv0 : (v 0).val = A0 - 1 := by simp [v]
  have hvin : v ∈ localOm0 ell p (bigSide M ell 0) 0 c := by
    have hh : localHalf ell p (bigSide M ell 0) 0 0 = 5 * M := by
      unfold localHalf collarSum; simp [bigSide_zero]
    unfold localOm0 localOm
    rw [hh]
    intro μ
    fin_cases μ
    · refine ⟨-1, by omega, by omega, ?_⟩
      show (((v 0).val : ℕ) : ℤ) ≡ (((c 0).val : ℕ) : ℤ) + -1 [ZMOD ((Lf 0 + 1 : ℕ) : ℤ)]
      rw [hv0, hc0]
      have e : ((A0 - 1 : ℕ) : ℤ) = (A0 : ℤ) + -1 := by omega
      rw [e]
    · have : v 1 = c 1 := by simp [v]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((v 1).val : ℕ) : ℤ) ≡ (((c 1).val : ℕ) : ℤ) + 0 [ZMOD ((Lf 1 + 1 : ℕ) : ℤ)]
      rw [this]; simp
    · have : v 2 = c 2 := by simp [v]
      refine ⟨0, by omega, by omega, ?_⟩
      show (((v 2).val : ℕ) : ℤ) ≡ (((c 2).val : ℕ) : ℤ) + 0 [ZMOD ((Lf 2 + 1 : ℕ) : ℤ)]
      rw [this]; simp
  have hvs := hsB (hsub hvin)
  have hv0m : v ∈ (TG A0 A B B0 Lf).Om 0 := by
    rcases hvs with h | h
    · exact AdalyFormal.M1.om_anti hAdm (Nat.zero_le i) h.1
    · exact AdalyFormal.M1.om_anti hAdm (Nat.zero_le (i + 1)) h.1
  rw [TG_om0] at hv0m
  omega

end AdalyFormal.P409L
