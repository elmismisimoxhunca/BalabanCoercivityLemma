import C5F

/-!
# C5G -- (F1) the print's j = 0 family `D_0` with blocks in `T_1 \ Omega_1`, and (F2) the index clause.

p.408 (corpus/pages/CMP99b_p408.md line 29, page image viewed): "Let us take here the set $T_1 \backslash \Omega_1$ instead of
$\Lambda_0 = \Omega_0 \backslash \Omega_1$."  So for `j = 0` a `D_0` cube needs only a block in `T_1 \ Omega_1` (`T_1` the whole lattice): the anchor
`x0` is any site of the cube with `x0 not in Omega_1`, possibly OUTSIDE `Omega_0`.

Main results: `cube5_in_union_print0` (for the wider family: `cube5 ∩ Omega_0` is empty, or lies in one block-closed index-0 set in
`IsClassSetW` at factor `12 ell` and in `IsClassUnion`), `cube5_print0_anchor_full` (anchor in `Omega_0`: the full `IsClassSetW` bundle),
and `cube5_index` (the index clause `i = j or i + 1 = j`; COPIED from the prosecution's
`compute/p409_cube5_prosecution_20261018/C5P.lean` (credit: the prosecutor), with `bj_unique`).
(Docstring corrected 2026-10-18 after prosecution finding G-F1: an earlier version announced a declaration `print0_two_block_fails`
that does not exist and is contradicted by `cube5_in_union_print0`.)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409C5

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.P409W
open AdalyFormal.GeneralClass (IsClassSetW)
open UNI.AllC (IsClassUnion UnionAt)

variable {L : PeriodicLatticeExtent}

/-- the print's `D_j` family: for `j >= 1` a block in `B^j`; for `j = 0` a block in `T_1 \ Omega_1` (p.408), i.e. `x0 not in Omega_1`
(`Omega_1 = Omega_{j+1}`), not necessarily in `Omega_0`. -/
def IsDCubePrint (ell M k : ℕ) (S : Tower L) (j : ℕ) (c : PeriodicLatticeSite L) : Prop :=
  j ≤ k ∧ GridCorner (bigSide M ell j) c ∧ ∃ x₀ : PeriodicLatticeSite L, x₀ ∈ dCube (bigSide M ell j) c ∧
    ((x₀ ∈ S.Om j ∧ x₀ ∉ S.Om (j + 1)) ∨ (j = 0 ∧ x₀ ∉ S.Om 1))

theorem IsDCube.toPrint {ell M k j : ℕ} {S : Tower L} {c : PeriodicLatticeSite L} (h : IsDCube ell M k S j c) :
    IsDCubePrint ell M k S j c := by
  obtain ⟨hjk, hg, x₀, hx, hc⟩ := h
  exact ⟨hjk, hg, x₀, hc, Or.inl hx⟩

theorem bj_unique {S : Tower L} (hmono : ∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j) {x : PeriodicLatticeSite L} {a b : ℕ}
    (ha : x ∈ towerBj S a) (hb : x ∈ towerBj S b) : a = b := by
  have key : ∀ {a b : ℕ}, a < b → x ∈ towerBj S a → x ∈ towerBj S b → False := fun {a b} hab ha hb =>
    ha.2 (AdalyFormal.GeneralClass.om_anti hmono (show a + 1 ≤ b by omega) hb.1)
  rcases lt_trichotomy a b with h | h | h
  · exact (key h ha hb).elim
  · exact h
  · exact (key h hb ha).elim

/-- COPIED from the prosecution (`C5P.cube5_index`): the index clause `i = j or i + 1 = j` joins the headline bundle. -/
theorem cube5_index {ell M R k j : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hA : Admissible ell M R k S) (hgt : ∀ μ : Fin 3, bigSide M ell k < L μ + 1)
    (hD : IsDCube ell M k S j c) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ),
      IsClassSetW ell M (12 * ell) k S sites i ∧ IsClassUnion ell M k S sites i ∧
      BlockClosed (bigSide M ell i) sites ∧
      (printedCube5 (bigSide M ell j) c ∩ S.Om 0) ⊆ sites ∧ (i = j ∨ i + 1 = j) := by
  obtain ⟨hjk, hgrid, x₀, hx0, hx0c⟩ := hD
  obtain ⟨sites, i, h1, h2, h3, h4⟩ := cube5_in_union hell hM hR hA hgt ⟨hjk, hgrid, x₀, hx0, hx0c⟩
  refine ⟨sites, i, h1, h2, h3, h4, ?_⟩
  have hx0c' : x₀ ∈ cubeR c (bigSide M ell j) := by rw [← dCube_eq]; exact hx0c
  have hin : x₀ ∈ sites := h4 ⟨by rw [printedCube5_eq]; exact cubeR_mono (by omega) hx0c',
    AdalyFormal.GeneralClass.om_anti hA.1 (Nat.zero_le j) hx0.1⟩
  rcases h2.1.2.2.1 hin with h | h
  · left; exact bj_unique hA.1 h hx0
  · right; exact bj_unique hA.1 h hx0

/-- anchor in `Omega_0`: the wider `j = 0` family reduces to the headline (full `IsClassSetW` bundle, two blocks included). -/
theorem cube5_print0_anchor_full {ell M R k : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hA : Admissible ell M R k S) (hgt : ∀ μ : Fin 3, bigSide M ell k < L μ + 1)
    (hjk : 0 ≤ k) (hgrid : GridCorner (bigSide M ell 0) c) (x₀ : PeriodicLatticeSite L)
    (hx : x₀ ∈ dCube (bigSide M ell 0) c) (h0 : x₀ ∈ S.Om 0) (h1 : x₀ ∉ S.Om 1) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ),
      IsClassSetW ell M (12 * ell) k S sites i ∧ IsClassUnion ell M k S sites i ∧
      BlockClosed (bigSide M ell i) sites ∧
      (printedCube5 (bigSide M ell 0) c ∩ S.Om 0) ⊆ sites ∧ i = 0 := by
  obtain ⟨sites, i, a, b, c', d, e⟩ := cube5_index hell hM hR hA hgt (j := 0) (c := c)
    ⟨hjk, hgrid, x₀, ⟨h0, h1⟩, hx⟩
  exact ⟨sites, i, a, b, c', d, by omega⟩

/-- `sh_mem_cube` with a general inner radius: shifting a site of `cubeR c r0` by `+-g` stays in `cubeR c r` when `r0 + g <= r`. -/
theorem sh_mem_cube2 {c x : PeriodicLatticeSite L} {g r0 r : ℕ} (hx : x ∈ cubeR c r0) (hgr : r0 + g ≤ r)
    (μ : Fin 3) (s : ℕ) (hs : s = g ∨ s + g = L μ + 1) : sh x μ s ∈ cubeR c r := by
  intro ν
  by_cases hν : ν = μ
  · subst hν
    obtain ⟨t, h1, h2, h3⟩ := hx ν
    have hmod : (((sh x ν s) ν).val : ℤ) ≡ ((x ν).val : ℤ) + (s : ℤ) [ZMOD ((L ν + 1 : ℕ) : ℤ)] := by
      rw [sh_self]
      have := Int.natCast_modEq_iff.2 (Nat.mod_modEq ((x ν).val + s) (L ν + 1))
      push_cast at this
      exact this
    rcases hs with rfl | hs
    · refine ⟨t + s, by omega, by omega, ?_⟩
      have := hmod.trans (Int.ModEq.add_right (s : ℤ) h3)
      have e : ((c ν).val : ℤ) + t + (s : ℤ) = ((c ν).val : ℤ) + (t + s) := by ring
      rwa [e] at this
    · refine ⟨t - g, by omega, by omega, ?_⟩
      have h4 : ((x ν).val : ℤ) + (s : ℤ) ≡ ((x ν).val : ℤ) + (-(g : ℤ)) [ZMOD ((L ν + 1 : ℕ) : ℤ)] := by
        apply Int.modEq_iff_dvd.2
        refine ⟨-1, ?_⟩
        push_cast
        omega
      have := (hmod.trans h4).trans (Int.ModEq.add_right (-(g : ℤ)) h3)
      have e : ((c ν).val : ℤ) + t + -(g : ℤ) = ((c ν).val : ℤ) + (t - g) := by ring
      rwa [e] at this
  · rw [sh_ne x μ ν s hν]
    obtain ⟨t, h1, h2, h3⟩ := hx ν
    exact ⟨t, by omega, by omega, h3⟩

/-- the wider print family at `j = 0` (`D_0` cubes with a block in `T_1 \ Omega_1`, p.408): either `tilde-square^5 cap Omega_0` is empty, or it lies in one
block-closed set of index `0` which is in `IsClassUnion` and in `IsClassSetW ell M (12 ell)` (box of side `12 ell * M`), exactly as for `j >= 1`. -/
theorem cube5_in_union_print0 {ell M R k : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hA : Admissible ell M R k S) (hgt : ∀ μ : Fin 3, bigSide M ell k < L μ + 1)
    (hD : IsDCubePrint ell M k S 0 c) :
    (printedCube5 (bigSide M ell 0) c ∩ S.Om 0 = ∅) ∨
    ∃ sites : Set (PeriodicLatticeSite L),
      IsClassSetW ell M (12 * ell) k S sites 0 ∧ IsClassUnion ell M k S sites 0 ∧
      BlockClosed (bigSide M ell 0) sites ∧
      (printedCube5 (bigSide M ell 0) c ∩ S.Om 0) ⊆ sites := by
  obtain ⟨hjk, hgrid, x₀, hx0c, hx0⟩ := hD
  have hell0 : 0 < ell := by omega
  have hg0 : bigSide M ell 0 = M := bigSide_zero M ell
  have hx0n : x₀ ∉ S.Om 1 := by
    rcases hx0 with h | h
    · exact h.2
    · exact h.2
  by_cases hx0O : x₀ ∈ S.Om 0
  · right
    obtain ⟨sites, i, h1, h2, h3, h4, h5⟩ := cube5_print0_anchor_full hell hM hR hA hgt hjk hgrid x₀ hx0c hx0O hx0n
    subst h5
    exact ⟨sites, h1, h2, h3, h4⟩
  · set g := bigSide M ell 0 with hgd
    have hx0c' : x₀ ∈ cubeR c g := by rw [← dCube_eq]; exact hx0c
    have hRM : 24 * M ≤ R * M := Nat.mul_le_mul_right M (by omega)
    have hno1 : ∀ y ∈ cubeR c (7 * g), y ∉ S.Om 1 := by
      intro y hy hy1
      have hk : 1 ≤ k := by
        by_contra hk
        have := hA.2.1 1 (by omega)
        rw [this] at hy1; exact absurd hy1 (Set.notMem_empty _)
      have hd := cube_dist hx0c' hy
      have hd' : pdist x₀ y ≤ R * M := by rw [hg0] at hd; omega
      exact hx0O ((hA.2.2.2.2.2 x₀).2 ⟨y, hy1, x₀, fun μ => rfl, hd'⟩)
    have hcube7 : printedCube5 g c ⊆ cubeR c (7 * g) := by
      rw [printedCube5_eq]; exact cubeR_mono (by omega)
    by_cases hE : printedCube5 g c ∩ S.Om 0 = ∅
    · exact Or.inl hE
    · right
      obtain ⟨y₀, hy₀P, hy₀0⟩ := Set.nonempty_iff_ne_empty.2 hE
      have hy₀n : y₀ ∉ S.Om 1 := hno1 y₀ (hcube7 hy₀P)
      have hy₀c : y₀ ∈ cubeR c (6 * g) := by rw [← printedCube5_eq]; exact hy₀P
      have hNd : ∀ μ : Fin 3, M ∣ L μ + 1 := fun μ => by
        have := hA.2.2.1 0 (Nat.zero_le k) μ; rwa [bigSide_zero] at this
      have hN2 : ∀ μ : Fin 3, 2 * M ≤ L μ + 1 := fun μ => by
        obtain ⟨t, ht⟩ := hNd μ
        have h1 := hgt μ
        have hMk : M ≤ bigSide M ell k := by
          have := bigSide_mono' (M := M) hell0 (Nat.zero_le k)
          rwa [bigSide_zero] at this
        have h2 : M < M * t := by omega
        have h3 : 2 ≤ t := by
          by_contra hh; push Not at hh
          interval_cases t <;> omega
        have := Nat.mul_le_mul_left M h3
        omega
      obtain ⟨y₁, hy₁, z, hz, hzd⟩ := (hA.2.2.2.2.2 y₀).1 hy₀0
      have hk : 1 ≤ k := by
        by_contra hk
        have := hA.2.1 1 (by omega)
        rw [this] at hy₁; exact absurd hy₁ (Set.notMem_empty _)
      obtain ⟨μ, s, hs, hzs⟩ := toward_site M R z y₁ hM (by omega) hN2 hzd
      have hN2μ := hN2 μ
      have hsN : s ≤ L μ + 1 := by omega
      have hMs : M ∣ s := by
        rcases hs with rfl | h
        · exact dvd_rfl
        · have h7 := hNd μ
          have : s = (L μ + 1) - M := by omega
          rw [this]; exact Nat.dvd_sub h7 dvd_rfl
      set y' := sh y₀ μ s with hy'd
      have hy'0 : y' ∈ S.Om 0 := by
        refine (hA.2.2.2.2.2 _).2 ⟨y₁, hy₁, sh z μ s, ?_, hzs⟩
        intro ν
        by_cases hν : ν = μ
        · subst hν
          rw [hy'd, sh_self, sh_self]
          exact div_shift M (L ν + 1) (z ν).val (y₀ ν).val s hM (hNd ν) hMs (hz ν)
        · rw [hy'd, sh_ne z μ ν s hν, sh_ne y₀ μ ν s hν]; exact hz ν
      have hy'c : y' ∈ cubeR c (7 * g) :=
        sh_mem_cube2 (g := g) hy₀c (by omega) μ s (by rw [hg0]; exact hs)
      have hy'n : y' ∉ S.Om 1 := hno1 y' hy'c
      have hs0' : 0 < s := by rcases hs with rfl | h <;> omega
      have hsN' : s < L μ + 1 := by
        rcases hs with rfl | h
        · omega
        · omega
      have hdiff : (y₀ μ).val / M ≠ (y' μ).val / M := by
        have := blocks_ne M (L μ + 1) (y₀ μ).val s hM (hNd μ) hMs hs0' hsN' (y₀ μ).isLt
        rw [hy'd, sh_self]
        exact fun h => this h.symm
      have hgN : ∀ μ : Fin 3, g ∣ L μ + 1 := fun μ => by rw [hg0]; exact hNd μ
      have hgc : ∀ μ : Fin 3, g ∣ (c μ).val := fun μ => Nat.dvd_of_mod_eq_zero (hgrid μ)
      have hgpos : 0 < g := by rw [hg0]; exact hM
      let sites : Set (PeriodicLatticeSite L) :=
        {x | ∃ q : PeriodicLatticeSite L, ((q ∈ printedCube5 g c ∧ q ∈ S.Om 0) ∨ q = y') ∧
          ∀ ν : Fin 3, (q ν).val / g = (x ν).val / g}
      have hself : ∀ q, ((q ∈ printedCube5 g c ∧ q ∈ S.Om 0) ∨ q = y') → q ∈ sites :=
        fun q h => ⟨q, h, fun _ => rfl⟩
      have hQ0 : ∀ q, ((q ∈ printedCube5 g c ∧ q ∈ S.Om 0) ∨ q = y') → q ∈ S.Om 0 ∧ q ∉ S.Om 1 := by
        intro q h
        rcases h with h | h
        · exact ⟨h.2, hno1 q (hcube7 h.1)⟩
        · rw [h]; exact ⟨hy'0, hy'n⟩
      have hbc : BlockClosed g sites := by
        intro x ⟨q, hq, hxq⟩ q' hq'
        exact ⟨q, hq, fun ν => (hxq ν).trans (hq' ν).symm⟩
      have hsubB : sites ⊆ towerBj S 0 ∪ towerBj S (0 + 1) := by
        intro x ⟨q, hq, hxq⟩
        left
        have hxq' : ∀ ν : Fin 3, (x ν).val / bigSide M ell 0 = (q ν).val / bigSide M ell 0 := fun ν => (hxq ν).symm
        refine ⟨om_cell hA (le_refl 0) (hQ0 q hq).1 hxq', fun h => (hQ0 q hq).2 ?_⟩
        exact om_cell hA (show 0 ≤ 1 by omega) h hxq
      have hmeet : (sites ∩ towerBj S 0).Nonempty :=
        ⟨y₀, hself y₀ (Or.inl ⟨hy₀P, hy₀0⟩), hy₀0, hy₀n⟩
      have hbox : ∃ z : PeriodicLatticeSite L, sites ⊆ siteBox z (12 * ell * bigSide M ell 0) := by
        refine ⟨zsite c (7 * g), fun x ⟨q, hq, hxq⟩ => ?_⟩
        have hqc : q ∈ cubeR c (7 * g) := by
          rcases hq with h | h
          · exact hcube7 h.1
          · rw [h]; exact hy'c
        have hyb : q ∈ siteBox (zsite c (7 * g)) (2 * (7 * g)) := cubeR_box c (7 * g) hqc
        have hxb : x ∈ siteBox (zsite c (7 * g)) (2 * (7 * g)) :=
          siteBox_closed hgpos hgN (zsite_dvd c (7 * g) _ hgN hgc (Dvd.intro_left 7 rfl)) (Dvd.dvd.mul_left (Dvd.intro_left 7 rfl) 2) hyb
            (fun ν => (hxq ν).symm)
        refine siteBox_mono ?_ hxb
        nlinarith
      have hU : IsClassUnion ell M k S sites 0 :=
        ⟨⟨Nat.zero_le k, hbc, hsubB, hmeet⟩, fun i' hi' =>
          (union_index_unique hA.1 hsubB hmeet hi'.2.2.1 hi'.2.2.2).symm⟩
      refine ⟨sites, ⟨Nat.zero_le k, hsubB, hmeet, hbox, y₀, hself y₀ (Or.inl ⟨hy₀P, hy₀0⟩), y',
        hself y' (Or.inr rfl), μ, ?_⟩, hU, hbc, fun y hy => hself y (Or.inl hy)⟩
      rw [bigSide_zero]
      exact hdiff

end AdalyFormal.P409C5
